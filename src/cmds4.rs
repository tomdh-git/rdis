// Subsystem-scale tools: global object resolver, code-pointer tables, struct merger across calls, worklist, runtime observation import, fact porting.
use crate::cmds::{fn_arg, page, rva_arg, Args};
use crate::cmds2::callers_of;
use crate::model::{self, hx};
use crate::sym::{Tgt, E};
use crate::Ctx;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet, HashSet};

fn sgn(v: i64) -> String { if v < 0 { format!("-{:#x}", -(v as i128)) } else { format!("{:#x}", v) } }

// ---------------------------------------------------------------- gobj: what object lives in a global slot

// The vtable whose address is the first qword at `rva` in the file image (a statically initialised object), if any.
pub(crate) fn static_vtable_at(ctx: &Ctx, rva: u32) -> Option<u32> {
    let v = ctx.pe.u64_at(rva)?;
    let r = v.wrapping_sub(ctx.image_base);
    if r < 0x1_0000_0000 && ctx.vts.as_ref().unwrap().by_rva.contains_key(&(r as u32)) { Some(r as u32) } else { None }
}

// Vtables that code stores into the first qword of the static object at `obj` (its constructor runs on the global itself).
fn inline_vtable_stores(ctx: &mut Ctx, obj: u32) -> Vec<(u32, u32, u32)> {
    let refs: Vec<(u32, u32)> = ctx.xrefs().to(obj).to_vec();
    let mut funcs: BTreeSet<u32> = BTreeSet::new();
    for (_, from) in refs.iter().take(4000) { funcs.insert(ctx.fn_start(*from)); }
    let mut out = vec![];
    for f in funcs.iter().take(60) {
        let s = ctx.sum(*f);
        for a in s.accs.iter().filter(|a| a.write && a.off == 0 && a.base == E::Glob(obj)) {
            if let Some(E::Glob(v)) = &a.value { if ctx.vts.as_ref().unwrap().by_rva.contains_key(v) { out.push((*f, a.ip, *v)); } }
        }
        // constructor called with the address of the object as `this`
        for c in s.calls.iter().filter(|c| c.args.first() == Some(&E::Glob(obj))) {
            if let Tgt::Direct(ct) = &c.tgt {
                let vs: Vec<u32> = ctx.vts.as_ref().unwrap().list.iter().filter(|v| v.ctors.iter().any(|x| x.func == *ct && x.store_off == 0)).map(|v| v.rva).collect();
                for v in vs { out.push((*f, c.ip, v)); }
            }
        }
    }
    out
}

// When the symbolic value of a store is unknown (xchg, or a register the executor lost): the `lea reg,[rip+X]` that directly feeds the stored register.
fn lea_feeding_store(s: &crate::sym::Sum, ip: u32) -> Option<u32> {
    let k = s.cfg.ins.iter().position(|i| i.ip() as u32 == ip)?;
    let st = &s.cfg.ins[k];
    let reg = if st.op1_kind() == iced_x86::OpKind::Register { st.op1_register().full_register() } else { return None; };
    for j in (k.saturating_sub(4)..k).rev() {
        let i = &s.cfg.ins[j];
        if i.ip() as u32 + i.len() as u32 != s.cfg.ins[j + 1].ip() as u32 { return None; }
        if i.flow_control() != iced_x86::FlowControl::Next { return None; }
        if i.op_count() > 0 && i.op0_kind() == iced_x86::OpKind::Register && i.op0_register().full_register() == reg {
            return if i.mnemonic() == iced_x86::Mnemonic::Lea && i.is_ip_rel_memory_operand() { Some(i.ip_rel_memory_address() as u32) } else { None };
        }
    }
    None
}

pub(crate) struct GRes { pub(crate) json: Value, pub(crate) vtable: Option<u32>, pub(crate) multi: Option<String>, pub(crate) evidence: Vec<String>, pub(crate) stores: usize }

pub(crate) fn resolve_global(ctx: &mut Ctx, g: u32) -> GRes {
    let refs: Vec<(u32, u32)> = ctx.xrefs().to(g).to_vec();
    let all_funcs: BTreeSet<u32> = refs.iter().map(|(_, from)| ctx.fn_start(*from)).collect();
    // a hot global can be referenced from tens of thousands of functions: only the ones holding a WRITING instruction are analysed (decoded at the reference site)
    let mut funcs: BTreeSet<u32> = BTreeSet::new();
    let mut read_sites = 0usize;
    for (_, from) in &refs {
        let b = ctx.pe.bytes(*from, 15);
        let mut d = iced_x86::Decoder::with_ip(64, b, *from as u64, iced_x86::DecoderOptions::NONE);
        if !d.can_decode() { continue; }
        let i = d.decode();
        let writes = i.op0_kind() == iced_x86::OpKind::Memory && i.is_ip_rel_memory_operand() && !matches!(i.mnemonic(), iced_x86::Mnemonic::Cmp | iced_x86::Mnemonic::Test | iced_x86::Mnemonic::Push | iced_x86::Mnemonic::Call | iced_x86::Mnemonic::Jmp | iced_x86::Mnemonic::Bt);
        if writes { funcs.insert(ctx.fn_start(*from)); } else { read_sites += 1; }
    }
    let mut stores = vec![];
    let mut vts_found: BTreeSet<u32> = BTreeSet::new();
    let mut evidence: Vec<String> = vec![];
    let mut readers = 0usize;
    let mut nstores = 0usize;
    for f in funcs.iter().take(400) {
        let s = ctx.sum(*f);
        for a in s.accs.iter().filter(|a| a.base == E::Glob(g)) {
            if !a.write { continue; }
            nstores += 1;
            let mut item = json!({"fn": ctx.flabel(*f), "ip": hx(a.ip), "offset_in_global": sgn(a.off), "stores": a.value.as_ref().map(|v| v.to_string()).unwrap_or_else(|| "?".into())});
            match &a.value {
                // the global IS the object: its first qword is a vtable
                Some(E::Glob(v)) if ctx.vts.as_ref().unwrap().by_rva.contains_key(v) && a.off == 0 => {
                    vts_found.insert(*v);
                    item["reading"] = json!(format!("static object: vtable {} stored into the global itself (proven by the store)", hx(*v)));
                    item["kind"] = json!("inline-object");
                }
                Some(E::Ret(k)) => {
                    let ev = s.calls.iter().find(|c| c.ip == *k);
                    match ev {
                        Some(ev) => {
                            let callee = if let Tgt::Direct(t) = &ev.tgt { Some(*t) } else { None };
                            item["produced_by_call"] = json!({"ip": hx(ev.ip), "callee": callee.map(|t| ctx.flabel(t))});
                            if let Some(E::Imm(sz)) = ev.args.first() { item["alloc_size_if_allocator"] = json!(sz); }
                            let mut cands: Vec<Value> = vec![];
                            // (a) constructor call on the returned pointer
                            for c in s.calls.iter().filter(|c| c.ip > *k && c.args.first() == Some(&E::Ret(*k))) {
                                if let Tgt::Direct(ct) = &c.tgt {
                                    for v in ctx.vts.as_ref().unwrap().list.iter().filter(|v| v.ctors.iter().any(|x| x.func == *ct)) {
                                        vts_found.insert(v.rva);
                                        evidence.push(format!("call:{}->{}", hx(c.ip), hx(*ct)));
                                        cands.push(json!({"how": "constructor call on the returned pointer", "ctor": ctx.flabel(*ct), "ctor_call_ip": hx(c.ip), "vtable": hx(v.rva), "class": ctx.vt_name(v)}));
                                    }
                                }
                            }
                            // (b) the producing callee is itself a constructor (factory returning an initialised object)
                            if let Some(t) = callee {
                                for v in ctx.vts.as_ref().unwrap().list.iter().filter(|v| v.ctors.iter().any(|x| x.func == t)) {
                                    vts_found.insert(v.rva);
                                    evidence.push(format!("call:{}->{}", hx(ev.ip), hx(t)));
                                    cands.push(json!({"how": "producer is a vtable-installing constructor", "vtable": hx(v.rva), "class": ctx.vt_name(v)}));
                                }
                            }
                            // (c) vtable stored through the returned pointer in this function
                            for w in s.accs.iter().filter(|w| w.write && w.base == E::Ret(*k) && w.off == 0) {
                                if let Some(E::Glob(v)) = &w.value { if ctx.vts.as_ref().unwrap().by_rva.contains_key(v) {
                                    vts_found.insert(*v);
                                    cands.push(json!({"how": "vtable stored through the returned pointer", "at": hx(w.ip), "vtable": hx(*v), "class": ctx.vt_name(&ctx.vts.as_ref().unwrap().list[ctx.vts.as_ref().unwrap().by_rva[v]])}));
                                } }
                            }
                            item["class_candidates"] = json!(cands);
                        }
                        None => item["reading"] = json!("stored value is a call result but the call was not recovered"),
                    }
                }
                other => {
                    // address of another static object?  (lea reg,[obj]; mov/xchg [G],reg)
                    let target = match other { Some(E::Glob(x)) if !ctx.pe.is_exec(*x) => Some(*x), _ => lea_feeding_store(&s, a.ip).filter(|x| !ctx.pe.is_exec(*x)) };
                    match target {
                        Some(obj) => {
                            item["stores"] = json!(format!("&data_{:x}", obj));
                            item["kind"] = json!("address-of-static-object");
                            let mut cands: Vec<Value> = vec![];
                            if let Some(v) = static_vtable_at(ctx, obj) {
                                vts_found.insert(v);
                                evidence.push(format!("ptr:{}->{}", hx(obj), hx(v)));
                                cands.push(json!({"how": "the static object's first qword in the file image is this vtable", "object": hx(obj), "vtable": hx(v), "class": ctx.vt_name(&ctx.vts.as_ref().unwrap().list[ctx.vts.as_ref().unwrap().by_rva[&v]])}));
                            }
                            for (cf, cip, v) in inline_vtable_stores(ctx, obj) {
                                vts_found.insert(v);
                                cands.push(json!({"how": "code installs this vtable into the static object", "object": hx(obj), "in": ctx.flabel(cf), "at": hx(cip), "vtable": hx(v), "class": ctx.vt_name(&ctx.vts.as_ref().unwrap().list[ctx.vts.as_ref().unwrap().by_rva[&v]])}));
                            }
                            if cands.is_empty() { item["reading"] = json!("points at a static object whose vtable is neither in the file image nor installed by a recognised store"); }
                            item["class_candidates"] = json!(cands);
                        }
                        None => item["reading"] = json!("stored value is not a call result, vtable or static object address: origin not determined (memory is not modelled)"),
                    }
                }
            }
            stores.push(item);
        }
    }
    let mut static_init = Value::Null;
    if let Some(v0) = ctx.pe.u64_at(g) {
        let r = v0.wrapping_sub(ctx.image_base);
        if v0 != 0 && r < 0x1_0000_0000 && ctx.pe.section_of(r as u32).is_some() && !ctx.pe.is_exec(r as u32) {
            let obj = r as u32;
            let sv = static_vtable_at(ctx, obj);
            if let Some(v) = sv { vts_found.insert(v); evidence.push(format!("ptr:{}->{}", hx(g), hx(obj))); }
            static_init = json!({"points_at": hx(obj), "vtable_in_image": sv.map(hx)});
        }
    }
    evidence.sort();
    evidence.dedup();
    let vt = if vts_found.len() == 1 { vts_found.iter().next().copied() } else { None };
    let verdict = match (vts_found.len(), &vt) {
        (0, _) => json!({"trust": "unknown", "why": if nstores == 0 { "no store to this global was found in any function that references it (it may be filled by a different mechanism, e.g. memcpy, a larger enclosing struct, or an import)" } else { "stores found but none yields a vtable (producer unknown)" }}),
        (1, Some(v)) => json!({"trust": "derived", "vtable": hx(*v), "class": ctx.vt_name(&ctx.vts.as_ref().unwrap().list[ctx.vts.as_ref().unwrap().by_rva[v]]), "why": "every vtable-yielding store agrees; a derived class installing a different vtable later is not excluded"}),
        (n, _) if n <= 4 => json!({"trust": "candidate", "vtables": vts_found.iter().map(|v| hx(*v)).collect::<Vec<_>>(), "why": "the global is given different objects (static initial value and/or several stores): it holds ONE of these classes at a time, which one is a runtime fact"}),
        _ => json!({"trust": "unknown", "why": "stores disagree: more than 4 different vtables", "vtables": vts_found.iter().map(|v| hx(*v)).collect::<Vec<_>>()}),
    };
    let multi: Option<String> = if vts_found.len() >= 2 && vts_found.len() <= 4 { Some(vts_found.iter().map(|v| hx(*v)).collect::<Vec<_>>().join(",")) } else { None };
    let _ = readers;
    let json = json!({"global": hx(g), "functions_referencing": all_funcs.len(), "functions_with_a_store": funcs.len(), "non_writing_reference_sites": read_sites, "static_initial_value": static_init, "stores": stores, "verdict": verdict,
        "propose": match (&vt, &multi) { (Some(v), _) => Some(format!("assert global-type {} {} --trust derived", hx(g), hx(*v))), (None, Some(m)) => Some(format!("assert global-type {} {} --trust candidate", hx(g), m)), _ => None }});
    GRes { json, vtable: vt, multi, evidence, stores: nstores }
}

// gobj <global> [--apply]   |   gobj --fn <fn> [--depth N] [--apply]  (resolve every global behind an unresolved virtual call in fn and its callees)
pub fn cmd_gobj(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let mut targets: Vec<u32> = vec![];
    let mut scope = Value::Null;
    if let Some(f) = a.s("fn") {
        let root = crate::resolve(ctx, &[f])?;
        let root = ctx.fn_start(root);
        let depth = a.num("depth", 1);
        let mut seen: HashSet<u32> = HashSet::new();
        let mut frontier = vec![root];
        let mut gs: BTreeSet<u32> = BTreeSet::new();
        for _ in 0..=depth {
            let mut next = vec![];
            for fnn in frontier {
                if !seen.insert(fnn) { continue; }
                let s = ctx.sum(fnn);
                for c in &s.calls { if let Tgt::Slot { obj: E::Load(inner, 8), .. } = &c.tgt { if let E::Glob(g) = &**inner { gs.insert(*g); } } }
                for e in model::direct_edges(ctx, fnn).iter() { if e.kind == "call" { next.push(e.to); } }
            }
            frontier = next;
        }
        scope = json!({"fn": ctx.flabel(root), "functions_scanned": seen.len(), "globals_behind_virtual_calls": gs.len()});
        targets = gs.into_iter().collect();
    } else {
        let g = rva_arg(ctx, a, 0)?;
        if ctx.pe.is_exec(g) { return Err(format!("{:#x} is executable memory, not a global data slot", g)); }
        targets.push(g);
    }
    let apply = a.flags.contains("apply");
    let mut out = vec![];
    let mut applied = vec![];
    for g in targets.iter().take(a.num("limit", 60)) {
        let r = resolve_global(ctx, *g);
        let mut j = r.json.clone();
        if apply {
            let val: Option<(String, &str)> = match (&r.vtable, &r.multi) { (Some(v), _) => Some((hx(*v), "derived")), (None, Some(m)) => Some((m.clone(), "candidate")), _ => None };
            if let Some((v, tr)) = val {
                if ctx.db.find("global-type", &hx(*g)).is_none() {
                    let mut aa = Args::default();
                    aa.pos = vec!["global-type".into(), hx(*g), v];
                    aa.opt.insert("trust".into(), tr.into());
                    aa.opt.insert("source".into(), "gobj".into());
                    aa.opt.insert("note".into(), format!("gobj: {} store(s) agree", r.stores));
                    let ev: Vec<String> = r.evidence.iter().take(3).cloned().collect();
                    if !ev.is_empty() { aa.opt.insert("ev".into(), ev.join(",")); }
                    match crate::cmds::cmd_assert(ctx, &aa) { Ok(v) => applied.push(json!({"global": hx(*g), "result": v})), Err(e) => applied.push(json!({"global": hx(*g), "error": e})) }
                    ctx.prep();
                }
            }
        }
        j["stores_count"] = json!(r.stores);
        out.push(j);
    }
    let resolved = out.iter().filter(|j| j["verdict"]["trust"] == "derived").count();
    let narrowed = out.iter().filter(|j| j["verdict"]["trust"] == "candidate").count();
    Ok(json!({"scope": scope, "globals": out.len(), "resolved_to_one_class": resolved, "narrowed_to_a_few_classes": narrowed, "results": page(out, a, 30), "applied": applied,
        "reading": "derived = the global's initialising stores all point at one vtable (constructor call on the allocation, a vtable-installing producer, the vtable stored into the global itself, or the address of a static object whose vtable is known). `--apply` asserts global-type facts at trust derived, so later `vcalls`/`path --virt derived` use them; retract any that are wrong."}))
}

// ---------------------------------------------------------------- ptables: arrays of code pointers (handler tables, registries, vtable-like arrays that are not vtables)

pub fn cmd_ptables(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let minlen = a.num("min", 3);
    let base = ctx.image_base;
    let vt_ranges: Vec<(u32, u32)> = ctx.vts.as_ref().unwrap().list.iter().map(|v| (v.rva, v.rva + 8 * v.slots.len() as u32)).collect();
    let in_vt = |r: u32| vt_ranges.iter().any(|(b, e)| r >= *b && r < *e);
    let mut found: Vec<(u32, usize, usize)> = vec![]; // rva, count, stride
    for s in ctx.pe.sections.iter().filter(|s| s.flags & 0x2000_0000 == 0 && s.rawsize > 0) {
        let d = &ctx.pe.data[s.raw as usize..(s.raw + s.rawsize.min(s.vsize)) as usize];
        let n = d.len() / 8;
        let isfn = |k: usize| -> bool { let v = u64::from_le_bytes(d[k * 8..k * 8 + 8].try_into().unwrap()); let r = v.wrapping_sub(base); r < 0x1_0000_0000 && ctx.pe.is_function_start(r as u32) };
        let mut k = 0;
        while k < n {
            if !isfn(k) { k += 1; continue; }
            let mut best = (1usize, 1usize);
            for stride in [1usize, 2, 3, 4, 5, 6] {
                let mut c = 1;
                while k + c * stride < n && isfn(k + c * stride) { c += 1; }
                if c > best.0 || (c == best.0 && stride < best.1) { best = (c, stride); }
            }
            let (c, stride) = best;
            if c >= minlen && !in_vt(s.rva + (k * 8) as u32) { found.push((s.rva + (k * 8) as u32, c, stride * 8)); }
            k += (c * stride).max(1);
        }
    }
    let refq = match a.s("ref") { Some(r) => Some(fn_arg_str(ctx, r)?), None => None };
    let mut items = vec![];
    for (rva, c, stride) in found {
        let refs: Vec<(u32, u32)> = ctx.xrefs().to(rva).to_vec();
        let ref_fns: BTreeSet<u32> = refs.iter().map(|(_, f)| ctx.fn_start(*f)).collect();
        if let Some(q) = refq { if !ref_fns.contains(&q) { continue; } }
        let targets: Vec<Value> = (0..c.min(a.num("targets", 6))).map(|i| { let v = ctx.pe.u64_at(rva + (i * stride) as u32).unwrap_or(0).wrapping_sub(base) as u32; ctx.flabel(v) }).collect();
        items.push(json!({"table": hx(rva), "entries": c, "stride_bytes": stride, "targets_sample": targets, "referenced_by": ref_fns.iter().take(5).map(|f| ctx.flabel(*f)).collect::<Vec<_>>(), "referenced_by_count": ref_fns.len()}));
    }
    items.sort_by_key(|j| std::cmp::Reverse(j["entries"].as_u64().unwrap_or(0)));
    Ok(json!({"min_entries": minlen, "tables": page(items, a, 40),
        "reading": "runs of aligned qwords that are all .pdata function starts (also strided: one function pointer per 16/24/... byte record). Existing vtables are excluded. A run is evidence of a handler/registry table, not proof: check `referenced_by` and what indexes it.",
        "trust": "proven that each listed qword equals a function start; the role of the table is a hint"}))
}

fn fn_arg_str(ctx: &Ctx, s: &str) -> Result<u32, String> {
    let r = crate::resolve(ctx, &[s])?;
    if !ctx.pe.is_exec(r) { return Err(format!("{:#x} is not in executable memory", r)); }
    Ok(ctx.fn_start(r))
}

// ---------------------------------------------------------------- structm: one field table merged across a call tree that passes `this`

#[derive(Default)]
struct F { sizes: BTreeSet<u8>, r: u32, w: u32, fp: bool, fns: BTreeSet<u32>, vt: BTreeSet<u32>, as_ptr: bool }

// structm <fn> [--depth N] [--fnlimit N]
pub fn cmd_structm(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let root = fn_arg(ctx, a, 0)?;
    let depth = a.num("depth", 3);
    let limit = a.num("fnlimit", 300);
    let mut fields: BTreeMap<i64, F> = BTreeMap::new();
    let mut children: BTreeMap<i64, BTreeMap<i64, F>> = BTreeMap::new();
    let mut visited: HashSet<(u32, i64)> = HashSet::new();
    let mut order: Vec<(u32, i64)> = vec![];
    let mut work: Vec<(u32, i64, usize)> = vec![(root, 0, 0)];
    while let Some((f, delta, d)) = work.pop() {
        if !visited.insert((f, delta)) || visited.len() > limit { continue; }
        order.push((f, delta));
        let s = ctx.sum(f);
        for x in s.accs.iter().filter(|x| !x.indexed) {
            if x.base == E::Arg(0) {
                let e = fields.entry(x.off + delta).or_default();
                e.sizes.insert(x.size);
                if x.read { e.r += 1; }
                if x.write { e.w += 1; }
                if x.fp { e.fp = true; }
                e.fns.insert(f);
                if let Some(E::Glob(v)) = &x.value { if ctx.vts.as_ref().unwrap().by_rva.contains_key(v) { e.vt.insert(*v); } }
            } else if let E::Load(inner, 8) = &x.base {
                let (b, k) = inner.split();
                if b == E::Arg(0) {
                    fields.entry(k + delta).or_default().as_ptr = true;
                    let e = children.entry(k + delta).or_default().entry(x.off).or_default();
                    e.sizes.insert(x.size);
                    if x.read { e.r += 1; }
                    if x.write { e.w += 1; }
                    if x.fp { e.fp = true; }
                    e.fns.insert(f);
                }
            }
        }
        if d < depth {
            for c in &s.calls {
                if let Tgt::Direct(t) = &c.tgt {
                    if let Some(first) = c.args.first() {
                        let (b, k) = first.split();
                        if b == E::Arg(0) { work.push((*t, delta + k, d + 1)); }
                    }
                }
            }
        }
    }
    let mk = |o: i64, f: &F, ctx: &Ctx| json!({"off": sgn(o), "sizes": f.sizes, "type_guess": if !f.vt.is_empty() { "vtable pointer".to_string() } else if f.as_ptr { "pointer to object (dereferenced)".into() } else if f.fp { "float/vector".into() } else if f.sizes.len() == 1 && f.sizes.contains(&1) { "u8/bool/flag".into() } else if f.sizes.contains(&8) { "int64 or pointer".into() } else { "integer".into() },
        "reads": f.r, "writes": f.w, "functions": f.fns.len(), "sample_fns": f.fns.iter().take(3).map(|x| ctx.flabel(*x)).collect::<Vec<_>>(), "vtables_stored": f.vt.iter().map(|v| hx(*v)).collect::<Vec<_>>()});
    let items: Vec<Value> = fields.iter().map(|(o, f)| mk(*o, f, ctx)).collect();
    let kids: Vec<Value> = children.iter().map(|(o, m)| json!({"pointer_field": sgn(*o), "fields": m.iter().map(|(co, f)| mk(*co, f, ctx)).collect::<Vec<_>>()})).collect();
    Ok(json!({"root": ctx.flabel(root), "functions_merged": order.len(), "depth": depth, "fields": page(items, a, 150), "child_objects": page(kids, a, 40),
        "reading": "offsets are relative to the root function's a0. A callee is merged only when it receives a0 (or a0+K) as its first argument via a direct call (offsets are shifted by K). Child objects = fields loaded as a pointer and then dereferenced.",
        "trust": "derived: only direct accesses through the traced `this`; aliasing, memcpy/rep movs copies and accesses via other pointers are not seen, so a field absent here may still exist"}))
}

// ---------------------------------------------------------------- worklist: the measurable "what is left" list for a subsystem

// worklist <fn> [<fn>...] [--depth N] [--maxfan N]
pub fn cmd_worklist(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let mut seeds = vec![];
    for i in 0..a.pos.len() { seeds.push(fn_arg(ctx, a, i)?); }
    if seeds.is_empty() { return Err("worklist <fn> [<fn>...] [--depth N] [--maxfan N]".into()); }
    let depth = a.num("depth", 3);
    let maxfan = a.num("maxfan", 60);
    let mut seen: BTreeMap<u32, usize> = BTreeMap::new();
    let mut frontier: Vec<u32> = seeds.clone();
    for d in 0..=depth {
        let mut next = vec![];
        for f in frontier {
            if seen.contains_key(&f) { continue; }
            if d > 0 {
                let fan = callers_of(ctx, f).iter().map(|c| c.0).collect::<BTreeSet<_>>().len();
                if fan > maxfan { continue; } // shared utility (allocator, logger, ...): not part of the subsystem
            }
            seen.insert(f, d);
            for e in model::direct_edges(ctx, f).iter() { if e.kind == "call" { next.push(e.to); } }
        }
        frontier = next;
    }
    let mut rows = vec![];
    let (mut named, mut unnamed_str, mut unnamed_nostr) = (0, 0, 0);
    let mut unknown_vcalls_total = 0usize;
    for (f, d) in &seen {
        let s = ctx.sum(*f);
        let is_named = ctx.names.contains_key(f) || ctx.db.find("name", &hx(*f)).is_some();
        let strs: Vec<String> = s.strs.iter().map(|x| x.2.clone()).collect::<BTreeSet<_>>().into_iter().take(3).collect();
        let mut unk = 0usize;
        let mut vc = 0usize;
        for c in &s.calls { if let Tgt::Slot { .. } = &c.tgt { vc += 1; if model::resolve_vcall(ctx, &s, c).targets.is_empty() { unk += 1; } } }
        unknown_vcalls_total += unk;
        if is_named { named += 1; } else if !strs.is_empty() { unnamed_str += 1; } else { unnamed_nostr += 1; }
        let in_vt = ctx.vts.as_ref().unwrap().fn_in.contains_key(f);
        rows.push((unk, json!({"fn": ctx.flabel(*f), "depth": d, "size": s.cfg.end - s.cfg.begin, "named": is_named, "strings": strs, "virtual_calls": vc, "virtual_calls_unresolved": unk, "vtable_member": in_vt,
            "propose_name_from_string": if !is_named { strs.first().cloned() } else { None }})));
    }
    rows.sort_by_key(|r| std::cmp::Reverse(r.0));
    let total = rows.len();
    Ok(json!({"seeds": seeds.iter().map(|s| ctx.flabel(*s)).collect::<Vec<_>>(), "functions": total, "named": named, "unnamed_with_string_anchor": unnamed_str, "unnamed_without_string": unnamed_nostr,
        "unresolved_virtual_calls_total": unknown_vcalls_total, "items": page(rows.into_iter().map(|r| r.1).collect(), a, 60),
        "reading": "functions reachable from the seeds by direct calls (callees with more than --maxfan distinct callers are treated as shared utilities and skipped). Sorted by unresolved virtual calls: those are the places where the static graph is blind, resolve them with `gobj --fn`, `assert global-type`, or `observe`. Counts are the measurable remaining work.",
        "trust": "proven (direct call structure); names are only those in the names file or the overlay"}))
}

// ---------------------------------------------------------------- observe: runtime observations (Cheat Engine etc.) as `observed` facts

// observe vcall <site> <target[,target..]> [--count N] [--source S]
// observe global <global> <vtable|Class> [--count N]
// observe import <file.json>   : [{"kind":"vcall","site":"0x..","target":"0x..","count":12}, {"kind":"global","global":"0x..","class":"0x<vtable>"}]
pub fn cmd_observe(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let sub = a.pos.first().ok_or("observe vcall|global|import ...")?.clone();
    let mut done = vec![];
    let mut items: Vec<(String, String, String, u64)> = vec![]; // kind, subject, value, count
    match sub.as_str() {
        "vcall" => items.push(("edge".into(), a.pos.get(1).ok_or("observe vcall <site> <targets>")?.clone(), a.pos.get(2).ok_or("missing targets")?.clone(), a.num("count", 1) as u64)),
        "global" => items.push(("global-type".into(), a.pos.get(1).ok_or("observe global <global> <class>")?.clone(), a.pos.get(2).ok_or("missing class")?.clone(), a.num("count", 1) as u64)),
        "import" => {
            let p = a.pos.get(1).ok_or("observe import <file.json>")?;
            let t = std::fs::read_to_string(p).map_err(|e| format!("{}: {}", p, e))?;
            let v: Value = serde_json::from_str(&t).map_err(|e| e.to_string())?;
            for o in v.as_array().ok_or("expected a JSON array")? {
                let cnt = o["count"].as_u64().unwrap_or(1);
                match o["kind"].as_str() {
                    Some("vcall") => items.push(("edge".into(), o["site"].as_str().unwrap_or("").into(), o["target"].as_str().unwrap_or("").into(), cnt)),
                    Some("global") => items.push(("global-type".into(), o["global"].as_str().unwrap_or("").into(), o["class"].as_str().unwrap_or("").into(), cnt)),
                    other => done.push(json!({"skipped": o, "why": format!("unknown kind {:?}", other)})),
                }
            }
        }
        _ => return Err("observe vcall|global|import ...".into()),
    }
    for (kind, subj, val, cnt) in items {
        let mut aa = Args::default();
        aa.pos = vec![kind.clone(), subj.clone(), val.clone()];
        aa.opt.insert("trust".into(), "observed".into());
        aa.opt.insert("source".into(), a.s("source").unwrap_or("runtime").into());
        aa.opt.insert("note".into(), format!("observed {} time(s)", cnt));
        match crate::cmds::cmd_assert(ctx, &aa) { Ok(v) => done.push(json!({"subject": subj, "value": val, "result": v})), Err(e) => done.push(json!({"subject": subj, "error": e})) }
        ctx.prep();
    }
    Ok(json!({"imported": done,
        "reading": "observed facts outrank static inference in vcall resolution and are shown with trust `observed`. They are evidence about THIS run/build only: a different build needs a fresh observation. Retract with `retract <id>` if the observation was taken in a different state."}))
}

// ---------------------------------------------------------------- portfacts: carry named functions to another build

// portfacts <other-exe> [--min-trust derived]
pub fn cmd_portfacts(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let other = a.pos.first().ok_or("portfacts <other-exe>")?.clone();
    let names: Vec<(u32, String)> = ctx.db.active().iter().filter(|f| f.op == "assert" && f.kind == "name").filter_map(|f| crate::parse_hex(&f.subject).map(|r| (r, f.value.as_str().unwrap_or("").to_string()))).collect();
    let mut out = vec![];
    for (r, name) in names.iter().take(a.num("limit", 40)) {
        let mut pa = Args::default();
        pa.pos = vec![other.clone(), hx(*r)];
        match crate::cmds3::cmd_port(ctx, &pa) {
            Ok(v) => out.push(json!({"name": name, "here": hx(*r), "verdict": v["verdict"], "best_candidate": v["candidates"].get(0).map(|c| c["rva_in_other"].clone())})),
            Err(e) => out.push(json!({"name": name, "here": hx(*r), "error": e})),
        }
    }
    Ok(json!({"other_exe": other, "facts_considered": names.len(), "ported": out,
        "reading": "each named function is looked up in the other exe; only `derived` verdicts are safe to carry as candidates, `hint`/`candidate` need a second route. Nothing is asserted automatically."}))
}
