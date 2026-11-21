// New-style commands: every one returns a JSON value. Claims carry a `trust` (proven | derived | candidate | hint | agent | unknown), see docs/RDIS_V2_PLAN.md.
use crate::cfg::EKind;
use crate::db::{self, addr_key, Fact};
use crate::pe;
use crate::model::{self, hx, resolve_vcall, Res};
use crate::sym::{Acc, Tgt, E};
use crate::Ctx;
use iced_x86::{Decoder, DecoderOptions, Instruction, OpKind};
use rusqlite::params;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::thread;

#[derive(Default)]
pub struct Args { pub pos: Vec<String>, pub opt: HashMap<String, String>, pub flags: HashSet<String> }

const BOOL_FLAGS: [&str; 9] = ["r", "w", "raw", "nochains", "i", "all", "json", "text", "alt"];

pub fn tokenize(line: &str) -> Vec<String> {
    let mut out = vec![];
    let mut cur = String::new();
    let mut q = false;
    let mut any = false;
    for c in line.chars() {
        match c { '"' => { q = !q; any = true; } c if c.is_whitespace() && !q => { if !cur.is_empty() || any { out.push(std::mem::take(&mut cur)); any = false; } } c => cur.push(c) }
    }
    if !cur.is_empty() || any { out.push(cur); }
    out
}

impl Args {
    pub fn parse(toks: &[String]) -> Args {
        let mut a = Args::default();
        let mut i = 0;
        while i < toks.len() {
            let t = &toks[i];
            if let Some(n) = t.strip_prefix("--") {
                if BOOL_FLAGS.contains(&n) { a.flags.insert(n.to_string()); }
                else if i + 1 < toks.len() { a.opt.insert(n.to_string(), toks[i + 1].clone()); i += 1; }
                else { a.flags.insert(n.to_string()); }
            } else if t == "-i" { a.flags.insert("i".into()); } else { a.pos.push(t.clone()); }
            i += 1;
        }
        a
    }
    pub fn num(&self, k: &str, d: usize) -> usize { self.opt.get(k).and_then(|v| v.parse().ok()).unwrap_or(d) }
    pub fn s(&self, k: &str) -> Option<&str> { self.opt.get(k).map(|s| s.as_str()) }
}

pub fn rva_arg(ctx: &Ctx, a: &Args, i: usize) -> Result<u32, String> {
    let t = a.pos.get(i).ok_or("missing address")?;
    // a signature spans several tokens: only when every token looks like a sig byte
    let rest: Vec<&str> = a.pos[i..].iter().map(|s| s.as_str()).collect();
    let one = [t.as_str()];
    crate::resolve(ctx, if rest.len() > 1 && rest.iter().all(|t| t.starts_with('?') || (t.len() == 2 && t.chars().all(|c| c.is_ascii_hexdigit()))) { &rest } else { &one })
}

// A function argument: must be in executable memory (data and unmapped addresses are refused instead of being analysed as code).
pub fn fn_arg(ctx: &Ctx, a: &Args, i: usize) -> Result<u32, String> {
    let r = rva_arg(ctx, a, i)?;
    if !ctx.pe.is_exec(r) { return Err(format!("{:#x} is not in executable memory: not a function", r)); }
    Ok(ctx.fn_start(r))
}

pub fn page(items: Vec<Value>, a: &Args, dmax: usize) -> Value {
    let total = items.len();
    let off = a.num("offset", 0);
    let max = a.num("max", dmax);
    let shown: Vec<Value> = items.into_iter().skip(off).take(max).collect();
    let next = if off + shown.len() < total { json!(off + shown.len()) } else { Value::Null };
    json!({"total": total, "offset": off, "items": shown, "next_offset": next})
}

fn sgn(v: i64) -> String { if v < 0 { format!("-{:#x}", -(v as i128)) } else { format!("{:#x}", v) } }

fn acc_json(a: &Acc) -> Value {
    let mut v = json!({"ip": hx(a.ip), "rw": if a.read && a.write { "RW" } else if a.write { "W" } else { "R" }, "size": a.size, "base": a.base.to_string(), "off": sgn(a.off), "insn_disp": sgn(a.disp), "mn": a.mn});
    if a.fp { v["fp"] = json!(true); }
    if a.indexed { v["indexed"] = json!(true); }
    if let Some(x) = &a.value { v["value"] = json!(x.to_string()); }
    v
}

fn tgt_json(ctx: &Ctx, s: &crate::sym::Sum, ev: &crate::sym::CallEv) -> Value {
    let args = {
        let mut a = model::fmt_args(&ev.args);
        while a.last().map_or(false, |x| x == "?") { a.pop(); }
        a
    };
    let mut v = json!({"ip": hx(ev.ip), "args": args, "tail": ev.tail});
    match &ev.tgt {
        Tgt::Direct(t) => { v["kind"] = json!("direct"); v["target"] = ctx.flabel(*t); v["trust"] = json!("proven"); }
        Tgt::Global(g) => { v["kind"] = json!("indirect-global"); v["via"] = json!(hx(*g)); v["trust"] = json!("unknown(pointer value at runtime)"); }
        Tgt::Mem(e) => { v["kind"] = json!("indirect-mem"); v["via"] = json!(e.to_string()); v["trust"] = json!("unknown"); }
        Tgt::Reg(e) => { v["kind"] = json!("indirect-reg"); v["via"] = json!(e.to_string()); v["trust"] = json!("unknown"); }
        Tgt::Slot { obj, vptr_off, disp } => {
            v["kind"] = json!("vcall");
            v["obj"] = json!(obj.to_string());
            v["vptr_off"] = json!(sgn(*vptr_off));
            v["slot"] = json!(*disp / 8);
            let r: Res = resolve_vcall(ctx, s, ev);
            v["trust"] = json!(r.trust);
            v["basis"] = json!(r.basis);
            v["targets"] = json!(r.targets.iter().take(12).map(|t| ctx.flabel(*t)).collect::<Vec<_>>());
            if r.targets.len() > 12 { v["targets_total"] = json!(r.targets.len()); }
        }
    }
    v
}

pub fn cmd_sum(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let f = fn_arg(ctx, a, 0)?;
    let s = ctx.sum(f);
    let only = a.s("only");
    let want = |k: &str| only.map_or(true, |o| o == k);
    let mut out = json!({"fn": ctx.flabel(f), "range": [hx(s.cfg.begin), hx(s.cfg.end)], "extent": if s.cfg.heuristic_extent { "heuristic(no .pdata entry)" } else { "proven(.pdata)" },
        "blocks": s.cfg.blocks.len(), "blocks_reached_by_dataflow": s.reached, "notes": s.notes, "legend": "a0..a3 = rcx,rdx,r8,r9 at entry; *(x) = 8-byte load at x; &stk = stack address; ret@ip = result of the call at ip; typed<N>@ip = result of the call at ip that was passed the 32-bit type hash of N (for entt this is the registry's storage/pool for N, NOT a component instance: do not read its fields as component fields)"});
    if want("calls") { out["calls"] = page(s.calls.iter().map(|e| tgt_json(ctx, &s, e)).collect(), a, 80); }
    if want("fields") {
        let mut agg: BTreeMap<(String, i64), (u32, u32, BTreeSet<u8>, u32, bool)> = BTreeMap::new();
        for x in &s.accs { if x.indexed { continue; } let e = agg.entry((x.base.to_string(), x.off)).or_insert((0, 0, BTreeSet::new(), x.ip, false)); if x.read { e.0 += 1; } if x.write { e.1 += 1; } e.2.insert(x.size); e.4 |= x.fp; }
        out["fields"] = page(agg.into_iter().map(|((b, o), (r, w, sz, ip, fp))| json!({"base": b, "off": sgn(o), "reads": r, "writes": w, "sizes": sz, "first_ip": hx(ip), "fp": fp})).collect(), a, 100);
    }
    if want("raw") || a.flags.contains("raw") { out["accesses"] = page(s.accs.iter().map(acc_json).collect(), a, 100); }
    if want("conds") { let mut c: Vec<_> = s.conds.values().collect(); c.sort_by_key(|x| x.ip); out["conds"] = page(c.into_iter().map(|c| json!({"ip": hx(c.ip), "if_taken": c.taken, "if_not_taken": c.not_taken, "setter": c.setter.map(hx), "exact": c.exact})).collect(), a, 60); }
    if want("strings") { out["strings"] = page(s.strs.iter().map(|(ip, ad, t)| json!({"ip": hx(*ip), "addr": hx(*ad), "text": t, "trust": "hint(string referenced by this function; not necessarily its name)"})).collect(), a, 30); }
    if want("comps") { out["components"] = json!(s.comp_refs.iter().map(|(ip, n)| json!({"ip": hx(*ip), "name": n, "trust": "derived(imm32 equals FNV-1a of the name)"})).collect::<Vec<_>>()); }
    if want("rets") { out["returns"] = json!(s.rets.iter().map(|(ip, e)| json!({"ip": hx(*ip), "rax": e.to_string()})).collect::<Vec<_>>()); }
    if want("stack") {
        let mut entries: Vec<(u32, Value)> = s.stack_slots.iter().flat_map(|(off, uses)| {
            uses.iter().map(move |u| (u.ip, json!({"ip": hx(u.ip), "kind": u.kind, "size": u.size, "offset": sgn(*off), "value": u.value})))
        }).collect();
        entries.sort_by_key(|(ip, _)| *ip);
        out["stack_slots"] = json!(entries.into_iter().map(|(_, v)| v).collect::<Vec<_>>());
    }
    if !s.cfg.switches.is_empty() { out["switches"] = json!(s.cfg.switches.iter().map(|w| json!({"ip": hx(w.ip), "table": hx(w.table), "cases": w.entries.len(), "bound": w.bound, "trust": if w.bound == "cmp-bound" { "proven" } else { "heuristic(scanned until an entry left the function)" }})).collect::<Vec<_>>()); }
    if !s.cfg.tail_calls.is_empty() { out["tail_jumps"] = json!(s.cfg.tail_calls.iter().map(|(ip, t)| json!({"ip": hx(*ip), "to": ctx.flabel(*t)})).collect::<Vec<_>>()); }
    Ok(out)
}

fn edge_cond(s: &crate::sym::Sum, term_ip: u32, k: EKind, cases: &[u32]) -> String {
    match k {
        EKind::Taken => s.conds.get(&term_ip).map_or("?".into(), |c| c.taken.clone()),
        EKind::NotTaken => s.conds.get(&term_ip).map_or("?".into(), |c| c.not_taken.clone()),
        EKind::Case => format!("switch@{:x} index in {:?}", term_ip, cases),
        EKind::Jmp => "jmp".into(),
        EKind::Fall => "fallthrough".into(),
    }
}

pub fn cmd_cfg(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let f = fn_arg(ctx, a, 0)?;
    let s = ctx.sum(f);
    let blocks: Vec<Value> = s.cfg.blocks.values().map(|b| json!({"start": hx(b.start), "end": hx(b.end), "term": hx(b.term_ip),
        "succ": b.succ.iter().map(|e| json!({"to": hx(e.to), "kind": format!("{:?}", e.kind), "cond": edge_cond(&s, b.term_ip, e.kind, &e.case), "outside": e.outside})).collect::<Vec<_>>()})).collect();
    Ok(json!({"fn": ctx.flabel(f), "extent": if s.cfg.heuristic_extent { "heuristic" } else { "proven(.pdata)" }, "unresolved": s.cfg.unresolved.iter().map(|(ip, w)| json!({"ip": hx(*ip), "why": w})).collect::<Vec<_>>(),
        "assumption": "calls are assumed to return (adds paths, never removes), so 'gates' are sound necessary conditions", "blocks": page(blocks, a, 120)}))
}

pub fn gates_of(ctx: &Ctx, s: &crate::sym::Sum, ip: u32) -> Value {
    let _ = ctx;
    let blk = match s.cfg.block_of(ip) { Some(b) => b.start, None => return json!({"error": "ip not in function"}) };
    if !s.cfg.reach_without(blk, None, None) { return json!({"reachable": false, "note": "block not reachable from the entry in this CFG (behind an unresolved indirect jump or dead)"}); }
    let g = s.cfg.gates(blk);
    let items: Vec<Value> = g.iter().map(|(bs, ei)| {
        let b = &s.cfg.blocks[bs];
        let e = &b.succ[*ei];
        json!({"branch_ip": hx(b.term_ip), "edge": format!("{:?}", e.kind), "must_hold": edge_cond(s, b.term_ip, e.kind, &e.case), "exact_flags": s.conds.get(&b.term_ip).map_or(true, |c| c.exact), "trust": "derived(necessary edge: removing it disconnects the block)"})
    }).collect();
    json!({"reachable": true, "block": hx(blk), "gates": items})
}

pub fn cmd_gates(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let f = fn_arg(ctx, a, 0)?;
    let ip = crate::parse_hex(a.pos.get(1).ok_or("gates <fn> <ip>")?).ok_or("bad ip")?;
    let s = ctx.sum(f);
    let mut v = gates_of(ctx, &s, ip);
    v["fn"] = ctx.flabel(f);
    v["ip"] = json!(hx(ip));
    Ok(v)
}

// ---- path / reach

pub fn bfs(ctx: &Ctx, from: u32, to: Option<u32>, mode: &str, depth: usize, banned: &HashSet<(u32, u32)>, cap: usize) -> (HashMap<u32, (u32, model::Edge, usize)>, bool) { bfs_skip(ctx, from, to, mode, depth, banned, cap, None) }

pub fn bfs_skip(ctx: &Ctx, from: u32, to: Option<u32>, mode: &str, depth: usize, banned: &HashSet<(u32, u32)>, cap: usize, skip: Option<u32>) -> (HashMap<u32, (u32, model::Edge, usize)>, bool) {
    let mut parent: HashMap<u32, (u32, model::Edge, usize)> = HashMap::new();
    let mut seen: HashSet<u32> = HashSet::new();
    seen.insert(from);
    let mut q = VecDeque::new();
    q.push_back((from, 0usize));
    while let Some((f, d)) = q.pop_front() {
        if Some(f) == to { return (parent, true); }
        if d >= depth || seen.len() > cap { continue; }
        for e in model::all_edges(ctx, f, mode) {
            let t = ctx.fn_start(e.to);
            if banned.contains(&(f, t)) || Some(t) == skip || !seen.insert(t) { continue; }
            parent.insert(t, (f, e, d + 1));
            q.push_back((t, d + 1));
        }
    }
    let hit = to.map_or(false, |t| parent.contains_key(&t));
    (parent, hit)
}

pub fn cmd_path(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let from = crate::cmds::fn_arg(ctx, a, 0)?;
    let to = crate::cmds::fn_arg(ctx, a, 1)?;
    let mode = a.s("virt").unwrap_or("none").to_string();
    let depth = a.num("depth", 8);
    let k = a.num("k", 3);
    let cap = a.num("cap", 400_000);
    let mut banned: HashSet<(u32, u32)> = HashSet::new();
    let mut paths: Vec<Value> = vec![];
    let mut tried: Vec<Vec<(u32, u32)>> = vec![];
    let mut queue: Vec<HashSet<(u32, u32)>> = vec![banned.clone()];
    while let Some(b) = queue.pop() {
        if paths.len() >= k { break; }
        let (parent, hit) = bfs(ctx, from, Some(to), &mode, depth, &b, cap);
        if !hit { continue; }
        let mut hops = vec![];
        let mut cur = to;
        let mut key = vec![];
        while cur != from { let (p, e, _) = &parent[&cur]; hops.push((*p, e.clone(), cur)); key.push((*p, cur)); cur = *p; }
        hops.reverse(); key.reverse();
        if tried.contains(&key) { continue; }
        tried.push(key.clone());
        let hv: Vec<Value> = hops.iter().map(|(p, e, c)| {
            let s = ctx.sum(*p);
            let g = gates_of(ctx, &s, e.site);
            json!({"from": ctx.flabel(*p), "to": ctx.flabel(*c), "site": hx(e.site), "kind": e.kind, "trust": e.trust, "gates": g})
        }).collect();
        paths.push(json!({"length": hv.len(), "hops": hv}));
        for kk in &key { let mut nb = b.clone(); nb.insert(*kk); queue.push(nb); }
        banned = b;
    }
    Ok(json!({"from": ctx.flabel(from), "to": ctx.flabel(to), "edge_mode": mode, "max_depth": depth,
        "note": "none = direct calls/tail-jumps only (proven). derived/cand/slot add virtual-call edges of that trust. A missing path means 'none found in this edge set', not 'impossible'.", "paths": paths}))
}

pub fn cmd_reach(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let from = crate::cmds::fn_arg(ctx, a, 0)?;
    let mode = a.s("virt").unwrap_or("none").to_string();
    let depth = a.num("depth", 4);
    let (parent, _) = bfs(ctx, from, None, &mode, depth, &HashSet::new(), a.num("cap", 200_000));
    let mut by_depth: BTreeMap<usize, usize> = BTreeMap::new();
    for (_, (_, _, d)) in &parent { *by_depth.entry(*d).or_default() += 1; }
    let mut items: Vec<(usize, u32)> = parent.iter().map(|(k, (_, _, d))| (*d, *k)).collect();
    items.sort();
    Ok(json!({"from": ctx.flabel(from), "edge_mode": mode, "count_by_depth": by_depth, "functions": page(items.into_iter().map(|(d, f)| { let mut l = ctx.flabel(f); l["depth"] = json!(d); l }).collect(), a, 100)}))
}

// ---- classes

pub fn find_vts(ctx: &Ctx, q: &str) -> Vec<usize> {
    let vts = ctx.vts.as_ref().unwrap();
    if let Some(r) = crate::parse_hex(q) { if let Some(i) = vts.by_rva.get(&r) { return vec![*i]; } }
    let ql = q.to_lowercase();
    vts.list.iter().enumerate().filter(|(_, v)| ctx.vt_name(v).to_lowercase() == ql).map(|(i, _)| i).chain(
        vts.list.iter().enumerate().filter(|(_, v)| ctx.vt_name(v).to_lowercase() != ql && ctx.vt_name(v).to_lowercase().contains(&ql)).map(|(i, _)| i)).collect()
}

fn vt_json(ctx: &Ctx, v: &model::Vt, full: bool) -> Value {
    let mut j = json!({"vtable": hx(v.rva), "name": ctx.vt_name(v), "name_trust": ctx.vt_name_trust(v), "slots": v.slots.len(), "slots_end": v.end,
        "evidence": v.ctors.iter().take(3).map(|c| json!({"fn": ctx.flabel(c.func), "lea_ip": hx(c.lea_ip), "store_ip": hx(c.store_ip), "store_off": sgn(c.store_off)})).collect::<Vec<_>>(), "ctor_sites": v.ctors.len()});
    if let Some(r) = &v.rtti { j["rtti"] = json!({"mangled": r.mangled, "bases": r.bases, "col": hx(r.col), "trust": "proven(COL signature+pSelf validated)"}); }
    if full { j["slot_targets"] = json!(v.slots.iter().enumerate().map(|(i, t)| { let mut l = ctx.flabel(*t); l["slot"] = json!(i); l["size"] = json!(ctx.pe.function_of(*t).map(|(b, e)| e - b)); l }).collect::<Vec<_>>()); }
    j
}

pub fn cmd_classes(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let flt = a.pos.first().map(|s| s.to_lowercase());
    let vts = ctx.vts.as_ref().unwrap();
    let mut items = vec![];
    for v in &vts.list {
        let n = ctx.vt_name(v);
        if let Some(f) = &flt { if !n.to_lowercase().contains(f) && !hx(v.rva).contains(f.as_str()) { continue; } }
        if a.flags.contains("rtti") && v.rtti.is_none() { continue; }
        items.push(vt_json(ctx, v, false));
    }
    Ok(json!({"note": "RTTI is stripped for most game classes in this build; a vtable is identified by a code that stores its address into an object. Names are RTTI, or agent-assigned via `assert class`.", "classes": page(items, a, 60)}))
}

pub fn cmd_class(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let q = a.pos.first().ok_or("class <vtable|name>")?;
    let hits = find_vts(ctx, q);
    if hits.is_empty() { return Err(format!("no vtable matches '{}'", q)); }
    let vts = ctx.vts.as_ref().unwrap();
    Ok(json!({"matches": hits.len(), "classes": hits.iter().take(5).map(|i| vt_json(ctx, &vts.list[*i], true)).collect::<Vec<_>>()}))
}

pub fn cmd_vslot(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let slot: usize = a.pos.first().and_then(|s| s.parse().ok()).ok_or("vslot <slot> [--of class]")?;
    let vts = ctx.vts.as_ref().unwrap();
    let m = model::slot_targets(ctx, slot);
    let of: Option<HashSet<usize>> = a.s("of").map(|q| find_vts(ctx, q).into_iter().collect());
    let mut items: Vec<Value> = vec![];
    for (t, cls) in m {
        if let Some(o) = &of { if !cls.iter().any(|c| o.contains(c)) { continue; } }
        let mut l = ctx.flabel(t);
        l["used_by_vtables"] = json!(cls.len());
        l["classes"] = json!(cls.iter().take(8).map(|i| ctx.vt_name(&vts.list[*i])).collect::<Vec<_>>());
        items.push(l);
    }
    items.sort_by_key(|v| std::cmp::Reverse(v["used_by_vtables"].as_u64().unwrap_or(0)));
    Ok(json!({"slot": slot, "byte_offset": sgn(slot as i64 * 8), "distinct_targets": page(items, a, 40)}))
}

pub fn cmd_vcalls(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let f = rva_arg(ctx, a, 0)?;
    let s = ctx.sum(f);
    let items: Vec<Value> = s.calls.iter().filter(|e| matches!(e.tgt, Tgt::Slot { .. })).map(|e| tgt_json(ctx, &s, e)).collect();
    Ok(json!({"fn": ctx.flabel(f), "vcalls": page(items, a, 80)}))
}

// ---- scans returning instruction addresses

pub fn scan_map<F: Fn(&Instruction) -> Option<u32> + Sync>(ctx: &Ctx, pred: F) -> Vec<(u32, u32)> {
    let threads = thread::available_parallelism().map_or(4, |n| n.get());
    let pe = &ctx.pe;
    let chunk = (pe.ranges.len() + threads - 1) / threads;
    let mut hits = vec![];
    let predr = &pred;
    thread::scope(|s| {
        let hs: Vec<_> = pe.ranges.chunks(chunk.max(1)).map(|rs| s.spawn(move || {
            let mut out = vec![];
            let mut ins = Instruction::default();
            for r in rs {
                if !pe.is_exec(r.begin) { continue; }
                let mut dec = Decoder::with_ip(64, pe.bytes(r.begin, (r.end - r.begin) as usize), r.begin as u64, DecoderOptions::NONE);
                while dec.can_decode() { dec.decode_out(&mut ins); if let Some(p) = predr(&ins) { out.push((ins.ip() as u32, p)); } }
            }
            out
        })).collect();
        for h in hs { hits.extend(h.join().unwrap()); }
    });
    hits.sort_unstable();
    hits
}

pub fn scan_insns<F: Fn(&Instruction) -> bool + Sync>(ctx: &Ctx, pred: F) -> Vec<u32> { scan_map(ctx, |i| if pred(i) { Some(0) } else { None }).into_iter().map(|x| x.0).collect() }

fn has_imm32(ins: &Instruction, v: u32) -> bool {
    (0..ins.op_count()).any(|k| matches!(ins.op_kind(k), OpKind::Immediate32 | OpKind::Immediate32to64) && ins.immediate(k) as u32 == v)
}

fn comp_hash(ctx: &Ctx, name: &str) -> u32 { let h = model::fnv1a(name); let _ = ctx; h }

pub fn comp_functions(ctx: &Ctx, name: &str) -> Vec<u32> {
    let h = comp_hash(ctx, name);
    let mut fs: BTreeSet<u32> = BTreeSet::new();
    for ip in scan_insns(ctx, |i| has_imm32(i, h)) { fs.insert(ctx.fn_start(ip)); }
    fs.into_iter().collect()
}

pub fn class_functions(ctx: &Ctx, q: &str) -> Vec<u32> {
    let vts = ctx.vts.as_ref().unwrap();
    let mut fs: BTreeSet<u32> = BTreeSet::new();
    for i in find_vts(ctx, q).into_iter().take(1) { for t in &vts.list[i].slots { fs.insert(*t); } }
    fs.into_iter().collect()
}

fn base_matches(b: &E, comp: Option<&str>, this: bool) -> bool {
    match (b, comp) { (E::Comp(n, _), Some(c)) => n == c, (E::Arg(0), _) if this => true, _ => false }
}

// ---- rw / struct / system

pub fn cmd_rw(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let off = i64::from_str_radix(a.pos.first().ok_or("rw <off> [--comp N|--class C|--fn F]")?.trim_start_matches("0x").trim_start_matches('+'), 16).map_err(|e| e.to_string())?;
    if off > 0x10000 { return Err(format!("displacement {:#x} is larger than 0x10000; this looks like a function address, not a field offset. fld/rw expect small field displacements (e.g. 0xE0). Use `fn` or `callees` for function addresses.", off)); }
    let (fns, comp, this, scope): (Vec<u32>, Option<String>, bool, String) = if let Some(c) = a.s("comp") { (comp_functions(ctx, c), None, false, format!("functions that use the type hash of {} (scope only: the base of an access is NOT tied to the component, see `sum` legend)", c)) }
        else if let Some(c) = a.s("class") { (class_functions(ctx, c), None, true, format!("vtable members of {}", c)) }
        else if let Some(f) = a.s("fn") { let r = crate::resolve(ctx, &[f])?; (vec![r], None, false, "one function".into()) }
        else {
            let mut set = BTreeSet::new();
            for ip in scan_insns(ctx, |i| (0..i.op_count()).any(|k| i.op_kind(k) == OpKind::Memory && !i.is_ip_rel_memory_operand() && i.memory_displacement64() as i64 == off)) { set.insert(ctx.fn_start(ip)); }
            (set.into_iter().collect(), None, false, "every function touching [reg+off] (base expression shown, not typed)".into())
        };
    let (rd, wr) = (!a.flags.contains("w"), !a.flags.contains("r"));
    let limit = a.num("fnlimit", 150);
    let mut items = vec![];
    let total_fns = fns.len();
    for f in fns.iter().take(limit) {
        let s = ctx.sum(*f);
        let hits: Vec<Value> = s.accs.iter().filter(|x| x.off == off && !x.indexed && ((x.write && wr) || (!x.write && rd)) && (comp.is_none() && !this || base_matches(&x.base, comp.as_deref(), this))).map(|x| {
            let mut j = acc_json(x);
            if a.flags.contains("gates") { j["gates"] = gates_of(ctx, &s, x.ip); }
            j
        }).collect();
        if !hits.is_empty() { items.push(json!({"fn": ctx.flabel(*f), "accesses": hits})); }
    }
    Ok(json!({"offset": sgn(off), "scope": scope, "functions_in_scope": total_fns, "functions_analysed": total_fns.min(limit), "results": page(items, a, 60),
        "trust": "each access is proven from the instruction; the base-expression typing is derived (see `sum` legend)"}))
}

pub fn cmd_struct(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let q = a.pos.first().ok_or("struct comp:<Name> | <class>")?.clone();
    if q.starts_with("comp:") { return Err("struct comp:<Name> is not supported: component instances are reached through inlined sparse-set lookups, so the tool cannot prove which pointer is the instance. Use `comp <Name>` (users, proven) and `sum <fn>`; record layouts you establish with `assert field Type+0xOFF name`.".into()); }
    let (fns, comp, this, label) = (class_functions(ctx, &q), None::<String>, true, format!("class {} (this = a0 in its vtable members)", q));
    #[derive(Default)]
    struct F { sizes: BTreeSet<u8>, kinds: BTreeSet<&'static str>, r: u32, w: u32, fns: BTreeSet<u32>, vals: BTreeSet<String> }
    let mut fields: BTreeMap<i64, F> = BTreeMap::new();
    let limit = a.num("fnlimit", 400);
    for f in fns.iter().take(limit) {
        let s = ctx.sum(*f);
        for x in s.accs.iter().filter(|x| !x.indexed && base_matches(&x.base, comp.as_deref(), this)) {
            let e = fields.entry(x.off).or_default();
            e.sizes.insert(x.size);
            e.kinds.insert(if x.fp { "float/vector" } else if x.size == 8 { "int64/ptr" } else { "int" });
            if x.read { e.r += 1; } if x.write { e.w += 1; }
            e.fns.insert(*f);
            if let Some(Value::String(_)) = None::<Value> {}
            if let Some(v) = &x.value { if let E::Glob(g) = v { if ctx.vts.as_ref().unwrap().by_rva.contains_key(g) { e.vals.insert(format!("vtable {}", hx(*g))); } } }
        }
    }
    let declared: Vec<Value> = ctx.db.active().iter().filter(|f| f.op == "assert" && f.kind == "field" && f.subject.starts_with(&format!("{}+", q))).map(|f| json!({"subject": f.subject, "value": f.value, "trust": f.trust, "id": f.id})).collect();
    let items: Vec<Value> = fields.into_iter().map(|(o, f)| json!({"off": sgn(o), "sizes": f.sizes, "kinds": f.kinds, "reads": f.r, "writes": f.w, "functions": f.fns.len(), "sample_fns": f.fns.iter().take(4).map(|x| ctx.flabel(*x)).collect::<Vec<_>>(), "stores": f.vals})).collect();
    Ok(json!({"struct": label, "functions_in_scope": fns.len(), "functions_analysed": fns.len().min(limit), "declared_by_agent": declared, "fields": page(items, a, 120),
        "trust": "derived: only offsets some analysed function touches directly through the base; nested objects and other functions' accesses are not included"}))
}

pub fn cmd_system(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let f = rva_arg(ctx, a, 0)?;
    let s = ctx.sum(f);
    let mut by: BTreeMap<String, (BTreeSet<u32>, BTreeMap<i64, (u32, u32, BTreeSet<u8>)>)> = BTreeMap::new();
    for (ip, n) in &s.comp_refs { by.entry(n.clone()).or_default().0.insert(*ip); }
    for x in &s.accs { if let E::Comp(n, _) = &x.base { if x.indexed { continue; } let e = by.entry(n.clone()).or_default().1.entry(x.off).or_insert((0, 0, BTreeSet::new())); if x.read { e.0 += 1; } if x.write { e.1 += 1; } e.2.insert(x.size); } }
    let comps: Vec<Value> = by.into_iter().map(|(n, (refs, fl))| json!({"component": n, "hash": hx(model::fnv1a(&n)), "hash_refs": refs.iter().map(|x| hx(*x)).collect::<Vec<_>>(),
        "fields": fl.into_iter().map(|(o, (r, w, sz))| json!({"off": sgn(o), "reads": r, "writes": w, "sizes": sz})).collect::<Vec<_>>(),
        "trust": "hash_refs proven (imm32 == FNV-1a of the name). fields: accesses through the value a call returned when given the hash (the storage/pool, not an instance)"})).collect();
    Ok(json!({"fn": ctx.flabel(f), "components": comps, "callees_direct": model::direct_edges(ctx, f).len()}))
}

pub fn cmd_comp(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let n = a.pos.first().ok_or("comp <TypeName>")?;
    let fns = comp_functions(ctx, n);
    let known = ctx.comps.as_ref().unwrap().contains_key(&model::fnv1a(n));
    // component size: after the `mov edx, <hash>` / call-to-assure pair the engine scales the index by the element size (`imul reg, reg, imm`); T10 W6: a size mismatch breaks even when the hash matches
    let hash = model::fnv1a(n);
    let mut sizes: BTreeMap<u32, u32> = BTreeMap::new();
    for f in fns.iter().take(200) {
        let s = ctx.sum(*f);
        let ranges: Vec<(u32, u32)> = std::iter::once((s.cfg.begin, s.cfg.end)).chain(s.cfg.ranges.iter().map(|r| (r.0, r.1))).collect();
        for (b, e) in ranges {
            let bytes = ctx.pe.bytes(b, e.saturating_sub(b) as usize).to_vec();
            let mut d = Decoder::with_ip(64, &bytes, b as u64, DecoderOptions::NONE);
            let mut after: Option<usize> = None;
            let mut k = 0usize;
            while d.can_decode() {
                let i = d.decode();
                k += 1;
                if (0..i.op_count()).any(|x| matches!(i.op_kind(x), OpKind::Immediate32 | OpKind::Immediate32to64) && i.immediate(x) as u32 == hash) { after = Some(k); }
                if let Some(a0) = after {
                    if k > a0 + 20 { after = None; }
                    else if i.mnemonic() == iced_x86::Mnemonic::Imul && i.op_count() == 3 && matches!(i.op_kind(2), OpKind::Immediate8 | OpKind::Immediate8to32 | OpKind::Immediate32 | OpKind::Immediate8to64 | OpKind::Immediate32to64) { *sizes.entry(i.immediate(2) as u32).or_default() += 1; after = None; }
                }
            }
        }
    }
    Ok(json!({"name": n, "hash": hx(hash), "name_seen_in_image": known, "size_candidates_from_imul_after_hash": sizes.iter().map(|(sz, c)| json!({"bytes": sz, "sites": c})).collect::<Vec<_>>(),
        "size_note": "hint: an imul-by-immediate within 20 instructions after the hash use; several distinct values mean unrelated multiplies were caught, zero means a zero-size tag component or an inlined/unscaled access", "functions": page(fns.iter().map(|f| ctx.flabel(*f)).collect(), a, 120),
        "trust": "proven: each function contains an imm32 equal to the FNV-1a hash (collision with an unrelated constant is possible but unlikely)"}))
}

// ---------------------------------------------------------------- bench: speed benchmarking

pub fn cmd_bench(ctx: &mut Ctx, _a: &Args) -> Result<Value, String> {
    let mut phases: Vec<Value> = vec![];
    let total_start = std::time::Instant::now();

    // Phase 1: PE load (time a reload)
    let t0 = std::time::Instant::now();
    let _pe2 = crate::pe::Pe::load(&ctx.exe);
    let load_ms = t0.elapsed().as_millis();
    phases.push(json!({"phase": "pe_load", "ms": load_ms}));

    // Phase 2: xref index (collect data under &mut, release before JSON build)
    let (xr_pairs, xr_ms) = {
        let t0 = std::time::Instant::now();
        let xr = ctx.xrefs();
        let n = xr.pairs.len();
        (n, t0.elapsed().as_millis())
    };
    phases.push(json!({"phase": "xref_index", "ms": xr_ms, "pairs": xr_pairs}));

    // Phase 3: vtable discovery
    let (vt_count, vt_ms) = {
        let t0 = std::time::Instant::now();
        ctx.prep();
        let vts = ctx.vts.as_ref().unwrap();
        let n = vts.list.len();
        (n, t0.elapsed().as_millis())
    };
    phases.push(json!({"phase": "vtables", "ms": vt_ms, "count": vt_count}));

    // Phase 4: sum on a few functions (collect fn list under &mut, then time sums)
    let (roots, image, image_base, fn_count) = {
        let roots: Vec<u32> = ctx.pe.ranges.iter().filter(|r| r.root == r.begin).take(10).map(|r| r.begin).collect();
        (roots, ctx.exe.clone(), ctx.image_base, ctx.pe.ranges.iter().filter(|r| r.root == r.begin).count())
    };
    let mut sum_ms_total = 0u128;
    let mut sum_count = 0u64;
    for r in &roots {
        let t0 = std::time::Instant::now();
        let _s = ctx.sum(*r);
        sum_ms_total += t0.elapsed().as_millis();
        sum_count += 1;
    }
    let sum_ms = if sum_count > 0 { sum_ms_total / sum_count as u128 } else { 0 };
    phases.push(json!({"phase": "sum_per_fn", "ms": sum_ms, "count": sum_count}));

    let total_ms = total_start.elapsed().as_millis();

    Ok(json!({
        "bench": {
            "total_ms": total_ms,
            "phases": phases,
            "image": image,
            "image_base": format!("{:#x}", image_base),
            "functions_pdata": fn_count,
            "vtables_discovered": vt_count,
            "xref_pairs": xr_pairs,
        },
        "note": "compare against IDA's 15-20 minutes for the same exe. rdis should be seconds.",
    }))
}

// ---- overlay commands

fn norm_subject(ctx: &Ctx, kind: &str, s: &str) -> Result<String, String> {
    match kind {
        "name" | "class" | "comment" | "edge" | "no-edge" | "global-type" => Ok(addr_key(crate::resolve(ctx, &[s])?)),
        _ => Ok(s.to_string()),
    }
}

pub fn cmd_assert(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let kind = a.pos.first().ok_or("assert <kind> <subject> <value...> [--trust t] [--ev e1,e2] [--note text] [--supersede id]")?.clone();
    let subj_raw = a.pos.get(1).ok_or("missing subject")?.clone();
    let subject = norm_subject(ctx, &kind, &subj_raw)?;
    let value = a.pos[2..].join(" ");
    if value.is_empty() && kind != "note" { return Err("missing value".into()); }
    let mut evidence: Vec<String> = a.s("ev").map(|e| e.split(',').map(|x| x.trim().to_string()).collect()).unwrap_or_default();
    if kind == "name" { if let Some(r) = crate::parse_hex(&subject) { if ctx.pe.is_function_start(r) { evidence.push(format!("fn:{}", subject)); } } }
    ctx.prep();
    for e in &evidence {
        let (st, d) = db::check_evidence(ctx, e);
        if st == "bad" || st == "BROKEN" { return Err(format!("evidence '{}' is rejected: {} ({}); evidence must hold in the binary right now", e, if st == "bad" { "malformed" } else { "does not hold" }, d)); }
    }
    let f = Fact { id: 0, ts: 0, op: "assert".into(), kind: kind.clone(), subject: subject.clone(), value: Value::String(value), trust: a.s("trust").unwrap_or("agent").into(), source: a.s("source").unwrap_or("agent").into(), evidence, note: a.s("note").unwrap_or("").into(), target: a.s("supersede").and_then(|s| s.parse().ok()) };
    let id = ctx.db.append(f);
    ctx.invalidate();
    Ok(json!({"asserted": id, "kind": kind, "subject": subject, "epoch": ctx.db.epoch, "note": "derived caches were invalidated; later answers use this fact"}))
}

pub fn cmd_retract(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    let id: u64 = a.pos.first().and_then(|s| s.parse().ok()).ok_or("retract <fact id>")?;
    let old = ctx.db.conn.query_row("SELECT * FROM facts WHERE id = ?1", params![id as i64], Fact::from_row).ok().ok_or("no such fact id")?;
    let f = Fact { id: 0, ts: 0, op: "retract".into(), kind: old.kind.clone(), subject: old.subject.clone(), value: Value::Null, trust: "agent".into(), source: "agent".into(), evidence: vec![], note: a.s("note").unwrap_or("").into(), target: Some(id) };
    ctx.db.append(f);
    ctx.invalidate();
    Ok(json!({"retracted": id, "subject": old.subject, "epoch": ctx.db.epoch}))
}

pub fn cmd_contest(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    let key = a.pos.first().ok_or("contest <derived key>  e.g. edge:0xSITE->0xTARGET | vtable:0xRVA")?.clone();
    let f = Fact { id: 0, ts: 0, op: "contest".into(), kind: "contest".into(), subject: key.clone(), value: Value::Null, trust: "agent".into(), source: "agent".into(), evidence: a.s("ev").map(|e| e.split(',').map(|x| x.to_string()).collect()).unwrap_or_default(), note: a.s("note").unwrap_or("").into(), target: None };
    let id = ctx.db.append(f);
    ctx.invalidate();
    Ok(json!({"contested": key, "id": id, "epoch": ctx.db.epoch}))
}

pub fn cmd_facts(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    let kind = a.pos.first().cloned();
    let items: Vec<Value> = ctx.db.active().iter().filter(|f| kind.as_ref().map_or(true, |k| &f.kind == k)).map(|f| f.to_json()).collect();
    Ok(json!({"epoch": ctx.db.epoch, "journal": ctx.db.path.display().to_string(), "facts": page(items, a, 100)}))
}

pub fn cmd_why(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let raw = a.pos.first().ok_or("why <addr|key>")?;
    let (subject, rva) = match crate::resolve(ctx, &[raw.as_str()]) { Ok(r) => (addr_key(r), Some(r)), Err(_) => (raw.clone(), None) };
    let mut derived = vec![];
    if let Some(r) = rva {
        if let Some(n) = ctx.names.get(&r) { derived.push(json!({"what": "name", "value": n, "source": "resolved view (overlay or legacy names file)"})); }
        if let Some((b, e)) = ctx.pe.function_of(r) { derived.push(json!({"what": "function", "range": [hx(b), hx(e)], "trust": "proven(.pdata)"})); }
        let vts = ctx.vts.as_ref().unwrap();
        if let Some(i) = vts.by_rva.get(&r) { derived.push(json!({"what": "vtable", "info": vt_json(ctx, &vts.list[*i], false)})); }
        if let Some(u) = vts.fn_in.get(&r) { derived.push(json!({"what": "member of vtables", "slots": u.iter().take(8).map(|(i, s)| format!("{}#{}", ctx.vt_name(&vts.list[*i]), s)).collect::<Vec<_>>(), "trust": "proven(pointer in a discovered vtable)"})); }
        if let Some(s) = ctx.pe.string_at(r) { derived.push(json!({"what": "string", "text": s})); }
    }
    Ok(json!({"subject": subject, "history": ctx.db.history(&subject), "derived": derived}))
}

pub fn cmd_audit(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let _ = a;
    let facts: Vec<Fact> = ctx.db.active().into_iter().filter(|f| f.op == "assert").collect();
    let mut items = vec![];
    let (mut ok, mut bad) = (0, 0);
    for f in &facts {
        let mut checks: Vec<Value> = f.evidence.iter().map(|e| { let (s, d) = db::check_evidence(ctx, e); json!({"evidence": e, "status": s, "detail": d}) }).collect();
        let r = crate::parse_hex(&f.subject);
        match f.kind.as_str() {
            "class" => { let h = r.map_or(false, |r| ctx.vts.as_ref().unwrap().by_rva.contains_key(&r)); checks.push(json!({"evidence": "vtable discovered at subject", "status": if h { "holds" } else { "BROKEN" }})); }
            "name" => { let h = r.map_or(false, |r| ctx.pe.is_exec(r)); checks.push(json!({"evidence": "subject is in executable memory", "status": if h { "holds" } else { "BROKEN" }})); }
            "edge" => { let h = r.map_or(false, |r| { let b = ctx.pe.bytes(r, 15); let mut d = Decoder::with_ip(64, b, r as u64, DecoderOptions::NONE); d.can_decode() && matches!(d.decode().flow_control(), iced_x86::FlowControl::IndirectCall | iced_x86::FlowControl::IndirectBranch | iced_x86::FlowControl::Call) }); checks.push(json!({"evidence": "site is a call/jmp instruction", "status": if h { "holds" } else { "BROKEN" }})); }
            _ => {}
        }
        let broken = checks.iter().any(|c| c["status"] == "BROKEN" || c["status"] == "bad");
        if broken { bad += 1; } else { ok += 1; }
        items.push(json!({"id": f.id, "kind": f.kind, "subject": f.subject, "value": f.value, "status": if broken { "BROKEN" } else if checks.iter().all(|c| c["status"] == "unchecked") { "unverifiable" } else { "holds" }, "checks": checks}));
    }
    Ok(json!({"facts_checked": facts.len(), "holding_or_unverifiable": ok, "broken": bad, "items": items}))
}

pub fn cmd_info(ctx: &mut Ctx, _a: &Args) -> Result<Value, String> {
    ctx.prep();
    let vts = ctx.vts.as_ref().unwrap();
    let d = &ctx.pe.data;
    let pe_off = pe::u32le(d, 0x3c) as usize;
    let ts = pe::u32le(d, pe_off + 8);
    let opt = pe_off + 24;
    let size_of_image = pe::u32le(d, opt + 56);
    // debug directory (data dir #6) -> IMAGE_DEBUG_DIRECTORY entries of type CODEVIEW(2) -> RSDS guid/age/path
    let dd = opt + 112 + 6 * 8;
    let (drva, dsz) = (pe::u32le(d, dd), pe::u32le(d, dd + 4));
    let mut pdb = Value::Null;
    if drva != 0 { if let Some(o) = ctx.pe.off(drva) { for k in 0..(dsz as usize / 28) {
        let e = o + k * 28;
        if e + 28 > d.len() || pe::u32le(d, e + 12) != 2 { continue; }
        let (ptr, sz) = (pe::u32le(d, e + 24) as usize, pe::u32le(d, e + 16) as usize);
        if ptr + 24 <= d.len() && &d[ptr..ptr + 4] == b"RSDS" && sz >= 24 {
            let g = &d[ptr + 4..ptr + 20];
            let guid = format!("{:08X}-{:04X}-{:04X}-{}-{}", u32::from_le_bytes([g[0], g[1], g[2], g[3]]), u16::from_le_bytes([g[4], g[5]]), u16::from_le_bytes([g[6], g[7]]), g[8..10].iter().map(|b| format!("{:02X}", b)).collect::<String>(), g[10..16].iter().map(|b| format!("{:02X}", b)).collect::<String>());
            let name: String = d[ptr + 24..(ptr + sz).min(d.len())].iter().take_while(|b| **b != 0).map(|b| *b as char).collect();
            pdb = json!({"guid": guid, "age": pe::u32le(d, ptr + 20), "path": name});
        }
    } } }
    let identity = json!({"file_size": d.len(), "time_date_stamp": format!("{:#x}", ts), "size_of_image": format!("{:#x}", size_of_image), "pdb": pdb,
        "note": "compare these against the running game's module before trusting any address: a different build gives different values (60.05 vs 62.01 mixups have happened)"});
    Ok(json!({"identity": identity, "exe": ctx.exe, "image_base": format!("{:#x}", ctx.image_base), "functions_pdata": ctx.pe.ranges.iter().filter(|r| r.root == r.begin).count(), "vtables_discovered": vts.list.len(), "vtables_with_rtti": vts.list.iter().filter(|v| v.rtti.is_some()).count(),
        "component_names_known": ctx.comps.as_ref().unwrap().len(), "overlay": {"journal": ctx.db.path.display().to_string(), "epoch": ctx.db.epoch, "active_facts": ctx.db.active().len()}, "xref_pairs": ctx.xrefs().pairs.len()}))
}

pub fn cmd_comps(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let flt = a.pos.first().map(|s| s.to_lowercase());
    let names = ctx.comps.as_ref().unwrap().clone();
    let hits = scan_map(ctx, |i| (0..i.op_count()).find_map(|k| if matches!(i.op_kind(k), OpKind::Immediate32 | OpKind::Immediate32to64) { let v = i.immediate(k) as u32; if names.contains_key(&v) { Some(v) } else { None } } else { None }));
    let mut by: BTreeMap<u32, BTreeSet<u32>> = BTreeMap::new();
    for (ip, h) in &hits { by.entry(*h).or_default().insert(ctx.fn_start(*ip)); }
    let mut items: Vec<(usize, Value)> = names.iter().filter(|(_, n)| flt.as_ref().map_or(true, |f| n.to_lowercase().contains(f))).map(|(h, n)| { let c = by.get(h).map_or(0, |s| s.len()); (c, json!({"name": n, "hash": hx(*h), "functions": c})) }).collect();
    items.sort_by_key(|x| std::cmp::Reverse(x.0));
    Ok(json!({"note": "names come from strings in the image; a name with 0 functions has no imm32 use (type hash not used under that name)", "components": page(items.into_iter().map(|x| x.1).collect(), a, 80)}))
}


// What must be true for the program to travel a whole call path A -> B: the gates of every hop, grouped per function (each hop's `a0..a3` are THAT function's own arguments, so
// conditions from different hops are never merged into one expression). Contradictions are only claimed inside a single function, on identical text.
pub fn cmd_needs(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    let p = cmd_path(ctx, a)?;
    let paths = p["paths"].as_array().cloned().unwrap_or_default();
    let mut out = vec![];
    for path in paths.iter().take(a.num("k", 3)) {
        let mut hops = vec![];
        let mut dead = false;
        for h in path["hops"].as_array().cloned().unwrap_or_default() {
            let g = &h["gates"];
            let reach = g["reachable"].as_bool().unwrap_or(false);
            let conds: Vec<String> = g["gates"].as_array().map(|v| v.iter().map(|x| x["must_hold"].as_str().unwrap_or("?").to_string()).collect()).unwrap_or_default();
            // identical condition text asserted both ways inside one function: x == c and x != c
            let mut contra = vec![];
            for c in &conds { if let Some((l, r)) = c.split_once(" == ") { let neg = format!("{} != {}", l, r); if conds.contains(&neg) { contra.push(format!("{} and {}", c, neg)); } } }
            if !reach || !contra.is_empty() { dead = true; }
            hops.push(json!({"function": h["from"], "calls": h["to"], "at": h["site"], "via": h["kind"], "edge_trust": h["trust"], "reachable_in_cfg": reach, "must_hold": conds, "contradictions": contra,
                "unknowns": conds.iter().filter(|c| c.contains('?')).count()}));
        }
        out.push(json!({"length": hops.len(), "hops": hops, "provably_infeasible": dead,
            "reading": "all must_hold lists are necessary conditions (each is a branch edge every route to the call site must take); they are not sufficient, and `?` stands for a value this analysis does not track (heap loads)"}));
    }
    Ok(json!({"from": p["from"], "to": p["to"], "edge_mode": p["edge_mode"], "paths": out, "note": p["note"]}))
}
