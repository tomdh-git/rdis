// Derived whole-image model: ECS component names, vtables/classes (+ strict RTTI), call edges, vcall resolution.
use crate::sym::{self, Env, Sum, Tgt, E};
use crate::Ctx;
use iced_x86::{Decoder, DecoderOptions, FlowControl, Instruction, Mnemonic, OpKind};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

pub fn hx(v: u32) -> String { format!("{:#x}", v) }

pub fn fnv1a(name: &str) -> u32 { name.bytes().fold(0x811c9dc5u32, |h, c| (h ^ c as u32).wrapping_mul(0x01000193)) }

// ---------------------------------------------------------------- component names

fn is_id(c: u8) -> bool { c.is_ascii_alphanumeric() || c == b'_' || c == b':' }

// Names of ECS types, from "[Type = X]" pretty-function strings and from mangled "...X@@" names that end in "Component".
// The 32-bit hash of the name is what appears as an immediate in code, so a name is only ever used through its hash.
pub fn scan_comp_names(ctx: &Ctx) -> HashMap<u32, String> {
    let mut names: BTreeSet<String> = BTreeSet::new();
    for s in ctx.pe.sections.iter().filter(|s| s.flags & 0x2000_0000 == 0 && s.rawsize > 0) {
        let d = &ctx.pe.data[s.raw as usize..(s.raw + s.rawsize.min(s.vsize)) as usize];
        let mut i = 0;
        while i + 8 < d.len() {
            if d[i] == b'T' && d[i..].starts_with(b"Type = ") {
                let mut j = i + 7;
                while j < d.len() && j < i + 200 && (is_id(d[j]) || d[j] == b' ' && false) { j += 1; }
                if j < d.len() && d[j] == b']' && j > i + 7 { names.insert(String::from_utf8_lossy(&d[i + 7..j]).to_string()); }
                i += 7;
            } else if d[i] == b'C' && d[i..].starts_with(b"Component@") {
                // mangled: the identifier ending here, minus the type-kind/qualifier letters the mangling put in front of it (U, V, AEAU, AEBU, ...)
                let mut st = i;
                while st > 0 && (d[st - 1].is_ascii_alphanumeric() || d[st - 1] == b'_') && i - st < 100 { st -= 1; }
                let raw = String::from_utf8_lossy(&d[st..i + 9]).to_string();
                for pre in ["", "U", "V", "AEAU", "AEBU", "AEAV", "AEBV", "PEAU", "PEBU", "PEAV", "PEBV", "$$CBU", "$$CBV"] {
                    if let Some(n) = raw.strip_prefix(pre) { if n.len() > 9 && n.as_bytes()[0].is_ascii_uppercase() && (pre.is_empty() || true) { names.insert(n.to_string()); } }
                }
                i += 9;
            } else { i += 1; }
        }
    }
    names.into_iter().map(|n| (fnv1a(&n), n)).collect()
}

// ---------------------------------------------------------------- vtables / classes

#[derive(Clone, Debug)]
pub struct Rtti { pub name: String, pub mangled: String, pub col: u32, pub td: u32, pub bases: Vec<String> }

#[derive(Clone, Debug)]
pub struct Ctor { pub func: u32, pub lea_ip: u32, pub store_ip: u32, pub store_off: i64 }

#[derive(Clone, Debug)]
pub struct Vt { pub rva: u32, pub slots: Vec<u32>, pub end: &'static str, pub ctors: Vec<Ctor>, pub rtti: Option<Rtti> }

pub struct Vts {
    pub list: Vec<Vt>,
    pub by_rva: HashMap<u32, usize>,
    pub fn_in: HashMap<u32, Vec<(usize, usize)>>, // function rva -> (vtable index, slot)
    pub ctor_of: HashMap<u32, Vec<usize>>,        // function rva -> vtables it installs (constructor evidence)
}

fn code_ptr(ctx: &Ctx, v: u64) -> Option<u32> {
    let r = v.wrapping_sub(ctx.image_base);
    if r < 0x1_0000_0000 && ctx.pe.is_exec(r as u32) { Some(r as u32) } else { None }
}

fn demangle(m: &str) -> String {
    let s = m.trim_start_matches(".?AV").trim_start_matches(".?AU").trim_end_matches("@@");
    if s.contains('?') { return m.to_string(); }
    let mut p: Vec<&str> = s.split('@').collect();
    p.reverse();
    p.join("::")
}

pub(crate) fn read_rtti(ctx: &Ctx, vt: u32) -> Option<Rtti> {
    let col_va = ctx.pe.u64_at(vt.checked_sub(8)?)?;
    let col = col_va.wrapping_sub(ctx.image_base);
    if col >= 0x1_0000_0000 { return None; }
    let col = col as u32;
    let u32at = |a: u32| -> Option<u32> { let b = ctx.pe.bytes(a, 4); if b.len() == 4 { Some(u32::from_le_bytes(b.try_into().unwrap())) } else { None } };
    if u32at(col)? != 1 || u32at(col + 20)? != col { return None; } // signature 1 (x64) and pSelf must point at itself
    let td = u32at(col + 12)?;
    let nm = ctx.pe.bytes(td + 16, 4);
    if nm != b".?AV" && nm != b".?AU" { return None; }
    let mut mangled = String::new();
    let mut k = 0;
    loop { let b = ctx.pe.bytes(td + 16 + k, 1); if b.is_empty() || b[0] == 0 || k > 8000 { break; } mangled.push(b[0] as char); k += 1; }
    let chd = u32at(col + 16)?;
    let nb = u32at(chd + 8)? as usize;
    let arr = u32at(chd + 12)?;
    let mut bases = vec![];
    for i in 0..nb.min(32) {
        let bcd = u32at(arr + 4 * i as u32)?;
        let btd = u32at(bcd)?;
        let mut n = String::new();
        let mut k = 0;
        loop { let b = ctx.pe.bytes(btd + 16 + k, 1); if b.is_empty() || b[0] == 0 || k > 8000 { break; } n.push(b[0] as char); k += 1; }
        bases.push(demangle(&n));
    }
    Some(Rtti { name: demangle(&mangled), mangled, col, td, bases })
}

pub fn discover_vtables(ctx: &mut Ctx) -> Vts {
    let pairs: Vec<(u32, u32)> = ctx.xrefs().pairs.clone();
    let mut cand: BTreeMap<u32, Vec<Ctor>> = BTreeMap::new();
    let mut last_t = u32::MAX;
    let mut t_ok = false;
    for (t, from) in &pairs {
        if *t != last_t {
            last_t = *t;
            t_ok = !ctx.pe.is_exec(*t) && ctx.pe.section_of(*t).is_some() && ctx.pe.u64_at(*t).and_then(|v| code_ptr(ctx, v)).is_some() && t % 8 == 0;
        }
        if !t_ok { continue; }
        // lea reg,[rip+T] followed (within 8 straight-line instructions) by mov [mem], reg
        let b = ctx.pe.bytes(*from, 15 * 10);
        let mut dec = Decoder::with_ip(64, b, *from as u64, DecoderOptions::NONE);
        let mut ins = Instruction::default();
        if !dec.can_decode() { continue; }
        dec.decode_out(&mut ins);
        if ins.mnemonic() != Mnemonic::Lea || ins.op0_kind() != OpKind::Register || !ins.is_ip_rel_memory_operand() { continue; }
        let reg = ins.op0_register().full_register();
        for _ in 0..8 {
            if !dec.can_decode() { break; }
            dec.decode_out(&mut ins);
            if !matches!(ins.flow_control(), FlowControl::Next) { break; }
            if ins.mnemonic() == Mnemonic::Mov && ins.op0_kind() == OpKind::Memory && ins.memory_index() == iced_x86::Register::None && ins.op1_kind() == OpKind::Register && ins.op1_register().full_register() == reg {
                let func = ctx.pe.function_of(*from).map_or(*from, |f| f.0);
                cand.entry(*t).or_default().push(Ctor { func, lea_ip: *from, store_ip: ins.ip() as u32, store_off: ins.memory_displacement64() as i64 });
                break;
            }
            if ins.op_count() > 0 && ins.op0_kind() == OpKind::Register && ins.op0_register().full_register() == reg { break; } // reg overwritten
        }
    }
    // Second source: statically initialised objects. A qword in a WRITABLE data section that points into read-only data at a place whose first entry is a .pdata
    // function start is the vptr of an object the linker laid out (no constructor code ever stores it). These get no constructor evidence (ctors is empty).
    {
        let base = ctx.image_base;
        let mut extra: BTreeSet<u32> = BTreeSet::new();
        for sec in ctx.pe.sections.iter().filter(|s| s.flags & 0x8000_0000 != 0 && s.flags & 0x2000_0000 == 0 && s.rawsize > 0) {
            let d = &ctx.pe.data[sec.raw as usize..(sec.raw + sec.rawsize.min(sec.vsize)) as usize];
            for k in 0..d.len() / 8 {
                let v = u64::from_le_bytes(d[k * 8..k * 8 + 8].try_into().unwrap());
                let r = v.wrapping_sub(base);
                if v == 0 || r >= 0x1_0000_0000 || r % 8 != 0 { continue; }
                let t = r as u32;
                if cand.contains_key(&t) || extra.contains(&t) { continue; }
                match ctx.pe.section_of(t) { Some(ts) if ts.flags & 0xA000_0000 == 0 => {} _ => continue } // target must be read-only, non-executable data
                let first = ctx.pe.u64_at(t).map(|x| x.wrapping_sub(base)).filter(|x| *x < 0x1_0000_0000).map(|x| x as u32);
                if first.map_or(false, |f| ctx.pe.is_exec(f)) { extra.insert(t); } // leaf functions have no .pdata entry, so executable is the test
            }
        }
        for t in extra { cand.entry(t).or_default(); }
    }
    let starts: BTreeSet<u32> = cand.keys().copied().collect();
    let mut list = vec![];
    for (t, ctors) in cand {
        let mut slots = vec![];
        let mut end = "non-code";
        let mut a = t;
        while slots.len() < 1024 {
            if a != t && starts.contains(&a) { end = "next-vtable"; break; }
            match ctx.pe.u64_at(a).and_then(|v| code_ptr(ctx, v)) { Some(x) => slots.push(x), None => break }
            a += 8;
        }
        let rtti = read_rtti(ctx, t);
        list.push(Vt { rva: t, slots, end, ctors, rtti });
    }
    let mut by_rva = HashMap::new();
    let mut fn_in: HashMap<u32, Vec<(usize, usize)>> = HashMap::new();
    for (i, v) in list.iter().enumerate() {
        by_rva.insert(v.rva, i);
        for (s, f) in v.slots.iter().enumerate() { fn_in.entry(*f).or_default().push((i, s)); }
    }
    let mut ctor_of: HashMap<u32, Vec<usize>> = HashMap::new();
    for (i, v) in list.iter().enumerate() { let fs: BTreeSet<u32> = v.ctors.iter().map(|c| c.func).collect(); for f in fs { ctor_of.entry(f).or_default().push(i); } }
    Vts { list, by_rva, fn_in, ctor_of }
}

impl Ctx {
    pub fn vt_name(&self, v: &Vt) -> String {
        if let Some(f) = self.db.find("class", &hx(v.rva)) { if let Some(s) = f.value.as_str() { return s.to_string(); } }
        match &v.rtti { Some(r) => r.name.clone(), None => format!("vtbl_{:x}", v.rva) }
    }
    pub fn vt_name_trust(&self, v: &Vt) -> &'static str {
        if self.db.find("class", &hx(v.rva)).is_some() { "agent" } else if v.rtti.is_some() { "proven(rtti)" } else { "unknown(no rtti: vtable identity only)" }
    }
    pub fn prep(&mut self) {
        if self.comps.is_none() {
            let mut m = scan_comp_names(self);
            for f in self.db.active() { if f.op == "assert" && f.kind == "component" { if let Some(n) = f.value.as_str() { m.insert(fnv1a(n), n.to_string()); } } }
            self.comps = Some(m);
        }
        if self.vts.is_none() { let v = discover_vtables(self); self.vts = Some(v); }
    }
    pub fn invalidate(&mut self) {
        self.sums.borrow_mut().clear();
        self.edges.borrow_mut().clear();
        self.comps = None;
        // names may have changed
        let mut names = self.legacy_names.clone();
        for f in self.db.active() { if f.op == "assert" && f.kind == "name" { if let (Some(a), Some(n)) = (u32::from_str_radix(f.subject.trim_start_matches("0x"), 16).ok(), f.value.as_str()) { names.insert(a, n.to_string()); } } }
        self.names = names;
    }
    pub fn sum(&self, rva: u32) -> Rc<Sum> {
        if let Some(s) = self.sums.borrow().get(&rva) { return s.clone(); }
        let env = Env { ctx: self, comps: self.comps.as_ref().expect("prep") };
        let s = Rc::new(sym::summarize(&env, rva));
        self.sums.borrow_mut().insert(rva, s.clone());
        s
    }
    pub fn fn_start(&self, rva: u32) -> u32 { self.pe.function_of(rva).map_or(rva, |f| f.0) }
    pub fn fname(&self, rva: u32) -> String { crate::listing::target_name(self, rva) }
    pub fn flabel(&self, rva: u32) -> Value {
        let mut v = json!({"rva": hx(rva), "name": self.fname(rva)});
        if let Some(vts) = &self.vts { if let Some(u) = vts.fn_in.get(&rva) { v["vtable_slots"] = json!(u.iter().take(6).map(|(i, s)| format!("{}#{}", self.vt_name(&vts.list[*i]), s)).collect::<Vec<_>>()); } }
        v
    }
}

// ---------------------------------------------------------------- vcall resolution

#[derive(Clone, Debug)]
pub struct Res { pub targets: Vec<u32>, pub trust: &'static str, pub basis: String, pub slot: Option<usize> }

pub fn resolve_vcall(ctx: &Ctx, sum: &Sum, ev: &sym::CallEv) -> Res {
    let (obj, vptr_off, disp) = match &ev.tgt { Tgt::Slot { obj, vptr_off, disp } => (obj, *vptr_off, *disp), _ => return Res { targets: vec![], trust: "n/a", basis: "not a slot call".into(), slot: None } };
    let vts = ctx.vts.as_ref().expect("prep");
    if disp < 0 || disp % 8 != 0 { return Res { targets: vec![], trust: "unknown", basis: format!("slot displacement {:#x} is not a multiple of 8", disp), slot: None }; }
    let slot = (disp / 8) as usize;
    // overlay edge fact for this call site wins
    if let Some(f) = ctx.db.find("edge", &hx(ev.ip)) {
        let ts: Vec<u32> = f.value.as_str().unwrap_or("").split(',').filter_map(|t| crate::parse_hex(t.trim())).collect();
        if !ts.is_empty() { return Res { targets: ts, trust: if f.trust == "observed" { "observed" } else if f.trust == "derived" { "derived" } else { "agent" }, basis: format!("overlay fact #{}: {}", f.id, f.note), slot: Some(slot) }; }
    }
    // (0) the agent told us what class the object held in a global is (`assert global-type <global> <Class>`)
    if let E::Load(inner, 8) = obj {
        if let E::Glob(g) = &**inner {
            if let Some(f) = ctx.db.find("global-type", &hx(*g)) {
                if let Some(q) = f.value.as_str() {
                    // several classes (a global that is switched between implementations at runtime): one target per class, never better than candidate
                    if q.contains(',') {
                        let mut ts: BTreeSet<u32> = BTreeSet::new();
                        for part in q.split(',') { if let Some(i) = crate::cmds::find_vts(ctx, part.trim()).first() { if let Some(t) = vts.list[*i].slots.get(slot) { ts.insert(*t); } } }
                        if !ts.is_empty() { return Res { targets: ts.into_iter().collect(), trust: "candidate", basis: format!("overlay fact #{}: global {} holds one of {} ({})", f.id, hx(*g), q, f.note), slot: Some(slot) }; }
                    }
                    let hits = crate::cmds::find_vts(ctx, q);
                    if let Some(i) = hits.first() {
                        if let Some(t) = vts.list[*i].slots.get(slot) {
                            return Res { targets: vec![*t], trust: if f.trust == "observed" { "observed" } else if f.trust == "derived" { "derived" } else { "agent" }, basis: format!("overlay fact #{}: global {} holds a {} ({})", f.id, hx(*g), q, f.note), slot: Some(slot) };
                        }
                    }
                }
            }
        }
    }
    // (1) a store of a known vtable into [obj+vptr_off] that dominates the call
    let call_blk = match sum.cfg.block_of(ev.ip) { Some(b) => b.start, None => return Res { targets: vec![], trust: "unknown", basis: "call not in a block".into(), slot: Some(slot) } };
    let stores: Vec<(&sym::Acc, u32)> = sum.accs.iter().filter(|a| a.write && !a.indexed && a.base == *obj && a.off == vptr_off).filter_map(|a| match &a.value { Some(E::Glob(g)) if vts.by_rva.contains_key(g) => Some((a, *g)), _ => None }).collect();
    let vset: BTreeSet<u32> = stores.iter().map(|s| s.1).collect();
    if vset.len() == 1 {
        let (acc, g) = stores.iter().find(|(a, _)| {
            let sb = sum.cfg.block_of(a.ip).map(|b| b.start);
            match sb { Some(sb) if sb == call_blk => a.ip < ev.ip, Some(sb) => sum.cfg.dominates(sb, call_blk), None => false }
        }).map(|(a, g)| (*a, *g)).unwrap_or((stores[0].0, u32::MAX));
        if g != u32::MAX {
            let vt = &vts.list[vts.by_rva[&g]];
            if let Some(t) = vt.slots.get(slot) {
                return Res { targets: vec![*t], trust: "derived", basis: format!("store of vtable {} into [obj+{:#x}] at {:x} dominates the call (assumes callees between them do not rewrite the vptr)", ctx.vt_name(vt), vptr_off, acc.ip), slot: Some(slot) };
            }
            return Res { targets: vec![], trust: "unknown", basis: format!("vtable {} has only {} slots", ctx.vt_name(vt), vt.slots.len()), slot: Some(slot) };
        }
    }
    // (2) this of a vtable member function
    if *obj == E::Arg(0) && vptr_off == 0 {
        if let Some(u) = vts.fn_in.get(&sum.cfg.begin) {
            let mut ts: BTreeSet<u32> = BTreeSet::new();
            let mut names = vec![];
            for (vi, _) in u { let v = &vts.list[*vi]; if let Some(t) = v.slots.get(slot) { ts.insert(*t); names.push(ctx.vt_name(v)); } }
            if !ts.is_empty() {
                names.sort(); names.dedup();
                return Res { targets: ts.into_iter().collect(), trust: "candidate", basis: format!("a0 is `this` of a member of vtable(s) {}: its dynamic class is one of them or a subclass (subclass overrides not included)", names.join(",")), slot: Some(slot) };
            }
        }
    }
    Res { targets: vec![], trust: "unknown", basis: "object class not determinable in this function".into(), slot: Some(slot) }
}

// all distinct targets at a slot over every known vtable
pub fn slot_targets(ctx: &Ctx, slot: usize) -> BTreeMap<u32, Vec<usize>> {
    let vts = ctx.vts.as_ref().expect("prep");
    let mut m: BTreeMap<u32, Vec<usize>> = BTreeMap::new();
    for (i, v) in vts.list.iter().enumerate() { if let Some(t) = v.slots.get(slot) { m.entry(*t).or_default().push(i); } }
    m
}

// ---------------------------------------------------------------- call edges

#[derive(Clone, Debug)]
pub struct Edge { pub site: u32, pub to: u32, pub kind: &'static str, pub trust: &'static str }

// Direct call/tail-jmp edges of a function, straight from the instruction bytes (cheap: no dataflow).
pub fn direct_edges(ctx: &Ctx, f: u32) -> Rc<Vec<Edge>> {
    if let Some(e) = ctx.edges.borrow().get(&f) { return e.clone(); }
    let mut out = vec![];
    let ranges: Vec<(u32, u32)> = match ctx.pe.function_of(f) {
        Some((b, e)) if b == f => { let mut r = vec![(b, e)]; r.extend(ctx.pe.fragments_of(b)); r }
        _ => vec![(f, crate::listing::heuristic_end(ctx, f))],
    };
    for (b, e) in &ranges {
        for ins in crate::listing::decode_range(ctx, *b, *e) {
            match ins.flow_control() {
                FlowControl::Call if ins.op0_kind() == OpKind::NearBranch64 => out.push(Edge { site: ins.ip() as u32, to: ins.near_branch_target() as u32, kind: "call", trust: "proven" }),
                FlowControl::UnconditionalBranch | FlowControl::ConditionalBranch if ins.op0_kind() == OpKind::NearBranch64 => {
                    let t = ins.near_branch_target() as u32;
                    if !ranges.iter().any(|r| t >= r.0 && t < r.1) { out.push(Edge { site: ins.ip() as u32, to: t, kind: "tail-jmp", trust: "proven" }); }
                }
                _ => {}
            }
        }
    }
    let rc = Rc::new(out);
    ctx.edges.borrow_mut().insert(f, rc.clone());
    rc
}

// Edges including virtual calls, by mode: none | derived | cand | slot
pub fn all_edges(ctx: &Ctx, f: u32, mode: &str) -> Vec<Edge> {
    let mut out: Vec<Edge> = direct_edges(ctx, f).as_ref().clone();
    if mode == "none" { return out; }
    let s = ctx.sum(f);
    for ev in &s.calls {
        if let Tgt::Slot { disp, .. } = &ev.tgt {
            let r = resolve_vcall(ctx, &s, ev);
            let want = match r.trust { "derived" | "agent" | "observed" => true, "candidate" => mode == "cand" || mode == "slot", _ => false };
            if want { for t in &r.targets { out.push(Edge { site: ev.ip, to: *t, kind: "vcall", trust: r.trust }); } }
            else if mode == "slot" && *disp >= 0 && disp % 8 == 0 {
                for (t, _) in slot_targets(ctx, (*disp / 8) as usize) { out.push(Edge { site: ev.ip, to: t, kind: "vcall-any-class", trust: "candidate" }); }
            }
        } else if let Tgt::Mem(_) | Tgt::Reg(_) | Tgt::Global(_) = &ev.tgt {
            if let Some(fct) = ctx.db.find("edge", &hx(ev.ip)) {
                for t in fct.value.as_str().unwrap_or("").split(',').filter_map(|t| crate::parse_hex(t.trim())) { out.push(Edge { site: ev.ip, to: t, kind: "indirect(overlay)", trust: if fct.trust == "observed" { "observed" } else { "agent" } }); }
            }
        }
    }
    // construct-and-hand-off: a function that installs a vtable creates an object whose virtual methods can run later (callbacks, std::function bodies, tasks
    // queued to another thread). Not a call: an edge of kind "constructs" that only the widest modes follow.
    if mode == "cand" || mode == "slot" {
        if let Some(vts) = ctx.vts.as_ref() {
            if let Some(ix) = vts.ctor_of.get(&f) {
                for i in ix.iter().take(64) {
                    let v = &vts.list[*i];
                    if v.slots.len() > 12 { continue; } // a big class: constructing it says little about which method runs
                    let site = v.ctors.iter().find(|c| c.func == f).map_or(f, |c| c.store_ip);
                    for t in &v.slots { out.push(Edge { site, to: *t, kind: "constructs", trust: "candidate" }); }
                }
            }
        }
    }
    out.retain(|e| !ctx.db.contested(&format!("edge:{}->{}", hx(e.site), hx(e.to))));
    out
}

pub fn fmt_args(a: &[E]) -> Vec<String> { a.iter().map(|e| e.to_string()).collect() }

pub fn known_functions(ctx: &Ctx) -> HashSet<u32> { ctx.pe.ranges.iter().filter(|r| r.root == r.begin).map(|r| r.begin).collect() }
