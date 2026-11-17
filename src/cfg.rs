// Control-flow graph of one function (main .pdata range plus its chained fragments).
//
// Soundness notes (the accuracy contract, see docs/RDIS_V2_PLAN.md):
//  * every edge is read from an instruction (fallthrough, jcc, jmp) or from a jump table whose entries were read from the image;
//  * a call is assumed to return (an over-approximation of the real paths: it can only ADD edges, so "necessary edge" answers stay sound);
//  * an indirect jmp that is not a recognised jump table is recorded in `unresolved`, never guessed.
use crate::Ctx;
use iced_x86::{ConditionCode, FlowControl, Instruction, Mnemonic, OpKind, Register};
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EKind { Fall, Taken, NotTaken, Jmp, Case }

#[derive(Clone, Debug)]
pub struct Edge { pub to: u32, pub kind: EKind, pub case: Vec<u32>, pub outside: bool }

#[derive(Clone, Debug)]
pub struct Block { pub start: u32, pub end: u32, pub first: usize, pub last: usize, pub succ: Vec<Edge>, pub term_ip: u32 }

#[derive(Clone, Debug)]
pub struct Switch { pub ip: u32, pub table: u32, pub entries: Vec<u32>, pub bound: &'static str, pub idx: Register }

pub struct Cfg {
    pub begin: u32,
    pub end: u32,
    pub ranges: Vec<(u32, u32)>,
    pub heuristic_extent: bool,
    pub ins: Vec<Instruction>,
    pub blocks: BTreeMap<u32, Block>,
    pub preds: HashMap<u32, Vec<(u32, usize)>>, // block start -> (pred block start, edge index)
    pub tail_calls: Vec<(u32, u32)>,             // (jmp ip, target) jmp out of the function
    pub tail_ind: Vec<u32>,                      // jmp [mem] / jmp reg that left the function without a table
    pub unresolved: Vec<(u32, String)>,
    pub switches: Vec<Switch>,
    pub need: BTreeSet<u32>, // jump-table targets that were not block leaders yet (the builder re-runs with them)
}

impl Cfg {
    pub fn contains(&self, rva: u32) -> bool { self.ranges.iter().any(|r| rva >= r.0 && rva < r.1) }

    pub fn block_of(&self, ip: u32) -> Option<&Block> {
        let (_, b) = self.blocks.range(..=ip).next_back()?;
        if ip < b.end { Some(b) } else { None }
    }

    pub fn ins_at(&self, ip: u32) -> Option<&Instruction> {
        self.ins.binary_search_by(|i| (i.ip() as u32).cmp(&ip)).ok().map(|i| &self.ins[i])
    }

    // Can `target` be reached from the entry without using edge `ban` (block start, edge index) and without passing through block `skip`?
    pub fn reach_without(&self, target: u32, ban: Option<(u32, usize)>, skip: Option<u32>) -> bool {
        if Some(self.begin) == skip { return false; }
        let mut seen: BTreeSet<u32> = BTreeSet::new();
        let mut st = vec![self.begin];
        seen.insert(self.begin);
        while let Some(b) = st.pop() {
            if b == target { return true; }
            let blk = match self.blocks.get(&b) { Some(x) => x, None => continue };
            for (i, e) in blk.succ.iter().enumerate() {
                if Some((b, i)) == ban || e.outside { continue; }
                if Some(e.to) == skip { continue; }
                if seen.insert(e.to) { st.push(e.to); }
            }
        }
        false
    }

    // Does block `a` dominate block `b` (every entry->b path passes through a)?
    pub fn dominates(&self, a: u32, b: u32) -> bool {
        if a == b { return true; }
        self.reach_without(b, None, None) && !self.reach_without(b, None, Some(a))
    }

    // The conditional edges whose removal makes `b` unreachable: necessary conditions for reaching it (exact on this CFG).
    pub fn gates(&self, b: u32) -> Vec<(u32, usize)> {
        let mut out = vec![];
        if !self.reach_without(b, None, None) { return out; }
        for (bs, blk) in &self.blocks {
            if blk.succ.len() < 2 { continue; }
            for (i, e) in blk.succ.iter().enumerate() {
                if e.outside { continue; }
                if !self.reach_without(b, Some((*bs, i)), None) { out.push((*bs, i)); }
            }
        }
        out
    }
}

fn in_ranges(r: &[(u32, u32)], x: u32) -> bool { r.iter().any(|p| x >= p.0 && x < p.1) }

pub fn build(ctx: &Ctx, begin: u32) -> Cfg {
    let mut extra: BTreeSet<u32> = BTreeSet::new();
    for _ in 0..6 {
        let c = build_inner(ctx, begin, &extra);
        if c.need.is_empty() || c.need.is_subset(&extra) { return c; }
        extra.extend(c.need.iter().copied());
    }
    build_inner(ctx, begin, &extra)
}

fn build_inner(ctx: &Ctx, begin: u32, extra: &BTreeSet<u32>) -> Cfg {
    let (mut ranges, heur) = match ctx.pe.function_of(begin) {
        Some((b, e)) if b == begin => {
            let mut r = vec![(b, e)];
            r.extend(ctx.pe.fragments_of(b));
            (r, false)
        }
        _ => (vec![(begin, crate::listing::heuristic_end(ctx, begin))], true),
    };
    ranges.sort();
    let mut ins: Vec<Instruction> = vec![];
    for r in &ranges { ins.extend(crate::listing::decode_range(ctx, r.0, r.1)); }
    // leaders
    let mut leaders: BTreeSet<u32> = BTreeSet::new();
    for r in &ranges { leaders.insert(r.0); }
    for e in extra { leaders.insert(*e); }
    for (n, i) in ins.iter().enumerate() {
        match i.flow_control() {
            FlowControl::ConditionalBranch | FlowControl::UnconditionalBranch => {
                if i.op0_kind() == OpKind::NearBranch64 {
                    let t = i.near_branch_target() as u32;
                    if in_ranges(&ranges, t) { leaders.insert(t); }
                }
                if let Some(nx) = ins.get(n + 1) { leaders.insert(nx.ip() as u32); }
            }
            FlowControl::Return | FlowControl::IndirectBranch | FlowControl::Exception => { if let Some(nx) = ins.get(n + 1) { leaders.insert(nx.ip() as u32); } }
            _ => {}
        }
    }
    // blocks
    let mut blocks: BTreeMap<u32, Block> = BTreeMap::new();
    let mut n = 0;
    while n < ins.len() {
        let first = n;
        let start = ins[n].ip() as u32;
        let mut last = n;
        loop {
            let i = &ins[last];
            let fc = i.flow_control();
            let term = matches!(fc, FlowControl::ConditionalBranch | FlowControl::UnconditionalBranch | FlowControl::Return | FlowControl::IndirectBranch | FlowControl::Exception);
            let next = ins.get(last + 1);
            let contiguous = next.map_or(false, |x| x.ip() == i.next_ip());
            if term || !contiguous || next.map_or(true, |x| leaders.contains(&(x.ip() as u32))) { break; }
            last += 1;
        }
        blocks.insert(start, Block { start, end: ins[last].next_ip() as u32, first, last, succ: vec![], term_ip: ins[last].ip() as u32 });
        n = last + 1;
    }
    let mut cfg = Cfg { begin, end: ranges.last().unwrap().1, ranges, heuristic_extent: heur, ins, blocks, preds: HashMap::new(), tail_calls: vec![], tail_ind: vec![], unresolved: vec![], switches: vec![], need: BTreeSet::new() };
    // edges
    let starts: Vec<u32> = cfg.blocks.keys().copied().collect();
    let mut switch_jobs: Vec<u32> = vec![];
    for s in &starts {
        let (first, last) = { let b = &cfg.blocks[s]; (b.first, b.last) };
        let t = cfg.ins[last];
        let mut succ: Vec<Edge> = vec![];
        let next = cfg.ins.get(last + 1).filter(|x| x.ip() == t.next_ip()).map(|x| x.ip() as u32);
        let fall = |succ: &mut Vec<Edge>, k: EKind| { if let Some(nx) = next { if cfg.blocks.contains_key(&nx) { succ.push(Edge { to: nx, kind: k, case: vec![], outside: false }); } } };
        match t.flow_control() {
            FlowControl::ConditionalBranch => {
                let tg = t.near_branch_target() as u32;
                let inside = cfg.blocks.contains_key(&tg);
                succ.push(Edge { to: tg, kind: EKind::Taken, case: vec![], outside: !inside });
                if !inside { cfg.tail_calls.push((t.ip() as u32, tg)); }
                fall(&mut succ, EKind::NotTaken);
            }
            FlowControl::UnconditionalBranch => {
                let tg = t.near_branch_target() as u32;
                if cfg.blocks.contains_key(&tg) { succ.push(Edge { to: tg, kind: EKind::Jmp, case: vec![], outside: false }); } else { cfg.tail_calls.push((t.ip() as u32, tg)); }
            }
            FlowControl::IndirectBranch => switch_jobs.push(*s),
            FlowControl::Return | FlowControl::Exception => {}
            _ => fall(&mut succ, EKind::Fall),
        }
        let _ = first;
        cfg.blocks.get_mut(s).unwrap().succ = succ;
    }
    cfg.rebuild_preds();
    // a switch can sit behind another switch's cases (its block has no predecessor until that one is resolved): retry failures until no progress
    let mut pending = switch_jobs;
    loop {
        let mut next = vec![];
        let mut progress = false;
        for s in pending.iter().copied() {
            let (u, t) = (cfg.unresolved.len(), cfg.tail_ind.len());
            cfg.resolve_switch(ctx, s);
            if cfg.unresolved.len() > u { cfg.unresolved.truncate(u); cfg.tail_ind.truncate(t); next.push(s); } else { progress = true; cfg.rebuild_preds(); }
        }
        if next.is_empty() { break; }
        if !progress { for s in next { cfg.resolve_switch(ctx, s); } break; }
        pending = next;
    }
    cfg.rebuild_preds();
    cfg
}

impl Cfg {
    fn rebuild_preds(&mut self) {
        let mut p: HashMap<u32, Vec<(u32, usize)>> = HashMap::new();
        for (s, b) in &self.blocks { for (i, e) in b.succ.iter().enumerate() { if !e.outside { p.entry(e.to).or_default().push((*s, i)); } } }
        self.preds = p;
    }

    // The unique instruction that defines `reg` on every path reaching the start of block `bs` (none of the paths may call, for volatile regs, or reach the entry undefined).
    fn reaching_def(&self, bs: u32, reg: Register) -> Result<usize, String> {
        let volatile = matches!(reg, Register::RAX | Register::RCX | Register::RDX | Register::R8 | Register::R9 | Register::R10 | Register::R11);
        let mut found: BTreeSet<usize> = BTreeSet::new();
        let mut seen: BTreeSet<u32> = BTreeSet::new();
        let mut stack: Vec<u32> = self.preds.get(&bs).map(|v| v.iter().map(|p| p.0).collect()).unwrap_or_default();
        if stack.is_empty() { return Err("is not defined on any path into the switch block (function entry)".into()); }
        while let Some(pb) = stack.pop() {
            if !seen.insert(pb) { continue; }
            let blk = &self.blocks[&pb];
            let mut hit = false;
            for k in (blk.first..=blk.last).rev() {
                let i = &self.ins[k];
                if volatile && matches!(i.mnemonic(), Mnemonic::Call) { return Err("is volatile and a call lies between its definition and the switch".into()); }
                let w = i.op_count() > 0 && i.op0_kind() == OpKind::Register && i.op0_register().full_register() == reg && !matches!(i.mnemonic(), Mnemonic::Cmp | Mnemonic::Test | Mnemonic::Push);
                if w { found.insert(k); hit = true; break; }
            }
            if hit { continue; }
            match self.preds.get(&pb) { Some(ps) if !ps.is_empty() => stack.extend(ps.iter().map(|p| p.0)), _ => { if self.ranges.iter().any(|r| r.0 == pb) { return Err("reaches the function entry undefined".into()); } /* no known predecessor and not an entry: only reachable through a not-yet-resolved indirect jump (typically a case of this very switch); ignored */ } }
        }
        if found.len() == 1 { Ok(*found.iter().next().unwrap()) } else { Err(format!("has {} different reaching definitions", found.len())) }
    }

    // jmp reg: recognise  [movsxd|mov] r, [B + I*4 + disp] ; add r, B ; jmp r   with  B = lea [rip+X]   (target = X + entry, rva space)
    fn resolve_switch(&mut self, ctx: &Ctx, bs: u32) {
        let blk = self.blocks[&bs].clone();
        let jmp = self.ins[blk.last];
        let ip = jmp.ip() as u32;
        if jmp.op0_kind() != OpKind::Register {
            self.tail_ind.push(ip);
            self.unresolved.push((ip, "jmp [mem]/indirect with no table pattern".into()));
            return;
        }
        let r = jmp.op0_register().full_register();
        let mut idx = blk.last;
        let find_prev = |cfg: &Cfg, from: usize, pred: &dyn Fn(&Instruction) -> bool| -> Option<usize> {
            let mut k = from;
            while k > blk.first { k -= 1; if pred(&cfg.ins[k]) { return Some(k); } }
            None
        };
        let writes = |i: &Instruction, reg: Register| -> bool { i.op_count() > 0 && i.op0_kind() == OpKind::Register && i.op0_register().full_register() == reg && !matches!(i.mnemonic(), Mnemonic::Cmp | Mnemonic::Test) };
        // add r, B
        let add_i = match find_prev(self, idx, &|i| writes(i, r)) { Some(k) => k, None => { self.unresolved.push((ip, "no def of jump reg in block".into())); return; } };
        let a = self.ins[add_i];
        if a.mnemonic() != Mnemonic::Add || a.op1_kind() != OpKind::Register { self.unresolved.push((ip, "jump reg not computed by add r,B".into())); return; }
        let b_reg = a.op1_register().full_register();
        idx = add_i;
        // load of the entry into r
        let ld_i = match find_prev(self, idx, &|i| writes(i, r)) { Some(k) => k, None => { self.unresolved.push((ip, "no table load".into())); return; } };
        let ld = self.ins[ld_i];
        if !matches!(ld.mnemonic(), Mnemonic::Movsxd | Mnemonic::Mov) || ld.op1_kind() != OpKind::Memory || ld.memory_index_scale() != 4 || ld.memory_base().full_register() != b_reg {
            self.unresolved.push((ip, "table load shape not [B+I*4+disp]".into())); return;
        }
        let disp = ld.memory_displacement64() as i64;
        let idx_reg = ld.memory_index().full_register();
        // two-level form: idx2 = movzx byte [B + I + d2] ; entry = [B + idx2*4 + disp]  (compilers emit this when many cases share few targets)
        let mut byte_tab: Option<(i64, Register)> = None;
        if let Some(bi) = find_prev(self, ld_i, &|i| writes(i, idx_reg)) {
            let bm = self.ins[bi];
            if bm.mnemonic() == Mnemonic::Movzx && bm.op1_kind() == OpKind::Memory && bm.memory_size() == iced_x86::MemorySize::UInt8 && bm.memory_index_scale() == 1 && bm.memory_base().full_register() == b_reg {
                byte_tab = Some((bm.memory_displacement64() as i64, bm.memory_index().full_register()));
            }
        }
        let mut cmp_reg = byte_tab.map(|b| b.1).unwrap_or(idx_reg);
        if byte_tab.is_some() {
            // the bounded value may have been copied/extended into the index register first (movsxd rcx, eax)
            let mi = find_prev(self, ld_i, &|i| i.mnemonic() == Mnemonic::Movzx && i.op1_kind() == OpKind::Memory).unwrap_or(ld_i);
            if let Some(ci) = find_prev(self, mi, &|i| writes(i, cmp_reg)) {
                let c = self.ins[ci];
                if matches!(c.mnemonic(), Mnemonic::Movsxd | Mnemonic::Mov | Mnemonic::Movsx | Mnemonic::Movzx) && c.op1_kind() == OpKind::Register { cmp_reg = c.op1_register().full_register(); }
            }
        }
        // B = lea [rip+X]
        let lea_i = match find_prev(self, ld_i, &|i| writes(i, b_reg)) { Some(k) => k, None => {
            // not in this block: walk predecessors backwards; accept only if every path reaches the very same single definition (a lea [rip+X])
            match self.reaching_def(bs, b_reg) {
                Ok(k) => k,
                Err(why) => { self.unresolved.push((ip, format!("table base register {}", why))); return; }
            }
        } };
        let lea = self.ins[lea_i];
        if lea.mnemonic() != Mnemonic::Lea || !lea.is_ip_rel_memory_operand() { self.unresolved.push((ip, "table base not lea [rip+X]".into())); return; }
        let x = lea.ip_rel_memory_address() as i64;
        let table = (x + disp) as u32;
        // bound: single predecessor block ending in cmp idx, N ; ja/jae (not-taken to us) or jbe/jb (taken to us)
        let mut bound: Option<usize> = None;
        if let Some(ps) = self.preds.get(&bs) {
            if ps.len() == 1 {
                let (pb, ei) = ps[0];
                let pblk = &self.blocks[&pb];
                let ek = pblk.succ[ei].kind;
                let jc = self.ins[pblk.last];
                let cc = jc.condition_code();
                let cmp = (pblk.first..pblk.last).rev().map(|k| self.ins[k]).find(|i| i.rflags_modified() != 0);
                if let Some(c) = cmp {
                    if c.mnemonic() == Mnemonic::Cmp && c.op0_kind() == OpKind::Register && c.op0_register().full_register() == cmp_reg && matches!(c.op1_kind(), OpKind::Immediate8 | OpKind::Immediate8to32 | OpKind::Immediate32 | OpKind::Immediate8to64 | OpKind::Immediate32to64) {
                        let n = c.immediate(1) as i64;
                        let cnt = match (cc, ek) {
                            (ConditionCode::a, EKind::NotTaken) | (ConditionCode::be, EKind::Taken) => Some(n + 1),
                            (ConditionCode::ae, EKind::NotTaken) | (ConditionCode::b, EKind::Taken) => Some(n),
                            _ => None,
                        };
                        if let Some(k) = cnt { if (1..=4096).contains(&k) { bound = Some(k as usize); } }
                    }
                }
            }
        }
        if let Some((d2, _)) = byte_tab {
            let k = match bound { Some(k) => k, None => { self.unresolved.push((ip, "two-level switch without a cmp bound".into())); return; } };
            let bytes = ctx.pe.bytes((x + d2) as u32, k);
            if bytes.len() < k { self.unresolved.push((ip, "byte index table runs off the image".into())); return; }
            let mut entries = vec![];
            for i in 0..k {
                let m = ctx.pe.bytes(table + 4 * bytes[i] as u32, 4);
                if m.len() < 4 { self.unresolved.push((ip, "table runs off the image".into())); return; }
                let t = (x + i32::from_le_bytes(m.try_into().unwrap()) as i64) as u32;
                if !self.blocks.contains_key(&t) {
                    if in_ranges(&self.ranges, t) && self.ins_at(t).is_some() { self.need.insert(t); }
                    self.unresolved.push((ip, format!("two-level table: case {} -> {:#x} is not a block of this function", i, t))); 
                }
                entries.push(t);
            }
            if self.unresolved.iter().any(|u| u.0 == ip) { return; }
            let mut by_target: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
            for (i, t) in entries.iter().enumerate() { by_target.entry(*t).or_default().push(i as u32); }
            let succ: Vec<Edge> = by_target.into_iter().map(|(t, cases)| Edge { to: t, kind: EKind::Case, case: cases, outside: false }).collect();
            self.blocks.get_mut(&bs).unwrap().succ = succ;
            self.switches.push(Switch { ip, table, entries, bound: "cmp-bound+byte-table", idx: cmp_reg });
            return;
        }
        let (count, how) = match bound { Some(k) => (k, "cmp-bound"), None => {
            // fall back: entries up to the first one that leaves the function (heuristic; reported as such)
            let mut k = 0usize;
            while k < 512 {
                let e = match ctx.pe.bytes(table + 4 * k as u32, 4) { b if b.len() == 4 => i32::from_le_bytes(b.try_into().unwrap()), _ => break };
                let t = (x + e as i64) as u32;
                if !in_ranges(&self.ranges, t) || self.ins_at(t).is_none() { break; }
                if !self.blocks.contains_key(&t) { self.need.insert(t); }
                k += 1;
            }
            (k, "scan")
        } };
        let mut entries = vec![];
        let mut bad: Option<String> = None;
        for k in 0..count {
            let b = ctx.pe.bytes(table + 4 * k as u32, 4);
            if b.len() < 4 { self.unresolved.push((ip, "table runs off the image".into())); return; }
            let e = i32::from_le_bytes(b.try_into().unwrap());
            let t = (x + e as i64) as u32;
            if !self.blocks.contains_key(&t) {
                if in_ranges(&self.ranges, t) && self.ins_at(t).is_some() { self.need.insert(t); }
                if bad.is_none() { bad = Some(format!("table entry {} -> {:#x} is not a block of this function", k, t)); }
            }
            entries.push(t);
        }
        if let Some(w) = bad { self.unresolved.push((ip, w)); return; }
        if entries.is_empty() { self.unresolved.push((ip, "empty table".into())); return; }
        let mut by_target: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
        for (k, t) in entries.iter().enumerate() { by_target.entry(*t).or_default().push(k as u32); }
        let succ: Vec<Edge> = by_target.into_iter().map(|(t, cases)| Edge { to: t, kind: EKind::Case, case: cases, outside: false }).collect();
        self.blocks.get_mut(&bs).unwrap().succ = succ;
        self.switches.push(Switch { ip, table, entries, bound: how, idx: idx_reg });
    }
}

pub fn cc_text(cc: ConditionCode) -> &'static str {
    use ConditionCode::*;
    match cc { e => "==", ne => "!=", l => "<s", ge => ">=s", le => "<=s", g => ">s", b => "<u", ae => ">=u", be => "<=u", a => ">u", s => "<0", ns => ">=0", o => "overflow", no => "!overflow", p => "parity", np => "!parity", _ => "?" }
}
