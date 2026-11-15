// Relationship helpers aimed at "how would an expert find the place to interpose / where can a marker ride".
use crate::cmds::*;
use crate::model::{self, hx};
use crate::sym::{Tgt, E};
use crate::Ctx;
use iced_x86::{Decoder, DecoderOptions, OpKind};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

fn sgn(v: i64) -> String { if v < 0 { format!("-{:#x}", -(v as i128)) } else { format!("{:#x}", v) } }

pub fn callers_of(ctx: &mut Ctx, f: u32) -> Vec<(u32, u32)> {
    let pairs: Vec<(u32, u32)> = ctx.xrefs().to(f).to_vec();
    let mut out = vec![];
    for (_, from) in pairs {
        let b = ctx.pe.bytes(from, 15);
        let mut d = Decoder::with_ip(64, b, from as u64, DecoderOptions::NONE);
        if !d.can_decode() { continue; }
        let i = d.decode();
        if matches!(i.flow_control(), iced_x86::FlowControl::Call | iced_x86::FlowControl::UnconditionalBranch) && i.op0_kind() == OpKind::NearBranch64 { out.push((ctx.fn_start(from), from)); }
    }
    out
}

// What each outcome of one branch leads to: the calls that CANNOT run unless that branch edge is taken (the edge is one of the call block's exact gates: removing it
// disconnects the block from the entry). Unlike plain reachability this also works inside loops. Calls that run on both outcomes are not attributed.
pub fn branch_outcomes(ctx: &Ctx, s: &crate::sym::Sum, branch_ip: u32) -> Value {
    let blk = match s.cfg.block_of(branch_ip) { Some(b) => b.start, None => return Value::Null };
    let mut gate_cache: HashMap<u32, Vec<(u32, usize)>> = HashMap::new();
    let mut out = vec![];
    for (i, e) in s.cfg.blocks[&blk].succ.iter().enumerate() {
        if e.outside { continue; }
        let mut calls = vec![];
        for c in &s.calls {
            let cb = match s.cfg.block_of(c.ip) { Some(b) => b.start, None => continue };
            let g = gate_cache.entry(cb).or_insert_with(|| if s.cfg.reach_without(cb, None, None) { s.cfg.gates(cb) } else { vec![] });
            if !g.contains(&(blk, i)) { continue; }
            calls.push(match &c.tgt {
                crate::sym::Tgt::Direct(t) => json!({"ip": hx(c.ip), "call": ctx.flabel(*t), "tail": c.tail}),
                crate::sym::Tgt::Slot { vptr_off, disp, .. } => json!({"ip": hx(c.ip), "virtual_slot": disp / 8, "vptr_off": vptr_off, "tail": c.tail}),
                other => json!({"ip": hx(c.ip), "indirect": format!("{:?}", other), "tail": c.tail}),
            });
        }
        let mut writes = vec![];
        for a in s.accs.iter().filter(|a| a.write && !a.fp) {
            let cb = match s.cfg.block_of(a.ip) { Some(b) => b.start, None => continue };
            let g = gate_cache.entry(cb).or_insert_with(|| if s.cfg.reach_without(cb, None, None) { s.cfg.gates(cb) } else { vec![] });
            if g.contains(&(blk, i)) { writes.push(json!({"ip": hx(a.ip), "to": format!("{}{}", a.base, if a.off >= 0 { format!("+{:#x}", a.off) } else { format!("-{:#x}", -a.off) }), "size": a.size, "value": a.value.as_ref().map(|v| v.to_string())})); }
        }
        out.push(json!({"edge": format!("{:?}", e.kind), "to": hx(e.to), "calls_that_need_this_outcome": calls, "memory_writes_that_need_this_outcome": writes,
            "target_block_itself": s.cfg.blocks.get(&e.to).map(|tb| json!({"range": [hx(tb.start), hx(tb.end)], "calls": s.calls.iter().filter(|c| c.ip >= tb.start && c.ip < tb.end).count(), "memory_writes": s.accs.iter().filter(|a| a.write && !a.fp && a.ip >= tb.start && a.ip < tb.end).count(), "predecessors": s.cfg.preds.get(&e.to).map_or(0, |p| p.len())})),
            "reading": "calls/writes listed are those that cannot execute unless this outcome is taken. Empty with predecessors>1 means this outcome rejoins code that the other outcome also reaches (common in loops): then the difference is only in the target block itself."}));
    }
    json!(out)
}

pub fn cmd_decide(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let f = crate::cmds::fn_arg(ctx, a, 0)?;
    let sites = callers_of(ctx, f);
    let total = sites.len();
    let mut items = vec![];
    for (caller, site) in sites.iter().take(a.num("callers", 80)) {
        let s = ctx.sum(*caller);
        let tag = format!("ret@{:x}", site);
        let conds: Vec<Value> = s.conds.values().filter(|c| c.taken.contains(&tag)).map(|c| {
            let blk = s.cfg.block_of(c.ip).map(|b| b.start);
            let succ: Vec<Value> = blk.map(|b| s.cfg.blocks[&b].succ.iter().map(|e| json!({"edge": format!("{:?}", e.kind), "to": hx(e.to)})).collect()).unwrap_or_default();
            json!({"branch_ip": hx(c.ip), "if_taken": c.taken, "if_not_taken": c.not_taken, "successors": succ, "outcomes": branch_outcomes(ctx, &s, c.ip)})
        }).collect();
        let passed_on = s.calls.iter().filter(|c| c.ip != *site && c.args.iter().any(|x| x.to_string().contains(&tag))).count();
        let stored = s.accs.iter().filter(|x| x.write && x.value.as_ref().map_or(false, |v| v.to_string().contains(&tag))).count();
        items.push(json!({"caller": ctx.flabel(*caller), "site": hx(*site), "result_tested_by": conds, "result_passed_to_calls": passed_on, "result_stored_to_memory": stored}));
    }
    let deciding = items.iter().filter(|i| i["result_tested_by"].as_array().map_or(false, |a| !a.is_empty())).count();
    Ok(json!({"fn": ctx.flabel(f), "call_sites_total": total, "sites_where_result_decides_a_branch": deciding, "sites": page(items, a, 60),
        "meaning": "a function whose return value is tested by a branch in its callers is a decision point: changing its result (or hooking it) selects which downstream path runs",
        "trust": "derived (the condition text contains this call's result expression; the value itself is computed at runtime)"}))
}

pub fn cmd_choke(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let from = crate::cmds::fn_arg(ctx, a, 0)?;
    let to = crate::cmds::fn_arg(ctx, a, 1)?;
    let mode = a.s("virt").unwrap_or("none").to_string();
    let depth = a.num("depth", 10);
    let cap = a.num("cap", 400_000);
    let (parent, hit) = bfs(ctx, from, Some(to), &mode, depth, &HashSet::new(), cap);
    if !hit { return Ok(json!({"from": ctx.flabel(from), "to": ctx.flabel(to), "edge_mode": mode, "reachable": false, "note": "no path in this edge set (not a proof of impossibility)"})); }
    let mut path = vec![to];
    let mut cur = to;
    while cur != from { cur = parent[&cur].0; path.push(cur); }
    path.reverse();
    let mut chokes = vec![];
    for n in &path[1..path.len() - 1] {
        let (_, still) = bfs_skip(ctx, from, Some(to), &mode, depth, &HashSet::new(), cap, Some(*n));
        if !still { chokes.push(ctx.flabel(*n)); }
    }
    let mut hops: Vec<u32> = model::all_edges(ctx, from, &mode).iter().map(|e| ctx.fn_start(e.to)).collect::<BTreeSet<_>>().into_iter().collect();
    hops.truncate(60);
    let mut first_hops = 0;
    for h in &hops { let (_, ok) = bfs_skip(ctx, *h, Some(to), &mode, depth.saturating_sub(1), &HashSet::new(), cap / 4, Some(from)); if ok { first_hops += 1; } }
    Ok(json!({"from": ctx.flabel(from), "to": ctx.flabel(to), "edge_mode": mode, "reachable": true, "shortest_path": path.iter().map(|p| ctx.flabel(*p)).collect::<Vec<_>>(),
        "chokepoints": chokes, "distinct_first_hops_reaching_target": first_hops,
        "meaning": "a chokepoint is on EVERY call path from..to in this edge set: one hook there sees all traffic. Empty = several independent routes (e.g. a batched and a non-batched renderer): hook the target or each route.",
        "trust": "derived over the chosen edge set (none = direct calls only; widen with --virt derived|cand|slot)"}))
}

pub fn cmd_common(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let fa = crate::cmds::fn_arg(ctx, a, 0)?;
    let fb = crate::cmds::fn_arg(ctx, a, 1)?;
    let depth = a.num("depth", 6);
    let up = |ctx: &mut Ctx, f: u32| -> HashMap<u32, usize> {
        let mut seen: HashMap<u32, usize> = HashMap::new();
        seen.insert(f, 0);
        let mut q = VecDeque::new();
        q.push_back(f);
        while let Some(x) = q.pop_front() {
            let d = seen[&x];
            if d >= depth || seen.len() > 60_000 { continue; }
            for (c, _) in callers_of(ctx, x) { if !seen.contains_key(&c) { seen.insert(c, d + 1); q.push_back(c); } }
        }
        seen
    };
    let ua = up(ctx, fa);
    let ub = up(ctx, fb);
    let mut common: Vec<(usize, u32, usize, usize)> = ua.iter().filter_map(|(f, da)| ub.get(f).map(|db| (da + db, *f, *da, *db))).collect();
    common.sort();
    Ok(json!({"a": ctx.flabel(fa), "b": ctx.flabel(fb), "depth_limit": depth,
        "nearest_common_callers": common.iter().take(a.num("max", 15)).map(|(t, f, da, db)| { let mut l = ctx.flabel(*f); l["depth_from_a"] = json!(da); l["depth_from_b"] = json!(db); l["total"] = json!(t); l }).collect::<Vec<_>>(),
        "meaning": "functions that (transitively) call both: where a producer and a consumer meet, i.e. the routine that owns the pipeline. Direct call edges only (virtual dispatch is not followed).", "trust": "proven (direct call edges from the xref index)"}))
}

pub fn cmd_uses(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let off = i64::from_str_radix(a.pos.first().ok_or("uses <off> [--class C | --fn F]")?.trim_start_matches("0x").trim_start_matches('+'), 16).map_err(|e| e.to_string())?;
    let (fns, this): (Vec<u32>, bool) = if let Some(c) = a.s("class") { (class_functions(ctx, c), true) } else if let Some(f) = a.s("fn") { (vec![crate::resolve(ctx, &[f])?], false) } else { return Err("give --class <name|vtable> or --fn <fn>".into()); };
    let mut items = vec![];
    let mut tot: BTreeMap<&'static str, u32> = BTreeMap::new();
    for f in fns.iter().take(a.num("fnlimit", 300)) {
        let s = ctx.sum(*f);
        let exprs: Vec<(u32, String)> = s.accs.iter().filter(|x| x.read && !x.write && !x.indexed && x.off == off && (!this || x.base == E::Arg(0))).map(|x| (x.ip, E::Load(Box::new(x.base.clone().add(x.off)), x.size).to_string())).collect();
        if exprs.is_empty() { continue; }
        let mut uses: Vec<Value> = vec![];
        for (rip, e) in &exprs {
            for c in s.conds.values().filter(|c| c.ip > *rip && c.taken.contains(e.as_str())) {
                let kind = if c.taken.contains(&format!("{} & ", e)) || c.taken.contains(&format!(" & {}", e)) { "masked-then-tested" } else { "compared" };
                *tot.entry(kind).or_default() += 1;
                uses.push(json!({"kind": kind, "branch_ip": hx(c.ip), "cond": c.taken}));
            }
            for c in s.calls.iter().filter(|c| c.ip > *rip) {
                for (i, x) in c.args.iter().enumerate() {
                    if x.to_string().contains(e.as_str()) {
                        *tot.entry("passed-to-call").or_default() += 1;
                        uses.push(json!({"kind": "passed-to-call", "call_ip": hx(c.ip), "arg": i, "arg_expr": x.to_string(), "callee": match &c.tgt { Tgt::Direct(t) => ctx.flabel(*t), _ => json!("indirect") }}));
                    }
                }
            }
            for x in s.accs.iter().filter(|x| x.ip > *rip) {
                if x.indexed && x.base.to_string().contains(e.as_str()) { *tot.entry("used-as-index/pointer").or_default() += 1; uses.push(json!({"kind": "used-as-index/pointer", "ip": hx(x.ip), "expr": x.base.to_string()})); }
                else if x.write && x.value.as_ref().map_or(false, |v| v.to_string().contains(e.as_str())) { *tot.entry("stored").or_default() += 1; uses.push(json!({"kind": "stored", "ip": hx(x.ip), "to": format!("{}+{}", x.base, sgn(x.off)), "value": x.value.as_ref().unwrap().to_string()})); }
            }
        }
        items.push(json!({"fn": ctx.flabel(*f), "reads_at": exprs.iter().map(|(i, e)| json!({"ip": hx(*i), "expr": e})).collect::<Vec<_>>(), "uses": uses}));
    }
    Ok(json!({"offset": sgn(off), "functions_in_scope": fns.len(), "totals": tot, "functions": page(items, a, 30),
        "how_to_read": "usage profile of the value read from that field. If every reader only compares it with small constants, masks it, or uses it as a bounded index, values/bits outside that range are free to carry a marker; if it is passed on or stored, follow it with `uses`/`rw` on the next field. A marker (e.g. +1000 on an id) must be removed again before any reader that indexes or compares it.",
        "trust": "derived: textual containment of the exact load expression in later events of the same function; memory is not modelled, so a store between the load and the use could change the value"}))
}

pub fn cmd_anchors(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let f = crate::cmds::fn_arg(ctx, a, 0)?;
    let s = ctx.sum(f);
    let mut strs = vec![];
    for (ip, ad, t) in &s.strs {
        let n = ctx.xrefs().to(*ad).len();
        strs.push(json!({"ip": hx(*ip), "addr": hx(*ad), "text": t, "functions_referencing_it": n, "uniqueness": if n == 1 { "unique" } else if n <= 3 { "rare" } else { "common" }}));
    }
    let mut callees: BTreeMap<u32, u32> = BTreeMap::new();
    for e in model::direct_edges(ctx, f).iter() { if e.kind == "call" { *callees.entry(e.to).or_default() += 1; } }
    let mut cl = vec![];
    for (t, n) in callees {
        let fan = callers_of(ctx, t).iter().map(|c| c.0).collect::<BTreeSet<_>>().len();
        cl.push((fan, t, n));
    }
    cl.sort();
    let vts = ctx.vts.as_ref().unwrap();
    let ctors: Vec<Value> = vts.list.iter().filter(|v| v.ctors.iter().any(|c| c.func == f)).map(|v| json!({"vtable": hx(v.rva), "class": ctx.vt_name(v)})).collect();
    let fan_in = callers_of(ctx, f).iter().map(|c| c.0).collect::<BTreeSet<_>>().len();
    Ok(json!({"fn": ctx.flabel(f), "size": s.cfg.end - s.cfg.begin, "blocks": s.cfg.blocks.len(), "distinct_callers": fan_in,
        "strings": strs, "callees_by_fan_in": cl.iter().take(25).map(|(fan, t, n)| { let mut l = ctx.flabel(*t); l["distinct_callers"] = json!(fan); l["call_sites_here"] = json!(n); l }).collect::<Vec<_>>(),
        "type_hash_immediates": s.comp_refs.iter().map(|(ip, n)| json!({"ip": hx(*ip), "type": n})).collect::<Vec<_>>(), "constructs_vtables": ctors,
        "meaning": "what an expert anchors on when re-finding this function in another build: a unique string, a callee with very few callers, a type-hash immediate, or the vtable it installs",
        "trust": "proven (counts come from the xref index; fan-in counts only direct call/jmp sites)"}))
}
