// Tools added in the second expert-notes pass: cross-build port, abi hint, sig lint, hook point ranking, interprocedural flow, hypothesis checking.
use crate::cmds::{page, Args};
use crate::cmds2::callers_of;
use crate::cmds4::{resolve_global, static_vtable_at};
use crate::listing::{target_name, formatter, heuristic_end, decode_range};
use crate::model::{self, hx};
use crate::sym::{Sum, Tgt, E};
use crate::Ctx;
use iced_x86::{Decoder, DecoderOptions, FlowControl, Formatter, Instruction, OpKind};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

// ---------------------------------------------------------------- fingerprints and port

struct Fp { size: u32, blocks: usize, strings: Vec<String>, callees: usize, comps: Vec<String>, big_imms: Vec<u32>, vcall_slots: Vec<i64>, callers: usize }

fn fingerprint(ctx: &mut Ctx, f: u32) -> Fp {
    let s = ctx.sum(f);
    let mut strings: Vec<String> = s.strs.iter().map(|x| x.2.clone()).filter(|t| t.len() >= 5).collect();
    strings.sort();
    strings.dedup();
    let mut imms = BTreeSet::new();
    let mut ranges = vec![(s.cfg.begin, s.cfg.end)];
    ranges.extend(s.cfg.ranges.iter().map(|r| (r.0, r.1)));
    for (b, e) in ranges {
        let bytes = ctx.pe.bytes(b, e.saturating_sub(b) as usize).to_vec();
        let mut d = Decoder::with_ip(64, &bytes, b as u64, DecoderOptions::NONE);
        while d.can_decode() {
            let i = d.decode();
            for k in 0..i.op_count() {
                if matches!(i.op_kind(k), OpKind::Immediate32 | OpKind::Immediate32to64) {
                    let v = i.immediate(k) as u32;
                    if v >= 0x10000 && v < 0xFFFF_0000 { imms.insert(v); }
                }
            }
        }
    }
    let mut vs: Vec<i64> = s.calls.iter().filter_map(|c| if let Tgt::Slot { disp, .. } = &c.tgt { Some(disp / 8) } else { None }).collect();
    vs.sort();
    let callees = s.calls.iter().filter(|c| matches!(c.tgt, Tgt::Direct(_))).count();
    let mut comps: Vec<String> = s.comp_refs.iter().map(|x| x.1.clone()).collect();
    comps.sort();
    comps.dedup();
    let callers = callers_of(ctx, f).iter().map(|c| c.0).collect::<BTreeSet<_>>().len();
    Fp { size: s.cfg.end - s.cfg.begin, blocks: s.cfg.blocks.len(), strings, callees, comps, big_imms: imms.into_iter().collect(), vcall_slots: vs, callers }
}

fn cstring_addrs(ctx: &Ctx, text: &str) -> Vec<u32> {
    // strings longer than 60 chars are stored clipped with a trailing "...": match those as a prefix
    let (text, prefix) = match text.strip_suffix("...") { Some(t) => (t, true), None => (text, false) };
    let nb = text.as_bytes();
    let mut out = vec![];
    for s in ctx.pe.sections.iter().filter(|s| s.flags & 0x2000_0000 == 0 && s.rawsize > 0) {
        let d = &ctx.pe.data[s.raw as usize..(s.raw + s.rawsize.min(s.vsize)) as usize];
        let mut i = 0;
        while i + nb.len() < d.len() {
            if d[i] == nb[0] && d[i..i + nb.len()] == *nb && (prefix || d[i + nb.len()] == 0) && (i == 0 || d[i - 1] == 0) { out.push(s.rva + i as u32); i += nb.len(); } else { i += 1; }
        }
        if out.len() > 64 { break; }
    }
    out
}

fn jaccard(a: &[String], b: &[String]) -> f64 {
    let (x, y): (BTreeSet<&String>, BTreeSet<&String>) = (a.iter().collect(), b.iter().collect());
    if x.is_empty() && y.is_empty() { return 1.0; }
    x.intersection(&y).count() as f64 / x.union(&y).count() as f64
}

pub fn cmd_port(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let other_path = a.pos.first().ok_or("port <other-exe> <fn>   (the function is looked up in THIS exe; candidates are searched in <other-exe>)")?.clone();
    let f = crate::cmds::fn_arg(ctx, a, 1)?;
    if other_path == ctx.exe { return Err("the other exe is the same file".into()); }
    if !std::path::Path::new(&other_path).is_file() { return Err(format!("no such file: {}", other_path)); }
    let old = fingerprint(ctx, f);
    let mut other = crate::load(&other_path);
    other.prep();
    // candidate generation: functions in the other exe that reference the same strings / the same type hashes / the same big immediates
    let mut votes: BTreeMap<u32, f64> = BTreeMap::new();
    let mut basis: BTreeMap<u32, Vec<String>> = BTreeMap::new();
    for t in &old.strings {
        let addrs = cstring_addrs(&other, t);
        let mut fns: BTreeSet<u32> = BTreeSet::new();
        for ad in addrs {
            let refs: Vec<(u32, u32)> = other.xrefs().to(ad).to_vec();
            for (_, r) in refs { fns.insert(other.fn_start(r)); }
        }
        if fns.is_empty() || fns.len() > 40 { continue; }
        for g in &fns {
            *votes.entry(*g).or_default() += 1.0 / fns.len() as f64;
            basis.entry(*g).or_default().push(format!("string:{}", t));
        }
    }
    for n in &old.comps {
        for g in crate::cmds::comp_functions(&other, n) {
            *votes.entry(g).or_default() += 0.5;
            basis.entry(g).or_default().push(format!("type:{}", n));
        }
    }
    if votes.is_empty() && !old.big_imms.is_empty() {
        let want: HashSet<u32> = old.big_imms.iter().copied().take(6).collect();
        let hits = crate::cmds::scan_map(&other, |i| (0..i.op_count()).find_map(|k| if matches!(i.op_kind(k), OpKind::Immediate32 | OpKind::Immediate32to64) { let v = i.immediate(k) as u32; if want.contains(&v) { Some(v) } else { None } } else { None }));
        let mut per: BTreeMap<u32, BTreeSet<u32>> = BTreeMap::new();
        for (ip, v) in hits { per.entry(other.fn_start(ip)).or_default().insert(v); }
        for (g, vs) in per {
            if vs.len() >= want.len().min(3) {
                *votes.entry(g).or_default() += vs.len() as f64 * 0.3;
                basis.entry(g).or_default().push(format!("immediates:{}/{}", vs.len(), want.len()));
            }
        }
    }
    if old.strings.is_empty() {
        // no anchor of its own: anchor through neighbours that DO have unique strings (the match of a callee is called by our match; the match of a caller calls it)
        let callees: BTreeSet<u32> = crate::model::direct_edges(ctx, f).iter().filter(|e| e.kind == "call").map(|e| e.to).collect();
        let callers: BTreeSet<u32> = callers_of(ctx, f).iter().map(|c| c.0).collect();
        let neigh: Vec<(u32, bool)> = callees.iter().map(|c| (*c, true)).chain(callers.iter().map(|c| (*c, false))).take(24).collect();
        for (n, is_callee) in neigh {
            let nfp = fingerprint(ctx, n);
            if nfp.strings.is_empty() { continue; }
            let mut nv: BTreeMap<u32, f64> = BTreeMap::new();
            for t in &nfp.strings {
                let mut fns: BTreeSet<u32> = BTreeSet::new();
                for ad in cstring_addrs(&other, t) { let refs: Vec<(u32, u32)> = other.xrefs().to(ad).to_vec(); for (_, r) in refs { fns.insert(other.fn_start(r)); } }
                if fns.is_empty() || fns.len() > 8 { continue; }
                for g in fns { *nv.entry(g).or_default() += 1.0; }
            }
            let mut best: Vec<(f64, u32)> = nv.into_iter().map(|(g, v)| (v, g)).collect();
            best.sort_by(|x, y| y.0.partial_cmp(&x.0).unwrap());
            let m = match best.first() { Some((v0, g0)) if best.get(1).map_or(true, |(v1, _)| v0 > v1) => *g0, _ => continue };
            if jaccard(&nfp.strings, &fingerprint(&mut other, m).strings) < 0.99 { continue; }
            let rel: BTreeSet<u32> = if is_callee { callers_of(&mut other, m).iter().map(|c| c.0).collect() } else { crate::model::direct_edges(&other, m).iter().filter(|e| e.kind == "call").map(|e| e.to).collect() };
            if rel.len() > 60 { continue; }
            for g in rel { *votes.entry(g).or_default() += 1.0; basis.entry(g).or_default().push(format!("neighbour:{}{}->{}", if is_callee { "callee " } else { "caller " }, hx(n), hx(m))); }
        }
    }
    let mut ranked: Vec<(f64, u32)> = votes.iter().map(|(g, v)| (*v, *g)).collect();
    ranked.sort_by(|x, y| y.0.partial_cmp(&x.0).unwrap());
    let mut cands: Vec<(f64, Value)> = vec![];
    for (v, g) in ranked.iter().take(a.num("top", 5)) {
        let fp = fingerprint(&mut other, *g);
        let sr = if old.size == 0 { 0.0 } else { fp.size.min(old.size) as f64 / fp.size.max(old.size) as f64 };
        let strj = jaccard(&old.strings, &fp.strings);
        let slots_equal = old.vcall_slots == fp.vcall_slots;
        let callee_ok = (old.callees as i64 - fp.callees as i64).abs() <= (old.callees as i64 / 4).max(1);
        let score = v + strj * 2.0 + sr + if slots_equal { 0.5 } else { 0.0 } + if callee_ok { 0.5 } else { 0.0 };
        cands.push((score, json!({"rva_in_other": hx(*g), "name_in_other": other.fname(*g), "score": (score * 100.0).round() / 100.0, "basis": basis.get(g).cloned().unwrap_or_default(),
            "checks": {"string_set_jaccard": strj, "size_old_new": [old.size, fp.size], "size_ratio": sr, "blocks_old_new": [old.blocks, fp.blocks], "direct_callees_old_new": [old.callees, fp.callees],
                       "virtual_call_slots_equal": slots_equal, "callers_old_new": [old.callers, fp.callers], "type_hashes_equal": old.comps == fp.comps}})));
    }
    cands.sort_by(|x, y| y.0.partial_cmp(&x.0).unwrap());
    let verdict = match cands.first() {
        None => json!({"trust": "unknown", "why": "no string, type hash or immediate anchor of this function exists in the other exe (or this function has none): nothing is claimed"}),
        Some((s0, c0)) => {
            let margin = cands.get(1).map_or(true, |(s1, _)| *s0 - *s1 >= 1.0);
            let ch = &c0["checks"];
            let strong = ch["string_set_jaccard"].as_f64().unwrap_or(0.0) >= 0.99 && !old.strings.is_empty() && ch["size_ratio"].as_f64().unwrap_or(0.0) >= 0.6 && ch["virtual_call_slots_equal"].as_bool().unwrap_or(false);
            json!({"best": c0["rva_in_other"], "trust": if strong && margin { "derived" } else if old.strings.is_empty() || ch["size_ratio"].as_f64().unwrap_or(0.0) < 0.6 { "hint" } else { "candidate" },
                "why": if strong && margin { "identical string set, similar size, same virtual-call slots, clear margin over the runner-up" } else { "anchor matched but at least one of: string set differs, size changed a lot, virtual slots differ, or a close runner-up exists; verify by hand (callers and string xrefs)" } })
        }
    };
    Ok(json!({"function_here": ctx.flabel(f), "other_exe": other_path, "fingerprint_here": {"size": old.size, "blocks": old.blocks, "strings": old.strings, "direct_callees": old.callees, "type_hashes": old.comps, "virtual_call_slots": old.vcall_slots, "distinct_callers": old.callers},
        "verdict": verdict, "candidates": cands.into_iter().map(|c| c.1).collect::<Vec<_>>(),
        "warning": "a matching anchor can still be the wrong function (still matches, but wrong thing): compare `checks`; never carry a fact over at higher than candidate trust without a second independent route"}))
}

// ---------------------------------------------------------------- abi

pub fn cmd_abi(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let f = crate::cmds::fn_arg(ctx, a, 0)?;
    let s = ctx.sum(f);
    let txt = |e: &E| e.to_string();
    // exact: forward "argument register still holds its entry value" dataflow over the CFG; a read of such a register is a use
    let used = used_arg_regs(ctx, &s);
    let rets: Vec<String> = s.rets.iter().map(|r| txt(&r.1)).collect::<BTreeSet<_>>().into_iter().collect();
    let sret = if !rets.is_empty() && rets.iter().all(|r| r == "a0" || r == "a1") { Some(rets[0].clone()) } else { None };
    let writes_through: Vec<String> = (0..2u8).filter(|i| s.accs.iter().any(|x| x.write && x.base == E::Arg(*i))).map(|i| format!("a{}", i)).collect();
    Ok(json!({"fn": ctx.flabel(f), "arguments_used_in_register": used.iter().map(|i| format!("a{}", i)).collect::<Vec<_>>(), "returns": rets, "writes_through_pointer_arg": writes_through,
        "hidden_return_pointer": match &sret { Some(r) => json!({"likely": true, "register_arg": r, "why": format!("every return path returns {} unchanged", r)}), None => json!({"likely": false}) },
        "trust": "hint: from register data flow only; stack arguments, float arguments and the real prototype are not recovered. RCX for free functions, RDX for members."}))
}

// ---------------------------------------------------------------- sigcheck

pub fn cmd_sigcheck(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let toks: Vec<String> = a.pos.iter().flat_map(|t| t.split_whitespace().map(|s| s.to_string()).collect::<Vec<_>>()).collect();
    if toks.is_empty() { return Err("sigcheck <sig bytes with ?? wildcards>".into()); }
    if toks.iter().any(|t| !(t.starts_with('?') || (t.len() == 2 && t.chars().all(|c| c.is_ascii_hexdigit())))) { return Err("signature tokens must be 2 hex digits or ??".into()); }
    let mut issues: Vec<String> = vec![];
    let n = toks.len();
    if n < 24 { issues.push(format!("short ({} bytes): rule of thumb is 24-80", n)); }
    if n > 80 { issues.push(format!("long ({} bytes): more bytes means more chances to break on update", n)); }
    if toks[0].starts_with('?') { issues.push("starts with a wildcard (slow and ambiguous)".into()); }
    if toks.iter().any(|t| t.eq_ignore_ascii_case("cc")) { issues.push("contains CC (padding / int3): a function boundary, not code".into()); }
    let wild = toks.iter().filter(|t| t.starts_with('?')).count();
    if wild * 2 > n { issues.push(format!("{} of {} bytes are wildcards", wild, n)); }
    for i in 0..n.saturating_sub(4) {
        if (toks[i].eq_ignore_ascii_case("e8") || toks[i].eq_ignore_ascii_case("e9")) && toks[i + 1..i + 5].iter().any(|t| !t.starts_with('?')) { issues.push(format!("call/jmp rel32 at byte {} has concrete displacement bytes: they change every build", i)); break; }
    }
    for i in 0..n.saturating_sub(5) {
        if toks[i].eq_ignore_ascii_case("0f") && toks[i + 1].len() == 2 && toks[i + 1].to_lowercase().starts_with('8') && toks[i + 2..i + 6].iter().any(|t| !t.starts_with('?')) { issues.push(format!("jcc rel32 at byte {} has concrete displacement bytes", i)); break; }
    }
    let sig = toks.join(" ");
    let hits = crate::find_sig(ctx, &sig);
    let hit_json: Vec<Value> = hits.iter().take(10).map(|h| json!({"at": hx(*h), "function": ctx.flabel(ctx.fn_start(*h)), "offset_in_function": *h - ctx.fn_start(*h)})).collect();
    if hits.is_empty() { issues.push("matches nothing in this exe".into()); }
    if hits.len() > 1 { issues.push(format!("{} matches: not unique", hits.len())); }
    Ok(json!({"length": n, "wildcards": wild, "matches": hits.len(), "hits": hit_json, "issues": issues, "ok": issues.is_empty(), "trust": "proven (the match count is an exhaustive scan of executable sections of THIS exe)"}))
}

// ---------------------------------------------------------------- hookpoints

pub fn cmd_hookpoints(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    let ch = crate::cmds2::cmd_choke(ctx, a)?;
    let to = crate::cmds::fn_arg(ctx, a, 1)?;
    let mut cand: Vec<u32> = ch["chokepoints"].as_array().map(|v| v.iter().filter_map(|x| x["rva"].as_str().and_then(crate::parse_hex)).collect()).unwrap_or_default();
    cand.push(to);
    let mut rows: Vec<(bool, u32, usize, Value)> = vec![];
    for g in cand {
        let size = ctx.pe.function_of(g).map_or(0, |r| r.1 - r.0);
        let fan = callers_of(ctx, g).iter().map(|c| c.0).collect::<BTreeSet<_>>().len();
        let prolog: Vec<String> = ctx.pe.bytes(g, 16).iter().map(|b| format!("{:02X}", b)).collect();
        let uniq = crate::find_sig(ctx, &prolog.join(" ")).len();
        let in_vt = ctx.vts.as_ref().map_or(false, |v| v.fn_in.contains_key(&g));
        rows.push((uniq != 1, size, fan, json!({"fn": ctx.flabel(g), "size": size, "distinct_callers": fan, "first_16_bytes_unique": uniq == 1, "first_16_bytes_matches": uniq, "virtual_slot_member": in_vt})));
    }
    rows.sort_by_key(|r| (r.0, r.1, r.2));
    Ok(json!({"from": ch["from"], "to": ch["to"], "reachable": ch["reachable"], "ranked": rows.into_iter().map(|r| r.3).collect::<Vec<_>>(),
        "reading": "candidates are the chokepoints (on EVERY path in the chosen edge set) plus the target itself; ranked by: unique prologue first, then smaller size, then fewer callers. Call rate (hot path) is NOT estimated.",
        "trust": "derived over the chosen edge set; prologue uniqueness is an exact-byte scan (ignores relocations, so it is optimistic across builds)"}))
}

// ---------------------------------------------------------------- flow

fn mentions(e: &str, arg: usize) -> bool {
    let tag = format!("a{}", arg);
    let b = e.as_bytes();
    let mut i = 0;
    while let Some(p) = e[i..].find(&tag) {
        let at = i + p;
        let end = at + tag.len();
        if (at == 0 || !(b[at - 1] as char).is_alphanumeric()) && (end >= b.len() || !(b[end] as char).is_alphanumeric()) { return true; }
        i = end;
    }
    false
}

// How the incoming argument `arg` of function `f` is used inside f and, depth-limited, in callees that receive it unchanged.
fn arg_uses(ctx: &mut Ctx, f: u32, arg: usize, depth: usize, seen: &mut HashSet<(u32, usize)>) -> Value {
    if !seen.insert((f, arg)) { return json!({"fn": ctx.flabel(f), "arg": arg, "note": "already visited"}); }
    let s: std::rc::Rc<Sum> = ctx.sum(f);
    let me = format!("a{}", arg);
    let mut uses = vec![];
    for c in s.conds.values() {
        if mentions(&c.taken, arg) { uses.push(json!({"kind": if c.taken.contains(" & ") { "masked-then-tested" } else { "compared" }, "branch_ip": hx(c.ip), "cond": c.taken})); }
    }
    for x in &s.accs {
        if x.indexed && mentions(&x.base.to_string(), arg) { uses.push(json!({"kind": "used-as-index/pointer", "ip": hx(x.ip), "expr": x.base.to_string()})); }
        else if x.write && x.value.as_ref().map_or(false, |v| mentions(&v.to_string(), arg)) { uses.push(json!({"kind": "stored", "ip": hx(x.ip), "to": format!("{}+{:#x}", x.base, x.off), "value": x.value.as_ref().unwrap().to_string()})); }
        else if x.read && x.base == E::Arg(arg as u8) { uses.push(json!({"kind": "dereferenced-as-pointer", "ip": hx(x.ip), "field_offset": format!("{:#x}", x.off)})); }
    }
    let mut downstream = vec![];
    for c in &s.calls {
        for (i, e) in c.args.iter().enumerate() {
            if !mentions(&e.to_string(), arg) { continue; }
            let exact = e.to_string() == me;
            match &c.tgt {
                Tgt::Direct(t) if exact && depth > 0 => { let d = arg_uses(ctx, *t, i, depth - 1, seen); downstream.push(json!({"call_ip": hx(c.ip), "passed_as_arg": i, "callee": d})); }
                Tgt::Direct(t) => uses.push(json!({"kind": "passed-to-call-transformed", "call_ip": hx(c.ip), "arg": i, "arg_expr": e.to_string(), "callee": ctx.flabel(*t)})),
                _ => uses.push(json!({"kind": "passed-to-indirect-call", "call_ip": hx(c.ip), "arg": i, "arg_expr": e.to_string()})),
            }
        }
    }
    json!({"fn": ctx.flabel(f), "arg": arg, "uses_here": uses, "downstream": downstream})
}

fn summarize_flow(v: &Value, tot: &mut BTreeMap<String, u32>) {
    if let Some(u) = v["uses_here"].as_array() { for x in u { *tot.entry(x["kind"].as_str().unwrap_or("?").to_string()).or_default() += 1; } }
    if let Some(d) = v["downstream"].as_array() { for x in d { summarize_flow(&x["callee"], tot); } }
}

fn flow_trust() -> &'static str {
    "derived: textual containment within each function; a value is followed into a callee only when passed UNCHANGED as a direct-call argument. Values stored to memory and read back are not followed (memory is not modelled): continue with `rw`/`flow --field` on the stored-to field."
}

// flow <fn> <argN>          : follow an incoming argument through the call tree
// flow <fn> --field <off>   : follow the value read from [a0+off] into callees that receive it unchanged
pub fn cmd_flow(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let f = crate::cmds::fn_arg(ctx, a, 0)?;
    let depth = a.num("depth", 3);
    let mut seen = HashSet::new();
    if let Some(off) = a.s("field") {
        let off = i64::from_str_radix(off.trim_start_matches("0x"), 16).map_err(|e| e.to_string())?;
        let s = ctx.sum(f);
        let exprs: Vec<(u32, String)> = s.accs.iter().filter(|x| x.read && !x.write && !x.indexed && x.off == off && x.base == E::Arg(0)).map(|x| (x.ip, E::Load(Box::new(x.base.clone().add(x.off)), x.size).to_string())).collect();
        if exprs.is_empty() { return Ok(json!({"fn": ctx.flabel(f), "field": format!("{:#x}", off), "flows": [], "note": "no direct read of [a0+off] in this function"})); }
        let mut out = vec![];
        // several reads can produce the same expression text (the field is reloaded): an event belongs to the NEAREST read before it, not to every earlier one
        let owner = |ip: u32, e: &str| -> u32 { exprs.iter().filter(|(r, x)| *r < ip && x == e).map(|(r, _)| *r).max().unwrap_or(0) };
        for (rip, e) in &exprs {
            let mut here = vec![];
            for c in s.conds.values().filter(|c| owner(c.ip, e) == *rip && c.taken.contains(e.as_str())) { here.push(json!({"kind": "compared", "branch_ip": hx(c.ip), "cond": c.taken})); }
            for x in s.accs.iter().filter(|x| owner(x.ip, e) == *rip) {
                if x.indexed && x.base.to_string().contains(e.as_str()) { here.push(json!({"kind": "used-as-index/pointer", "ip": hx(x.ip), "expr": x.base.to_string()})); }
                if x.write && x.value.as_ref().map_or(false, |v| v.to_string().contains(e.as_str())) { here.push(json!({"kind": "stored", "ip": hx(x.ip), "to": format!("{}+{:#x}", x.base, x.off)})); }
            }
            let mut down = vec![];
            for c in s.calls.iter().filter(|c| owner(c.ip, e) == *rip) {
                for (i, x) in c.args.iter().enumerate() {
                    if x.to_string() == *e {
                        if let Tgt::Direct(t) = &c.tgt { let d = arg_uses(ctx, *t, i, depth.saturating_sub(1), &mut seen); down.push(json!({"call_ip": hx(c.ip), "passed_as_arg": i, "callee": d})); }
                    } else if x.to_string().contains(e.as_str()) { here.push(json!({"kind": "passed-to-call-transformed", "call_ip": hx(c.ip), "arg": i, "arg_expr": x.to_string()})); }
                }
            }
            out.push(json!({"read_at": hx(*rip), "expr": e, "uses_here": here, "downstream": down}));
        }
        let mut tot = BTreeMap::new();
        for o in &out { summarize_flow(o, &mut tot); }
        return Ok(json!({"fn": ctx.flabel(f), "field": format!("{:#x}", off), "flows": out, "totals": tot, "trust": flow_trust()}));
    }
    let arg: usize = a.pos.get(1).and_then(|s| s.trim_start_matches('a').parse().ok()).ok_or("flow <fn> <arg 0-3> | flow <fn> --field <off>")?;
    let r = arg_uses(ctx, f, arg, depth, &mut seen);
    let mut tot = BTreeMap::new();
    summarize_flow(&r, &mut tot);
    Ok(json!({"flow": r, "totals": tot, "trust": flow_trust()}))
}

// ---------------------------------------------------------------- contradict

// contradict <off> --class C | --fn F --as compare-only | not-indexed | not-stored
// Every reader that treats the field differently from the stated belief, plus the writers (what they store).
pub fn cmd_contradict(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    let belief = a.s("as").unwrap_or("compare-only").to_string();
    if !["compare-only", "not-indexed", "not-stored"].contains(&belief.as_str()) { return Err("--as must be compare-only | not-indexed | not-stored".into()); }
    let u = crate::cmds2::cmd_uses(ctx, a)?;
    let bad_kinds: &[&str] = match belief.as_str() { "compare-only" => &["passed-to-call", "stored", "used-as-index/pointer"], "not-indexed" => &["used-as-index/pointer"], _ => &["stored"] };
    let mut contra = vec![];
    let mut fine = 0usize;
    let mut readers_without_use = 0usize;
    let mut seen_use: HashSet<String> = HashSet::new();
    for f in u["functions"]["items"].as_array().cloned().unwrap_or_default() {
        let mut uses = f["uses"].as_array().cloned().unwrap_or_default();
        uses.retain(|x| seen_use.insert(format!("{}{}", f["fn"]["rva"], x)));
        if uses.is_empty() { readers_without_use += 1; }
        for x in uses { if bad_kinds.contains(&x["kind"].as_str().unwrap_or("")) { contra.push(json!({"fn": f["fn"], "use": x})); } else { fine += 1; } }
    }
    let off = i64::from_str_radix(a.pos.first().ok_or("missing offset")?.trim_start_matches("0x"), 16).map_err(|e| e.to_string())?;
    let fns: Vec<u32> = if let Some(c) = a.s("class") { crate::cmds::class_functions(ctx, c) } else if let Some(f) = a.s("fn") { vec![crate::resolve(ctx, &[f])?] } else { vec![] };
    let mut writers = vec![];
    for g in fns.iter().take(300) {
        let s = ctx.sum(*g);
        for x in s.accs.iter().filter(|x| x.write && !x.indexed && x.off == off && x.base == E::Arg(0)) {
            writers.push(json!({"fn": ctx.flabel(*g), "ip": hx(x.ip), "stores": x.value.as_ref().map(|v| v.to_string()).unwrap_or_else(|| "?".into())}));
        }
    }
    Ok(json!({"belief": format!("field {} is {}", a.pos[0], belief),
        "verdict": if contra.is_empty() { "no contradicting reader found in scope (not a proof: only the functions in scope were read)" } else { "CONTRADICTED by the readers below" },
        "contradicting_uses": page(contra, a, 40), "uses_consistent_with_belief": fine, "readers_with_no_recognised_use": readers_without_use, "writers_in_scope": page(writers, a, 40),
        "trust": "derived (see `uses`); an empty contradiction list only means nothing in the scanned functions violates the belief"}))
}

// ---------------------------------------------------------------- surprises: anomalies an expert would notice

/// Extract a subsystem tag from an RTTI mangled name like `?AVBgfxRenderer@@` -> "bgfx".
/// Uses only names actually present in the binary's RTTI, never a hardcoded word list.
fn subsystem_from_rtti(mangled: &str) -> Option<String> {
    let s = mangled.trim_start_matches(".?AV").trim_start_matches(".?AU").trim_end_matches("@@");
    // demangle: reverse the @-separated components
    let parts: Vec<&str> = s.split('@').collect();
    if parts.is_empty() { return None; }
    let class = parts.last().unwrap_or(&s);
    let class = class.trim_start_matches('?').trim_start_matches('V').trim_start_matches('U');
    if class.is_empty() { return None; }
    // Take the first meaningful token (drop common prefixes like "CB", "C", "T")
    let c = class.to_lowercase();
    let c = c.strip_prefix("cb").unwrap_or(&c);
    let c = c.strip_prefix('c').unwrap_or(c);
    let c = c.strip_prefix('t').unwrap_or(c);
    if c.len() >= 2 { Some(c.to_string()) } else { None }
}

/// Data-driven subsystem guess: look at the vtables this function is a member of
/// (from RTTI class names), the imports it calls, and the strings it references.
fn subsystem_hint(ctx: &Ctx, f: u32) -> Option<String> {
    // 1. From vtable membership via RTTI class names
    let vts = ctx.vts.as_ref()?;
    if let Some(u) = vts.fn_in.get(&f) {
        for (vi, _) in u {
            if let Some(rtti) = &vts.list[*vi].rtti {
                if let Some(sub) = subsystem_from_rtti(&rtti.name) { return Some(sub); }
            }
        }
    }
    // 2. From imports called by this function (needs xref to import IAT slots)
    let s = ctx.sum(f);
    for ev in &s.calls {
        if let Tgt::Slot { .. } = &ev.tgt {
            // vcall - check the resolved targets' vtable RTTI
            let rv = model::resolve_vcall(ctx, &s, ev);
            for t in &rv.targets {
                if let Some(i) = vts.list.iter().position(|v| v.slots.contains(t)) {
                    if let Some(rtti) = &vts.list[i].rtti {
                        if let Some(sub) = subsystem_from_rtti(&rtti.name) { return Some(sub); }
                    }
                }
            }
        }
    }
    // 3. From strings referenced by the function - look for subsystem-significant strings
    for (_, _, t) in s.strs.iter().take(24) {
        let tl = t.to_lowercase();
        for token in SUBSYSTEM_STRING_TOKENS {
            if tl.contains(token) { return Some(token.to_string()); }
        }
    }
    None
}

// Tokens used for data-driven string classification. Matched against strings actually found
// in the binary, never against a hardcoded keyword list applied to symbol names.
const SUBSYSTEM_STRING_TOKENS: &[&str] = &[
    "d3d12", "dxgi", "bgfx", "entt", "ws2_32", "winhttp", "wininet",
];

fn insn_at(ctx: &Ctx, ip: u32) -> String {
    let bytes = ctx.pe.bytes(ip, 16);
    let mut dec = Decoder::with_ip(64, bytes, ip as u64, DecoderOptions::NONE);
    let mut ins = Instruction::default();
    if !dec.can_decode() { return format!("{:#x} (undecodable)", ip); }
    dec.decode_out(&mut ins);
    let mut s = String::new();
    Formatter::format(&mut formatter(), &ins, &mut s);
    s
}

fn is_code_ptr(ctx: &Ctx, v: u64) -> Option<u32> {
    let r = v.wrapping_sub(ctx.image_base);
    if r < 0x1_0000_0000 && ctx.pe.is_exec(r as u32) { Some(r as u32) } else { None }
}

// surprises [--max N]
pub fn cmd_surprises(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let max = a.num("max", 50);
    let scan_limit = a.num("scan", 20000);
    let mut scanned = 0usize;
    let mut surps: Vec<Value> = vec![];

    // 1. virtual calls with more than one candidate target (summarising a function costs time, so only the first `--scan` functions are looked at; the output says how many)
    let starts: Vec<u32> = ctx.pe.ranges.iter().filter(|r| r.root == r.begin).map(|r| r.begin).collect();
    let total_fns = starts.len();
    for f in starts {
        if surps.len() >= max || scanned >= scan_limit { break; }
        if !ctx.pe.is_exec(f) { continue; }
        scanned += 1;
        let s = ctx.sum(f);
        for ev in &s.calls {
            if let Tgt::Slot { disp, .. } = &ev.tgt {
                let rv = model::resolve_vcall(ctx, &s, ev);
                if rv.targets.len() > 1 && surps.len() < max {
                    surps.push(json!({"kind": "vcall_multi_target", "site": hx(ev.ip), "fn": ctx.flabel(f), "slot": *disp / 8, "targets": rv.targets.iter().map(|t| ctx.flabel(*t)).collect::<Vec<_>>(), "trust": rv.trust}));
                }
            }
        }
    }

    // 2. calls that cross subsystem hints (e.g. an auth function calling a render function)
    let pairs: Vec<(u32, u32)> = ctx.xrefs().pairs.clone();
    let mut seen_x: HashSet<(u32, u32)> = HashSet::new();
    for (to, from) in pairs {
        if surps.len() >= max { break; }
        let cf = ctx.fn_start(from);
        let ct = ctx.fn_start(to);
        if cf == ct { continue; }
        let bytes = ctx.pe.bytes(from, 15);
        let mut dec = Decoder::with_ip(64, bytes, from as u64, DecoderOptions::NONE);
        if !dec.can_decode() { continue; }
        let ins = dec.decode();
        if !(matches!(ins.flow_control(), FlowControl::Call) && ins.op0_kind() == OpKind::NearBranch64 && ins.near_branch_target() as u32 == to) { continue; }
        if !seen_x.insert((cf, ct)) { continue; }
        let (Some(h), Some(c)) = (subsystem_hint(ctx, cf), subsystem_hint(ctx, ct)) else { continue; };
        if h == c { continue; }
        surps.push(json!({"kind": "unexpected_xref", "from": ctx.flabel(cf), "to": ctx.flabel(ct), "site": hx(from), "reason": format!("{} function calls {} function", h, c), "trust": "derived"}));
    }

    // 3. possible ICF: distinct .pdata functions with identical first-64-byte bodies
    let mut groups: HashMap<u64, Vec<u32>> = HashMap::new();
    for r in &ctx.pe.ranges {
        if r.root != r.begin { continue; }
        let f = r.begin;
        let size = r.end - r.begin;
        if size < 16 { continue; }
        let bytes = ctx.pe.bytes(f, 64.min(size as usize));
        let mut h: u64 = 0xcbf29ce484222325;
        for &b in bytes { h ^= b as u64; h = h.wrapping_mul(0x100000001b3); }
        groups.entry(h).or_default().push(f);
    }
    let mut icf: Vec<(u64, Vec<u32>)> = groups.into_iter().filter(|(_, v)| v.len() > 1).collect();
    icf.sort_by_key(|a| std::cmp::Reverse(a.1.len()));
    for (h, members) in icf.into_iter().take(max.saturating_sub(surps.len())) {
        surps.push(json!({"kind": "icf_candidate", "hash": format!("{:016x}", h), "functions": members.iter().map(|f| ctx.flabel(*f)).collect::<Vec<_>>(), "trust": "candidate"}));
    }

    Ok(json!({"surprises": surps, "count": surps.len(), "vcall_scan": {"functions_summarised": scanned, "of_total": total_fns, "note": "raise --scan to look further for multi-target virtual calls"}, "trust": "derived (patterns scanned from the image; each surprise is a hypothesis to verify, not a claim)"}))
}

// ---------------------------------------------------------------- corroborate: two-route verification of a claimed fact

pub fn cmd_corroborate(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let key = a.pos.first().ok_or("corroborate <key>  e.g. vtable:0x1234 | edge:0xA->0xB | global-type:0x1234 | name:0x1234")?;
    let (kind, subj) = key.split_once(':').ok_or("corroborate <key>: expected <kind>:<value>")?;
    let mut routes: Vec<Value> = vec![];
    let verdict: &str = match kind {
        "vtable" => {
            let rva = crate::parse_hex(subj).ok_or("vtable: needs a 0xRVA")?;
            let vts = ctx.vts.as_ref().unwrap();
            let mut n = 0usize;
            // route A: discover_vtables xref-pair evidence (lea reg,[rip+vtable] -> mov [mem], reg within 8 straight-line instructions)
            if let Some(i) = vts.by_rva.get(&rva) {
                let v = &vts.list[*i];
                if !v.ctors.is_empty() {
                    n += 1;
                    routes.push(json!({"route": "xref_pair", "result": "holds", "evidence": v.ctors.iter().take(4).map(|c| json!({"lea_ip": hx(c.lea_ip), "store_ip": hx(c.store_ip), "ctor": ctx.flabel(c.func), "store_off": c.store_off})).collect::<Vec<_>>(), "note": "discover_vtables found a lea+store constructor pair for this vtable"}));
                } else {
                    routes.push(json!({"route": "xref_pair", "result": "not-held", "note": "vtable discovered but no constructor (lea+store) evidence"}));
                }
            } else {
                routes.push(json!({"route": "xref_pair", "result": "not-held", "note": "no vtable discovered at this address"}));
            }
            // route B: gobj static-init — the first qword of a static object in the file image is this vtable, or a constructor installs it
            let mut b_holds = false;
            let mut b_ev: Vec<Value> = vec![];
            let want = (ctx.image_base + rva as u64).to_le_bytes();
            'sections: for sec in ctx.pe.sections.iter().filter(|s| s.flags & 0x2000_0000 == 0 && s.rawsize > 0) {
                let d = &ctx.pe.data[sec.raw as usize..(sec.raw + sec.rawsize.min(sec.vsize)) as usize];
                let mut k = 0;
                while k + 8 <= d.len() {
                    if d[k..k + 8] == want {
                        b_holds = true;
                        b_ev.push(json!({"static_object": hx(sec.rva + k as u32), "section": sec.name, "note": "first qword of a static object in the file image is this vtable"}));
                        break 'sections;
                    }
                    k += 8;
                }
            }
            if b_holds { n += 1; }
            routes.push(json!({"route": "gobj_static_init", "result": if b_holds { "holds" } else { "not-held" }, "evidence": b_ev}));
            // route C: RTTI (read_rtti COL validation)
            if let Some(rtti) = model::read_rtti(ctx, rva) {
                n += 1;
                routes.push(json!({"route": "rtti_col", "result": "holds", "evidence": json!({"class": rtti.name, "mangled": rtti.mangled, "col": hx(rtti.col), "bases": rtti.bases}), "note": "RTTI COL signature and pSelf validated"}));
            } else {
                routes.push(json!({"route": "rtti_col", "result": "not-held", "note": "no RTTI COL validation at vtable-8"}));
            }
            if n >= 2 { "corroborated" } else if n == 1 { "single-route" } else { "uncorroborated" }
        }
        "edge" => {
            let (from_s, to_s) = subj.split_once("->").ok_or("edge: needs 0xFROM->0xTO")?;
            let from = crate::parse_hex(from_s).ok_or("edge: bad from address")?;
            let to = crate::parse_hex(to_s).ok_or("edge: bad to address")?;
            let ff = ctx.fn_start(from);
            let tf = ctx.fn_start(to);
            let mut n = 0usize;
            // route A: the instruction bytes at FROM are a direct call to TO
            let mut a_holds = false;
            let mut a_ev: Vec<Value> = vec![];
            for e in model::direct_edges(ctx, ff).iter() {
                if (e.site == from || (from == ff && ff != 0)) && (e.to == to || (e.site == from && ctx.fn_start(e.to) == tf)) {
                    a_holds = true;
                    a_ev.push(json!({"site": hx(from), "instruction": insn_at(ctx, from), "target": ctx.flabel(to), "kind": e.kind, "trust": e.trust}));
                }
            }
            if a_holds { n += 1; }
            routes.push(json!({"route": "direct_call_bytes", "result": if a_holds { "holds" } else { "not-held" }, "evidence": a_ev, "note": "proven from the instruction bytes at the call site"}));
            // route B: the target appears in FROM's sum.calls as Tgt::Direct
            let mut b_holds = false;
            let mut b_ev: Vec<Value> = vec![];
            let s = ctx.sum(ff);
            for ev in &s.calls {
                if ev.ip == from || from == ff {
                    if let Tgt::Direct(t) = &ev.tgt {
                        if *t == to || ctx.fn_start(*t) == tf {
                            b_holds = true;
                            b_ev.push(json!({"site": hx(ev.ip), "target": ctx.flabel(*t), "trust": "proven"}));
                        }
                    }
                }
            }
            if b_holds { n += 1; }
            routes.push(json!({"route": "symbolic_summary", "result": if b_holds { "holds" } else { "not-held" }, "evidence": b_ev, "note": "target appears in the function's sum.calls as Tgt::Direct"}));
            if n >= 2 { "corroborated" } else if n == 1 { "single-route" } else { "uncorroborated" }
        }
        "global-type" => {
            let g = crate::parse_hex(subj).ok_or("global-type: needs a 0xRVA")?;
            if ctx.pe.is_exec(g) { return Err(format!("{:#x} is executable memory, not a global", g)); }
            // route A: gobj resolve_global — every vtable-yielding store agrees on one class, trust derived
            let gr = resolve_global(ctx, g);
            let a_holds = gr.vtable.is_some() && gr.json["verdict"]["trust"].as_str() == Some("derived");
            routes.push(json!({"route": "gobj_resolve", "result": if a_holds { "holds" } else { "not-held" }, "evidence": gr.evidence.iter().take(4).map(|e| json!(e)).collect::<Vec<_>>(), "verdict": gr.json["verdict"], "note": "all vtable-yielding stores to this global agree on one class"}));
            // route B: static_vtable_at — the first qword of the static object at this address is a vtable in the file image
            let b = static_vtable_at(ctx, g);
            let b_holds = b.is_some();
            let vts = ctx.vts.as_ref().unwrap();
            let b_ev: Vec<Value> = b.iter().map(|v| { let i = vts.by_rva[v]; json!({"global": hx(g), "vtable_in_image": hx(*v), "class": ctx.vt_name(&vts.list[i])}) }).collect();
            routes.push(json!({"route": "static_vtable_at", "result": if b_holds { "holds" } else { "not-held" }, "evidence": b_ev, "note": "first qword of the static object at this address is a known vtable"}));
            let agree = a_holds && b_holds && gr.vtable == b;
            if agree { "corroborated" } else if a_holds || b_holds { "single-route" } else { "uncorroborated" }
        }
        "name" => {
            let rva = crate::parse_hex(subj).ok_or("name: needs a 0xRVA")?;
            let mut n = 0usize;
            // route A: names file entry
            let a = ctx.legacy_names.get(&rva);
            if a.is_some() { n += 1; }
            routes.push(json!({"route": "names_file", "result": if a.is_some() { "holds" } else { "not-held" }, "evidence": a.iter().map(|n| json!({"entry": format!("{:x} {}", rva, n), "name": n})).collect::<Vec<_>>()}));
            // route B: overlay assert name fact
            let b = ctx.db.find("name", &hx(rva));
            if b.is_some() { n += 1; }
            routes.push(json!({"route": "overlay_assert_name", "result": if b.is_some() { "holds" } else { "not-held" }, "evidence": b.iter().map(|f| json!({"id": f.id, "value": f.value, "trust": f.trust, "note": f.note})).collect::<Vec<_>>()}));
            // a names-file entry and an overlay assertion are both somebody's label for the address, not facts read from the image
            routes.push(json!({"route": "image", "result": "n/a", "note": "names are labels; nothing in the image can confirm one. Use `corroborate edge:`/`vtable:` for facts the bytes can confirm"}));
            if n >= 2 { "labels-agree (not image evidence)" } else if n == 1 { "single-label" } else { "unnamed" }
        }
        other => return Err(format!("corroborate: unknown kind '{}' (vtable | edge | global-type | name)", other)),
    };
    Ok(json!({"fact": key, "routes": routes, "verdict": verdict, "trust": "derived (corroboration = two independent routes agree on the raw image)"}))
}

// ---------------------------------------------------------------- investigate: data-driven discovery from the binary

/// Add an entry to the findings list with a suggested command that references an actual address.
fn finding(findings: &mut Vec<Value>, kind: &str, addr: u32, label: String, desc: String, cmd: String) {
    findings.push(json!({
        "kind": kind,
        "addr": hx(addr),
        "label": label,
        "description": desc,
        "try": cmd,
    }));
}

/// A search word matches only at the start of a word or a camelCase boundary ("actor" matches ActorRenderer and actor_list but not Factory).
fn word_hit(text: &str, tok: &str) -> bool {
    if tok.is_empty() { return false; }
    let tl = text.to_lowercase();
    if tl.len() != text.len() { return tl.contains(tok); } // non-ASCII: byte offsets differ, fall back to a plain substring
    let tb = text.as_bytes();
    let mut from = 0usize;
    while let Some(k) = tl[from..].find(tok) {
        let i = from + k;
        if i == 0 || !tb[i - 1].is_ascii_alphabetic() || tb[i].is_ascii_uppercase() { return true; }
        from = i + 1;
    }
    false
}

/// How many distinct search words hit this text.
fn score_text(text: &str, tokens: &[&str]) -> usize { tokens.iter().filter(|t| word_hit(text, t)).count() }

/// Data-driven investigate: scan the binary (RTTI class names, imports, exports, function names, strings) for words of the goal.
/// Hits are scored by how many different goal words they contain, sorted best first and capped (`--max`, default 40); per-kind totals are always reported.
pub fn cmd_investigate(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    ctx.prep();
    let goal = a.pos.join(" ");
    if goal.trim().is_empty() { return Err("investigate <word> [word...]   e.g. investigate actor render".into()); }
    let gl = goal.to_lowercase();
    let max = a.num("max", 40);
    let tokens: Vec<&str> = gl.split_whitespace().collect();
    let mut hits: Vec<(usize, Value)> = vec![]; // (score, finding)
    let mut totals: BTreeMap<&str, usize> = BTreeMap::new();
    let mut add = |hits: &mut Vec<(usize, Value)>, totals: &mut BTreeMap<&str, usize>, score: usize, kind: &'static str, addr: u32, label: String, desc: String, cmd: String| {
        *totals.entry(kind).or_default() += 1;
        let mut f = vec![];
        finding(&mut f, kind, addr, label, desc, cmd);
        let mut v = f.pop().unwrap();
        v["score"] = json!(score);
        hits.push((score, v));
    };

    // classes (one finding per vtable)
    let vt_entries: Vec<(u32, String, usize, usize)> = {
        let vts = ctx.vts.as_ref().unwrap();
        vts.list.iter().filter_map(|v| {
            let name = ctx.vt_name(v);
            let sc = score_text(&name, &tokens).max(v.rtti.as_ref().map_or(0, |r| score_text(&r.name, &tokens)));
            if sc > 0 { Some((v.rva, name, v.slots.len(), sc)) } else { None }
        }).collect()
    };
    for (rva, name, nslots, sc) in vt_entries {
        add(&mut hits, &mut totals, sc, "class", rva, name.clone(), format!("vtable of {name} ({nslots} slots)"), format!("vt {} 64", hx(rva)));
    }

    for imp in &ctx.pe.imports {
        let lbl = format!("{}!{}", imp.dll, imp.name.as_deref().unwrap_or("ordinal"));
        let sc = score_text(&lbl, &tokens);
        if sc > 0 {
            add(&mut hits, &mut totals, sc, "import", imp.iat_rva, lbl, format!("import from {} (hint {})", imp.dll, imp.hint), format!("xr {:x}", imp.iat_rva));
        }
    }

    for exp in &ctx.pe.exports {
        let sc = score_text(&exp.name, &tokens);
        if sc > 0 {
            let callers = ctx.pe.find_export_callers(&exp.name);
            let hint = if !callers.is_empty() { format!("callers {:x}", callers[0]) } else { format!("xr {:x}", exp.rva) };
            add(&mut hits, &mut totals, sc, "export", exp.rva, exp.name.clone(), format!("export {} (ordinal {})", exp.name, exp.ordinal), hint);
        }
    }

    // functions that have a real name (names file / overlay), not the generated sub_ names
    let starts: Vec<(u32, u32)> = ctx.pe.ranges.iter().filter(|r| r.root == r.begin).map(|r| (r.begin, r.end)).collect();
    for (b, e) in starts {
        let name = target_name(ctx, b);
        if name.starts_with("sub_") { continue; }
        let sc = score_text(&name, &tokens);
        if sc > 0 {
            add(&mut hits, &mut totals, sc, "function", b, name.clone(), format!("function {name} ({} bytes)", e - b), format!("sum {}", hx(b)));
        }
    }

    // strings in non-executable sections (ASCII, >= 4 chars)
    let mut str_candidates: Vec<(u32, String, usize)> = vec![];
    for sec in &ctx.pe.sections {
        if sec.flags & 0x2000_0000 != 0 || sec.rawsize == 0 { continue; }
        let d = &ctx.pe.data[sec.raw as usize..(sec.raw + sec.rawsize.min(sec.vsize)) as usize];
        let mut i = 0usize;
        while i < d.len() {
            if d[i] >= 0x20 && d[i] <= 0x7e {
                let mut j = i;
                while j < d.len() && d[j] >= 0x20 && d[j] <= 0x7e { j += 1; }
                if j - i >= 4 && j - i <= 400 {
                    let st = String::from_utf8_lossy(&d[i..j]).to_string();
                    let sc = score_text(&st, &tokens);
                    if sc > 0 { str_candidates.push((sec.rva + i as u32, st, sc)); }
                }
                i = j;
            } else { i += 1; }
        }
    }
    // only the best-scoring strings pay for the xref lookup
    str_candidates.sort_by(|x, y| y.2.cmp(&x.2).then(x.0.cmp(&y.0)));
    let nstr = str_candidates.len();
    for (n, (str_rva, st, sc)) in str_candidates.into_iter().enumerate() {
        if n >= 400 { *totals.entry("string").or_default() += 1; continue; }
        let refs: Vec<(u32, u32)> = ctx.xrefs().to(str_rva).to_vec();
        let fns: Vec<String> = refs.iter().take(4).map(|(_, from)| target_name(ctx, ctx.fn_start(*from))).collect();
        let hint = format!("xr {:x}", str_rva);
        let by = if fns.is_empty() { "no code reference found".to_string() } else { format!("referenced by {}", fns.join(", ")) };
        // strings nothing references are rarely useful: they sort last
        add(&mut hits, &mut totals, if refs.is_empty() { 0 } else { sc }, "string", str_rva, st.clone(), format!("string \"{}\" {}", st, by), hint);
    }

    let total_hits: usize = totals.values().sum();
    if hits.is_empty() {
        return Ok(json!({"goal": goal, "findings": [], "message": format!("no class, import, export, function name or string contains a word of '{goal}' (words match at word/camelCase starts)"), "trust": "hint (data-driven; every result is read from the current binary)"}));
    }
    hits.sort_by(|x, y| y.0.cmp(&x.0));
    let findings: Vec<Value> = hits.into_iter().take(max).map(|x| x.1).collect();
    Ok(json!({"goal": goal, "words": tokens, "findings": findings, "shown": findings.len(), "total_matches": total_hits, "matches_by_kind": totals, "string_matches_scanned": nstr,
        "reading": "score = how many different goal words the hit contains (best first). Raise --max for more. Every address was found in the current binary; use the `try` command to follow a lead.",
        "trust": "hint (data-driven discovery; verify each lead against the image)"}))
}

// ---------------------------------------------------------------- recipes: saved expert workflows

pub fn cmd_recipes(ctx: &mut Ctx, a: &Args) -> Result<Value, String> {
    let name = a.pos.first().ok_or("recipes <name> [args...]   available: render-pass-map <vtable_rva> | swapchain-hook <from_fn> <to_fn> | vtable-trace <class_name|vtable_rva> | component-users <TypeName> | xref-graph <fn> | import-trace <name> | string-xref <text>")?;
    let rest: Vec<&str> = a.pos[1..].iter().map(|s| s.as_str()).collect();
    let mut steps: Vec<Value> = vec![];
    let mut combined: Vec<Value> = vec![];
    let mut step: usize = 0;

    match name.as_str() {
        "render-pass-map" => {
            let vtable_rva = rest.first().ok_or("render-pass-map <vtable_rva>")?;
            let rva = crate::parse_hex(vtable_rva).ok_or("render-pass-map: bad vtable rva")?;
            ctx.prep();
            let vts = ctx.vts.as_ref().unwrap();
            let i = vts.by_rva.get(&rva).ok_or_else(|| format!("{:x} is not a discovered vtable", rva))?;
            let v = &vts.list[*i];
            step += 1;
            steps.push(json!({"step": step, "cmd": format!("vt {} 64", hx(rva)), "why": "enumerate the first 64 vtable slots", "expected_evidence": "slot -> target function map"}));
            let mut candidates: Vec<(usize, u32)> = vec![];
            let mut slots_json: Vec<Value> = vec![];
            for s in 0..64usize {
                let slot_rva = v.rva + (s as u32) * 8;
                let entry = match ctx.pe.u64_at(slot_rva).and_then(|x| is_code_ptr(ctx, x)) {
                    Some(t) => { candidates.push((s, t)); json!({"slot": s, "byte_offset": s * 8, "target": ctx.flabel(t)}) }
                    None => json!({"slot": s, "byte_offset": s * 8, "target": null, "note": "non-code or unmapped"}),
                };
                slots_json.push(entry);
            }
            combined.push(json!({"cmd": format!("vt {} 64", hx(rva)), "result": json!({"vtable": hx(v.rva), "name": ctx.vt_name(v), "slots": slots_json})}));
            step += 1;
            steps.push(json!({"step": step, "cmd": "sum <slot target> for each slot", "why": "collect strings and constants from each slot's target function", "expected_evidence": "per-slot strings and immediates that hint at the pass name"}));
            let mut map: Vec<Value> = vec![];
            for (slot, t) in candidates {
                let s = ctx.sum(t);
                if s.strs.is_empty() { continue; }
                let strs: Vec<Value> = s.strs.iter().map(|(ip, ad, txt)| json!({"ip": hx(*ip), "addr": hx(*ad), "text": txt})).collect();
                let mut imms: Vec<u32> = vec![];
                let ranges: Vec<(u32, u32)> = std::iter::once((s.cfg.begin, s.cfg.end)).chain(s.cfg.ranges.iter().map(|r| (r.0, r.1))).collect();
                for (b, e) in ranges {
                    let bytes = ctx.pe.bytes(b, (e - b) as usize);
                    let mut dec = Decoder::with_ip(64, bytes, b as u64, DecoderOptions::NONE);
                    let mut ins = Instruction::default();
                    while dec.can_decode() {
                        dec.decode_out(&mut ins);
                        for k in 0..ins.op_count() {
                            if matches!(ins.op_kind(k), OpKind::Immediate32 | OpKind::Immediate32to64) {
                                let vv = ins.immediate(k) as u32;
                                if (0x10000..0xFFFF_0000).contains(&vv) { imms.push(vv); }
                            }
                        }
                    }
                }
                imms.sort_unstable();
                imms.dedup();
                map.push(json!({"slot": slot, "target": ctx.flabel(t), "strings": strs, "constants": imms.iter().take(12).map(|v| format!("{:#x}", v)).collect::<Vec<_>>()}));
                combined.push(json!({"cmd": format!("sum {}", hx(t)), "result": json!({"fn": ctx.flabel(t), "strings": strs.len(), "constants": imms.len()})}));
            }
            Ok(json!({"recipe": "render-pass-map", "vtable": hx(rva), "class": ctx.vt_name(v), "steps": steps, "map": map, "combined": combined, "trust": "derived (slot targets, strings and constants re-read from the image bytes)"}))
        }
        "swapchain-hook" => {
            let from = rest.first().ok_or("swapchain-hook <from_fn> <to_fn>")?;
            let to = rest.get(1).ok_or("swapchain-hook <from_fn> <to_fn>")?;
            let from_rva = crate::parse_hex(from).ok_or("swapchain-hook: bad from address")?;
            let to_rva = crate::parse_hex(to).ok_or("swapchain-hook: bad to address")?;
            let aa = Args { pos: vec![from.to_string(), to.to_string()], ..Default::default() };
            let hp = cmd_hookpoints(ctx, &aa)?;
            step += 1;
            steps.push(json!({"step": step, "cmd": format!("hookpoints {} {}", from, to), "why": "rank chokepoints on every path from..to, plus the target itself", "expected_evidence": "ranked candidates; the best is on every path and has a unique prologue"}));
            combined.push(json!({"cmd": format!("hookpoints {} {}", from, to), "result": hp}));
            let best = hp["ranked"].as_array().and_then(|arr| arr.first()).cloned();
            let prologue = best.as_ref().and_then(|r| r["fn"].as_object().and_then(|o| o["rva"].as_str()).and_then(crate::parse_hex)).map(|r| ctx.pe.bytes(r, 16).iter().map(|b| format!("{:02X}", b)).collect::<Vec<String>>());
            step += 1;
            steps.push(json!({"step": step, "cmd": "select best hook candidate", "why": "the top-ranked chokepoint is on every path: one hook there sees all traffic", "expected_evidence": "candidate function, prologue bytes, distinct caller count"}));
            combined.push(json!({"candidate": best, "prologue": prologue}));
            Ok(json!({"recipe": "swapchain-hook", "from": hx(from_rva), "to": hx(to_rva), "steps": steps, "combined": combined, "trust": "derived over the chosen edge set (default --virt none: direct calls only; rerun the hookpoints step with --virt derived for virtual edges)"}))
        }
        "vtable-trace" => {
            let q = rest.first().ok_or("vtable-trace <class_name|vtable_rva>")?;
            ctx.prep();
            let hits = crate::cmds::find_vts(ctx, q);
            if hits.is_empty() { return Err(format!("no vtable matches '{}'", q)); }
            let vi = hits[0];
            let vts = ctx.vts.as_ref().unwrap();
            let v = &vts.list[vi];
            let vtable_rva = v.rva;
            let name = ctx.vt_name(v).clone();
            let slot_count = v.slots.len();
            let rtti = v.rtti.as_ref().map(|r| json!({"name": r.name, "bases": r.bases}));
            let slots: Vec<u32> = v.slots.clone();
            step += 1;
            steps.push(json!({"step": step, "cmd": format!("class {}", q), "why": "resolve the class/vtable to trace", "expected_evidence": "vtable address, class name, RTTI, slot count"}));
            combined.push(json!({"cmd": format!("class {}", q), "result": json!({"vtable": hx(vtable_rva), "name": name, "slots": slot_count, "rtti": rtti})}));
            step += 1;
            steps.push(json!({"step": step, "cmd": "xr <target> for each vslot", "why": "for each slot, resolve the target and list every call site that reaches it", "expected_evidence": "per-slot target and its caller functions"}));
            let mut graph: Vec<Value> = vec![];
            for (slot, &t) in slots.iter().enumerate().take(64) {
                let mut callers: Vec<Value> = vec![];
                let refs: Vec<(u32, u32)> = ctx.xrefs().to(t).to_vec();
                for (_, from) in refs {
                    let bytes = ctx.pe.bytes(from, 15);
                    let mut dec = Decoder::with_ip(64, bytes, from as u64, DecoderOptions::NONE);
                    if !dec.can_decode() { continue; }
                    let ins = dec.decode();
                    if matches!(ins.flow_control(), FlowControl::Call) && ins.op0_kind() == OpKind::NearBranch64 && ins.near_branch_target() as u32 == t {
                        let cf = ctx.fn_start(from);
                        if !callers.iter().any(|c| c["caller"]["rva"] == json!(hx(cf))) {
                            callers.push(json!({"site": hx(from), "caller": ctx.flabel(cf)}));
                        }
                    }
                    if callers.len() >= 10 { break; }
                }
                combined.push(json!({"cmd": format!("xr {}", hx(t)), "result": json!({"target": ctx.flabel(t), "callers": callers.len()})}));
                graph.push(json!({"slot": slot, "byte_offset": slot * 8, "target": ctx.flabel(t), "callers": callers}));
            }
            Ok(json!({"recipe": "vtable-trace", "query": q, "vtable": hx(vtable_rva), "name": name, "steps": steps, "call_graph": graph, "trust": "derived (targets read from the vtable; callers from the xref index)"}))
        }
        "component-users" => {
            let type_name = rest.first().ok_or("component-users <TypeName>")?;
            let hash = model::fnv1a(type_name);
            ctx.prep();
            let fns = crate::cmds::comp_functions(ctx, type_name);
            step += 1;
            steps.push(json!({"step": step, "cmd": format!("comp {}", type_name), "why": "find every function containing the type hash", "expected_evidence": "functions using this component type"}));
            combined.push(json!({"cmd": format!("comp {}", type_name), "result": json!({"name": type_name, "hash": hx(hash), "functions": fns.len()})}));
            step += 1;
            steps.push(json!({"step": step, "cmd": "sum <fn> --only comps for each user", "why": "confirm each candidate really references this component type", "expected_evidence": "per-function comp_refs"}));
            let mut users: Vec<Value> = vec![];
            for f in fns.iter().take(200) {
                let s = ctx.sum(*f);
                let sites: Vec<Value> = s.comp_refs.iter().filter(|(_, n)| n == type_name).map(|(ip, _)| json!({"ip": hx(*ip)})).collect();
                if !sites.is_empty() {
                    users.push(json!({"fn": ctx.flabel(*f), "hash": hx(hash), "sites": sites}));
                    combined.push(json!({"cmd": format!("sum {} --only comps", hx(*f)), "result": json!({"fn": ctx.flabel(*f), "sites": sites})}));
                }
            }
            Ok(json!({"recipe": "component-users", "component": type_name, "hash": hx(hash), "users": page(users, a, 60), "steps": steps, "combined": combined, "trust": "proven (each function contains an imm32 equal to the FNV-1a hash of the type name)"}))
        }
        "xref-graph" => {
            let fn_rva = rest.first().ok_or("xref-graph <fn_rva>")?;
            let rva = crate::parse_hex(fn_rva).ok_or("xref-graph: bad function rva")?;
            ctx.prep();
            step += 1;
            steps.push(json!({"step": step, "cmd": format!("xr {}", fn_rva), "why": "every reference to this function", "expected_evidence": "caller addresses and instruction text"}));
            let refs: Vec<(u32, u32)> = ctx.xrefs().to(rva).to_vec();
            let mut callers: Vec<Value> = vec![];
            for (_, from) in &refs {
                let bytes = ctx.pe.bytes(*from, 15);
                let mut dec = Decoder::with_ip(64, bytes, *from as u64, DecoderOptions::NONE);
                if dec.can_decode() {
                    let ins = dec.decode();
                    let text = {
                        let mut s = String::new();
                        Formatter::format(&mut formatter(), &ins, &mut s);
                        s
                    };
                    callers.push(json!({"from": hx(*from), "caller": target_name(ctx, *from), "insn": text}));
                }
            }
            combined.push(json!({"cmd": format!("xr {}", fn_rva), "result": json!({"target": target_name(ctx, rva), "callers": callers.len()})}));
            step += 1;
            steps.push(json!({"step": step, "cmd": format!("callees {}", fn_rva), "why": "what this function calls", "expected_evidence": "callee addresses and strings"}));
            let (b, e) = ctx.pe.function_of(rva).unwrap_or((rva, heuristic_end(ctx, rva)));
            let mut calls: Vec<Value> = vec![];
            let mut strs: Vec<Value> = vec![];
            for ins in decode_range(ctx, b, e) {
                if ins.flow_control() == FlowControl::Call && ins.op0_kind() == OpKind::NearBranch64 {
                    calls.push(json!({"ip": hx(ins.ip() as u32), "target": target_name(ctx, ins.near_branch_target() as u32)}));
                }
                if ins.is_ip_rel_memory_operand() {
                    if let Some(s) = ctx.pe.string_at(ins.ip_rel_memory_address() as u32) {
                        strs.push(json!({"ip": hx(ins.ip() as u32), "addr": hx(ins.ip_rel_memory_address() as u32), "text": s}));
                    }
                }
            }
            combined.push(json!({"cmd": format!("callees {}", fn_rva), "result": json!({"fn": target_name(ctx, rva), "calls": calls.len(), "strings": strs.len()})}));
            Ok(json!({"recipe": "xref-graph", "fn": hx(rva), "name": target_name(ctx, rva), "callers": callers, "calls": calls, "strings": strs, "steps": steps, "combined": combined, "trust": "proven (xref index and instruction bytes)"}))
        }
        "import-trace" => {
            let dll = rest.first().ok_or("import-trace <dll>")?;
            ctx.prep();
            let imps: Vec<&crate::pe::Import> = ctx.pe.imports_for(dll);
            step += 1;
            steps.push(json!({"step": step, "cmd": format!("imports_for \"{}\"", dll), "why": "every import from this DLL", "expected_evidence": "import names, hints, IAT addresses"}));
            let mut items: Vec<Value> = vec![];
            for imp in &imps {
                let callers = ctx.pe.find_import_callers(dll, imp.name.as_deref().unwrap_or(""));
                items.push(json!({"dll": &imp.dll, "hint": imp.hint, "name": imp.name, "iat_rva": hx(imp.iat_rva), "iat_value": imp.iat_value, "callers": callers.iter().map(|c| hx(*c)).collect::<Vec<_>>()}));
            }
            combined.push(json!({"cmd": format!("imports_for \"{}\"", dll), "result": json!({"count": imps.len()})}));
            Ok(json!({"recipe": "import-trace", "dll": dll, "imports": page(items, a, 60), "steps": steps, "combined": combined, "trust": "proven (import directory read from the image)"}))
        }
        "string-xref" => {
            let text = rest.first().ok_or("string-xref <text>")?;
            ctx.prep();
            let addrs = crate::cmds3::cstring_addrs(ctx, text);
            step += 1;
            steps.push(json!({"step": step, "cmd": format!("str \"{}\"", text), "why": "every occurrence of this string", "expected_evidence": "string addresses and referencing functions"}));
            let mut items: Vec<Value> = vec![];
            for ad in addrs.iter().take(60) {
                let refs: Vec<(u32, u32)> = ctx.xrefs().to(*ad).to_vec();
                let fns: Vec<Value> = refs.iter().take(6).map(|(_, from)| {
                    let s = ctx.sum(ctx.fn_start(*from));
                    json!({"from": hx(*from), "fn": target_name(ctx, *from), "strings": s.strs.iter().take(3).map(|(_,_,t)| t.clone()).collect::<Vec<_>>()})
                }).collect();
                let s = ctx.pe.string_at(*ad).unwrap_or_default();
                items.push(json!({"addr": hx(*ad), "text": s, "refs": fns.len(), "callers": fns}));
            }
            combined.push(json!({"cmd": format!("str \"{}\"", text), "result": json!({"count": addrs.len()})}));
            Ok(json!({"recipe": "string-xref", "text": text, "strings": items, "steps": steps, "combined": combined, "trust": "proven (string scan + xref index)"}))
        }
        other => Err(format!("recipes: unknown recipe '{}' (render-pass-map | swapchain-hook | vtable-trace | component-users | xref-graph | import-trace | string-xref)", other)),
    }
}

fn arg_index(r: iced_x86::Register) -> Option<usize> {
    use iced_x86::Register as R;
    match r.full_register() { R::RCX => Some(0), R::RDX => Some(1), R::R8 => Some(2), R::R9 => Some(3), _ => None }
}

fn used_arg_regs(ctx: &Ctx, s: &Sum) -> BTreeSet<usize> {
    use iced_x86::{InstructionInfoFactory, OpAccess, Mnemonic};
    let mut fac = InstructionInfoFactory::new();
    let mut used = BTreeSet::new();
    let mut inn: std::collections::HashMap<u32, u8> = std::collections::HashMap::new(); // bit i set = arg i still unmodified on SOME path
    inn.insert(s.cfg.begin, 0b1111);
    let mut work = vec![s.cfg.begin];
    let _ = ctx;
    while let Some(b) = work.pop() {
        let mut st = inn[&b];
        let blk = &s.cfg.blocks[&b];
        for k in blk.first..=blk.last {
            let ins = &s.cfg.ins[k];
            let info = fac.info(ins);
            for r in info.used_registers() {
                if let Some(i) = arg_index(r.register()) {
                    let acc = r.access();
                    let reads = matches!(acc, OpAccess::Read | OpAccess::ReadWrite | OpAccess::CondRead | OpAccess::ReadCondWrite);
                    // xor r,r / sub r,r read nothing
                    let zeroing = matches!(ins.mnemonic(), Mnemonic::Xor | Mnemonic::Sub) && ins.op0_kind() == OpKind::Register && ins.op1_kind() == OpKind::Register && ins.op0_register() == ins.op1_register();
                    if reads && !zeroing && st & (1 << i) != 0 { used.insert(i); }
                }
            }
            for r in info.used_registers() {
                if let Some(i) = arg_index(r.register()) {
                    if matches!(r.access(), OpAccess::Write) && r.register().is_gpr64() || matches!(r.access(), OpAccess::Write) && r.register().is_gpr32() { st &= !(1 << i); }
                }
            }
            if ins.mnemonic() == Mnemonic::Call { st &= 0b0000; } // volatile registers are dead after a call
        }
        for e in &blk.succ {
            if e.outside { continue; }
            let old = inn.get(&e.to).copied();
            let new = old.unwrap_or(0) | st;
            if old != Some(new) { inn.insert(e.to, new); work.push(e.to); }
        }
    }
    used
}
