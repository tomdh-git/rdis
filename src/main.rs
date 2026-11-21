// rdis: an IDA-like read-only analyzer for the game exe.
//
//   rdis <exe>                     interactive prompt
//   rdis <exe> -c "cmd; cmd"       run commands and exit (the exe and the xref index load once)
//   rdis <exe> <cmd> args...       one command
//   rdis <exe> <rva|sig> [--max N] [--calls] [--find-sig]    the old form: fn / callees / find
//
// Commands: fn dis xr callers callees str fld vt find name names sec help. Run `help` for the details.
use std::cell::RefCell;
use std::rc::Rc;
thread_local! { static CAP: RefCell<Option<String>> = RefCell::new(None); }
pub static PRETTY: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);
// All command output goes through `emit` so the same commands serve the terminal and the MCP server (which captures it).
pub fn capture<F: FnOnce()>(f: F) -> String {
    CAP.with(|c| *c.borrow_mut() = Some(String::new()));
    f();
    CAP.with(|c| c.borrow_mut().take().unwrap_or_default())
}
pub fn emit(s: &str) {
    let done = CAP.with(|c| match c.borrow_mut().as_mut() { Some(b) => { b.push_str(s); b.push_str("\n"); true } None => false });
    if !done { std::println!("{}", s); }
}
macro_rules! println { () => { $crate::emit("") }; ($($a:tt)*) => { $crate::emit(&format!($($a)*)) }; }
mod cfg;
mod cmds;
mod walk;
mod cmds2;
mod cmds3;
mod cmds4;
mod db;
mod index;
mod listing;
mod mcp;
mod model;
mod pe;
mod sym;

use iced_x86::{Decoder, DecoderOptions, FlowControl, Instruction, Mnemonic, OpKind, Register};
use listing::{decode_range, formatter, heuristic_end, list_function, target_name, Opts};
use pe::Pe;
use std::collections::{BTreeMap, HashMap};
use std::io::{BufRead, Write};
use std::{env, fs, path::PathBuf, thread};

pub struct Ctx {
    pub pe: Pe,
    pub exe: String,
    pub image_base: u64,
    pub names: HashMap<u32, String>,
    names_path: PathBuf,
    xr: Option<index::Xrefs>,
    pub legacy_names: HashMap<u32, String>,
    pub db: db::Db,
    pub comps: Option<HashMap<u32, String>>,
    pub vts: Option<model::Vts>,
    pub sums: RefCell<HashMap<u32, Rc<sym::Sum>>>,
    pub edges: RefCell<HashMap<u32, Rc<Vec<model::Edge>>>>,
}

impl Ctx {
    pub fn xrefs(&mut self) -> &index::Xrefs {
        if self.xr.is_none() { self.xr = Some(index::build(&self.pe, &self.exe)); }
        self.xr.as_ref().unwrap()
    }
}

pub fn load(exe: &str) -> Ctx {
    let pe = Pe::load(exe);
    let image_base = u64::from_le_bytes(pe.data[pe::u32le(&pe.data, 0x3c) as usize + 24 + 24..][..8].try_into().unwrap());
    let ver = std::path::Path::new(exe).parent().and_then(|p| p.file_name()).map(|n| n.to_string_lossy().to_string()).unwrap_or_else(|| "exe".into());
    let mut dir = env::current_exe().unwrap_or_default();
    for _ in 0..3 { dir.pop(); }
    dir.push("names");
    let _ = fs::create_dir_all(&dir);
    let names_path = dir.join(format!("{}.txt", ver));
    let mut names = HashMap::new();
    if let Ok(t) = fs::read_to_string(&names_path) {
        for l in t.lines() {
            if let Some((a, n)) = l.split_once(' ') {
                if let Ok(r) = u32::from_str_radix(a.trim_start_matches("0x"), 16) { names.insert(r, n.trim().to_string()); }
            }
        }
    }
    let db = db::Db::load(dir.join(format!("{}.facts.jsonl", ver))).expect("open facts db");
    let mut ctx = Ctx { pe, exe: exe.to_string(), image_base, legacy_names: names.clone(), names, names_path, xr: None, db, comps: None, vts: None, sums: RefCell::new(HashMap::new()), edges: RefCell::new(HashMap::new()) };
    ctx.invalidate();
    ctx
}

pub fn parse_hex(t: &str) -> Option<u32> {
    let t = t.trim_start_matches("0x").trim_start_matches("sub_").trim_start_matches("data_").trim_start_matches("loc_");
    u32::from_str_radix(t, 16).ok()
}

fn is_sig_token(t: &str) -> bool { t.starts_with('?') || (t.len() == 2 && t.chars().all(|c| c.is_ascii_hexdigit())) }

pub fn find_sig(ctx: &Ctx, sig: &str) -> Vec<u32> {
    let pat: Vec<Option<u8>> = sig.split_whitespace().map(|t| if t.starts_with('?') { None } else { Some(u8::from_str_radix(t, 16).unwrap()) }).collect();
    let mut out = vec![];
    for s in ctx.pe.sections.iter().filter(|s| s.flags & 0x2000_0000 != 0) {
        let d = &ctx.pe.data[s.raw as usize..(s.raw + s.rawsize.min(s.vsize)) as usize];
        'o: for i in 0..d.len().saturating_sub(pat.len()) {
            for (j, p) in pat.iter().enumerate() {
                if let Some(b) = p { if d[i + j] != *b { continue 'o; } }
            }
            out.push(s.rva + i as u32);
        }
    }
    out
}

// An address argument: 0xRVA, sub_RVA, a name from the names file, or a byte signature (must match exactly once).
pub fn resolve(ctx: &Ctx, toks: &[&str]) -> Result<u32, String> {
    if toks.is_empty() { return Err("missing address".into()); }
    if toks.len() > 1 && toks.iter().all(|t| is_sig_token(t)) {
        let hits = find_sig(ctx, &toks.join(" "));
        return match hits.len() { 1 => Ok(hits[0]), 0 => Err("sig: no match".into()), n => Err(format!("sig: {} matches {:x?}", n, &hits[..n.min(8)])) };
    }
    let t = toks[0];
    if let Some((r, _)) = ctx.names.iter().find(|(_, n)| n.as_str() == t) { return Ok(*r); }
    parse_hex(t).ok_or_else(|| format!("cannot resolve '{}'", t))
}

fn text_at(ctx: &Ctx, rva: u32) -> String {
    let bytes = ctx.pe.bytes(rva, 16);
    let mut dec = Decoder::with_ip(64, bytes, rva as u64, DecoderOptions::NONE);
    let mut ins = Instruction::default();
    if !dec.can_decode() { return "?".into(); }
    dec.decode_out(&mut ins);
    let mut s = String::new();
    iced_x86::Formatter::format(&mut formatter(), &ins, &mut s);
    s
}

fn func_label(ctx: &Ctx, rva: u32) -> String {
    match ctx.pe.function_of(rva) {
        Some((b, _)) => { let n = target_name(ctx, b); if b == rva { n } else { format!("{}+{:#x}", n, rva - b) } }
        None => format!("{:x}", rva),
    }
}

fn cmd_fn(ctx: &mut Ctx, rva: u32, o: &Opts) {
    let (b, e) = match ctx.pe.function_of(rva) {
        Some(x) => x,
        None => (rva, heuristic_end(ctx, rva)),
    };
    if b != rva && ctx.pe.function_of(rva).is_some() { println!("; {:#x} is inside {}", rva, target_name(ctx, b)); }
    list_function(ctx, b, e, o);
}

fn cmd_xr(ctx: &mut Ctx, rva: u32, max: usize, calls_only: bool) {
    let list: Vec<(u32, u32)> = ctx.xrefs().to(rva).to_vec();
    let mut shown = 0;
    let mut seen: BTreeMap<u32, u32> = BTreeMap::new();
    for (_, from) in &list {
        let text = text_at(ctx, *from);
        let is_flow = text.starts_with("call") || text.starts_with("jmp");
        if calls_only && !is_flow { continue; }
        if calls_only {
            let f = ctx.pe.function_of(*from).map_or(*from, |f| f.0);
            *seen.entry(f).or_insert(0) += 1;
            continue;
        }
        if shown < max { println!("  {:x}  {:<28} {}", from, func_label(ctx, *from), text); }
        shown += 1;
    }
    if calls_only {
        for (f, n) in seen.iter().take(max) { println!("  {:<28} {} call site(s)", target_name(ctx, *f), n); }
        println!("-- {} calling function(s){}", seen.len(), if seen.len() > max { format!(", {} shown (--max)", max) } else { String::new() });
        if let Some((b, _)) = ctx.pe.function_of(rva) { if b != rva { println!("note: {:#x} is inside {} (starts at {:#x}); callers of an interior address are only jumps into it. For the callers of the function use: callers {:#x}", rva, target_name(ctx, b), b, b); } }
    } else {
        println!("-- {} xref(s){}", list.len(), if shown > max { format!(", {} shown", max) } else { String::new() });
    }
}

fn cmd_callees(ctx: &mut Ctx, rva: u32) {
    let (b, e) = ctx.pe.function_of(rva).unwrap_or((rva, heuristic_end(ctx, rva)));
    let mut calls: BTreeMap<u32, u32> = BTreeMap::new();
    let mut strs: Vec<(u32, String)> = vec![];
    for ins in decode_range(ctx, b, e) {
        if ins.flow_control() == FlowControl::Call && ins.op0_kind() == OpKind::NearBranch64 { *calls.entry(ins.near_branch_target() as u32).or_insert(0) += 1; }
        if ins.is_ip_rel_memory_operand() {
            if let Some(s) = ctx.pe.string_at(ins.ip_rel_memory_address() as u32) { strs.push((ins.ip() as u32, s)); }
        }
    }
    println!("{}  [{:#x}..{:#x})", target_name(ctx, b), b, e);
    for (t, n) in &calls { println!("  call {:<28} x{}", target_name(ctx, *t), n); }
    for (ip, s) in &strs { println!("  str  {:x}  \"{}\"", ip, s); }
}

fn cmd_str(ctx: &mut Ctx, needle: &str, max: usize, ci: bool) {
    let nb: Vec<u8> = if ci { needle.to_lowercase().into_bytes() } else { needle.as_bytes().to_vec() };
    let wide: Vec<u8> = nb.iter().flat_map(|c| [*c, 0]).collect();
    let mut hits: Vec<(u32, bool)> = vec![];
    for s in ctx.pe.sections.iter().filter(|s| s.flags & 0x2000_0000 == 0 && s.rawsize > 0) {
        let d = &ctx.pe.data[s.raw as usize..(s.raw + s.rawsize.min(s.vsize)) as usize];
        for (pat, w) in [(&nb, false), (&wide, true)] {
            let mut i = 0;
            while i + pat.len() <= d.len() {
                let ok = if ci { d[i..i + pat.len()].iter().zip(pat.iter()).all(|(a, b)| a.to_ascii_lowercase() == *b) } else { d[i..i + pat.len()] == pat[..] };
                if ok { hits.push((s.rva + i as u32, w)); i += pat.len(); } else { i += 1; }
            }
        }
        if hits.len() > 5000 { break; }
    }
    let mut printed = 0;
    for (rva, w) in hits {
        if printed >= max { println!("... more (--max)"); break; }
        let mut start = rva;
        let step = if w { 2 } else { 1 };
        for _ in 0..200 {
            let prev = ctx.pe.bytes(start - step, step as usize);
            if prev.is_empty() || !(0x20..0x7f).contains(&prev[0]) || (w && prev[1] != 0) { break; }
            start -= step;
        }
        let text = ctx.pe.string_at(start).unwrap_or_default();
        let refs: Vec<(u32, u32)> = ctx.xrefs().to(start).to_vec();
        let fns: Vec<String> = refs.iter().take(6).map(|(_, f)| func_label(ctx, *f)).collect();
        println!("{:x}  \"{}\"  {}", start, text, if fns.is_empty() { "(no code refs)".into() } else { fns.join(", ") });
        printed += 1;
    }
}

struct Fld { disp: i64, base: Option<Register>, reads: bool, writes: bool }

fn is_write(ins: &Instruction, k: u32) -> bool {
    k == 0 && !matches!(ins.mnemonic(), Mnemonic::Cmp | Mnemonic::Test | Mnemonic::Push | Mnemonic::Call | Mnemonic::Jmp | Mnemonic::Bt | Mnemonic::Ucomiss | Mnemonic::Comiss | Mnemonic::Prefetchw | Mnemonic::Prefetcht0)
}

fn cmd_fld(ctx: &Ctx, f: &Fld, max: usize) {
    let threads = thread::available_parallelism().map_or(4, |n| n.get());
    let chunk = (ctx.pe.ranges.len() + threads - 1) / threads;
    let mut hits: Vec<(u32, bool)> = vec![];
    let pe = &ctx.pe;
    thread::scope(|s| {
        let hs: Vec<_> = pe.ranges.chunks(chunk.max(1)).map(|rs| s.spawn(move || {
            let mut out = vec![];
            let mut ins = Instruction::default();
            for r in rs {
                if !pe.is_exec(r.begin) { continue; }
                let bytes = pe.bytes(r.begin, (r.end - r.begin) as usize);
                let mut dec = Decoder::with_ip(64, bytes, r.begin as u64, DecoderOptions::NONE);
                while dec.can_decode() {
                    dec.decode_out(&mut ins);
                    for k in 0..ins.op_count() {
                        if ins.op_kind(k) != OpKind::Memory || ins.is_ip_rel_memory_operand() { continue; }
                        if ins.memory_displacement64() as i64 != f.disp { continue; }
                        if let Some(b) = f.base { if ins.memory_base().full_register() != b { continue; } }
                        let w = is_write(&ins, k);
                        if (w && f.writes) || (!w && f.reads) { out.push((ins.ip() as u32, w)); break; }
                    }
                }
            }
            out
        })).collect();
        for h in hs { hits.extend(h.join().unwrap()); }
    });
    hits.sort_unstable();
    for (ip, w) in hits.iter().take(max) { println!("  {:x}  {:<30} {} {}", ip, func_label(ctx, *ip), if *w { "W" } else { "R" }, text_at(ctx, *ip)); }
    println!("-- {} access(es){}", hits.len(), if hits.len() > max { format!(", {} shown", max) } else { String::new() });
}

// Instructions with this immediate (components are found by a type hash, so a component's users show up here).
fn cmd_imm(ctx: &Ctx, value: u64, max: usize) {
    let threads = thread::available_parallelism().map_or(4, |n| n.get());
    let chunk = (ctx.pe.ranges.len() + threads - 1) / threads;
    let mut hits: Vec<u32> = vec![];
    let pe = &ctx.pe;
    thread::scope(|s| {
        let hs: Vec<_> = pe.ranges.chunks(chunk.max(1)).map(|rs| s.spawn(move || {
            let mut out = vec![];
            let mut ins = Instruction::default();
            for r in rs {
                if !pe.is_exec(r.begin) { continue; }
                let bytes = pe.bytes(r.begin, (r.end - r.begin) as usize);
                let mut dec = Decoder::with_ip(64, bytes, r.begin as u64, DecoderOptions::NONE);
                while dec.can_decode() {
                    dec.decode_out(&mut ins);
                    for k in 0..ins.op_count() {
                        let v = match ins.op_kind(k) {
                            OpKind::Immediate8 => ins.immediate8() as u64, OpKind::Immediate16 => ins.immediate16() as u64,
                            OpKind::Immediate32 => ins.immediate32() as u64, OpKind::Immediate64 => ins.immediate64(),
                            OpKind::Immediate8to32 => ins.immediate8to32() as u32 as u64, OpKind::Immediate32to64 => ins.immediate32to64() as u64,
                            _ => continue,
                        };
                        if v == value || (value <= 0xFFFF_FFFF && v as u32 as u64 == value && matches!(ins.op_kind(k), OpKind::Immediate32 | OpKind::Immediate32to64)) { out.push(ins.ip() as u32); break; }
                    }
                }
            }
            out
        })).collect();
        for h in hs { hits.extend(h.join().unwrap()); }
    });
    hits.sort_unstable();
    for ip in hits.iter().take(max) { println!("  {:x}  {:<30} {}", ip, func_label(ctx, *ip), text_at(ctx, *ip)); }
    println!("-- {} hit(s){}", hits.len(), if hits.len() > max { format!(", {} shown", max) } else { String::new() });
}

// Where the address is stored as a pointer in the data sections (vtable slots, function tables).
fn cmd_ptr(ctx: &Ctx, rva: u32, max: usize) {
    let want = (ctx.image_base + rva as u64).to_le_bytes();
    let mut n = 0;
    for s in ctx.pe.sections.iter().filter(|s| s.flags & 0x2000_0000 == 0 && s.rawsize > 0) {
        let d = &ctx.pe.data[s.raw as usize..(s.raw + s.rawsize.min(s.vsize)) as usize];
        let mut i = 0;
        while i + 8 <= d.len() {
            if d[i..i + 8] == want {
                n += 1;
                if n <= max { println!("  {:x} ({})", s.rva + i as u32, s.name); }
                i += 8;
            } else { i += 8; }
        }
    }
    println!("-- {} pointer(s)", n);
}

fn cmd_vt(ctx: &Ctx, rva: u32, n: usize) {
    for i in 0..n {
        let slot = rva + (i as u32) * 8;
        let v = match ctx.pe.u64_at(slot) { Some(v) => v, None => break };
        let t = v.wrapping_sub(ctx.image_base);
        if t >= 0x1_0000_0000 || !ctx.pe.is_exec(t as u32) { println!("{:3} +{:#05x}  non-code {:#x}", i, i * 8, v); if v == 0 { break; } continue; }
        let t = t as u32;
        let size = ctx.pe.function_of(t).map(|(b, e)| e - b).unwrap_or_else(|| heuristic_end_size(ctx, t));
        println!("{:3} +{:#05x}  {:<20} size {:#x}  {}", i, i * 8, target_name(ctx, t), size, text_at(ctx, t));
    }
}

fn heuristic_end_size(ctx: &Ctx, t: u32) -> u32 { heuristic_end(ctx, t) - t }

#[allow(dead_code)]
fn cmd_name(ctx: &mut Ctx, rva: u32, name: &str) {
    ctx.names.insert(rva, name.to_string());
    let mut f = fs::OpenOptions::new().create(true).append(true).open(&ctx.names_path).expect("names file");
    let _ = writeln!(f, "{:x} {}", rva, name);
    println!("named {:#x} = {}", rva, name);
}

const HELP: &str = "commands (addresses: 0xRVA, sub_RVA, a name, or a byte signature):
  fn <addr> [--max N] [--nochains]   annotated function: labels, call names, strings, vcall slots, pointer chains (a0 = first argument)
  dis <addr> [n]                     linear listing of n instructions (default 40)
   walk <addr> [--reg R]              control-flow walk from <addr>: follow straight-line code,
                                       both sides of conditional jumps and the target of
                                       unconditional jmps, continue after calls, stop a path
                                       at ret/int3/ud2 and at an indirect jmp; print
                                       reachable instructions sorted by address
  xr <addr> [--max N]                every call/jmp/rip-relative reference to the address
  callers <addr>                     the functions that call or jump to it
  callees <addr>                     what a function calls, and the strings it references
  str <text> [--max N] [-i]          strings (ascii and utf-16) containing the text, with the functions that reference them
  fld <disp> [--base rcx] [--r|--w] [--max N]   instructions touching [reg+disp] anywhere in .pdata functions (all, reads only, or writes only)
  imm <value> [--max N]              instructions with that immediate (ECS component type hashes: 0x75DF36B7 = ActorRotationComponent)
  comp <TypeName> [--max N]          users of an ECS component: its hash is the FNV-1a 32 of the type name (ActorRotationComponent, MobBodyRotationComponent, ...)
  ptr <addr>                         where the address is stored as a pointer in the data (vtable slots)
  vt <addr> [n]                      vtable slots with their targets
  find <sig>                         signature matches
  name <addr> <name> | names         name an address (saved under tools/rdis/names) | list the names
  sec                                sections";

pub fn run(ctx: &mut Ctx, line: &str) {
    if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_inner(ctx, line))).is_err() { println!("{}", serde_json::json!({"error": format!("internal error while running '{}'; the analysis could not complete, so nothing is claimed", line)})); }
}

fn run_inner(ctx: &mut Ctx, line: &str) {
    let toks: Vec<&str> = line.split_whitespace().collect();
    if toks.is_empty() { return; }
    {
        let t = cmds::tokenize(line);
        let args = cmds::Args::parse(&t[1..]);
        let res: Option<Result<serde_json::Value, String>> = match t[0].as_str() {
            "sum" => Some(cmds::cmd_sum(ctx, &args)), "cfg" => Some(cmds::cmd_cfg(ctx, &args)), "gates" => Some(cmds::cmd_gates(ctx, &args)),
            "path" => Some(cmds::cmd_path(ctx, &args)), "reach" => Some(cmds::cmd_reach(ctx, &args)), "classes" => Some(cmds::cmd_classes(ctx, &args)),
            "class" => Some(cmds::cmd_class(ctx, &args)), "vslot" => Some(cmds::cmd_vslot(ctx, &args)), "vcalls" => Some(cmds::cmd_vcalls(ctx, &args)),
            "rw" => Some(cmds::cmd_rw(ctx, &args)), "struct" => Some(cmds::cmd_struct(ctx, &args)), "system" => Some(cmds::cmd_system(ctx, &args)),
            "assert" => Some(cmds::cmd_assert(ctx, &args)), "retract" => Some(cmds::cmd_retract(ctx, &args)), "contest" => Some(cmds::cmd_contest(ctx, &args)),
            "bench" => Some(cmds::cmd_bench(ctx, &args)),
            "facts" => Some(cmds::cmd_facts(ctx, &args)), "why" => Some(cmds::cmd_why(ctx, &args)), "audit" => Some(cmds::cmd_audit(ctx, &args)),
            "info" => Some(cmds::cmd_info(ctx, &args)), "comps" => Some(cmds::cmd_comps(ctx, &args)), "decide" => Some(cmds2::cmd_decide(ctx, &args)), "choke" => Some(cmds2::cmd_choke(ctx, &args)), "needs" => Some(cmds::cmd_needs(ctx, &args)), "port" => Some(cmds3::cmd_port(ctx, &args)), "gobj" => Some(cmds4::cmd_gobj(ctx, &args)), "ptables" => Some(cmds4::cmd_ptables(ctx, &args)), "structm" => Some(cmds4::cmd_structm(ctx, &args)), "struct-from-fn" => Some(cmds4::cmd_struct_from_fn(ctx, &args)), "worklist" => Some(cmds4::cmd_worklist(ctx, &args)), "observe" => Some(cmds4::cmd_observe(ctx, &args)), "portfacts" => Some(cmds4::cmd_portfacts(ctx, &args)), "abi" => Some(cmds3::cmd_abi(ctx, &args)), "sigcheck" => Some(cmds3::cmd_sigcheck(ctx, &args)), "mksig" => Some(cmds3::cmd_mksig(ctx, &args)), "hookpoints" => Some(cmds3::cmd_hookpoints(ctx, &args)), "flow" => Some(cmds3::cmd_flow(ctx, &args)), "contradict" => Some(cmds3::cmd_contradict(ctx, &args)), "surprises" => Some(cmds3::cmd_surprises(ctx, &args)), "corroborate" => Some(cmds3::cmd_corroborate(ctx, &args)), "investigate" => Some(cmds3::cmd_investigate(ctx, &args)), "recipes" => Some(cmds3::cmd_recipes(ctx, &args)), "common" => Some(cmds2::cmd_common(ctx, &args)), "uses" => Some(cmds2::cmd_uses(ctx, &args)), "anchors" => Some(cmds2::cmd_anchors(ctx, &args)), "comp" => Some(cmds::cmd_comp(ctx, &args)),
            "name" => { let mut a2 = vec!["name".to_string()]; a2.extend(t[1..].iter().cloned()); Some(cmds::cmd_assert(ctx, &cmds::Args::parse(&a2))) }
            _ => None,
        };
        if let Some(r) = res {
            match r {
                Ok(v) => println!("{}", if PRETTY.load(std::sync::atomic::Ordering::Relaxed) { serde_json::to_string_pretty(&v).unwrap() } else { v.to_string() }),
                Err(e) => println!("{}", serde_json::json!({"error": e})),
            }
            return;
        }
    }
    let mut max = 200usize;
    let mut chains = true;
    let (mut r, mut w, mut ci) = (true, true, false);
    let mut base: Option<Register> = None;
    let mut rest: Vec<&str> = vec![];
    let mut i = 1;
    while i < toks.len() {
        match toks[i] {
            "--max" => { max = toks.get(i + 1).and_then(|t| t.parse().ok()).unwrap_or(max); i += 1; }
            "--nochains" => chains = false,
            "--r" => w = false,
            "--w" => r = false,
            "-i" => ci = true,
            "--base" => { base = toks.get(i + 1).and_then(|t| reg_of(t)); i += 1; }
            "--reg" => { base = toks.get(i + 1).and_then(|t| reg_of(t)); i += 1; }
            t => rest.push(t),
        }
        i += 1;
    }
    let opts = Opts { chains, max };
    let res: Result<(), String> = (|| {
        match toks[0] {
            "help" | "?" => println!("{}", HELP),
            "sec" => for s in &ctx.pe.sections { println!("{:<8} rva {:#x} vsize {:#x} flags {:#x}", s.name, s.rva, s.vsize, s.flags); },
            "names" => { let mut v: Vec<_> = ctx.names.iter().collect(); v.sort(); for (a, n) in v { println!("{:x} {}", a, n); } }
            "fn" => { let a = resolve(ctx, &rest)?; cmd_fn(ctx, a, &opts); }
            "dis" => {
                let n = rest.get(1).and_then(|t| t.parse().ok()).unwrap_or(40usize);
                let a = resolve(ctx, &rest[..1.min(rest.len())])?;
                list_function(ctx, a, a + 0x2000, &Opts { chains, max: n });
            }
            "xr" => { let a = resolve(ctx, &rest)?; cmd_xr(ctx, a, max, false); }
            "callers" => { let a = resolve(ctx, &rest)?; cmd_xr(ctx, a, max, true); }
            "callees" => { let a = resolve(ctx, &rest)?; cmd_callees(ctx, a); }
            "str" => cmd_str(ctx, &rest.join(" "), max, ci),
            "walk" => {
                let a = resolve(ctx, &rest)?;
                walk::walk(ctx, a, base);
            }
            "fld" => {
                let d = rest.first().ok_or("fld needs a displacement")?;
                let disp = i64::from_str_radix(d.trim_start_matches("0x"), 16).map_err(|e| e.to_string())?;
                if disp > 0x10000 {
                    return Err(format!("displacement {:#x} is larger than 0x10000; this looks like a function address, not a field offset. fld/rw expect small field displacements (e.g. 0xE0). Use `fn` or `callees` for function addresses.", disp));
                }
                cmd_fld(ctx, &Fld { disp, base, reads: r, writes: w }, max);
            }
            "imm" => { let v = rest.first().ok_or("imm needs a value")?; cmd_imm(ctx, u64::from_str_radix(v.trim_start_matches("0x"), 16).map_err(|e| e.to_string())?, max); }
            "comp" => {
                let n = rest.first().ok_or("comp needs a component type name")?;
                let h = n.bytes().fold(0x811c9dc5u32, |h, c| (h ^ c as u32).wrapping_mul(0x01000193));
                println!("{} = {:#x} (FNV-1a 32 of the type name, the ECS component hash)", n, h);
                cmd_imm(ctx, h as u64, max);
            }
            "ptr" => { let a = resolve(ctx, &rest)?; cmd_ptr(ctx, a, max); }
            "vt" => { let n = rest.get(1).and_then(|t| t.parse().ok()).unwrap_or(32usize); let a = resolve(ctx, &rest[..1.min(rest.len())])?; cmd_vt(ctx, a, n); }
            "find" => { let hits = find_sig(ctx, &rest.join(" ")); for h in hits.iter().take(max) { println!("{:x}  {}", h, func_label(ctx, *h)); } println!("-- {} hit(s)", hits.len()); }
            "name" => { let a = resolve(ctx, &rest[..1.min(rest.len())])?; cmd_name(ctx, a, rest.get(1).ok_or("name needs a name")?); }
            other => return Err(format!("unknown command '{}' (help)", other)),
        }
        Ok(())
    })();
    if let Err(e) = res { println!("error: {}", e); }
}

fn reg_of(t: &str) -> Option<Register> {
    use Register::*;
    Some(match t { "rax" => RAX, "rcx" => RCX, "rdx" => RDX, "rbx" => RBX, "rsp" => RSP, "rbp" => RBP, "rsi" => RSI, "rdi" => RDI, "r8" => R8, "r9" => R9, "r10" => R10, "r11" => R11, "r12" => R12, "r13" => R13, "r14" => R14, "r15" => R15, _ => return Option::None })
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.is_empty() { eprintln!("usage: rdis <exe> [-c \"cmd; cmd\" | cmd args...]   (rdis <exe> then `help`)"); std::process::exit(2); }
    let mut ctx = load(&args[0]);
    if args.len() > 1 { PRETTY.store(false, std::sync::atomic::Ordering::Relaxed); }
    const CMDS: [&str; 63] = ["gobj", "ptables", "structm", "struct-from-fn", "worklist", "observe", "portfacts", "port", "abi", "sigcheck", "mksig", "hookpoints", "flow", "contradict", "surprises", "corroborate", "investigate", "recipes", "bench", "needs", "decide", "choke", "common", "uses", "anchors", "comps", "sum", "cfg", "gates", "path", "reach", "classes", "class", "vslot", "vcalls", "rw", "struct", "system", "assert", "retract", "contest", "facts", "why", "audit", "info", "fn", "ptr", "comp", "dis", "xr", "callers", "callees", "str", "fld", "imm", "vt", "find", "name", "names", "sec", "help", "?", "walk"];
    if args.len() == 2 && args[1] == "--mcp" {
        PRETTY.store(false, std::sync::atomic::Ordering::Relaxed);
        mcp::serve(&mut ctx);
    } else if args.len() == 1 {
        let stdin = std::io::stdin();
        loop {
            print!("rdis> ");
            let _ = std::io::stdout().flush();
            let mut l = String::new();
            if stdin.lock().read_line(&mut l).unwrap_or(0) == 0 { break; }
            if matches!(l.trim(), "q" | "quit" | "exit") { break; }
            run(&mut ctx, l.trim());
        }
    } else if args[1] == "-c" {
        for c in args[2..].join(" ").split(';') { println!("> {}", c.trim()); run(&mut ctx, c.trim()); }
    } else if CMDS.contains(&args[1].as_str()) {
        run(&mut ctx, &args[1..].join(" "));
    } else {
        // the old form: rdis <exe> <rva|sig> [--max N] [--calls] [--find-sig]
        let rest: Vec<String> = args[1..].iter().filter(|a| a.as_str() != "--calls" && a.as_str() != "--find-sig").cloned().collect();
        let cmd = if args.iter().any(|a| a == "--find-sig") { "find" } else if args.iter().any(|a| a == "--calls") { "callees" } else { "fn" };
        run(&mut ctx, &format!("{} {}", cmd, rest.join(" ")));
    }
}
