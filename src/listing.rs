// Annotated function listing: basic-block labels with their incoming jumps, resolved call/jump targets, strings behind rip-relative loads, vtable-call slots,
// and a linear pointer-chain tracker ("a0" is the first argument) that names what a memory operand is a field of.
use crate::Ctx;
use iced_x86::{Decoder, DecoderOptions, FlowControl, Formatter, Instruction, IntelFormatter, Mnemonic, OpKind, Register};
use std::collections::{BTreeMap, HashMap};

pub struct Opts {
    pub chains: bool, // annotate memory operands with the pointer chain they come from
    pub max: usize,
}

pub fn formatter() -> IntelFormatter {
    let mut f = IntelFormatter::new();
    f.options_mut().set_hex_prefix("0x");
    f.options_mut().set_hex_suffix("");
    f.options_mut().set_branch_leading_zeros(false);
    f.options_mut().set_uppercase_hex(true);
    f
}

// The end of a function .pdata does not cover (small leaf getters): decode until a `ret` that is past every forward jump.
pub fn heuristic_end(ctx: &Ctx, begin: u32) -> u32 {
    let bytes = ctx.pe.bytes(begin, 0x4000);
    let mut dec = Decoder::with_ip(64, bytes, begin as u64, DecoderOptions::NONE);
    let mut ins = Instruction::default();
    let mut far = 0u64;
    while dec.can_decode() {
        dec.decode_out(&mut ins);
        if matches!(ins.flow_control(), FlowControl::ConditionalBranch | FlowControl::UnconditionalBranch) && ins.op0_kind() == OpKind::NearBranch64 && ins.near_branch_target() > far {
            far = ins.near_branch_target();
        }
        if ins.flow_control() == FlowControl::Return && ins.ip() >= far { return ins.next_ip() as u32; }
        if ins.is_invalid() { break; }
    }
    ins.next_ip() as u32
}

pub fn decode_range(ctx: &Ctx, begin: u32, end: u32) -> Vec<Instruction> {
    let bytes = ctx.pe.bytes(begin, (end - begin) as usize);
    let mut dec = Decoder::with_ip(64, bytes, begin as u64, DecoderOptions::NONE);
    let mut out = vec![];
    while dec.can_decode() {
        let mut ins = Instruction::default();
        dec.decode_out(&mut ins);
        out.push(ins);
    }
    out
}

pub fn target_name(ctx: &Ctx, rva: u32) -> String {
    if let Some(n) = ctx.names.get(&rva) { return n.clone(); }
    if ctx.pe.is_exec(rva) { format!("sub_{:x}", rva) } else { format!("data_{:x}", rva) }
}

fn full(r: Register) -> Register { r.full_register() }

// Does this instruction write its first operand? (memory or register)
fn writes_op0(m: Mnemonic) -> bool {
    !matches!(m, Mnemonic::Cmp | Mnemonic::Test | Mnemonic::Push | Mnemonic::Call | Mnemonic::Jmp | Mnemonic::Bt | Mnemonic::Ucomiss | Mnemonic::Ucomisd | Mnemonic::Comiss | Mnemonic::Comisd | Mnemonic::Nop | Mnemonic::Prefetchw | Mnemonic::Prefetcht0 | Mnemonic::Cmpxchg)
}

pub struct Chains {
    regs: HashMap<Register, String>,
}

impl Chains {
    pub fn new() -> Chains {
        let mut regs = HashMap::new();
        for (r, n) in [(Register::RCX, "a0"), (Register::RDX, "a1"), (Register::R8, "a2"), (Register::R9, "a3")] { regs.insert(r, n.to_string()); }
        Chains { regs }
    }

    pub fn clear(&mut self) { self.regs.clear(); }

    // The chain of the memory operand's base register, e.g. "*(a0+0x1C8)".
    pub fn operand(&self, ins: &Instruction) -> Option<String> {
        let base = full(ins.memory_base());
        let s = self.regs.get(&base)?;
        let d = ins.memory_displacement64() as i64;
        let disp = if d < 0 { format!("-{:#X}", -(d)) } else { format!("+{:#X}", d) };
        if ins.memory_index() != Register::None { return Some(format!("{}{}+idx", s, disp)); }
        Some(format!("{}{}", s, disp))
    }

    pub fn step(&mut self, ins: &Instruction) {
        match ins.flow_control() {
            FlowControl::Call | FlowControl::IndirectCall => {
                for r in [Register::RAX, Register::RCX, Register::RDX, Register::R8, Register::R9, Register::R10, Register::R11] { self.regs.remove(&r); }
                if ins.op0_kind() == OpKind::NearBranch64 {
                    self.regs.insert(Register::RAX, format!("ret@{:x}", ins.near_branch_target()));
                }
                return;
            }
            _ => {}
        }
        if ins.op_count() == 0 || ins.op0_kind() != OpKind::Register { return; }
        let dst = full(ins.op0_register());
        if !dst.is_gpr64() { return; }
        let new = match ins.mnemonic() {
            Mnemonic::Mov if ins.op1_kind() == OpKind::Register => self.regs.get(&full(ins.op1_register())).cloned(),
            Mnemonic::Mov if ins.op1_kind() == OpKind::Memory && !ins.is_ip_rel_memory_operand() => self.operand(ins).map(|s| format!("*({})", s)),
            Mnemonic::Lea if !ins.is_ip_rel_memory_operand() => self.operand(ins),
            Mnemonic::Cmp | Mnemonic::Test | Mnemonic::Push => return,
            _ => None,
        };
        match new {
            Some(s) if s.len() <= 56 => { self.regs.insert(dst, s); }
            _ => { self.regs.remove(&dst); }
        }
    }
}

pub fn list_function(ctx: &mut Ctx, begin: u32, end: u32, o: &Opts) {
    let instrs = decode_range(ctx, begin, end);
    let mut labels: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    for ins in &instrs {
        if matches!(ins.flow_control(), FlowControl::ConditionalBranch | FlowControl::UnconditionalBranch) && ins.op0_kind() == OpKind::NearBranch64 {
            let t = ins.near_branch_target() as u32;
            if t >= begin && t < end { labels.entry(t).or_default().push(ins.ip() as u32); }
        }
    }
    let callers = ctx.xrefs().to(begin).len();
    let name = ctx.names.get(&begin).cloned().unwrap_or_else(|| format!("sub_{:x}", begin));
    println!("{}  [{:#x}..{:#x})  size {:#x}  {} xrefs in", name, begin, end, end - begin, callers);
    let frags = ctx.pe.fragments_of(begin);
    if !frags.is_empty() {
        println!("  chained fragments: {}", frags.iter().map(|f| format!("{:#x}..{:#x}", f.0, f.1)).collect::<Vec<_>>().join(", "));
    }
    let mut fmt = formatter();
    let mut chains = Chains::new();
    let mut barrier = false;
    for (n, ins) in instrs.iter().enumerate() {
        if n >= o.max { println!("  ... (--max {})", o.max); break; }
        let ip = ins.ip() as u32;
        if let Some(from) = labels.get(&ip) {
            let list: Vec<String> = from.iter().take(6).map(|f| format!("{:x}", f)).collect();
            println!("\nloc_{:x}:  ; from {}{}", ip, list.join(", "), if from.len() > 6 { ", ..." } else { "" });
            if barrier { chains.clear(); }
        }
        let mut text = String::new();
        fmt.format(ins, &mut text);
        let note = annotate(ctx, ins, begin, end, &labels, &chains, o.chains);
        println!("  {:x}  {:<46}{}", ip, text, note);
        chains.step(ins);
        barrier = matches!(ins.flow_control(), FlowControl::UnconditionalBranch | FlowControl::Return | FlowControl::IndirectBranch);
    }
}

fn annotate(ctx: &Ctx, ins: &Instruction, begin: u32, end: u32, labels: &BTreeMap<u32, Vec<u32>>, chains: &Chains, show_chains: bool) -> String {
    let mut parts: Vec<String> = vec![];
    if ins.op_count() > 0 && ins.op0_kind() == OpKind::NearBranch64 {
        let t = ins.near_branch_target() as u32;
        if ins.flow_control() == FlowControl::Call || t < begin || t >= end || !labels.contains_key(&t) {
            parts.push(format!("-> {}", target_name(ctx, t)));
        } else {
            parts.push(format!("-> loc_{:x}", t));
        }
    }
    if ins.is_ip_rel_memory_operand() {
        let a = ins.ip_rel_memory_address() as u32;
        let mut s = format!("[{}]", target_name(ctx, a));
        if let Some(st) = ctx.pe.string_at(a) { s.push_str(&format!(" \"{}\"", st)); }
        else if ins.mnemonic() != Mnemonic::Lea {
            if let Some(v) = ctx.pe.u64_at(a) {
                let v = v.wrapping_sub(ctx.image_base) as u32;
                if (v as u64) < 0x1_0000_0000 && ctx.pe.is_exec(v) { s.push_str(&format!(" = {}", target_name(ctx, v))); }
            }
        }
        parts.push(s);
    } else if (0..ins.op_count()).any(|k| ins.op_kind(k) == OpKind::Memory) {
        let d = ins.memory_displacement64();
        if ins.flow_control() == FlowControl::IndirectCall && d % 8 == 0 && d < 0x4000 && ins.memory_base() != Register::None {
            let on = chains.operand(ins).map(|c| format!(" via {}", c.rsplit_once('+').map_or(c.clone(), |x| x.0.to_string()))).unwrap_or_default();
            parts.push(format!("vcall slot {} (+{:#X}){}", d / 8, d, on));
        } else if show_chains {
            if let Some(c) = chains.operand(ins) {
                let rw = if ins.op0_kind() == OpKind::Memory && writes_op0(ins.mnemonic()) { "W" } else { "R" };
                parts.push(format!("{} {}", rw, c));
            }
        }
    }
    if parts.is_empty() { String::new() } else { format!("; {}", parts.join("  ")) }
}
