// Symbolic summary of one function: a forward dataflow over the CFG with symbolic registers and stack slots.
//
// What is tracked (and what is dropped, never guessed):
//   regs: 16 GPR + 16 XMM, each an expression (Arg/Imm/Load/Ret/Comp/Add/...); at a join differing values become Unk.
//   stack: slots relative to the entry rsp (Stack(off)); at a join only identical slots survive; calls kill the outgoing-arg area; if the address of
//   a stack slot escapes (passed/stored), calls and unknown-base stores drop all slots.
//   heap memory is NOT modelled: a load is Load(addr-expression), i.e. "the value at that address at that time", not forwarded from earlier stores.
use crate::cfg::{self, Cfg, EKind};
use crate::Ctx;
use iced_x86::{ConditionCode, Instruction, InstructionInfoFactory, Mnemonic, OpAccess, OpKind, Register};
use std::collections::{BTreeMap, HashMap};
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum E {
    Arg(u8),
    Imm(i64),
    Load(Box<E>, u8),
    Ret(u32),
    Comp(String, u32),
    Add(Box<E>, i64),
    Bin(&'static str, Box<E>, Box<E>),
    Un(&'static str, Box<E>),
    Stack(i64),
    Glob(u32),
    Named(String),
    Unk,
}

fn hx(v: i64) -> String { if v < 0 { format!("-{:#X}", -(v as i128)) } else { format!("{:#X}", v) } }

impl fmt::Display for E {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            E::Arg(n) => write!(f, "a{}", n),
            E::Imm(v) => write!(f, "{}", hx(*v)),
            E::Load(e, 8) => write!(f, "*({})", e),
            E::Load(e, s) => write!(f, "*u{}({})", *s as u32 * 8, e),
            E::Ret(ip) => write!(f, "ret@{:x}", ip),
            E::Comp(n, ip) => write!(f, "typed<{}>@{:x}", n, ip),
            E::Add(b, k) => if *k < 0 { write!(f, "{}-{:#X}", b, -k) } else { write!(f, "{}+{:#X}", b, k) },
            E::Bin(op, a, b) => write!(f, "({} {} {})", a, op, b),
            E::Un(op, a) => write!(f, "{}({})", op, a),
            E::Stack(o) => write!(f, "&stk{}{:#X}", if *o < 0 { "-" } else { "+" }, o.abs()),
            E::Glob(g) => write!(f, "&data_{:x}", g),
            E::Named(n) => write!(f, "{}", n),
            E::Unk => write!(f, "?"),
        }
    }
}

impl E {
    pub fn size(&self) -> usize {
        match self { E::Load(e, _) | E::Add(e, _) | E::Un(_, e) => 1 + e.size(), E::Bin(_, a, b) => 1 + a.size() + b.size(), _ => 1 }
    }
    pub fn is_unk(&self) -> bool { matches!(self, E::Unk) }
    pub fn add(self, k: i64) -> E {
        if k == 0 { return self; }
        match self {
            E::Imm(a) => E::Imm(a.wrapping_add(k)),
            E::Add(b, a) => { let n = a.wrapping_add(k); if n == 0 { *b } else { E::Add(b, n) } }
            E::Stack(a) => E::Stack(a + k),
            E::Glob(a) => E::Glob((a as i64 + k) as u32),
            E::Unk => E::Unk,
            e => E::Add(Box::new(e), k),
        }
    }
    pub fn bin(op: &'static str, a: E, b: E) -> E {
        if a.is_unk() || b.is_unk() { return E::Unk; }
        if let (E::Imm(x), E::Imm(y)) = (&a, &b) {
            let r = match op { "+" => Some(x.wrapping_add(*y)), "-" => Some(x.wrapping_sub(*y)), "&" => Some(x & y), "|" => Some(x | y), "^" => Some(x ^ y), "<<" => Some(x.wrapping_shl(*y as u32)), "*" => Some(x.wrapping_mul(*y)), _ => None };
            if let Some(v) = r { return E::Imm(v); }
        }
        if op == "+" { if let E::Imm(k) = b { return a.add(k); } if let E::Imm(k) = a { return b.add(k); } }
        if op == "-" { if let E::Imm(k) = b { return a.add(-k); } }
        let e = E::Bin(op, Box::new(a), Box::new(b));
        if e.size() > 14 { E::Unk } else { e }
    }
    pub fn un(op: &'static str, a: E) -> E { if a.is_unk() { E::Unk } else { let e = E::Un(op, Box::new(a)); if e.size() > 14 { E::Unk } else { e } } }
    pub fn load(addr: E, size: u8) -> E { if addr.is_unk() { E::Unk } else { let e = E::Load(Box::new(addr), size); if e.size() > 14 { E::Unk } else { e } } }
    // (base, constant offset) view of an address expression
    pub fn split(&self) -> (E, i64) {
        match self { E::Add(b, k) => ((**b).clone(), *k), E::Imm(v) => (E::Imm(0), *v), e => (e.clone(), 0) }
    }
}

const NREG: usize = 32; // 0..15 gpr, 16..31 xmm

fn gi(r: Register) -> Option<usize> {
    if r == Register::None { return Option::None; }
    if r.is_xmm() || r.is_ymm() || r.is_zmm() { let n = r.number(); return if n < 16 { Some(16 + n) } else { Option::None }; }
    if !r.is_gpr() { return None; }
    use Register as R;
    Some(match r.full_register() { R::RAX => 0, R::RCX => 1, R::RDX => 2, R::RBX => 3, R::RSP => 4, R::RBP => 5, R::RSI => 6, R::RDI => 7, R::R8 => 8, R::R9 => 9, R::R10 => 10, R::R11 => 11, R::R12 => 12, R::R13 => 13, R::R14 => 14, R::R15 => 15, _ => return Option::None })
}

#[derive(Clone, PartialEq)]
struct St { regs: Vec<E>, stack: BTreeMap<i64, (E, u8)>, escaped: bool }

impl St {
    fn entry() -> St {
        let mut regs = vec![E::Unk; NREG];
        regs[1] = E::Arg(0); regs[2] = E::Arg(1); regs[8] = E::Arg(2); regs[9] = E::Arg(3);
        regs[4] = E::Stack(0);
        St { regs, stack: BTreeMap::new(), escaped: false }
    }
    fn merge(&self, o: &St) -> St {
        let regs = self.regs.iter().zip(o.regs.iter()).map(|(a, b)| if a == b { a.clone() } else { E::Unk }).collect();
        let mut stack = BTreeMap::new();
        for (k, v) in &self.stack { if o.stack.get(k) == Some(v) { stack.insert(*k, v.clone()); } }
        St { regs, stack, escaped: self.escaped || o.escaped }
    }
    fn kill_overlap(&mut self, off: i64, size: i64) {
        let ks: Vec<i64> = self.stack.range(off - 16..off + size).filter(|(k, (_, s))| **k < off + size && off < **k + *s as i64).map(|(k, _)| *k).collect();
        for k in ks { self.stack.remove(&k); }
    }
}

#[derive(Clone, Debug)]
pub struct Acc { pub disp: i64, pub ip: u32, pub read: bool, pub write: bool, pub size: u8, pub base: E, pub off: i64, pub indexed: bool, pub fp: bool, pub mn: String, pub value: Option<E> }

#[derive(Clone, Debug)]
pub enum Tgt { Direct(u32), Slot { obj: E, vptr_off: i64, disp: i64 }, Global(u32), Mem(E), Reg(E) }

#[derive(Clone, Debug)]
pub struct CallEv { pub ip: u32, pub tgt: Tgt, pub args: Vec<E>, pub tail: bool }

#[derive(Clone, Debug)]
pub struct Cond { pub ip: u32, pub taken: String, pub not_taken: String, pub setter: Option<u32>, pub exact: bool }

pub struct Sum {
    pub cfg: Cfg,
    pub accs: Vec<Acc>,
    pub stack_slots: BTreeMap<i64, Vec<StackSlotUse>>,
    pub calls: Vec<CallEv>,
    pub conds: HashMap<u32, Cond>,
    pub rets: Vec<(u32, E)>,
    pub strs: Vec<(u32, u32, String)>,
    pub comp_refs: Vec<(u32, String)>,
    pub notes: Vec<String>,
    pub reached: usize,
}

// A single use of a stack slot: a direct load/store of, or address taken of, [rsp+off].
#[derive(Clone, Debug)]
pub struct StackSlotUse {
    pub ip: u32,
    pub kind: String,   // "store" | "load" | "address"
    pub size: u8,
    pub value: Option<String>,
    pub base_offset: i64,
}

impl fmt::Display for StackSlotUse {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {} size={}", self.kind, hx(self.base_offset), self.size)?;
        if let Some(v) = &self.value { write!(f, " = {}", v)?; }
        Ok(())
    }
}

#[derive(Clone)]
struct Setter { ip: u32, mn: Mnemonic, a: E, b: E, known: bool }

pub struct Env<'a> { pub ctx: &'a Ctx, pub comps: &'a HashMap<u32, String> }

fn imm_of(i: &Instruction, k: u32) -> Option<i64> {
    match i.op_kind(k) {
        OpKind::Immediate8 | OpKind::Immediate16 | OpKind::Immediate32 | OpKind::Immediate64 | OpKind::Immediate8to16 | OpKind::Immediate8to32 | OpKind::Immediate8to64 | OpKind::Immediate32to64 => Some(i.immediate(k) as i64),
        _ => None,
    }
}

fn reg_read(st: &St, r: Register) -> E {
    let i = match gi(r) { Some(i) => i, None => return E::Unk };
    let v = st.regs[i].clone();
    if i >= 16 { return v; }
    match r.size() {
        8 => v,
        4 => match v { E::Imm(x) => E::Imm(x as u32 as i64), E::Load(_, s) if s <= 4 => v, v => E::un("u32", v) },
        2 => match v { E::Imm(x) => E::Imm(x as u16 as i64), v => E::un("u16", v) },
        1 => if r.is_gpr8() && matches!(r, Register::AH | Register::BH | Register::CH | Register::DH) { E::Unk } else { match v { E::Imm(x) => E::Imm(x as u8 as i64), v => E::un("u8", v) } },
        _ => E::Unk,
    }
}

fn reg_write(st: &mut St, r: Register, v: E) {
    let i = match gi(r) { Some(i) => i, None => return };
    if i >= 16 { st.regs[i] = v; return; }
    st.regs[i] = match r.size() {
        8 => v,
        4 => match v { E::Imm(x) => E::Imm(x as u32 as i64), E::Load(_, s) if s <= 4 => v, v => E::un("u32", v) },
        _ => E::Unk,
    };
}

// effective address of the explicit memory operand: (base, off, indexed)
fn mem_addr(st: &St, ins: &Instruction) -> (E, i64, bool) {
    if ins.is_ip_rel_memory_operand() { return (E::Glob(ins.ip_rel_memory_address() as u32), 0, false); }
    let seg = ins.segment_prefix();
    if matches!(seg, Register::GS | Register::FS) { return (E::un(if seg == Register::GS { "gs" } else { "fs" }, E::Imm(0)), ins.memory_displacement64() as i64, ins.memory_index() != Register::None); }
    let mut base = if ins.memory_base() == Register::None { E::Imm(0) } else { reg_read(st, ins.memory_base()) };
    let disp = ins.memory_displacement64() as i64;
    let mut indexed = false;
    if ins.memory_index() != Register::None {
        indexed = true;
        let idx = reg_read(st, ins.memory_index());
        base = E::bin("+", base, E::bin("*", idx, E::Imm(ins.memory_index_scale() as i64)));
    }
    let (b, k) = base.split();
    (b, k.wrapping_add(disp), indexed)
}

fn load_val(st: &St, base: &E, off: i64, indexed: bool, size: u8) -> E {
    if let (E::Stack(o), false) = (base, indexed) {
        let a = o + off;
        if let Some((v, s)) = st.stack.get(&a) {
            if *s == size { return v.clone(); }
            if size < *s { return E::un(match size { 1 => "u8", 2 => "u16", _ => "u32" }, v.clone()); }
            return E::Unk;
        }
        if a >= 0x28 && a % 8 == 0 && size == 8 { return E::Arg(4 + ((a - 0x28) / 8) as u8); }
        return E::Unk;
    }
    if indexed { if let E::Stack(_) = base { return E::Unk; } }
    E::load(base.clone().add(off), size)
}

fn store_val(st: &mut St, base: &E, off: i64, indexed: bool, size: u8, v: E) {
    match (base, indexed) {
        (E::Stack(o), false) => {
            let a = o + off;
            st.kill_overlap(a, size as i64);
            if !v.is_unk() { st.stack.insert(a, (v, size)); }
        }
        (E::Stack(_), true) => st.stack.clear(),
        _ => {
            if matches!(v, E::Stack(_)) { st.escaped = true; }
            if st.escaped { st.stack.clear(); }
        }
    }
}

fn fp_mn(m: Mnemonic) -> bool {
    let s = format!("{:?}", m).to_lowercase();
    (s.ends_with("ss") || s.ends_with("sd") || s.ends_with("ps") || s.ends_with("pd")) && !matches!(m, Mnemonic::Movsd if false) || s.starts_with("v") && s.len() > 3
}

struct Rec<'a> { sum: &'a mut Sum, fac: InstructionInfoFactory, ls: Option<Setter> }

fn opv(st: &St, ins: &Instruction, k: u32) -> E {
    match ins.op_kind(k) {
        OpKind::Register => { let r = ins.op_register(k); if r.is_gpr() || r.is_xmm() || r.is_ymm() { reg_read(st, r) } else { E::Unk } }
        OpKind::Memory => { let (b, o, ix) = mem_addr(st, ins); load_val(st, &b, o, ix, ins.memory_size().size().min(255) as u8) }
        _ => match imm_of(ins, k) { Some(v) => E::Imm(v), None => E::Unk },
    }
}

fn setter_for(st: &St, ins: &Instruction) -> Option<Setter> {
    if ins.rflags_modified() == 0 { return None; }
    use Mnemonic::*;
    let ok = matches!(ins.mnemonic(), Cmp | Test | Sub | Add | And | Or | Xor | Inc | Dec | Neg | Ucomiss | Comiss | Ucomisd | Comisd | Bt);
    let a = if ins.op_count() > 0 { opv(st, ins, 0) } else { E::Unk };
    let b = if ins.op_count() > 1 { opv(st, ins, 1) } else { E::Unk };
    Some(Setter { ip: ins.ip() as u32, mn: ins.mnemonic(), a, b, known: ok })
}

fn cond_text(s: &Option<Setter>, cc: ConditionCode) -> (String, bool) {
    let s = match s { Some(s) => s, None => return (format!("flags? {}", cfg::cc_text(cc)), false) };
    use Mnemonic::*;
    let op = cfg::cc_text(cc);
    if !s.known { return (format!("flags({:?} ..) {}", s.mn, op), false); }
    match s.mn {
        Cmp | Sub => (format!("{} {} {}", s.a, op, s.b), true),
        Test | And => if s.a == s.b { (format!("{} {} 0", s.a, op), true) } else { (format!("({} & {}) {} 0", s.a, s.b, op), true) },
        Ucomiss | Comiss | Ucomisd | Comisd => (format!("fcmp({}, {}) {}", s.a, s.b, op), true),
        Bt => (format!("bit({}, {}) {}", s.a, s.b, match cc { ConditionCode::b => "set", ConditionCode::ae => "clear", _ => "?" }), matches!(cc, ConditionCode::b | ConditionCode::ae)),
        _ => (format!("({:?} {}, {}) {} 0", s.mn, s.a, s.b, op), matches!(cc, ConditionCode::e | ConditionCode::ne | ConditionCode::s | ConditionCode::ns)),
    }
}

// transfer one instruction; records events when `rec` is given
fn exec(st: &mut St, ins: &Instruction, env: &Env, rec: &mut Option<Rec>) {
    use Mnemonic::*;
    let ip = ins.ip() as u32;
    let mn = ins.mnemonic();
    // flag setter tracking (needs the PRE state)
    if let Some(r) = rec.as_mut() {
        if matches!(ins.flow_control(), iced_x86::FlowControl::Call | iced_x86::FlowControl::IndirectCall) { r.ls = None; }
        else if let Some(s) = setter_for(st, ins) { r.ls = Some(s); }
    }
    // component hash immediates
    if let Some(r) = rec.as_mut() {
        for k in 0..ins.op_count() { if let Some(v) = imm_of(ins, k) { if let Some(n) = env.comps.get(&(v as u32)) { if matches!(ins.op_kind(k), OpKind::Immediate32 | OpKind::Immediate32to64) { r.sum.comp_refs.push((ip, n.clone())); } } } }
        if ins.is_ip_rel_memory_operand() {
            let a = ins.ip_rel_memory_address() as u32;
            if let Some(s) = env.ctx.pe.string_at(a) { r.sum.strs.push((ip, a, s)); }
        }
    }
    // memory access event (explicit memory operand only)
    let has_mem = (0..ins.op_count()).any(|k| ins.op_kind(k) == OpKind::Memory);
    if has_mem && !matches!(mn, Lea | Nop | Prefetchw | Prefetcht0 | Prefetcht1 | Prefetcht2 | Prefetchnta) {
        if let Some(r) = rec.as_mut() {
            let (b, o, ix) = mem_addr(st, ins);
            let info = r.fac.info(ins);
            let acc = info.used_memory().iter().map(|m| m.access()).find(|a| *a != OpAccess::NoMemAccess).unwrap_or(OpAccess::Read);
            let write = matches!(acc, OpAccess::Write | OpAccess::CondWrite | OpAccess::ReadWrite | OpAccess::ReadCondWrite);
            let read = matches!(acc, OpAccess::Read | OpAccess::CondRead | OpAccess::ReadWrite | OpAccess::ReadCondWrite);
            let fp = (0..ins.op_count()).any(|k| ins.op_kind(k) == OpKind::Register && { let rg = ins.op_register(k); rg.is_xmm() || rg.is_ymm() || rg.is_zmm() });
            let value = if write && ins.op_count() > 1 && ins.op0_kind() == OpKind::Memory {
                match mn {
                    Xchg | Cmpxchg | Mov | Movss | Movsd | Movaps | Movups | Movq => Some(opv(st, ins, 1)),
                    _ => None,
                }
            } else { None };
            // stack-slot usage: a direct load/store of, or address taken of, a stack slot ([rsp+off])
            if let E::Stack(so) = b {
                if !ix {
                    let abs = so.wrapping_add(o);
                    let kind = if write { "store" } else { "load" };
                    let sval = if write && ins.op_count() > 1 && ins.op1_kind() == OpKind::Register {
                        Some(opv(st, ins, 1).to_string())
                    } else { None };
                    r.sum.stack_slots.entry(abs).or_default().push(StackSlotUse { ip, kind: kind.to_string(), size: ins.memory_size().size().min(255) as u8, value: sval, base_offset: abs });
                }
            }
            r.sum.accs.push(Acc { disp: if ins.is_ip_rel_memory_operand() { 0 } else { ins.memory_displacement64() as i64 }, ip, read, write, size: ins.memory_size().size().min(255) as u8, base: b, off: o, indexed: ix, fp, mn: format!("{:?}", mn).to_lowercase(), value });
        }
    }
    // lea reg, [rsp+off]: taking the address of a stack slot (no memory is accessed)
    if mn == Lea {
        if let Some(r) = rec.as_mut() {
            let (b, o, _ix) = mem_addr(st, ins);
            if let E::Stack(so) = b {
                let abs = so.wrapping_add(o);
                r.sum.stack_slots.entry(abs).or_default().push(StackSlotUse { ip, kind: "address".to_string(), size: ins.memory_size().size().min(255) as u8, value: None, base_offset: abs });
            }
        }
    }
    match ins.flow_control() {
        iced_x86::FlowControl::Call | iced_x86::FlowControl::IndirectCall => {
            let args: Vec<E> = [1usize, 2, 8, 9].iter().map(|i| st.regs[*i].clone()).collect();
            if args.iter().any(|a| matches!(a, E::Stack(_))) { st.escaped = true; }
            let tgt = target_of(st, ins, env);
            let mut comp: Option<String> = None;
            for a in &args { if let E::Imm(v) = a { if let Some(n) = env.comps.get(&(*v as u32)) { if *v >= 0x1000 { comp = Some(n.clone()); } } } }
            if let Some(r) = rec.as_mut() { r.sum.calls.push(CallEv { ip, tgt, args, tail: false }); }
            for i in [0usize, 1, 2, 8, 9, 10, 11] { st.regs[i] = E::Unk; }
            for i in 16..32 { st.regs[i] = E::Unk; }
            st.regs[0] = match comp { Some(n) => E::Comp(n, ip), None => E::Ret(ip) };
            let sp = match &st.regs[4] { E::Stack(o) => Some(*o), _ => None };
            if st.escaped { st.stack.clear(); } else if let Some(sp) = sp { st.kill_overlap(sp, 0x48); }
            return;
        }
        iced_x86::FlowControl::IndirectBranch => {
            if let Some(r) = rec.as_mut() {
                if !r.sum.cfg.switches.iter().any(|s| s.ip == ip) {
                    let tgt = target_of(st, ins, env);
                    let args: Vec<E> = [1usize, 2, 8, 9].iter().map(|i| st.regs[*i].clone()).collect();
                    r.sum.calls.push(CallEv { ip, tgt, args, tail: true });
                }
            }
            return;
        }
        iced_x86::FlowControl::UnconditionalBranch => {
            if let Some(r) = rec.as_mut() {
                if ins.op0_kind() == OpKind::NearBranch64 {
                    let t = ins.near_branch_target() as u32;
                    if r.sum.cfg.tail_calls.iter().any(|x| x.0 == ip) {
                        let args: Vec<E> = [1usize, 2, 8, 9].iter().map(|i| st.regs[*i].clone()).collect();
                        r.sum.calls.push(CallEv { ip, tgt: Tgt::Direct(t), args, tail: true });
                    }
                }
            }
            return;
        }
        iced_x86::FlowControl::Return => { if let Some(r) = rec.as_mut() { r.sum.rets.push((ip, st.regs[0].clone())); } return; }
        iced_x86::FlowControl::ConditionalBranch => return,
        _ => {}
    }
    // data flow
    let dst_reg = if ins.op_count() > 0 && ins.op0_kind() == OpKind::Register { Some(ins.op0_register()) } else { None };
    let dst_mem = ins.op_count() > 0 && ins.op0_kind() == OpKind::Memory;
    match mn {
        Mov | Movq | Movd | Movaps | Movups | Movdqa | Movdqu | Movss | Movsd | Movapd | Movupd if ins.op_count() == 2 && !(matches!(mn, Movss | Movsd) && dst_reg.map_or(false, |r| r.is_xmm()) && ins.op1_kind() == OpKind::Register) => {
            let sz = match ins.op1_kind() { OpKind::Memory => ins.memory_size().size() as u8, _ => if dst_mem { ins.memory_size().size() as u8 } else { 0 } };
            let v = opv(st, ins, 1);
            if let Some(r) = dst_reg { reg_write(st, r, v); }
            else if dst_mem { let (b, o, ix) = mem_addr(st, ins); store_val(st, &b, o, ix, sz.max(1), v); }
        }
        Movzx | Movsx | Movsxd if ins.op_count() == 2 => {
            let v = match (mn, ins.op1_kind()) {
                (Movzx, OpKind::Memory) => { let (b, o, ix) = mem_addr(st, ins); load_val(st, &b, o, ix, ins.memory_size().size() as u8) }
                (Movzx, _) => { let s = opv(st, ins, 1); s }
                (_, _) => E::un("sx", opv(st, ins, 1)),
            };
            if let Some(r) = dst_reg { reg_write(st, r, v); }
        }
        Lea => {
            let (b, o, ix) = mem_addr(st, ins);
            let v = if ix { E::bin("+", b, E::Imm(o)) } else { b.add(o) };
            if let Some(r) = dst_reg { reg_write(st, r, v); }
        }
        Add | Sub | And | Or | Xor | Imul | Shl | Shr | Sar if dst_reg.is_some() && ins.op_count() >= 2 => {
            let r = dst_reg.unwrap();
            if matches!(mn, Xor) && ins.op1_kind() == OpKind::Register && ins.op1_register() == r { reg_write(st, r, E::Imm(0)); }
            else {
                let (a, b) = if ins.op_count() == 3 { (opv(st, ins, 1), opv(st, ins, 2)) } else { (opv(st, ins, 0), opv(st, ins, 1)) };
                let op = match mn { Add => "+", Sub => "-", And => "&", Or => "|", Xor => "^", Imul => "*", Shl => "<<", Shr => ">>u", _ => ">>s" };
                let v = if r.size() == 8 { E::bin(op, a, b) } else { E::Unk };
                reg_write(st, r, v);
            }
        }
        Inc | Dec if dst_reg.is_some() => { let r = dst_reg.unwrap(); let v = reg_read(st, r); reg_write(st, r, if r.size() == 8 { v.add(if mn == Inc { 1 } else { -1 }) } else { E::Unk }); }
        Push => {
            let v = opv(st, ins, 0);
            if let E::Stack(o) = st.regs[4].clone() { st.regs[4] = E::Stack(o - 8); store_val(st, &E::Stack(o - 8), 0, false, 8, v); } else { st.regs[4] = E::Unk; }
        }
        Pop => {
            if let E::Stack(o) = st.regs[4].clone() {
                let v = load_val(st, &E::Stack(o), 0, false, 8);
                st.regs[4] = E::Stack(o + 8);
                if let Some(r) = dst_reg { reg_write(st, r, v); }
            } else { st.regs[4] = E::Unk; if let Some(r) = dst_reg { reg_write(st, r, E::Unk); } }
        }
        Cmp | Test | Nop | Int3 | Ud2 | Prefetchw | Prefetcht0 | Prefetcht1 | Prefetcht2 | Prefetchnta | Ucomiss | Ucomisd | Comiss | Comisd | Bt | Lfence | Mfence | Sfence | Pause | Endbr64 => {}
        _ => {
            // unknown effect: every written register becomes Unk, a written memory operand invalidates what it may alias
            let mut fac = InstructionInfoFactory::new();
            let info = fac.info(ins);
            for r in info.used_registers() {
                if matches!(r.access(), OpAccess::Write | OpAccess::CondWrite | OpAccess::ReadWrite | OpAccess::ReadCondWrite) {
                    if let Some(i) = gi(r.register()) { st.regs[i] = E::Unk; }
                }
            }
            if dst_mem {
                let (b, o, ix) = mem_addr(st, ins);
                store_val(st, &b, o, ix, ins.memory_size().size().max(1) as u8, E::Unk);
            } else if has_mem && info.used_memory().iter().any(|m| matches!(m.access(), OpAccess::Write | OpAccess::ReadWrite | OpAccess::CondWrite | OpAccess::ReadCondWrite)) {
                if st.escaped { st.stack.clear(); }
            }
        }
    }
    // rsp changes we do not model
    if matches!(mn, Sub | Add | And) && dst_reg.map_or(false, |r| r.full_register() == Register::RSP) {
        match (mn, imm_of(ins, 1), st.regs[4].clone()) {
            (Sub, Some(v), E::Stack(o)) => st.regs[4] = E::Stack(o - v),
            (Add, Some(v), E::Stack(o)) => st.regs[4] = E::Stack(o + v),
            _ => { st.regs[4] = E::Unk; if let Some(r) = rec.as_mut() { let n = format!("frame tracking lost at {:x} ({:?} rsp)", ip, mn); if !r.sum.notes.contains(&n) { r.sum.notes.push(n); } } }
        }
    }
}

// Windows CFG: `call [__guard_dispatch_icall_fptr]` takes the real target in rax; the global's initial value points at a `jmp rax` stub.
pub fn is_guard_thunk(ctx: &Ctx, g: u32) -> bool {
    let p = match ctx.pe.u64_at(g) { Some(p) => p.wrapping_sub(ctx.image_base), None => return false };
    if p >= 0x1_0000_0000 || !ctx.pe.is_exec(p as u32) { return false; }
    let b = ctx.pe.bytes(p as u32, 3);
    b.len() >= 2 && (b[..2] == [0xFF, 0xE0] || (b.len() >= 3 && b[..3] == [0x41, 0xFF, 0xE3]) || b[..2] == [0xFF, 0xE1])
}

fn classify(v: E) -> Tgt {
    if let E::Load(a, 8) = &v { let (b, d) = a.split(); if let E::Load(inner, 8) = &b { let (ob, k) = inner.split(); return Tgt::Slot { obj: ob, vptr_off: k, disp: d }; } }
    Tgt::Reg(v)
}

fn target_of(st: &St, ins: &Instruction, env: &Env) -> Tgt {
    match ins.op0_kind() {
        OpKind::NearBranch64 => Tgt::Direct(ins.near_branch_target() as u32),
        OpKind::Memory => {
            if ins.is_ip_rel_memory_operand() {
                let g = ins.ip_rel_memory_address() as u32;
                if is_guard_thunk(env.ctx, g) { return classify(st.regs[0].clone()); } // CFG dispatch: target is in rax
                return Tgt::Global(g);
            }
            let (b, o, ix) = mem_addr(st, ins);
            if !ix { if let E::Load(inner, 8) = &b { let (ob, k) = inner.split(); return Tgt::Slot { obj: ob, vptr_off: k, disp: o }; } }
            Tgt::Mem(b.add(o))
        }
        OpKind::Register => classify(reg_read(st, ins.op0_register())),
        _ => Tgt::Reg(E::Unk),
    }
}

pub fn summarize(env: &Env, begin: u32) -> Sum {
    let cfg = cfg::build(env.ctx, begin);
    let mut sum = Sum { cfg, accs: vec![], stack_slots: BTreeMap::new(), calls: vec![], conds: HashMap::new(), rets: vec![], strs: vec![], comp_refs: vec![], notes: vec![], reached: 0 };
    if !sum.cfg.blocks.contains_key(&sum.cfg.begin) { sum.notes.push(format!("no decodable code at {:#x}: nothing is known about this address", begin)); return sum; }
    // fixpoint on block entry states
    let starts: Vec<u32> = sum.cfg.blocks.keys().copied().collect();
    let mut inst: HashMap<u32, St> = HashMap::new();
    inst.insert(sum.cfg.begin, St::entry());
    let mut work: Vec<u32> = vec![sum.cfg.begin];
    let mut iters = 0usize;
    let cap = starts.len() * 30 + 100;
    while let Some(b) = work.pop() {
        iters += 1;
        if iters > cap { sum.notes.push("dataflow iteration cap hit; some states may be stale".into()); break; }
        let mut st = inst[&b].clone();
        let blk = sum.cfg.blocks[&b].clone();
        for i in blk.first..=blk.last { let ins = sum.cfg.ins[i]; exec(&mut st, &ins, env, &mut None); }
        for e in &blk.succ {
            if e.outside { continue; }
            let nst = match inst.get(&e.to) { Some(old) => { let m = old.merge(&st); if &m == old { continue; } m } None => st.clone() };
            inst.insert(e.to, nst);
            if !work.contains(&e.to) { work.push(e.to); }
        }
    }
    sum.reached = inst.len();
    // recording pass in address order
    let mut last_setter: HashMap<u32, Option<Setter>> = HashMap::new();
    let reached = sum.reached;
    let mut rec_sum = sum;
    for b in &starts {
        let mut st = match inst.get(b) { Some(s) => s.clone(), None => continue };
        let blk = rec_sum.cfg.blocks[b].clone();
        let mut ls: Option<Setter> = None;
        if let Some(ps) = rec_sum.cfg.preds.get(b) { if ps.len() == 1 { ls = last_setter.get(&ps[0].0).cloned().flatten(); } }
        let mut rec = Some(Rec { sum: &mut rec_sum, fac: InstructionInfoFactory::new(), ls });
        for i in blk.first..=blk.last {
            let ins = rec.as_ref().unwrap().sum.cfg.ins[i];
            if ins.flow_control() == iced_x86::FlowControl::ConditionalBranch {
                let r = rec.as_mut().unwrap();
                let cc = ins.condition_code();
                let (t, ex1) = cond_text(&r.ls, cc);
                let (n, _) = cond_text(&r.ls, negate(cc));
                let setter = r.ls.as_ref().map(|s| s.ip);
                r.sum.conds.insert(ins.ip() as u32, Cond { ip: ins.ip() as u32, taken: t, not_taken: n, setter, exact: ex1 && setter.is_some() });
            }
            exec(&mut st, &ins, env, &mut rec);
        }
        let ls = rec.take().unwrap().ls;
        last_setter.insert(*b, ls);
    }
    // switch conditions
    let sw: Vec<cfg::Switch> = rec_sum.cfg.switches.clone();
    let _ = sw;
    rec_sum.reached = reached;
    for (ip, why) in rec_sum.cfg.unresolved.clone() { rec_sum.notes.push(format!("unresolved indirect jump at {:x}: {}", ip, why)); }
    if starts.len() > rec_sum.reached { rec_sum.notes.push(format!("{} block(s) not reached by the dataflow (dead or behind an unresolved jump)", starts.len() - rec_sum.reached)); }
    let _ = EKind::Fall;
    rec_sum
}

fn negate(cc: ConditionCode) -> ConditionCode {
    use ConditionCode::*;
    match cc { o => no, no => o, b => ae, ae => b, e => ne, ne => e, be => a, a => be, s => ns, ns => s, p => np, np => p, l => ge, ge => l, le => g, g => le, None => None }
}
