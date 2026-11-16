// Control-flow walk from an RVA.
//
//   walk <rva> [--reg R]
//
// Follows straight-line code, both sides of conditional jumps, the target of
// unconditional jumps, and the fallthrough past calls. A path stops at ret /
// int3 / ud2 and at an indirect jmp (printed with `; indirect jmp`). Every
// instruction is visited at most once and the walk is capped at 4000
// instructions. Reachable instructions are printed sorted by address in the
// same `0xRVA  instruction` format as `rdis dis`.
//
// With `--reg R` a table of every [R+off] memory operand is printed after the
// listing: offset, direction (R/W), size if inferable, and RVA.
use crate::Ctx;
use iced_x86::{Decoder, DecoderOptions, FlowControl, Formatter, Instruction, Mnemonic, OpKind, Register};
use std::collections::BTreeSet;

const WALK_CAP: usize = 4000;

struct MemUse {
    rva: u32,
    off: i64,
    write: bool,
    size: usize,
}

fn is_read_only(m: Mnemonic) -> bool {
    matches!(
        m,
        Mnemonic::Cmp
            | Mnemonic::Test
            | Mnemonic::Push
            | Mnemonic::Call
            | Mnemonic::Jmp
            | Mnemonic::Bt
            | Mnemonic::Ucomiss
            | Mnemonic::Comiss
            | Mnemonic::Prefetchw
            | Mnemonic::Prefetcht0
    )
}

fn decode_at(ctx: &Ctx, rva: u32) -> Option<Instruction> {
    let bytes = ctx.pe.bytes(rva, 16);
    if bytes.is_empty() {
        return None;
    }
    let mut dec = Decoder::with_ip(64, bytes, rva as u64, DecoderOptions::NONE);
    let mut ins = Instruction::default();
    if !dec.can_decode() {
        return None;
    }
    dec.decode_out(&mut ins);
    if ins.is_invalid() {
        return None;
    }
    Some(ins)
}

fn reg_label(r: Register) -> &'static str {
    use Register::*;
    match r {
        RAX => "rax",
        RCX => "rcx",
        RDX => "rdx",
        RBX => "rbx",
        RSP => "rsp",
        RBP => "rbp",
        RSI => "rsi",
        RDI => "rdi",
        R8 => "r8",
        R9 => "r9",
        R10 => "r10",
        R11 => "r11",
        R12 => "r12",
        R13 => "r13",
        R14 => "r14",
        R15 => "r15",
        _ => "?",
    }
}

fn disp_text(off: i64) -> String {
    if off < 0 {
        format!("-{:#X}", -(off))
    } else {
        format!("+{:#X}", off)
    }
}

pub fn walk(ctx: &Ctx, start: u32, reg: Option<Register>) {
    let mut seen: BTreeSet<u32> = BTreeSet::new();
    let mut indirect: BTreeSet<u32> = BTreeSet::new();
    let mut lines: Vec<(u32, String)> = vec![];
    let mut memuses: Vec<MemUse> = vec![];
    let mut stack: Vec<u32> = vec![start];

    while let Some(a) = stack.pop() {
        if seen.len() >= WALK_CAP {
            break;
        }
        if !seen.insert(a) {
            continue;
        }
        let ins = match decode_at(ctx, a) {
            Some(i) => i,
            None => continue,
        };
        let mut text = String::new();
        crate::listing::formatter().format(&ins, &mut text);
        lines.push((a, text));

        if let Some(r) = reg {
            for k in 0..ins.op_count() {
                if ins.op_kind(k) == OpKind::Memory && ins.memory_base().full_register() == r {
                    let write = k == 0 && !is_read_only(ins.mnemonic());
                    memuses.push(MemUse {
                        rva: a,
                        off: ins.memory_displacement64() as i64,
                        write,
                        size: ins.memory_size().size(),
                    });
                }
            }
        }

        match ins.flow_control() {
            FlowControl::ConditionalBranch => {
                if ins.op0_kind() == OpKind::NearBranch64 {
                    let t = ins.near_branch_target() as u32;
                    if ctx.pe.is_exec(t) && !seen.contains(&t) {
                        stack.push(t);
                    }
                }
                let nx = ins.next_ip() as u32;
                if !seen.contains(&nx) {
                    stack.push(nx);
                }
            }
            FlowControl::UnconditionalBranch => {
                if ins.op0_kind() == OpKind::NearBranch64 {
                    let t = ins.near_branch_target() as u32;
                    if ctx.pe.is_exec(t) && !seen.contains(&t) {
                        stack.push(t);
                    }
                }
            }
            FlowControl::Call | FlowControl::IndirectCall => {
                let nx = ins.next_ip() as u32;
                if !seen.contains(&nx) {
                    stack.push(nx);
                }
            }
            FlowControl::IndirectBranch => {
                indirect.insert(a);
            }
            FlowControl::Return | FlowControl::Exception => {}
            _ => {
                let nx = ins.next_ip() as u32;
                if !seen.contains(&nx) {
                    stack.push(nx);
                }
            }
        }
    }

    lines.sort_by_key(|(a, _)| *a);
    for (a, text) in &lines {
        if indirect.contains(a) {
            println!("  {:x}  {:<46} ; indirect jmp", a, text);
        } else {
            println!("  {:x}  {}", a, text);
        }
    }
    println!(
        "-- {} instruction(s){}",
        seen.len(),
        if seen.len() >= WALK_CAP {
            " (cap)"
        } else {
            ""
        }
    );

    if let Some(r) = reg {
        let rn = reg_label(r);
        memuses.sort_by_key(|m| (m.rva, m.off));
        println!("  [{}+off] accesses:", rn);
        for m in &memuses {
            println!(
                "    {:x}  {} [{}{}]  size {}",
                m.rva,
                if m.write { "W" } else { "R" },
                rn,
                disp_text(m.off),
                m.size
            );
        }
        println!("-- {} [{}+off] access(es)", memuses.len(), rn);
    }
}