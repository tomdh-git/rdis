use iced_x86::{Decoder, DecoderOptions, FlowControl, Formatter, Instruction, Mnemonic, OpKind};
use std::collections::{BTreeSet, VecDeque};

use crate::listing::Opts;
use crate::Ctx;

pub fn walk(ctx: &mut Ctx, start_rva: u32, base_reg: Option<iced_x86::Register>) {
    let (b, e) = match ctx.pe.function_of(start_rva) {
        Some(f) => f,
        None => (start_rva, crate::heuristic_end(ctx, start_rva)),
    };

    let mut visited = BTreeSet::new();
    let mut queue = VecDeque::new();
    queue.push_back(start_rva);

    let mut instructions: BTreeSet<u32> = BTreeSet::new();

    while let Some(rva) = queue.pop_front() {
        if !visited.insert(rva) {
            continue;
        }
        if rva < b || rva >= e {
            continue;
        }

        let bytes = ctx.pe.bytes(rva, 16);
        if bytes.is_empty() {
            continue;
        }

        let mut dec = Decoder::with_ip(64, bytes, rva as u64, DecoderOptions::NONE);
        if !dec.can_decode() {
            continue;
        }

        let mut ins = Instruction::default();
        dec.decode_out(&mut ins);

        instructions.insert(ins.ip() as u32);

        let flow = ins.flow_control();

        // Stop at these instructions
        if matches!(
            flow,
            FlowControl::Return
                | FlowControl::Interrupt
                | FlowControl::Exception
        ) {
            continue;
        }
        if matches!(ins.mnemonic(), Mnemonic::Int3 | Mnemonic::Ud2) {
            continue;
        }

        // Indirect jump - stop here
        if matches!(flow, FlowControl::IndirectBranch) {
            continue;
        }

        // Next sequential instruction
        let next_ip = ins.next_ip() as u32;
        if next_ip >= b && next_ip < e {
            queue.push_back(next_ip);
        }

        // Branch targets
        if matches!(
            flow,
            FlowControl::ConditionalBranch
                | FlowControl::UnconditionalBranch
                | FlowControl::Call
        ) {
            if ins.op0_kind() == OpKind::NearBranch64 {
                let target = ins.near_branch_target() as u32;
                if target >= b && target < e {
                    queue.push_back(target);
                }
            }
        }
    }

    // Print all reachable instructions sorted by address
    let opts = Opts {
        chains: false,
        max: instructions.len(),
    };
    for ip in instructions {
        let bytes = ctx.pe.bytes(ip, 16);
        let mut dec = Decoder::with_ip(64, bytes, ip as u64, DecoderOptions::NONE);
        let mut ins = Instruction::default();
        if dec.can_decode() {
            dec.decode_out(&mut ins);
            let mut s = String::new();
            crate::listing::formatter().format(&ins, &mut s);
            println!("{:x}  {}", ip, s);
        }
    }
}