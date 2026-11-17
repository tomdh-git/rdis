// Cross-reference index: every direct call/jmp target and every rip-relative data reference in the functions .pdata covers, as sorted (target, from) rva pairs.
// Built in parallel over the functions and cached on disk next to the build, keyed by the exe's size and timestamp.
use crate::pe::Pe;
use iced_x86::{Decoder, DecoderOptions, FlowControl, Instruction, OpKind};
use std::{fs, path::PathBuf, thread};

pub struct Xrefs {
    pub pairs: Vec<(u32, u32)>,
}

impl Xrefs {
    pub fn to(&self, target: u32) -> &[(u32, u32)] {
        let lo = self.pairs.partition_point(|p| p.0 < target);
        let hi = self.pairs.partition_point(|p| p.0 <= target);
        &self.pairs[lo..hi]
    }
}

fn cache_path(pe: &Pe, exe: &str) -> PathBuf {
    let stamp = (pe.data.len() as u64) ^ ((crate::pe::u32le(&pe.data, crate::pe::u32le(&pe.data, 0x3c) as usize + 8) as u64) << 32);
    let name = std::path::Path::new(exe).parent().and_then(|p| p.file_name()).map(|n| n.to_string_lossy().to_string()).unwrap_or_default();
    let mut dir = std::env::current_exe().unwrap_or_default();
    dir.pop();
    dir.push("rdis-cache");
    let _ = fs::create_dir_all(&dir);
    dir.push(format!("{}-{:x}.xr", name, stamp));
    dir
}

pub fn build(pe: &Pe, exe: &str) -> Xrefs {
    let path = cache_path(pe, exe);
    if let Ok(raw) = fs::read(&path) {
        let pairs = raw.chunks_exact(8).map(|c| (u32::from_le_bytes(c[0..4].try_into().unwrap()), u32::from_le_bytes(c[4..8].try_into().unwrap()))).collect();
        return Xrefs { pairs };
    }
    eprintln!("indexing {} functions (cached afterwards)...", pe.ranges.len());
    let threads = thread::available_parallelism().map_or(4, |n| n.get());
    let chunk = (pe.ranges.len() + threads - 1) / threads;
    let mut all: Vec<(u32, u32)> = vec![];
    thread::scope(|s| {
        let hs: Vec<_> = pe.ranges.chunks(chunk.max(1)).map(|rs| s.spawn(move || {
            let mut out = Vec::new();
            for r in rs {
                if !pe.is_exec(r.begin) { continue; }
                let bytes = pe.bytes(r.begin, (r.end - r.begin) as usize);
                let mut dec = Decoder::with_ip(64, bytes, r.begin as u64, DecoderOptions::NONE);
                let mut ins = Instruction::default();
                while dec.can_decode() {
                    dec.decode_out(&mut ins);
                    collect(&ins, &mut out);
                }
            }
            out
        })).collect();
        for h in hs { all.extend(h.join().unwrap()); }
    });
    all.sort_unstable();
    all.dedup();
    let mut raw = Vec::with_capacity(all.len() * 8);
    for p in &all { raw.extend_from_slice(&p.0.to_le_bytes()); raw.extend_from_slice(&p.1.to_le_bytes()); }
    let _ = fs::write(&path, raw);
    Xrefs { pairs: all }
}

fn collect(ins: &Instruction, out: &mut Vec<(u32, u32)>) {
    let from = ins.ip() as u32;
    match ins.flow_control() {
        FlowControl::Call | FlowControl::UnconditionalBranch if ins.op0_kind() == OpKind::NearBranch64 => {
            out.push((ins.near_branch_target() as u32, from));
            return;
        }
        _ => {}
    }
    if ins.is_ip_rel_memory_operand() {
        out.push((ins.ip_rel_memory_address() as u32, from));
    }
}
