// PE image: sections, the .pdata function table (with chained unwind fragments resolved to their primary function), string reads, and the import/export directories.
use std::fs;

pub struct Section {
    pub name: String,
    pub rva: u32,
    pub vsize: u32,
    pub raw: u32,
    pub rawsize: u32,
    pub flags: u32,
}

#[derive(Clone, Debug)]
pub struct Import {
    pub dll: String,
    pub hint: u16,
    pub name: Option<String>,
    pub iat_rva: u32,
    pub iat_value: u64,
}

#[derive(Clone, Debug)]
pub struct Export {
    pub name: String,
    pub rva: u32,
    pub ordinal: u16,
    pub forwarder: Option<String>,
}

// One RUNTIME_FUNCTION entry. `root` is the begin of the primary function this range belongs to (itself unless it is a chained fragment).
#[derive(Clone, Copy)]
pub struct Range {
    pub begin: u32,
    pub end: u32,
    pub root: u32,
}

pub struct Pe {
    pub data: Vec<u8>,
    pub sections: Vec<Section>,
    pub ranges: Vec<Range>, // sorted by begin
    pub imports: Vec<Import>,
    pub exports: Vec<Export>,
}

pub fn u16le(d: &[u8], o: usize) -> u32 { u16::from_le_bytes([d[o], d[o + 1]]) as u32 }
pub fn u32le(d: &[u8], o: usize) -> u32 { u32::from_le_bytes([d[o], d[o + 1], d[o + 2], d[o + 3]]) }

impl Pe {
    pub fn load(path: &str) -> Pe {
        let data = fs::read(path).expect("read exe");
        let pe = u32le(&data, 0x3c) as usize;
        let n = u16le(&data, pe + 6) as usize;
        let opt = u16le(&data, pe + 20) as usize;
        let mut sections = vec![];
        for i in 0..n {
            let s = pe + 24 + opt + i * 40;
            let name = String::from_utf8_lossy(&data[s..s + 8]).trim_end_matches('\0').to_string();
            sections.push(Section { name, rva: u32le(&data, s + 12), vsize: u32le(&data, s + 8), raw: u32le(&data, s + 20), rawsize: u32le(&data, s + 16), flags: u32le(&data, s + 36) });
        }
        let mut p = Pe { data, sections, ranges: vec![], imports: vec![], exports: vec![] };
        let exc = pe + 24 + 0x70 + 3 * 8; // data directory 3: exception table
        let (rva, size) = (u32le(&p.data, exc), u32le(&p.data, exc + 4));
        p.read_pdata(rva, size);
        p.read_imports();
        p.read_exports();
        p
    }

    // ---- import directory (data directory index 1) ----
    fn read_imports(&mut self) {
        let dd = self.data_directory(1);
        let Some((rva, size)) = dd else { return };
        if size == 0 { return; }
        let base = match self.off(rva) { Some(o) => o, None => return };
        let mut i = 0usize;
        loop {
            let o = base + i * 20;
            if o + 20 > self.data.len() { break; }
            let ilt_rva = u32le(&self.data, o);
            if ilt_rva == 0 { break; } // NULL terminator
            let dll_rva = u32le(&self.data, o + 12);
            let iat_rva = u32le(&self.data, o + 16);
            let dll = match self.cstr(dll_rva) { Some(s) => s, None => { i += 1; continue; } };
            let ilt_base = match self.off(ilt_rva) { Some(o) => o, None => { i += 1; continue; } };
            let iat_base = match self.off(iat_rva) { Some(o) => o, None => { i += 1; continue; } };
            let mut j = 0usize;
            loop {
                let eo = ilt_base + j * 8;
                if eo + 8 > self.data.len() { break; }
                let ilt_val = u64::from_le_bytes(self.data[eo..eo + 8].try_into().unwrap());
                if ilt_val == 0 { break; }
                let io_o = iat_base + j * 8;
                let iat_val = if io_o + 8 <= self.data.len() { u64::from_le_bytes(self.data[io_o..io_o + 8].try_into().unwrap()) } else { 0 };
                let (hint, name) = if ilt_val & 0x8000_0000_0000_0000 != 0 {
                    (ilt_val as u16, None) // import by ordinal
                } else {
                    let hno_base = match self.off(ilt_val as u32) { Some(o) => o, None => { j += 1; continue; } };
                    if hno_base + 2 > self.data.len() { j += 1; continue; }
                    let h = u16::from_le_bytes([self.data[hno_base], self.data[hno_base + 1]]);
                    let nm = self.cstr(ilt_val as u32 + 2);
                    (h, nm)
                };
                self.imports.push(Import { dll: dll.clone(), hint, name, iat_rva: iat_rva + (j as u32) * 8, iat_value: iat_val });
                j += 1;
            }
            i += 1;
        }
        let _ = size;
    }

    // ---- export directory (data directory index 0) ----
    fn read_exports(&mut self) {
        let dd = self.data_directory(0);
        let Some((rva, size)) = dd else { return };
        if size == 0 { return; }
        let base = match self.off(rva) { Some(o) => o, None => return };
        let _name_rva = u32le(&self.data, base + 12);
        let num_names = u32le(&self.data, base + 24) as usize;
        let addr_of_names = u32le(&self.data, base + 32);
        let addr_of_name_ordinals = u32le(&self.data, base + 36);
        let addr_of_functions = u32le(&self.data, base + 28);
        let names_base = match self.off(addr_of_names) { Some(o) => o, None => return };
        let ords_base = match self.off(addr_of_name_ordinals) { Some(o) => o, None => return };
        let funcs_base = match self.off(addr_of_functions) { Some(o) => o, None => return };
        for n in 0..num_names {
            let no = names_base + n * 4;
            if no + 4 > self.data.len() { break; }
            let name_rva = u32le(&self.data, no) as u32;
            let name = match self.cstr(name_rva) { Some(s) => s, None => continue };
            let ord_o = ords_base + n * 2;
            if ord_o + 2 > self.data.len() { continue; }
            let ord = u16le(&self.data, ord_o) as usize;
            let fo = funcs_base + ord * 4;
            if fo + 4 > self.data.len() { continue; }
            let func_rva = u32le(&self.data, fo);
            let forwarder = if func_rva >= rva && func_rva < rva + size {
                self.cstr(func_rva)
            } else { None };
            self.exports.push(Export { name, rva: func_rva, ordinal: ord as u16, forwarder });
        }
    }

    fn data_directory(&self, index: usize) -> Option<(u32, u32)> {
        let pe = u32le(&self.data, 0x3c) as usize;
        let opt = u16le(&self.data, pe + 20) as usize;
        let dd = pe + 24 + opt + 96 + index * 8;
        if dd + 8 > self.data.len() { return None; }
        let (rva, size) = (u32le(&self.data, dd), u32le(&self.data, dd + 4));
        if rva == 0 && size == 0 { return None; }
        Some((rva, size))
    }

    // NUL-terminated ASCII string at rva, or None if not resolvable.
    fn cstr(&self, rva: u32) -> Option<String> {
        let o = self.off(rva)?;
        let mut end = o;
        while end < self.data.len() && self.data[end] != 0 { end += 1; }
        if end == o { return None; }
        String::from_utf8(self.data[o..end].to_vec()).ok()
    }

    // ---- public query API ----

    pub fn imports_for(&self, dll: &str) -> Vec<&Import> {
        self.imports.iter().filter(|i| i.dll.eq_ignore_ascii_case(dll)).collect()
    }

    pub fn import_by_name(&self, dll: &str, name: &str) -> Option<&Import> {
        self.imports.iter().find(|i| i.dll.eq_ignore_ascii_case(dll) && i.name.as_deref() == Some(name))
    }

    pub fn export_by_name(&self, name: &str) -> Option<&Export> {
        self.exports.iter().find(|e| e.name == name)
    }

    /// Scan executable sections for `call qword ptr [iat_rva]` where the IAT entry corresponds to this import.
    /// Returns call-site RVAs.
    pub fn find_import_callers(&self, dll: &str, name: &str) -> Vec<u32> {
        let imp = match self.import_by_name(dll, name) { Some(i) => i, None => return vec![] };
        let mut out = vec![];
        for s in &self.sections {
            if s.flags & 0x2000_0000 == 0 { continue; }
            let d = &self.data[s.raw as usize..(s.raw + s.rawsize.min(s.vsize)) as usize];
            let mut i = 0usize;
            while i + 6 <= d.len() {
                // FF 15 <disp32>  -> call qword ptr [rip + disp32]
                if d[i] == 0xFF && d[i + 1] == 0x15 {
                    let disp = i32::from_le_bytes([d[i + 2], d[i + 3], d[i + 4], d[i + 5]]) as i64;
                    let target_rva = (s.rva + i as u32 + 6).wrapping_add(disp as u32);
                    if target_rva == imp.iat_rva {
                        out.push(s.rva + i as u32);
                    }
                    i += 6;
                } else {
                    i += 1;
                }
            }
        }
        out
    }

    /// Scan executable sections for `call <export_rva>` direct calls to the export's RVA.
    pub fn find_export_callers(&self, name: &str) -> Vec<u32> {
        let exp = match self.export_by_name(name) { Some(e) => e, None => return vec![] };
        let mut out = vec![];
        for s in &self.sections {
            if s.flags & 0x2000_0000 == 0 { continue; }
            let d = &self.data[s.raw as usize..(s.raw + s.rawsize.min(s.vsize)) as usize];
            let mut i = 0usize;
            while i + 5 <= d.len() {
                // E8 <rel32> -> call rel32
                if d[i] == 0xE8 {
                    let rel = i32::from_le_bytes([d[i + 1], d[i + 2], d[i + 3], d[i + 4]]) as i64;
                    let target_rva = (s.rva + i as u32 + 5).wrapping_add(rel as u32);
                    if target_rva == exp.rva {
                        out.push(s.rva + i as u32);
                    }
                    i += 5;
                } else {
                    i += 1;
                }
            }
        }
        out
    }

    fn read_pdata(&mut self, rva: u32, size: u32) {
        let base = match self.off(rva) { Some(o) => o, None => return };
        let count = (size / 12) as usize;
        let mut raw = Vec::with_capacity(count);
        for i in 0..count {
            let o = base + i * 12;
            raw.push((u32le(&self.data, o), u32le(&self.data, o + 4), u32le(&self.data, o + 8)));
        }
        raw.sort_unstable();
        for &(b, e, u) in &raw {
            let root = self.chain_parent(u).unwrap_or(b);
            self.ranges.push(Range { begin: b, end: e, root });
        }
        // a fragment chains to the RUNTIME_FUNCTION of its parent, which may itself be a fragment
        for _ in 0..4 {
            let snapshot: Vec<Range> = self.ranges.clone();
            for r in self.ranges.iter_mut() {
                if r.root != r.begin {
                    if let Ok(i) = snapshot.binary_search_by(|x| x.begin.cmp(&r.root)) {
                        r.root = snapshot[i].root;
                    }
                }
            }
        }
    }

    // The begin of the parent function when the unwind info at `unwind` is a chain (flag 0x4), else None.
    fn chain_parent(&self, unwind: u32) -> Option<u32> {
        let o = self.off(unwind & !1)?;
        let flags = self.data[o] >> 3;
        if flags & 4 == 0 { return None; }
        let codes = self.data[o + 2] as usize;
        let at = o + 4 + ((codes * 2 + 3) & !3);
        Some(u32le(&self.data, at))
    }

    pub fn off(&self, rva: u32) -> Option<usize> {
        for s in &self.sections {
            if rva >= s.rva && rva < s.rva + s.vsize.max(s.rawsize) {
                let d = rva - s.rva;
                if d >= s.rawsize { return None; }
                return Some((s.raw + d) as usize);
            }
        }
        None
    }

    pub fn section_of(&self, rva: u32) -> Option<&Section> {
        self.sections.iter().find(|s| rva >= s.rva && rva < s.rva + s.vsize.max(s.rawsize))
    }

    pub fn is_exec(&self, rva: u32) -> bool {
        self.section_of(rva).map_or(false, |s| s.flags & 0x2000_0000 != 0)
    }

    /// Bytes at rva, truncated at section end. Returns empty slice when the RVA can't be resolved — callers that need to distinguish
    /// "no data" from "invalid address" should use `bytes_opt` instead.
    pub fn bytes(&self, rva: u32, len: usize) -> &[u8] {
        match self.off(rva) {
            Some(o) => &self.data[o..(o + len).min(self.data.len())],
            None => &[],
        }
    }

    /// Bytes at rva as `Option<&[u8]>`. None when the RVA cannot be resolved to a file offset, so callers never mistake
    /// an invalid address for "zero-length data".
    pub fn bytes_opt(&self, rva: u32, len: usize) -> Option<&[u8]> {
        let o = self.off(rva)?;
        Some(&self.data[o..(o + len).min(self.data.len())])
    }

    pub fn u64_at(&self, rva: u32) -> Option<u64> {
        let b = self.bytes(rva, 8);
        if b.len() < 8 { None } else { Some(u64::from_le_bytes(b.try_into().unwrap())) }
    }

    // The range containing rva, if any.
    pub fn range_of(&self, rva: u32) -> Option<Range> {
        let i = match self.ranges.binary_search_by(|r| r.begin.cmp(&rva)) { Ok(i) => i, Err(0) => return None, Err(i) => i - 1 };
        let r = self.ranges[i];
        if rva < r.end { Some(r) } else { None }
    }

    // The primary function containing rva: its [begin, end) of the main body, or None when .pdata does not cover it.
    pub fn function_of(&self, rva: u32) -> Option<(u32, u32)> {
        let r = self.range_of(rva)?;
        let i = self.ranges.binary_search_by(|x| x.begin.cmp(&r.root)).ok()?;
        Some((self.ranges[i].begin, self.ranges[i].end))
    }

    pub fn fragments_of(&self, root: u32) -> Vec<(u32, u32)> {
        self.ranges.iter().filter(|r| r.root == root && r.begin != root).map(|r| (r.begin, r.end)).collect()
    }

    pub fn is_function_start(&self, rva: u32) -> bool {
        self.ranges.binary_search_by(|r| r.begin.cmp(&rva)).map_or(false, |i| self.ranges[i].root == rva)
    }

    // A printable ascii (>= 4 chars) or utf-16 string at rva, shortened to 60 chars.
    pub fn string_at(&self, rva: u32) -> Option<String> {
        let b = self.bytes(rva, 160);
        if b.len() < 8 { return None; }
        let sec = self.section_of(rva)?;
        if sec.flags & 0x2000_0000 != 0 { return None; }
        let a: Vec<u8> = b.iter().copied().take_while(|c| (0x20..0x7f).contains(c)).collect();
        if a.len() >= 4 && b.get(a.len()) == Some(&0) {
            return Some(clip(String::from_utf8_lossy(&a).to_string()));
        }
        let mut w = String::new();
        for p in b.chunks_exact(2) {
            let c = u16::from_le_bytes([p[0], p[1]]);
            if (0x20..0x7f).contains(&c) { w.push(c as u8 as char); } else { break; }
        }
        if w.len() >= 4 && b.len() >= w.len() * 2 + 2 && b[w.len() * 2] == 0 && b[w.len() * 2 + 1] == 0 {
            return Some(format!("L{}", clip(w)));
        }
        None
    }
}

fn clip(mut s: String) -> String {
    if s.len() > 60 { s.truncate(60); s.push_str("..."); }
    s
}
