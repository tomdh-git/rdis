// The revisable belief store: SQLite-backed journal of assertions / retractions / contests layered over the deterministic derived analysis.
//
// Table `facts` (see schema below). The file path is still `<ver>.facts.jsonl` but it is now a SQLite database.
// An old JSONL journal found at this path is imported on first open and kept as <name>.legacy.
use crate::Ctx;
use rusqlite::{params, Connection};
use serde_json::{json, Value};
use std::collections::HashSet;
use std::path::PathBuf;

const SCHEMA: &str = "
CREATE TABLE IF NOT EXISTS facts (
    id INTEGER PRIMARY KEY,
    ts INTEGER NOT NULL,
    op TEXT NOT NULL,
    kind TEXT NOT NULL,
    subject TEXT NOT NULL,
    value TEXT NOT NULL,
    trust TEXT NOT NULL,
    source TEXT NOT NULL,
    note TEXT NOT NULL DEFAULT '',
    target INTEGER,
    evidence TEXT NOT NULL DEFAULT '[]'
);
CREATE INDEX IF NOT EXISTS idx_facts_kind_subject ON facts(kind, subject);
CREATE INDEX IF NOT EXISTS idx_facts_trust ON facts(trust);
CREATE INDEX IF NOT EXISTS idx_facts_source ON facts(source);
CREATE INDEX IF NOT EXISTS idx_facts_subject ON facts(subject);
CREATE INDEX IF NOT EXISTS idx_facts_op ON facts(op);
";

#[derive(Clone, Debug)]
pub struct Fact {
    pub id: u64,
    pub ts: u64,
    pub op: String,
    pub kind: String,
    pub subject: String,
    pub value: Value,
    pub trust: String,
    pub source: String,
    pub evidence: Vec<String>,
    pub note: String,
    pub target: Option<u64>,
}

impl Fact {
    pub fn to_json(&self) -> Value {
        json!({"id": self.id, "ts": self.ts, "op": self.op, "kind": self.kind, "subject": self.subject, "value": self.value, "trust": self.trust, "source": self.source, "evidence": self.evidence, "note": self.note, "target": self.target})
    }
    pub(crate) fn from_row(row: &rusqlite::Row) -> rusqlite::Result<Fact> {
        let value: String = row.get(5)?;
        let evidence: String = row.get(10).unwrap_or_default();
        Ok(Fact {
            id: row.get(0)?,
            ts: row.get(1)?,
            op: row.get(2)?,
            kind: row.get(3)?,
            subject: row.get(4)?,
            value: serde_json::from_str(&value).unwrap_or(Value::Null),
            trust: row.get(6)?,
            source: row.get(7)?,
            evidence: serde_json::from_str(&evidence).unwrap_or_default(),
            note: row.get(8)?,
            target: row.get::<_, Option<i64>>(9)?.map(|t| t as u64),
        })
    }
}

pub fn addr_key(rva: u32) -> String { format!("{:#x}", rva) }

pub struct Db {
    pub path: PathBuf,
    pub conn: Connection,
    pub epoch: u64,
}

impl Db {
    pub fn load(path: PathBuf) -> Result<Db, rusqlite::Error> {
        // A file written by the old append-only JSONL journal is converted once (the original is kept as <name>.legacy).
        let mut legacy: Option<Vec<u8>> = None;
        if let Ok(b) = std::fs::read(&path) {
            if !b.is_empty() && !b.starts_with(b"SQLite format 3\0") {
                std::fs::rename(&path, path.with_extension("jsonl.legacy")).expect("move legacy journal aside");
                legacy = Some(b);
            }
        }
        let conn = Connection::open(&path)?;
        conn.execute_batch(SCHEMA)?;
        let mut db = Db { path, conn, epoch: 0 };
        if let Some(b) = legacy {
            for line in String::from_utf8_lossy(&b).lines().filter(|l| !l.trim().is_empty()) {
                let j: Value = serde_json::from_str(line).expect("legacy journal line is not JSON");
                let sv = |k: &str| j[k].as_str().unwrap_or("").to_string();
                let f = Fact { id: j["id"].as_u64().unwrap_or(0), ts: j["ts"].as_u64().unwrap_or(0), op: sv("op"), kind: sv("kind"), subject: sv("subject"), value: j["value"].clone(), trust: sv("trust"), source: sv("source"),
                    evidence: j["evidence"].as_array().map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect()).unwrap_or_default(), note: sv("note"), target: j["target"].as_u64() };
                db.insert_row(&f);
            }
        }
        db.epoch = db.conn.query_row("SELECT COUNT(*) FROM facts", [], |r| r.get(0))?;
        Ok(db)
    }

    fn insert_row(&self, f: &Fact) {
        self.conn.execute(
            "INSERT INTO facts (id, ts, op, kind, subject, value, trust, source, note, target, evidence) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11)",
            params![f.id, f.ts, f.op, f.kind, f.subject, serde_json::to_string(&f.value).unwrap(), f.trust, f.source, f.note, f.target.map(|t| t as i64), serde_json::to_string(&f.evidence).unwrap()],
        ).expect("insert fact");
    }

    pub fn append(&mut self, mut f: Fact) -> u64 {
        let id = {
            let max: Option<u64> = self.conn.query_row("SELECT MAX(id) FROM facts", [], |r| r.get(0)).expect("read max fact id");
            max.unwrap_or(0) + 1
        };
        f.id = id;
        f.ts = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs());
        self.insert_row(&f);
        self.epoch += 1;
        id
    }

    fn dead(&self) -> HashSet<u64> {
        let mut d = HashSet::new();
        let ok = self.conn.prepare("SELECT target FROM facts WHERE (op = 'retract' OR op = 'assert') AND target IS NOT NULL");
        if let Ok(mut stmt) = ok {
            let rows = stmt.query_map([], |r| r.get::<_, i64>(0).map(|t| t as u64));
            if let Ok(rows) = rows {
                for r in rows.flatten() { d.insert(r); }
            }
        }
        d
    }

    // active assertions and contests
    pub fn active(&self) -> Vec<Fact> {
        let d = self.dead();
        let mut out = vec![];
        if let Ok(mut stmt) = self.conn.prepare("SELECT * FROM facts WHERE (op = 'assert' OR op = 'contest') ORDER BY id") {
            if let Ok(rows) = stmt.query_map([], |r| Fact::from_row(r)) {
                for r in rows.flatten() { if !d.contains(&r.id) { out.push(r); } }
            }
        }
        out
    }

    pub fn contested(&self, key: &str) -> bool {
        self.conn.prepare("SELECT 1 FROM facts WHERE op = 'contest' AND subject = ?1")
            .and_then(|mut stmt| stmt.query_row(params![key], |_| Ok(())))
            .is_ok()
    }

    pub fn find(&self, kind: &str, subject: &str) -> Option<Fact> {
        let d = self.dead();
        let mut stmt = match self.conn.prepare("SELECT * FROM facts WHERE op = 'assert' AND kind = ?1 AND subject = ?2 ORDER BY id DESC LIMIT 1") {
            Ok(s) => s,
            Err(_) => return None,
        };
        let rows = stmt.query_map(params![kind, subject], |r| Fact::from_row(r));
        match rows {
            Ok(mut rows) => match rows.next() {
                Some(Ok(f)) if !d.contains(&f.id) => Some(f),
                _ => None,
            },
            Err(_) => None,
        }
    }

    // everything ever said about a subject, oldest first, with its status
    pub fn history(&self, subject: &str) -> Vec<Value> {
        let d = self.dead();
        let mut out = vec![];
        if let Ok(mut stmt) = self.conn.prepare("SELECT * FROM facts WHERE subject = ?1 ORDER BY id") {
            if let Ok(rows) = stmt.query_map(params![subject], |r| Fact::from_row(r)) {
                for r in rows.flatten() {
                    let mut j = r.to_json();
                    j["status"] = json!(if d.contains(&r.id) { "superseded/retracted" } else { "active" });
                    out.push(j);
                }
            }
        }
        out
    }
}

// Re-check one evidence item against the image. Grammar: bytes:<rva>:<hex> | str:<rva>:<text> | call:<from>-><to> | ptr:<slot>-><target> | fn:<rva> | note:<free text>
pub fn check_evidence(ctx: &Ctx, ev: &str) -> (&'static str, String) {
    let (k, rest) = match ev.split_once(':') { Some(x) => x, None => return ("unchecked", ev.to_string()) };
    let hexv = |s: &str| u32::from_str_radix(s.trim_start_matches("0x"), 16).ok();
    match k {
        "bytes" => {
            let (a, h) = match rest.split_once(':') { Some(x) => x, None => return ("bad", "bytes:<rva>:<hex>".into()) };
            let (a, want) = match (hexv(a), (0..h.len() / 2).map(|i| u8::from_str_radix(&h[2 * i..2 * i + 2], 16).ok()).collect::<Option<Vec<u8>>>()) { (Some(a), Some(w)) => (a, w), _ => return ("bad", "unparsable".into()) };
            let have = ctx.pe.bytes(a, want.len());
            if have == &want[..] { ("holds", String::new()) } else { ("BROKEN", format!("bytes now {}", have.iter().map(|b| format!("{:02x}", b)).collect::<String>())) }
        }
        "str" => {
            let (a, t) = match rest.split_once(':') { Some(x) => x, None => return ("bad", "str:<rva>:<text>".into()) };
            match hexv(a).and_then(|a| ctx.pe.string_at(a)) { Some(s) if s.contains(t) || s.trim_start_matches('L').starts_with(t) => ("holds", String::new()), other => ("BROKEN", format!("string now {:?}", other)) }
        }
        "call" => {
            let (f, t) = match rest.split_once("->") { Some(x) => x, None => return ("bad", "call:<from>-><to>".into()) };
            let (f, t) = match (hexv(f), hexv(t)) { (Some(f), Some(t)) => (f, t), _ => return ("bad", "unparsable".into()) };
            let b = ctx.pe.bytes(f, 15);
            let mut dec = iced_x86::Decoder::with_ip(64, b, f as u64, iced_x86::DecoderOptions::NONE);
            if !dec.can_decode() { return ("BROKEN", "cannot decode".into()); }
            let i = dec.decode();
            if i.op0_kind() == iced_x86::OpKind::NearBranch64 && i.near_branch_target() as u32 == t { ("holds", String::new()) } else { ("BROKEN", "no longer a branch to the target".into()) }
        }
        "ptr" => {
            let (s, t) = match rest.split_once("->") { Some(x) => x, None => return ("bad", "ptr:<slot>-><target>".into()) };
            let (s, t) = match (hexv(s), hexv(t)) { (Some(s), Some(t)) => (s, t), _ => return ("bad", "unparsable".into()) };
            match ctx.pe.u64_at(s) { Some(v) if v == ctx.image_base + t as u64 => ("holds", String::new()), v => ("BROKEN", format!("slot now {:?}", v)) }
        }
        "fn" => match hexv(rest) { Some(a) if ctx.pe.is_function_start(a) => ("holds", String::new()), _ => ("BROKEN", "not a .pdata function start".into()) },
        _ => ("unchecked", ev.to_string()),
    }
}
