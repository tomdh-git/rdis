// Minimal MCP server over stdio (newline-delimited JSON-RPC 2.0). One process keeps the exe, the xref index, the memoised analyses and the overlay db loaded.
// Every rdis command is a tool; its single argument `args` is the command line exactly as the CLI takes it.
use crate::Ctx;
use serde_json::{json, Value};
use std::io::{BufRead, Write};

const TOOLS: &[(&str, &str)] = &[
    ("info", "Image + overlay summary (counts of functions, vtables, component names, active facts)."),
    ("sum", "Symbolic summary of a function: calls (with args, vcall resolution + trust), field accesses by base expression, branch conditions, strings, ECS components. args: <fn> [--only calls|fields|raw|conds|strings|comps|rets] [--max N --offset N]"),
    ("cfg", "Basic blocks and edges with conditions, switches and unresolved indirect jumps. args: <fn>"),
    ("gates", "Necessary conditions to reach an instruction inside a function (exact over the CFG). args: <fn> <ip>"),
    ("path", "Call paths A->B with the gating conditions at every hop. args: <A> <B> [--virt none|derived|cand|slot] [--depth N] [--k N]"),
    ("reach", "Functions reachable from A. args: <A> [--virt ...] [--depth N]"),
    ("callers", "Functions that call/jump to an address. args: <addr>"),
    ("callees", "What a function calls + its strings. args: <addr>"),
    ("xr", "Every call/jmp/rip-relative reference to an address. args: <addr> [--max N]"),
    ("fn", "Annotated linear listing of a function. args: <addr> [--max N]"),
    ("dis", "Linear disassembly. args: <addr> [n]"),
    ("classes", "Discovered vtables/classes (RTTI is mostly stripped; identity = vtable). args: [filter] [--rtti]"),
    ("class", "One class: slot targets, constructor evidence, RTTI bases. args: <vtable-rva|name>"),
    ("vslot", "Who implements virtual slot N across all vtables. args: <slot> [--of class]"),
    ("vcalls", "Virtual calls of a function with their resolution. args: <fn>"),
    ("rw", "Readers/writers of a field offset. args: <off> [--comp Name | --class C | --fn F] [--w|--r] [--gates]"),
    ("struct", "Field table inferred from accesses. args: comp:<Name> | <class>"),
    ("system", "ECS components a function touches with field offsets. args: <fn>"),
    ("comps", "ECS type names found in the image with the number of functions using each hash. args: [filter]"),
    ("decide", "Decision points: where callers branch on this function's return value. args: <fn>"),
    ("needs", "What must be true to travel a whole call path A->B: gates of every hop grouped per function (never merged across frames), contradictions inside one function, unknown (?) counts. args: <A> <B> [--virt ...] [--k N]"),
    ("gobj", "Global object resolver: what class lives in a global slot, from its initialising stores (constructor on the allocation, vtable store). `--fn F [--depth N]` resolves every global behind an unresolved virtual call of F and callees; `--apply` records global-type facts so vcalls/path use them. args: <global> [--apply] | --fn <fn> [--depth N] [--apply]"),
    ("ptables", "Arrays of code pointers in data (handler/registry tables, strided records), excluding vtables. args: [--min N] [--ref <fn>] [--max N]"),
    ("structm", "One field table merged across the call tree that passes `this` (a0 or a0+K) by direct calls, with type guesses and child objects. args: <fn> [--depth N]"),
    ("worklist", "Subsystem worklist from seed functions: reachable functions, named/unnamed, string anchors, unresolved virtual calls (the measurable remaining work). args: <fn> [<fn>...] [--depth N] [--maxfan N]"),
    ("observe", "Record runtime observations (trust `observed`, outranks static inference). args: vcall <site> <target[,..]> [--count N] | global <global> <vtable|Class> | import <file.json>"),
    ("portfacts", "Look up every named function of this build in another exe (uses port). args: <other-exe> [--limit N]"),
    ("port", "Cross-build match: find this exe's function in ANOTHER exe by strings, type hashes, immediates, then verify (string-set jaccard, size, vcall slots, callee counts). Never above candidate/derived. args: <other-exe> <fn> [--top N]"),
    ("abi", "Hint: which register args are used, hidden return pointer (sret) guess. args: <fn>"),
    ("sigcheck", "Lint a byte signature (length, wildcards, CC, rel32 displacements) and count exact matches in this exe. args: <sig>"),
    ("mksig", "Create a unique byte signature for a function: disassembles from the start, wildcards rip-relative and call/jmp displacements, extends until unique. args: <fn> [--max N] [--kind fn|call|vindex|offset|global] [--tier core|feature|cosmetic] [--mask OFF:VALUE:MASK] [--alt [SNIPPET]] [--vindex N]"),
    ("hookpoints", "Ranked hook candidates between A and B: chokepoints + target, by unique prologue, size, fan-in. args: <A> <B> [--virt ...]"),
    ("flow", "Interprocedural value flow: follow an argument (or a field read) through callees that receive it unchanged; reports compared/masked/indexed/stored/dereferenced uses. args: <fn> <arg 0-3> | <fn> --field <off> [--depth N]"),
    ("contradict", "Hypothesis check for a field: list every reader that violates the belief and the writers. args: <off> --class C | --fn F --as compare-only|not-indexed|not-stored"),
    ("choke", "Call-graph chokepoints between A and B (functions on every path). args: <A> <B> [--virt ...]"),
    ("common", "Nearest common callers of two functions (where a producer and consumer meet). args: <A> <B> [--depth N]"),
    ("uses", "Usage profile of a field value: compared/masked/indexed/passed/stored (carrier discovery). args: <off> --class C | --fn F"),
    ("anchors", "Anchors for re-finding a function: unique strings, low-fan-in callees, type hashes, installed vtables. args: <fn>"),
    ("comp", "Functions using an ECS component type hash. args: <TypeName>"),
    ("str", "Find strings (ascii+utf16) and their referencing functions. args: <text> [-i] [--max N]"),
    ("fld", "Instructions touching [reg+disp]. args: <disp> [--base rcx] [--r|--w]"),
    ("imm", "Instructions with an immediate. args: <hex>"),
    ("ptr", "Where an address is stored as a pointer in data. args: <addr>"),
    ("vt", "Raw vtable slots. args: <addr> [n]"),
    ("find", "Byte-signature search. args: <sig>"),
    ("assert", "Add a belief to the overlay db. args: <kind> <subject> <value...> [--trust t] [--ev bytes:..,call:..,str:..,ptr:..,fn:..] [--note text] [--supersede id]. kinds: name class comment edge field component note"),
    ("retract", "Withdraw a belief. args: <fact id>"),
    ("contest", "Mark a derived fact as wrong. args: <key e.g. edge:0xSITE->0xTARGET> [--note]"),
    ("facts", "List active overlay facts. args: [kind]"),
    ("why", "Evidence chain and history for an address/key. args: <addr|key>"),
    ("audit", "Re-check every active fact's evidence against the binary."),
    ("bench", "Speed benchmark: PE load, xref index, vtable discovery, sum timing. Reports wall time per phase."),
];

fn text(v: Value) -> Value { json!({"content": [{"type": "text", "text": v}], "isError": false}) }

pub fn serve(ctx: &mut Ctx) {
    let stdin = std::io::stdin();
    let mut out = std::io::stdout();
    for line in stdin.lock().lines() {
        let line = match line { Ok(l) => l, Err(_) => break };
        if line.trim().is_empty() { continue; }
        let req: Value = match serde_json::from_str(&line) { Ok(v) => v, Err(_) => { let _ = writeln!(out, "{}", json!({"jsonrpc": "2.0", "id": null, "error": {"code": -32700, "message": "parse error"}})); let _ = out.flush(); continue; } };
        let id = req.get("id").cloned();
        let method = req["method"].as_str().unwrap_or("");
        let params = &req["params"];
        let result: Option<Value> = match method {
            "initialize" => Some(json!({"protocolVersion": params["protocolVersion"].as_str().unwrap_or("2024-11-05"), "capabilities": {"tools": {}},
                "serverInfo": {"name": "rdis", "version": "2.0"},
                "instructions": "Binary analysis of the game exe. Every claim has a trust level: proven > derived > candidate > hint > agent > unknown. Prefer `sum`, `path`, `gates`, `rw`, `struct` for relationships; use `assert`/`contest`/`retract` to record or revise beliefs (they invalidate caches and later answers use them); `audit` re-verifies them."})),
            "tools/list" => Some(json!({"tools": TOOLS.iter().map(|(n, d)| json!({"name": n, "description": d, "inputSchema": {"type": "object", "properties": {"args": {"type": "string", "description": "command-line arguments"}}}})).chain(std::iter::once(json!({"name": "batch", "description": "Run several commands in one call (each a full command line).", "inputSchema": {"type": "object", "properties": {"commands": {"type": "array", "items": {"type": "string"}}}, "required": ["commands"]}}))).collect::<Vec<_>>()})),
            "tools/call" => {
                let name = params["name"].as_str().unwrap_or("");
                let lines: Vec<String> = if name == "batch" { params["arguments"]["commands"].as_array().map(|a| a.iter().filter_map(|x| x.as_str().map(|s| s.to_string())).collect()).unwrap_or_default() }
                    else { vec![format!("{} {}", name, params["arguments"]["args"].as_str().unwrap_or(""))] };
                let mut res = String::new();
                for l in &lines {
                    let o = crate::capture(|| { let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| crate::run(ctx, l.trim()))); if r.is_err() { crate::emit("{\"error\":\"internal panic while running the command\"}"); } });
                    if lines.len() > 1 { res.push_str(&format!("> {}\n", l)); }
                    res.push_str(&o);
                }
                let is_err = lines.len() == 1 && res.trim_start().starts_with("{\"error\"");
                Some(json!({"content": [{"type": "text", "text": res}], "isError": is_err}))
            }
            "ping" => Some(json!({})),
            _ => None,
        };
        let _ = text;
        if let (Some(id), Some(r)) = (id.clone(), result) {
            let _ = writeln!(out, "{}", json!({"jsonrpc": "2.0", "id": id, "result": r}));
            let _ = out.flush();
        } else if let Some(id) = id {
            let _ = writeln!(out, "{}", json!({"jsonrpc": "2.0", "id": id, "error": {"code": -32601, "message": "method not found"}}));
            let _ = out.flush();
        }
    }
}
