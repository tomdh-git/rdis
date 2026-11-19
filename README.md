# rdis

> High-performance x86_64 PE static analysis, control-flow disassembly, and reverse-engineering engine tailored for large Windows executables.

`rdis` is built in Rust using `iced-x86` and bundled SQLite. It is engineered to analyze massive game binaries (such as *Minecraft: Bedrock Edition* / `Minecraft.Windows.exe`) orders of magnitude faster than conventional disassemblers—performing in milliseconds what typically takes minutes in IDA or Ghidra.

---

## Features

- **Blazing Fast Startup & Indexing**: Sub-second PE headers, section table, exception directory (`.pdata`), and cross-reference indexing.
- **Control-Flow Analysis**:
  - `walk` — Follows straight-line code, branches, unconditional jumps, and function call continuations.
  - `fn` — Annotated function view with labels, resolved callee names, strings, vcall slots, and argument pointer chains (`a0`, `a1`, etc.).
  - `dis` — Linear instruction disassembly.
- **Cross-References & Call Graphs**:
  - `xr` — Instant RIP-relative references, call sites, and jump targets.
  - `callers` & `callees` — Immediate upstream and downstream call hierarchy analysis.
  - `str` — ASCII and UTF-16 string cross-reference search.
- **Game Engine & Struct Specialization**:
  - `fld` & `rw` — Finds instructions touching specific struct field displacements (e.g. `[rcx + 0x58]`).
  - `imm` — Scans for immediate values and 32-bit/64-bit constants.
  - `comp` — Locates users of ECS component types hashed via FNV-1a (e.g. `ActorRotationComponent`).
  - `vt`, `vcalls`, `vslot` — Virtual method table reconstruction, slot resolution, and virtual dispatch analysis.
- **Overlay Knowledge Graph (SQLite Persistence)**:
  - `assert` — Record verified facts (names, classes, fields, edges) into an overlay database.
  - `retract` / `contest` — Withdraw or challenge hypotheses.
  - `facts` / `why` — Inspect the provenance chain and evidence supporting any address.
  - `audit` — Verifies every asserted fact against the binary bytes and instructions.
- **AI & Automation Ready**:
  - `--mcp` — Built-in Model Context Protocol server for seamless LLM tool integration.
  - Consistent JSON output on stdout for automated pipelines and subagents.

---

## Installation & Building

### Prerequisites
- [Rust](https://rustup.rs/) (edition 2021, stable channel)
- C/C++ build tools (for compiling bundled `libsqlite3-sys`)

### Build Release Binary
```bash
cargo build --release
```
The optimized executable will be generated at `target/release/rdis.exe`.

---

## Usage

Basic command syntax:
```bash
rdis <target_exe> <command> [args...]
```

Execute multiple commands in a single session:
```bash
rdis <target_exe> -c "info; sec; classes; surprises --max 10"
```

Start the MCP server:
```bash
rdis <target_exe> --mcp
```

### Core Commands Reference

| Command | Syntax | Description |
| :--- | :--- | :--- |
| **`help` / `?`** | `rdis <exe> help` | Display full command list and syntax. |
| **`info`** | `rdis <exe> info` | Emit PE headers, image base, entry point, and `.pdata` function count in JSON. |
| **`sec`** | `rdis <exe> sec` | List all PE sections, virtual addresses, raw sizes, and characteristics. |
| **`fn`** | `rdis <exe> fn <addr> [--max N] [--nochains]` | Disassemble and annotate a function with argument chains, vcalls, strings, and labels. |
| **`dis`** | `rdis <exe> dis <addr> [n]` | Linear disassembly of `n` instructions (default 40). |
| **`walk`** | `rdis <exe> walk <addr> [--reg R]` | Follow CFG paths from address across branches until ret/indirect jmp. |
| **`xr`** | `rdis <exe> xr <addr> [--max N]` | Find all calls, jumps, and RIP-relative memory reads touching `<addr>`. |
| **`callers`** | `rdis <exe> callers <addr>` | List all functions calling or jumping to `<addr>`. |
| **`callees`** | `rdis <exe> callees <addr>` | List all functions and string literals referenced by `<addr>`. |
| **`str`** | `rdis <exe> str <query> [-i] [--max N]` | Search ASCII and UTF-16 string literals and print their referencing functions. |
| **`fld`** | `rdis <exe> fld <disp> [--base reg] [--r\|--w]` | Find instructions accessing `[reg + disp]` (e.g. `[rcx + 0x10]`). |
| **`imm`** | `rdis <exe> imm <value>` | Find instructions with a specific immediate (e.g. ECS component hashes). |
| **`comp`** | `rdis <exe> comp <TypeName>` | Find functions querying or using a given ECS component type. |
| **`vt`** | `rdis <exe> vt <addr> [n]` | Inspect virtual method table slots and targets. |
| **`find`** | `rdis <exe> find <byte_signature>` | Scan binary for a byte pattern with wildcards (`?` or `??`). |
| **`assert`** | `rdis <exe> assert <kind> <subject> <val>` | Save an analytical fact into the overlay SQLite database. |
| **`facts`** | `rdis <exe> facts [kind]` | Query active facts in the SQLite overlay journal. |
| **`retract`** | `rdis <exe> retract <id>` | Retract an asserted fact by its ID. |
| **`audit`** | `rdis <exe> audit` | Audit all active facts and check if their evidence remains valid. |

*(Addresses can be supplied as hexadecimal RVAs like `0x4A3D0`, IDA-style `sub_4A3D0`, a named label, or a signature).*

---

## Testing

`rdis` includes native Rust integration tests as well as automated PowerShell test suites:

### 1. Cargo Unit & Integration Tests
```bash
cargo test
```
Executes native CLI tests in `tests/cli_tests.rs`.

### 2. Fast CI Integration Test
```powershell
powershell -File tests/ci_test.ps1
```
Tests CLI help, PE parsing, disassembly, function decompilation, and overlay database persistence.

### 3. Full Benchmark & Accuracy Suite
```powershell
powershell -File tests/test_speed_accuracy.ps1
```
Runs a comprehensive 60-command performance, accuracy, and SQLite persistence benchmark suite.

---

## CI & Automated Releases

On each tag release (e.g. `v0.1.0`), GitHub Actions builds an optimized `rdis.exe` on Windows and packages `rdis-windows-x86_64.zip` containing the executable and documentation.
