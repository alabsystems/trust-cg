// trust-cg-codegen/tests/wasm_r4_lane.rs - wasm32 lane: determinism, limits, link boundary
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Regressions for the wasm32 lane, each pinned with the trust-ir input that
//! exposed it and checked against the trust-ir reference interpreter (or an
//! exact value / a named refusal):
//!
//! * the emitted bytes are a function of the input alone — the same module
//!   compiled again, in this thread or a fresh one (fresh hash-map seeds),
//!   gives the same bytes;
//! * a closed module refuses static data (zero-initialized globals included)
//!   past the memory it owns, and the sized closed policy holds it with a
//!   minimum stack whatever the data's size;
//! * a `CallingConv::Rust` aggregate never crosses an object's link boundary,
//!   a padded singleton is passed by address as rustc and clang pass it, and
//!   a function address inside an aggregate constant counts as taken;
//! * an object never names one non-local symbol twice, nor defines a symbol
//!   the linker synthesizes; a closed module never exports a name twice;
//! * a frame alignment past 2^30 is refused, not a compiler panic;
//! * non-dominated uses and mistyped branch arguments are refused;
//! * deep dominator trees and huge sparse switches compile on a 2 MiB stack;
//! * large functions keep few locals (the coalescer has no all-or-nothing
//!   cliff), and many simultaneously live memory values compile quickly;
//! * allocations in disjoint scopes share frame bytes;
//! * 128-bit atomics and zero-sized enum lanes compile; closures are refused
//!   by name; `frem` never binds to a module-defined `fmod`.
//! * a memory-carried lane read through a pointer is a copy: a later write
//!   through the pointer (`InsertField`, `Store`, a callee) never changes it.

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::wasm::{self, WasmLowerError, WasmMemoryPolicy, WasmModulePolicy};
use trust_ir::{
    InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty, parser,
};

const HEADER: &str = "module \"r4\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n";

/// Rename `%name` values and `bbname` blocks to the text format's numeric
/// spellings, per function, in order of first appearance.
fn number_names(text: &str) -> String {
    use std::collections::HashMap;
    let mut out = String::with_capacity(text.len());
    let mut values: HashMap<String, usize> = HashMap::new();
    let mut blocks: HashMap<String, usize> = HashMap::new();
    for line in text.lines() {
        let head = line.trim_start_matches("internal ");
        if head.starts_with("fn ") || head.starts_with("rustcc fn ") {
            values.clear();
            blocks.clear();
        }
        let bytes = line.as_bytes();
        let mut i = 0;
        let ident_end = |mut j: usize| {
            while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
                j += 1;
            }
            j
        };
        while i < bytes.len() {
            let word_start =
                i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_');
            if bytes[i] == b'%' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_alphabetic() {
                let end = ident_end(i + 1);
                let n = values.len();
                let id = *values.entry(line[i + 1..end].to_string()).or_insert(n);
                let _ = write!(out, "%{id}");
                i = end;
            } else if word_start
                && line[i..].starts_with("bb")
                && i + 2 < bytes.len()
                && bytes[i + 2].is_ascii_alphabetic()
            {
                let end = ident_end(i + 2);
                let n = blocks.len();
                let id = *blocks.entry(line[i + 2..end].to_string()).or_insert(n);
                let _ = write!(out, "bb{id}");
                i = end;
            } else {
                out.push(bytes[i] as char);
                i += 1;
            }
        }
        out.push('\n');
    }
    out
}

/// Parse a module body (named values allowed) under [`HEADER`].
fn parse(body: &str) -> Module {
    let text = number_names(&format!("{HEADER}{body}"));
    parser::parse_module(&text).unwrap_or_else(|e| {
        let numbered: String = text
            .lines()
            .enumerate()
            .map(|(i, l)| format!("{:4} {l}\n", i + 1))
            .collect();
        panic!("test module failed to parse: {e}\n{numbered}")
    })
}

fn node() -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("node"))
        .find(|p| p.is_file())
}

fn wasm_ld() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("WASM_LD") {
        return Some(PathBuf::from(p));
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("wasm-ld"))
        .find(|p| p.is_file())
}

/// A scratch directory no other test thread uses.
fn scratch(tag: &str) -> PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("tcg_wasm_r4_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn validate(bytes: &[u8]) {
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
}

/// The interpreter's answer for `(i64, i64) -> i64` function `name`, or `None`
/// when the reference execution refuses the input.
fn interpret(module: &Module, name: &str, a: i64, b: i64) -> Option<i64> {
    let f = module.function_by_name(name).expect("function");
    let arg = |v: i64| InterpretValue::int(Ty::I64, i128::from(v)).expect("i64 value");
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 50_000_000,
            max_call_depth: 256,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, vec![arg(a), arg(b)])
        .ok()?;
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => Some(i.as_signed() as i64),
        other => panic!("{name} returned {other:?}"),
    }
}

/// Run `(i64, i64) -> i64` export `name` over `inputs` in one instance
/// (`None` is a trap); `None` for the whole column when node is absent.
fn run_wasm(bytes: &[u8], name: &str, inputs: &[(i64, i64)]) -> Option<Vec<Option<i64>>> {
    let node = node()?;
    let dir = scratch("run");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let js = "const fs = require('fs');\n\
              const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
              const imports = {};\n\
              for (const i of WebAssembly.Module.imports(m)) {\n\
                imports[i.module] ??= {};\n\
                if (i.kind === 'function') imports[i.module][i.name] = () => { throw new Error('import ' + i.name); };\n\
              }\n\
              const inst = new WebAssembly.Instance(m, imports);\n\
              const f = inst.exports[process.argv[3]];\n\
              const inputs = JSON.parse(fs.readFileSync(process.argv[4]));\n\
              const out = inputs.map(([a, b]) => { try { return f(BigInt(a), BigInt(b)).toString(); } \
              catch (e) { if (e instanceof WebAssembly.RuntimeError) return null; throw e; } });\n\
              process.stdout.write(JSON.stringify(out));\n";
    std::fs::write(dir.join("run.js"), js).unwrap();
    let pairs: Vec<[String; 2]> = inputs
        .iter()
        .map(|(a, b)| [a.to_string(), b.to_string()])
        .collect();
    std::fs::write(
        dir.join("inputs.json"),
        serde_json::to_string(&pairs).unwrap(),
    )
    .unwrap();
    let run = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .arg(name)
        .arg(dir.join("inputs.json"))
        .output()
        .expect("run node");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "node failed on {name}: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let got: Vec<Option<String>> = serde_json::from_slice(&run.stdout).expect("node JSON");
    Some(
        got.into_iter()
            .map(|v| v.map(|s| s.parse::<i64>().unwrap()))
            .collect(),
    )
}

/// Link relocatable objects into a runnable module (every definition
/// exported). `None` when no linker is available.
fn link(objects: &[&[u8]]) -> Option<Vec<u8>> {
    let ld = wasm_ld()?;
    let dir = scratch("link");
    let mut cmd = Command::new(&ld);
    cmd.args([
        "--no-entry",
        "--export-dynamic",
        "--stack-first",
        "-z",
        "stack-size=1048576",
        "-o",
    ])
    .arg(dir.join("m.wasm"));
    for (i, object) in objects.iter().enumerate() {
        let path = dir.join(format!("m{i}.o"));
        std::fs::write(&path, object).unwrap();
        cmd.arg(path);
    }
    let out = cmd.output().expect("run wasm-ld");
    assert!(
        out.status.success(),
        "wasm-ld refused the objects: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let linked = std::fs::read(dir.join("m.wasm")).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    Some(linked)
}

/// `name` in `bytes` agrees with the interpreter on every input. Returns the
/// number of checks (0 when node is absent).
fn agrees(module: &Module, bytes: &[u8], name: &str, inputs: &[(i64, i64)]) -> usize {
    validate(bytes);
    let Some(got) = run_wasm(bytes, name, inputs) else {
        return 0;
    };
    for (&(a, b), got) in inputs.iter().zip(&got) {
        let want = interpret(module, name, a, b);
        assert_eq!(
            *got, want,
            "{name}({a}, {b}): wasm {got:?}, interpreter {want:?}"
        );
    }
    inputs.len()
}

fn owned(pages: u32) -> WasmModulePolicy {
    WasmModulePolicy {
        memory: WasmMemoryPolicy::Owned {
            pages,
            export: None,
        },
        ..WasmModulePolicy::closed()
    }
}

fn closed_with(module: &Module, policy: &WasmModulePolicy) -> Vec<u8> {
    wasm::compile_module_with_policy_and_license(module, policy, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile: {e}"))
}

/// Run `f` on a thread with a 2 MiB stack — the default of a spawned Rust
/// thread and less than rustc's codegen thread — so a lowering that recursed
/// per basic block or per `switch` case would overflow here.
fn on_small_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("the lowering overflowed a 2 MiB stack")
}

/// The locals the first defined function of `bytes` declares (parameters
/// excluded).
fn declared_locals(bytes: &[u8]) -> u64 {
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let Ok(wasmparser::Payload::CodeSectionEntry(body)) = payload {
            let mut n = 0u64;
            for local in body.get_locals_reader().expect("locals") {
                n += u64::from(local.expect("local").0);
            }
            return n;
        }
    }
    panic!("no function body")
}

// ---- 1. Byte determinism ----

/// A chain of aggregates, each dead before the next is made: every home is
/// placed at one frame offset, so their prologue/definition order is decided
/// by the tie-break alone (`nondeterministic_codegen.trust_ir`,
/// `min_prologue_tie.trust_ir`).
fn tied_homes(n: usize, extra_scalars: usize) -> String {
    let mut body = String::from(
        "struct @P { : i64 @0, : i64 @8 } size=16 align=8 id=0\n\n\
         functy.0 = (i64, i64) -> (i64)\n\n\
         fn @tied(functy.0) {\nbbentry(%a: i64, %b: i64):\n    %x0 = add i64 %a, %b\n",
    );
    for i in 0..n {
        let _ = writeln!(body, "    %p{i} = make_aggregate struct.0 (%x{i}, %a)");
        let _ = writeln!(body, "    %x{} = extractfield i64 %p{i}, 0", i + 1);
    }
    let mut last = format!("x{n}");
    for k in 0..extra_scalars {
        let _ = writeln!(body, "    %s{k} = add i64 %{last}, %b");
        last = format!("s{k}");
    }
    let _ = writeln!(body, "    ret %{last}\n}}");
    body
}

const PROLOGUE_TIE: &str = r#"
struct @P { : i32 @0, : i32 @4 } size=8 align=4 id=0

functy.0 = (i32, i32) -> (i32)

fn @f(functy.0) {
bbentry(%a: i32, %b: i32):
    %p = make_aggregate struct.0 (%a, %b)
    %x = extractfield i32 %p, 0
    %q = make_aggregate struct.0 (%b, %x)
    %y = extractfield i32 %q, 1
    ret %y
}
"#;

#[test]
fn the_same_module_always_compiles_to_the_same_bytes() {
    let modules = [
        parse(PROLOGUE_TIE),
        parse(&tied_homes(12, 0)),
        parse(&tied_homes(24, 80)),
    ];
    for module in &modules {
        let closed =
            wasm::compile_module_with_license(module, &permit_unlicensed()).expect("compile");
        let object =
            wasm::compile_object_with_license(module, &permit_unlicensed()).expect("object");
        let (_, evidence) = wasm::compile_module_with_evidence_policy_and_license(
            module,
            &wasm::WasmModulePolicy::closed(),
            &permit_unlicensed(),
        )
        .expect("evidence");
        // Each compile builds its maps afresh (new hash seeds); a spawned
        // thread also starts from fresh per-thread keys.
        for _ in 0..16 {
            assert_eq!(
                wasm::compile_module_with_license(module, &permit_unlicensed()).expect("compile"),
                closed
            );
            assert_eq!(
                wasm::compile_object_with_license(module, &permit_unlicensed()).expect("object"),
                object
            );
        }
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let m = module.clone();
                std::thread::spawn(move || {
                    let (bytes, ev) = wasm::compile_module_with_evidence_policy_and_license(
                        &m,
                        &wasm::WasmModulePolicy::closed(),
                        &permit_unlicensed(),
                    )
                    .expect("compile");
                    (
                        bytes,
                        ev.module_sha256,
                        wasm::compile_object_with_license(&m, &permit_unlicensed())
                            .expect("object"),
                    )
                })
            })
            .collect();
        for t in threads {
            let (bytes, sha, obj) = t.join().expect("thread");
            assert_eq!(bytes, closed, "closed bytes differ across threads");
            assert_eq!(sha, evidence.module_sha256, "evidence digest differs");
            assert_eq!(obj, object, "object bytes differ across threads");
        }
    }
    let tied = &modules[2];
    let bytes = wasm::compile_module_with_license(tied, &permit_unlicensed()).unwrap();
    agrees(
        tied,
        &bytes,
        "tied",
        &[(0, 0), (3, 4), (-7, 11), (i64::MAX, 1)],
    );
}

// ---- 2. Static data past the owned memory ----

/// `min_touch.trust_ir` / `min_frame.trust_ir`: an initializer-less (BSS)
/// global of `bytes` bytes, a function reading its last byte, and one with
/// only a frame.
fn bss_module(bytes: u32) -> Module {
    parse(&format!(
        "type ty.0 = u8\n\n\
         functy.0 = (i64, i64) -> (i64)\n\n\
         global internal mut @g [ty.0 x {bytes}]\n\n\
         fn @touch(functy.0) {{\nbbentry(%a: i64, %b: i64):\n\
             %g = global_addr @global.0\n    %i = const i32 {last}\n\
             %p = gep u8, ptr %g, %i\n    %v = trunc i64 %a to u8\n\
             store u8 %v, ptr %p\n    %w = load u8, ptr %p\n\
             %r = zext u8 %w to i64\n    ret %r\n}}\n\n\
         fn @framed(functy.0) {{\nbbentry(%a: i64, %b: i64):\n\
             %c = alloca i64\n    store i64 %a, ptr %c\n    %r = load i64, ptr %c\n    ret %r\n}}\n",
        last = bytes - 1,
    ))
}

#[test]
fn bss_past_the_owned_memory_is_refused_and_a_sized_closed_module_holds_it() {
    // 4 pages end at 262144; the area starts at 8.
    let past = bss_module(262_137);
    match wasm::compile_module_with_policy_and_license(&past, &owned(4), &permit_unlicensed()) {
        Err(WasmLowerError::StaticDataOverflow(m)) => {
            assert!(m.contains("zero-initialized globals included"), "{m}")
        }
        other => panic!("BSS past the owned memory must be refused, got {other:?}"),
    }
    // Exactly filling the memory is accepted and the last byte is usable.
    let fits = bss_module(262_136);
    let bytes = closed_with(&fits, &owned(4));
    agrees(&fits, &bytes, "touch", &[(5, 0), (255, 0), (-1, 0)]);

    // The sized closed policy owns enough pages for the data plus a stack.
    let big = bss_module(200_000);
    let policy = wasm::sized_closed_policy(&big).expect("size");
    let WasmMemoryPolicy::Owned { pages, .. } = policy.memory else {
        panic!("closed memory is owned")
    };
    assert!(u64::from(pages) * 65536 >= 200_008 + 65536, "{pages} pages");
    let bytes = closed_with(&big, &policy);
    agrees(&big, &bytes, "touch", &[(5, 0), (77, 0)]);
    agrees(&big, &bytes, "framed", &[(7, 0), (-3, 0)]);

    // A module with no static data keeps the default policy's bytes.
    let empty = parse(PROLOGUE_TIE);
    assert_eq!(
        wasm::sized_closed_policy(&empty).expect("size"),
        WasmModulePolicy::closed()
    );
}

/// `stk60000.trust_ir` / `stk66000.trust_ir`: the same 8 KiB frame beside
/// `bytes` of zero-initialized data.
fn frame_beside_bss(bytes: u32) -> Module {
    parse(&format!(
        "type ty.0 = u8\n\nfuncty.0 = (i64, i64) -> (i64)\n\n\
         global internal mut @g [ty.0 x {bytes}]\n\n\
         fn @f(functy.0) {{\nbbentry(%a: i64, %b: i64):\n\
             %buf = alloca [ty.0 x 8192]\n    %i = const i32 4000\n\
             %p = gep u8, ptr %buf, %i\n    %v = trunc i64 %a to u8\n\
             store u8 %v, ptr %p\n    %w = load u8, ptr %p\n\
             %r = zext u8 %w to i64\n    ret %r\n}}\n"
    ))
}

/// Every module the sized closed policy owns has at least
/// `WASM_CLOSED_MIN_STACK_BYTES` of stack above its data, whatever the data's
/// size: 60,000 bytes of data used to keep one page and leave ~5.5 KiB (the
/// 8 KiB frame trapped) while 66,000 bytes grew the memory and ran.
#[test]
fn the_sized_closed_policy_always_leaves_its_minimum_stack() {
    for bytes in [100, 60_000, 65_000, 65_528, 66_000, 131_064] {
        let module = frame_beside_bss(bytes);
        let policy = wasm::sized_closed_policy(&module).expect("size");
        let WasmMemoryPolicy::Owned { pages, .. } = policy.memory else {
            panic!("closed memory is owned")
        };
        // The data area starts at 8.
        let end = 8 + u64::from(bytes);
        assert!(
            u64::from(pages) * 65536 - end >= u64::from(wasm::WASM_CLOSED_MIN_STACK_BYTES),
            "{bytes} bytes of data: {pages} pages leave too little stack"
        );
        let wasm_bytes = closed_with(&module, &policy);
        agrees(&module, &wasm_bytes, "f", &[(7, 0), (200, 0), (-1, 0)]);
    }
}

/// `closed_static_data_70k.trust_ir`: one 72,000-byte immutable table read
/// by index — refused by the one-page default, held by the sized policy.
#[test]
fn a_closed_module_is_not_capped_at_one_page_of_static_data() {
    let values: Vec<String> = (0..18_000u32)
        .map(|i| ((i * 7919) % 100_003).to_string())
        .collect();
    let module = parse(&format!(
        "type ty.0 = i32\n\nfuncty.0 = (i64, i64) -> (i64)\n\n\
         global @big [ty.0 x 18000] = array[ {} ]\n\n\
         fn @f(functy.0) {{\nbbentry(%a: i64, %b: i64):\n\
             %n = const i64 18000\n    %i = urem i64 %a, %n\n    %j = trunc i64 %i to i32\n\
             %g = global_addr @global.0\n    %p = gep i32, ptr %g, %j\n\
             %v = load i32, ptr %p\n    %r = sext i32 %v to i64\n    ret %r\n}}\n",
        values.join(", ")
    ));
    assert!(
        wasm::compile_module_with_license(&module, &permit_unlicensed()).is_err(),
        "one page cannot hold 72 KB"
    );
    let bytes = closed_with(&module, &wasm::sized_closed_policy(&module).expect("size"));
    agrees(
        &module,
        &bytes,
        "f",
        &[(12_345, 0), (17_999, 0), (0, 0), (-5, 0)],
    );
}

// ---- 3. The Rust convention at a link boundary ----

const RUST_AGG: &str = "struct @P { : u8 @0, : u8 @1, : u16 @2 } size=4 align=2 id=0\n\n\
                        functy.0 = (struct.0) -> (i64)\nfuncty.1 = (i64, i64) -> (i64)\n\n";

/// `caller.trust_ir`: a caller building a 4-byte struct for a Rust-convention
/// callee.
fn rust_callee(callee: &str) -> Module {
    parse(&format!(
        "{RUST_AGG}{callee}\n\
         fn @user(functy.1) {{\nbbentry(%a: i64, %b: i64):\n\
             %x = trunc i64 %a to u8\n    %y = const u8 2\n    %z = trunc i64 %b to u16\n\
             %s = make_aggregate struct.0 (%x, %y, %z)\n    %r = call @func.0(%s)\n    ret %r\n}}\n"
    ))
}

const RUST_BODY: &str = "(functy.0) {\nbbentry(%s: struct.0):\n\
                         %x = extractfield u8 %s, 0\n    %z = extractfield u16 %s, 2\n\
                         %xw = zext u8 %x to i64\n    %zw = zext u16 %z to i64\n\
                         %k = const i64 100000\n    %m = mul i64 %xw, %k\n\
                         %r = add i64 %m, %zw\n    ret %r\n}\n";

fn assert_rust_link_refusal(module: &Module) {
    match wasm::compile_object_with_license(module, &permit_unlicensed()) {
        Err(WasmLowerError::UnsupportedAbi(m)) => {
            assert!(m.contains("[TCG-WASM-RUST-ABI-LINK]"), "{m}")
        }
        other => panic!("a Rust-convention aggregate crossed the link boundary: {other:?}"),
    }
}

#[test]
fn a_rust_convention_aggregate_never_crosses_an_object_link_boundary() {
    // A declaration (the callee is rustc's): refused.
    assert_rust_link_refusal(&rust_callee("rustcc fn @ext(functy.0) {\n}\n"));
    // An exported definition other objects may call: refused.
    assert_rust_link_refusal(&rust_callee(&format!("rustcc fn @ext{RUST_BODY}")));
    // A module-local definition only this object calls: compiled, and
    // linked it computes what the interpreter does.
    let local = rust_callee(&format!("internal rustcc fn @ext{RUST_BODY}"));
    let object = wasm::compile_object_with_license(&local, &permit_unlicensed())
        .expect("a module-local Rust callee compiles");
    if let Some(linked) = link(&[&object]) {
        agrees(
            &local,
            &linked,
            "user",
            &[(1, 3), (0x34, 0x1234), (255, 65535)],
        );
    }
    // Its address taken, the pointer may reach foreign code: refused.
    assert_rust_link_refusal(&parse(&format!(
        "{RUST_AGG}functy.2 = () -> (i64)\n\n\
         internal rustcc fn @cb{RUST_BODY}\n\
         fn @drive(functy.2) {{\nbbentry:\n    %f = const functy.0 fndef<func.0>\n\
             %x = const u8 1\n    %y = const u8 2\n    %z = const u16 3\n\
             %s = make_aggregate struct.0 (%x, %y, %z)\n\
             %r = call_indirect %f(functy.0)(%s) cc=rustcc\n    ret %r\n}}\n"
    )));
    // Scalars, 128-bit integers and struct singletons cross as rustc passes
    // them.
    let scalar = parse(
        "struct @W { : i64 @0 } size=8 align=8 id=0\n\n\
         functy.0 = (i64, i128, struct.0) -> (i64)\nfuncty.1 = (i64, i64) -> (i64)\n\n\
         rustcc fn @ext(functy.0) {\n}\n\n\
         fn @user(functy.1) {\nbbentry(%a: i64, %b: i64):\n    %w = sext i64 %b to i128\n\
             %s = make_aggregate struct.0 (%a)\n    %r = call @func.0(%a, %w, %s)\n    ret %r\n}\n",
    );
    wasm::compile_object_with_license(&scalar, &permit_unlicensed())
        .expect("scalar lanes cross the boundary");
    // A declaration nothing references needs no import at all — neither a
    // Rust aggregate one nor a C variadic one (`va.trust_ir`).
    let unused = parse(&format!(
        "{RUST_AGG}functy.2 = (ptr, ...) -> (i32)\n\n\
         rustcc fn @ext(functy.0) {{\n}}\n\nfn @printf(functy.2) {{\n}}\n\n\
         fn @user(functy.1) {{\nbbentry(%a: i64, %b: i64):\n    %r = add i64 %a, %b\n    ret %r\n}}\n"
    ));
    let object = wasm::compile_object_with_license(&unused, &permit_unlicensed())
        .expect("unreferenced declarations are not imported");
    let imports = wasmparser::Parser::new(0)
        .parse_all(&object)
        .filter_map(|p| match p {
            Ok(wasmparser::Payload::ImportSection(r)) => Some(r),
            _ => None,
        })
        .flat_map(|r| r.into_iter().map(|i| i.expect("import").name.to_string()))
        .collect::<Vec<_>>();
    assert!(
        !imports.iter().any(|n| n == "ext" || n == "printf"),
        "{imports:?}"
    );
}

/// `a8c.trust_ir` / `al.rs`: a singleton PADDED past its member
/// (`#[repr(C, align(8))] struct A8C(u32)`, size 8). rustc and clang pass it
/// by address and return it through `sret` — LLVM's wasm32 IR is
/// `define i32 @ext_a8c(ptr dereferenceable(8) %s)` and
/// `define void @ret_a8c(ptr sret([8 x i8]) %_0, i32 %x)` — so `CALLEE_LLVM`
/// spells exactly that ABI with explicit pointers. The lane used to pass the
/// member's value where the callee reads an address (`user(7)` was 0).
const PADDED_CALLER: &str = "struct @A8 { : u32 @0 } size=8 align=8 repr=c id=0\n\n\
    functy.0 = (struct.0) -> (u32)\nfuncty.1 = (u32) -> (struct.0)\n\
    functy.2 = (i64, i64) -> (i64)\n\n\
    fn @ext_a8c(functy.0) {\n}\n\nfn @ret_a8c(functy.1) {\n}\n\n\
    fn @user(functy.2) {\nbbentry(%a: i64, %b: i64):\n\
        %x = trunc i64 %a to u32\n    %s = make_aggregate struct.0 (%x)\n\
        %r = call @func.0(%s)\n    %y = trunc i64 %b to u32\n    %t = call @func.1(%y)\n\
        %z = extractfield u32 %t, 0\n    %rw = zext u32 %r to i64\n    %zw = zext u32 %z to i64\n\
        %k = const i64 4294967296\n    %h = mul i64 %zw, %k\n    %o = add i64 %h, %rw\n\
        ret %o\n}\n";

const CALLEE_LLVM: &str = "functy.0 = (ptr) -> (u32)\nfuncty.1 = (ptr, u32) -> ()\n\n\
    fn @ext_a8c(functy.0) {\nbbentry(%p: ptr):\n    %v = load u32, ptr %p\n\
        %k = const u32 3\n    %r = mul u32 %v, %k\n    ret %r\n}\n\n\
    fn @ret_a8c(functy.1) {\nbbentry(%p: ptr, %x: u32):\n    store u32 %x, ptr %p\n    ret\n}\n";

#[test]
fn a_padded_singleton_is_passed_by_address_and_never_as_its_member() {
    let unpinned = parse(&PADDED_CALLER.replace(" repr=c", ""));
    let error = wasm::compile_object_with_license(&unpinned, &permit_unlicensed())
        .expect_err("an external aggregate must declare its representation");
    assert!(
        format!("{error:?}").contains("FfiStructReprUnpinned"),
        "{error}"
    );
    let caller = wasm::compile_object_with_license(&parse(PADDED_CALLER), &permit_unlicensed())
        .expect("C caller compiles");
    let callee = wasm::compile_object_with_license(&parse(CALLEE_LLVM), &permit_unlicensed())
        .expect("callee compiles");
    if let Some(linked) = link(&[&caller, &callee]) {
        validate(&linked);
        let inputs = [(7, 9), (100, 0), (0x4000_0001, 0xffff_ffff)];
        if let Some(got) = run_wasm(&linked, "user", &inputs) {
            for (&(a, b), got) in inputs.iter().zip(&got) {
                let want = i64::from((a as u32).wrapping_mul(3)) + (i64::from(b as u32) << 32);
                assert_eq!(*got, Some(want), "user({a}, {b})");
            }
        }
    }
    // Under the Rust convention a padded singleton is no singleton either:
    // rustc passes `#[repr(align(8))] struct A8(u32)` by address and casts a
    // 4-byte padded `u16` wrapper to an integer — refused at the boundary.
    for padded in [
        "struct @A8 { : u32 @0 } size=8 align=8 id=0\n\n",
        "struct @W { : u16 @0 } size=4 align=4 id=0\n\n",
    ] {
        assert_rust_link_refusal(&parse(&format!(
            "{padded}functy.0 = (struct.0) -> (i64)\nfuncty.1 = (i64, i64) -> (i64)\n\n\
             rustcc fn @ext(functy.0) {{\n}}\n\n\
             fn @user(functy.1) {{\nbbentry(%a: i64, %b: i64):\n    %u = undef struct.0\n\
                 %r = call @func.0(%u)\n    ret %r\n}}\n"
        )));
    }
}

/// `N1`/`N2`/`N3.trust_ir`: a function address inside an aggregate CONSTANT
/// in code (the vtable shape) is an address taken and a reference, exactly as
/// a top-level `fndef` is. It used to be invisible: an address-taken internal
/// Rust-convention aggregate function was compiled, and a declaration named
/// only there was dropped as unreferenced, then failed with "function pointer
/// to unknown FuncId".
#[test]
fn a_function_address_inside_an_aggregate_constant_is_seen() {
    // The table's lanes are `ptr`s, so each names the function by its symbol
    // (`symaddr`, the function's table index on wasm32): trust-ir types
    // `fndef` at a function type only.
    let vtable = |decls: &str, sigs: &str, callee: &str| {
        parse(&format!(
            "struct @P {{ : u8 @0, : u8 @1, : u16 @2 }} size=4 align=2 id=0\n\
             type ty.0 = ptr\n\n{sigs}functy.1 = (i64, i64) -> (i64)\n\n{decls}\n\
             fn @get_cb(functy.1) {{\nbbentry(%a: i64, %b: i64):\n\
                 %t = const [ty.0 x 2] splat[ symaddr<{callee}>; 2 ]\n\
                 %zero = const usize 0\n    %p = extractelement ptr %t, %zero\n    %i = ptrtoint ptr %p to u32\n\
                 %r = zext u32 %i to i64\n    ret %r\n}}\n"
        ))
    };
    let agg = "functy.0 = (struct.0) -> (i32)\n";
    assert_rust_link_refusal(&vtable(
        "internal rustcc fn @cb(functy.0) {\nbbentry(%s: struct.0):\n\
             %z = extractfield u16 %s, 2\n    %r = zext u16 %z to i32\n    ret %r\n}\n",
        agg,
        "cb",
    ));
    assert_rust_link_refusal(&vtable("rustcc fn @ext(functy.0) {\n}\n", agg, "ext"));
    match wasm::compile_object_with_license(
        &vtable(
            "fn @printf(functy.0) {\n}\n",
            "functy.0 = (ptr, ...) -> (i32)\n",
            "printf",
        ),
        &permit_unlicensed(),
    ) {
        Err(WasmLowerError::UnsupportedAbi(m)) => assert!(m.contains("C variadic"), "{m}"),
        other => {
            panic!("a variadic declaration named in a constant must be refused, got {other:?}")
        }
    }

    // Under the C convention the same shape compiles, and calling through the
    // table agrees with the interpreter, closed and linked.
    let module = parse(
        "functy.0 = (i64) -> (i64)\nfuncty.1 = (i64, i64) -> (i64)\ntype ty.0 = functy.0\n\n\
         internal fn @inc(functy.0) {\nbbentry(%x: i64):\n    %k = const i64 1\n\
             %r = add i64 %x, %k\n    ret %r\n}\n\n\
         internal fn @dbl(functy.0) {\nbbentry(%x: i64):\n    %r = add i64 %x, %x\n    ret %r\n}\n\n\
         fn @user(functy.1) {\nbbentry(%a: i64, %b: i64):\n\
             %t = const [ty.0 x 2] array[fndef<func.0>, fndef<func.1>]\n\
             %i0 = const i32 0\n    %i1 = const i32 1\n\
             %f = extractelement functy.0 %t, %i0\n    %g = extractelement functy.0 %t, %i1\n\
             %x = call_indirect %f(functy.0)(%a)\n    %y = call_indirect %g(functy.0)(%b)\n\
             %k = const i64 1000\n    %m = mul i64 %x, %k\n    %r = add i64 %m, %y\n    ret %r\n}\n",
    );
    let inputs = [(5, 7), (-1, 0), (1 << 40, 3)];
    agrees(
        &module,
        &wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("closed"),
        "user",
        &inputs,
    );
    let object = wasm::compile_object_with_license(&module, &permit_unlicensed()).expect("object");
    if let Some(linked) = link(&[&object]) {
        agrees(&module, &linked, "user", &inputs);
    }
}

// ---- 4. Symbol names ----

fn assert_symbol_refusal(body: &str, tag: &str) {
    let module = parse(body);
    let result = wasm::compile_object_with_license(&module, &permit_unlicensed());
    if let Err(WasmLowerError::InvalidTrustIr(refusal)) = &result {
        assert!(
            refusal.any(|error| matches!(
                error,
                trust_ir_build::ValidationError::DuplicateFunctionSymbol { .. }
            )),
            "{refusal}"
        );
        return;
    }
    match result {
        Err(WasmLowerError::ContractSurface(m)) => assert!(m.contains(tag), "{m}"),
        other => panic!("expected a {tag} refusal, got {other:?}"),
    }
}

#[test]
fn an_object_names_each_non_local_symbol_once() {
    let ret = "functy.0 = () -> (i32)\n\n";
    let body = "{\nbbentry:\n    %c = const i32 8\n    ret %c\n}\n";
    // A global and a function of one name (`min.trust_ir`).
    assert_symbol_refusal(
        &format!("{ret}global @same i32 = 1\n\nfn @same(functy.0) {body}"),
        "[TCG-WASM-SYMBOL]",
    );
    // Two defined globals of one name (`v5`).
    assert_symbol_refusal(
        &format!("{ret}global @g i32 = 1\nglobal @g i32 = 2\n\nfn @f(functy.0) {body}"),
        "[TCG-WASM-SYMBOL]",
    );
    // Names the linker owns (`w1`, `w2`, `ctors.trust_ir`).
    assert_symbol_refusal(
        &format!("{ret}global @__stack_pointer i32 = 1\n\nfn @f(functy.0) {body}"),
        "`wasm-ld` synthesizes",
    );
    assert_symbol_refusal(
        &format!("{ret}fn @__indirect_function_table(functy.0) {body}"),
        "`wasm-ld` synthesizes",
    );
    assert_symbol_refusal(
        &format!("{ret}fn @__wasm_call_ctors(functy.0) {body}"),
        "`wasm-ld` synthesizes",
    );
    // `frem`'s `fmod` import beside a data reference of that name (`w3`), and
    // a frame's `__stack_pointer` import beside one (`w5`).
    assert_symbol_refusal(
        "functy.0 = (f64, f64) -> (f64)\nfuncty.1 = () -> (ptr)\n\n\
         fn @r(functy.0) {\nbbentry(%a: f64, %b: f64):\n    %c = frem f64 %a, %b\n    ret %c\n}\n\n\
         fn @p(functy.1) {\nbbentry:\n    %s = const ptr symaddr<fmod>\n    ret %s\n}\n",
        "[TCG-WASM-SYMBOL]",
    );
    assert_symbol_refusal(
        "functy.0 = (i32) -> (i32)\nfuncty.1 = () -> (ptr)\n\n\
         fn @f(functy.0) {\nbbentry(%a: i32):\n    %c = alloca i32\n    store i32 %a, ptr %c\n\
             %r = load i32, ptr %c\n    ret %r\n}\n\n\
         fn @p(functy.1) {\nbbentry:\n    %s = const ptr symaddr<__stack_pointer>\n    ret %s\n}\n",
        "[TCG-WASM-SYMBOL]",
    );
    // Disagreeing declarations of one name.
    assert_symbol_refusal(
        "functy.0 = (i32) -> (i32)\nfuncty.1 = (i64) -> (i64)\nfuncty.2 = (i32) -> (i32)\n\n\
         fn @ext(functy.0) {\n}\n\nfn @ext(functy.1) {\n}\n\n\
         fn @h(functy.2) {\nbbentry(%a: i32):\n    %r = call @func.0(%a)\n    ret %r\n}\n",
        "[TCG-WASM-SYMBOL]",
    );

    // Module-local definitions are local symbols: no collision.
    let local = parse(&format!(
        "{ret}global internal @same i32 = 1\n\nfn @same(functy.0) {body}\n\
         internal fn @__wasm_call_ctors(functy.0) {body}"
    ));
    wasm::compile_object_with_license(&local, &permit_unlicensed())
        .expect("local symbols never collide");

    // Duplicate source declarations are refused even when their types agree.
    // A valid module's two calls name one canonical external declaration.
    let twice = parse(
        "functy.0 = (i64, i64) -> (i64)\n\n\
         fn @ext(functy.0) {\n}\n\nfn @ext(functy.0) {\n}\n\n\
         fn @h(functy.0) {\nbbentry(%a: i64, %b: i64):\n    %x = call @func.0(%a, %b)\n\
             %y = call @func.1(%x, %b)\n    ret %y\n}\n",
    );
    let error = wasm::compile_object_with_license(&twice, &permit_unlicensed())
        .expect_err("duplicate function declarations remain invalid");
    assert!(
        format!("{error:?}").contains("DuplicateFunctionSymbol"),
        "{error}"
    );
    let canonical = parse(
        "functy.0 = (i64, i64) -> (i64)\n\n\
         fn @ext(functy.0) {\n}\n\n\
         fn @h(functy.0) {\nbbentry(%a: i64, %b: i64):\n    %x = call @func.0(%a, %b)\n\
             %y = call @func.0(%x, %b)\n    ret %y\n}\n",
    );
    assert!(trust_ir_build::validate_module(&canonical).is_empty());
    let object = wasm::compile_object_with_license(&canonical, &permit_unlicensed())
        .expect("two calls share a canonical external declaration");
    let imported = wasmparser::Parser::new(0)
        .parse_all(&object)
        .filter_map(|p| match p {
            Ok(wasmparser::Payload::ImportSection(r)) => Some(r),
            _ => None,
        })
        .flat_map(|r| r.into_iter().map(|i| i.expect("import").name.to_string()))
        .filter(|n| n == "ext")
        .count();
    assert_eq!(imported, 1, "one import for the shared declaration");
    let def = parse(
        "functy.0 = (i64, i64) -> (i64)\n\n\
         fn @ext(functy.0) {\nbbentry(%a: i64, %b: i64):\n    %r = add i64 %a, %b\n    ret %r\n}\n",
    );
    let def_obj =
        wasm::compile_object_with_license(&def, &permit_unlicensed()).expect("definition");
    if let Some(linked) = link(&[&object, &def_obj])
        && let Some(got) = run_wasm(&linked, "h", &[(1, 10), (5, -2)])
    {
        assert_eq!(got, vec![Some(21), Some(1)]);
    }
}

#[test]
fn a_closed_module_never_exports_a_name_twice() {
    let module = parse(
        "functy.0 = (i64, i64) -> (i64)\n\n\
         fn @memory(functy.0) {\nbbentry(%a: i64, %b: i64):\n    %r = add i64 %a, %b\n    ret %r\n}\n",
    );
    let exporting = WasmModulePolicy {
        memory: WasmMemoryPolicy::Owned {
            pages: 1,
            export: Some("memory".to_string()),
        },
        ..WasmModulePolicy::closed()
    };
    match wasm::compile_module_with_policy_and_license(&module, &exporting, &permit_unlicensed()) {
        Err(WasmLowerError::ContractSurface(m)) => assert!(m.contains("[TCG-WASM-EXPORT]"), "{m}"),
        other => panic!("a duplicate export must be refused, got {other:?}"),
    }
    // Without the memory export the module is fine.
    validate(&wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compile"));
}

/// `frem_binds_user_fmod.trust_ir`: the object lane calls `fmod` by name for
/// `frem`; a module that DEFINES `fmod` (whatever its linkage or body) would
/// have `frem` bound to that body, so it is refused. A declaration is the
/// library routine and is called.
#[test]
fn frem_never_binds_to_a_module_defined_fmod() {
    let with = |fmod: &str| {
        parse(&format!(
            "functy.0 = (f64, f64) -> (f64)\nfuncty.1 = (i64, i64) -> (i64)\n\n{fmod}\n\
             fn @f(functy.1) {{\nbbentry(%a: i64, %b: i64):\n    %x = sitofp i64 %a to f64\n\
                 %y = sitofp i64 %b to f64\n    %r = frem f64 %x, %y\n\
                 %i = fptosi.sat f64 %r to i64\n    ret %i\n}}\n"
        ))
    };
    let body =
        "(functy.0) {\nbbentry(%a: f64, %b: f64):\n    %r = fadd f64 %a, %b\n    ret %r\n}\n";
    for def in [
        format!("fn @fmod{body}"),
        format!("internal fn @fmod{body}"),
    ] {
        match wasm::compile_object_with_license(&with(&def), &permit_unlicensed()) {
            Err(WasmLowerError::ContractSurface(m)) => assert!(m.contains("`fmod`"), "{m}"),
            other => panic!("frem bound to a defined fmod: {other:?}"),
        }
    }
    let declared = with("fn @fmod(functy.0) {\n}\n");
    wasm::compile_object_with_license(&declared, &permit_unlicensed())
        .expect("a declared fmod is the library routine");
    // The closed module keeps using trust-ir's own helper.
    let defined = with(&format!("fn @fmod{body}"));
    let bytes = wasm::compile_module_with_license(&defined, &permit_unlicensed()).expect("closed");
    agrees(&defined, &bytes, "f", &[(17, 5), (-17, 5), (7, 0)]);
}

// ---- 5. Frame alignment ----

#[test]
fn a_frame_alignment_past_2_pow_30_is_refused_not_a_panic() {
    let alloca = |align: &str| {
        parse(&format!(
            "functy.0 = (i64, i64) -> (i64)\n\n\
             fn @f(functy.0) {{\nbbentry(%a: i64, %b: i64):\n    %c = alloca i64{align}\n\
                 store i64 %a, ptr %c\n    %v = load i64, ptr %c\n    %r = add i64 %v, %b\n    ret %r\n}}\n"
        ))
    };
    let zst = parse(
        "struct @Z { } size=0 align=2147483648 id=0\n\nfuncty.0 = (i64, i64) -> (i64)\n\n\
         fn @f(functy.0) {\nbbentry(%a: i64, %b: i64):\n    %z = alloca struct.0\n\
             %r = add i64 %a, %b\n    ret %r\n}\n",
    );
    for module in [alloca(", align 2147483648"), zst] {
        for result in [
            wasm::compile_module_with_license(&module, &permit_unlicensed()),
            wasm::compile_object_with_license(&module, &permit_unlicensed()),
        ] {
            match result {
                Err(WasmLowerError::FrameLayoutOverflow(m)) => assert!(m.contains("2^30"), "{m}"),
                other => panic!("expected a frame-alignment refusal, got {other:?}"),
            }
        }
    }
    match wasm::compile_module_with_license(&alloca(", align 4294967296"), &permit_unlicensed()) {
        Err(WasmLowerError::FrameLayoutOverflow(m)) => {
            assert!(m.contains("exceeds the wasm32 address space"), "{m}")
        }
        other => panic!("{other:?}"),
    }
    match wasm::compile_module_with_license(&alloca(", align 3"), &permit_unlicensed()) {
        Err(WasmLowerError::InvalidTrustIr(refusal)) => assert!(
            refusal.any(|error| matches!(
                error,
                trust_ir_build::ValidationError::AccessAlignInvalid { align: 3, .. }
            )),
            "{refusal}"
        ),
        other => panic!("{other:?}"),
    }
    let ok = alloca(", align 1073741824");
    let bytes = closed_with(&ok, &owned(4));
    validate(&bytes);
}

// ---- 6. Strict SSA ----

/// `nd2.trust_ir`: an aggregate alias made in one iteration is read in the
/// next, from a block its definition does not dominate.
const ND_ALIAS: &str = r#"
struct @S { : i64 @0, : i64 @8 } size=16 align=8 id=0

functy.0 = (i64, i64) -> (i64)

fn @f(functy.0) {
bbentry(%a: i64, %b: i64):
    %z = const i64 0
    br bbloop(%z)
bbloop(%i: i64):
    %s = make_aggregate struct.0 (%a, %i)
    %first = icmp eq i64 %i, %z
    condbr %first, bbagain, bbout
bbagain:
    %keep = copy struct.0 %s
    %one = const i64 1
    %j = add i64 %i, %one
    br bbloop(%j)
bbout:
    %r = extractfield i64 %keep, 1
    ret %r
}
"#;

/// `nd3.trust_ir`: an `Alloca` pointer escapes the same way.
const ND_ALLOCA: &str = r#"
functy.0 = (i64, i64) -> (i64)

fn @f(functy.0) {
bbentry(%a: i64, %b: i64):
    %z = const i64 0
    br bbloop(%z)
bbloop(%i: i64):
    %c = alloca i64
    %v = add i64 %a, %i
    store i64 %v, ptr %c
    %first = icmp eq i64 %i, %z
    condbr %first, bbagain, bbout
bbagain:
    %keep = copy ptr %c
    %one = const i64 1
    %j = add i64 %i, %one
    br bbloop(%j)
bbout:
    %r = load i64, ptr %keep
    ret %r
}
"#;

fn assert_ill_formed(module: &Module, what: &str) {
    for result in [
        wasm::compile_module_with_license(module, &permit_unlicensed()),
        wasm::compile_object_with_license(module, &permit_unlicensed()),
    ] {
        if let Err(WasmLowerError::InvalidTrustIr(refusal)) = &result {
            assert!(
                refusal.any(|error| match error {
                    trust_ir_build::ValidationError::UseBeforeDefInBlock { .. } =>
                        what == "does not dominate",
                    trust_ir_build::ValidationError::BranchArgTypeMismatch { .. } =>
                        what == "binds",
                    _ => false,
                }),
                "{refusal}"
            );
            continue;
        }
        match result {
            Err(WasmLowerError::IllFormedSsa(m)) => assert!(m.contains(what), "{m}"),
            other => panic!("expected an SSA refusal ({what}), got {other:?}"),
        }
    }
}

#[test]
fn non_dominated_uses_and_mistyped_edge_arguments_are_refused() {
    assert_ill_formed(&parse(ND_ALIAS), "does not dominate");
    assert_ill_formed(&parse(ND_ALLOCA), "does not dominate");
    // A narrow argument bound to a parameter of another narrow type: the
    // canonical carrier forms differ (sign- vs zero-extended).
    assert_ill_formed(
        &parse(
            "functy.0 = (i64, i64) -> (i64)\n\n\
             fn @f(functy.0) {\nbbentry(%a: i64, %b: i64):\n    %x = trunc i64 %a to i8\n    br bbnext(%x)\n\
             bbnext(%y: u16):\n    %r = zext u16 %y to i64\n    ret %r\n}\n",
        ),
        "binds",
    );
    // A memory-carried argument of another size.
    assert_ill_formed(
        &parse(
            "struct @A { : i64 @0 } size=8 align=8 id=0\n\
             struct @B { : i64 @0, : i64 @8 } size=16 align=8 id=1\n\n\
             functy.0 = (i64, i64) -> (i64)\n\n\
             fn @f(functy.0) {\nbbentry(%a: i64, %b: i64):\n    %s = make_aggregate struct.0 (%a)\n\
                 br bbnext(%s)\n\
             bbnext(%t: struct.1):\n    %r = extractfield i64 %t, 1\n    ret %r\n}\n",
        ),
        "binds",
    );
}

// ---- 7. Deep control flow on a small stack ----

/// A debug build's overflow-checked chain (`cb_1000.trust_ir`): every block
/// is the only successor of the previous one, so the dominator tree is a
/// path `n` deep; every overflow edge goes to one shared trap.
fn checked_chain(n: usize) -> String {
    let mut s = String::from(
        "functy.0 = (i64, i64) -> (i64)\n\nfn @chain(functy.0) {\nbb0(%0: i64, %1: i64):\n\
         %2 = const i64 255\n    %3 = and i64 %0, %2\n    br bb1(%3)\n",
    );
    let mut v = 10;
    for i in 1..=n {
        let (x, t, f) = (v, v + 1, v + 2);
        v += 3;
        let _ = writeln!(
            s,
            "bb{i}(%{x}: i64):\n    %{t}, %{f} = add.overflow i64 %{x}, %3\n    condbr %{f}, bb{}, bb{}(%{t})",
            n + 2,
            i + 1
        );
    }
    let _ = writeln!(
        s,
        "bb{}(%{v}: i64):\n    ret %{v}\nbb{}:\n    unreachable\n}}",
        n + 1,
        n + 2
    );
    s
}

/// A chain of `n` if/else diamonds, each joining before the next.
fn diamond_chain(n: usize) -> String {
    let mut s = String::from(
        "functy.0 = (i64, i64) -> (i64)\n\nfn @chain(functy.0) {\nbb0(%0: i64, %1: i64):\n\
         %2 = const i64 1\n    %3 = const i64 0\n    br bb1(%0)\n",
    );
    let mut v = 10;
    for i in 0..n {
        let (h, a, b, j) = (3 * i + 1, 3 * i + 2, 3 * i + 3, 3 * i + 4);
        let (x, bit, c, t1, t2) = (v, v + 1, v + 2, v + 3, v + 4);
        v += 5;
        let _ = write!(
            s,
            "bb{h}(%{x}: i64):\n    %{bit} = and i64 %{x}, %2\n    %{c} = icmp eq i64 %{bit}, %3\n\
             condbr %{c}, bb{a}, bb{b}\nbb{a}:\n    %{t1} = add i64 %{x}, %1\n    br bb{j}(%{t1})\n\
             bb{b}:\n    %{t2} = sub i64 %{x}, %2\n    br bb{j}(%{t2})\n"
        );
    }
    let _ = writeln!(s, "bb{}(%{v}: i64):\n    ret %{v}\n}}", 3 * n + 1);
    s
}

/// One `switch` over `n` sparse case values of `ty`; `pairs` sends two case
/// values to each arm (the MIR shape of `a | b =>`), making every arm a merge
/// child of the switch block.
fn sparse_switch(n: usize, ty: &str, pairs: bool) -> String {
    // A case is a value of the selector's type: at `i32` the multiple wraps to
    // its two's-complement value (1_000_003 is odd, so the cases stay distinct).
    let value = |i: usize| {
        let v = (i as i128 + 1) * 1_000_003;
        if ty == "i32" { v as i32 as i128 } else { v }.to_string()
    };
    let arm = |i: usize| if pairs { i / 2 + 2 } else { i + 2 };
    let arms = if pairs { n / 2 } else { n };
    let mut s =
        "functy.0 = (i64, i64) -> (i64)\n\nfn @sw(functy.0) {\nbb0(%0: i64, %1: i64):\n".to_owned();
    let scrutinee = if ty == "i64" {
        "%0".to_string()
    } else {
        let cast = if ty == "i32" { "trunc" } else { "sext" };
        let _ = writeln!(s, "    %9 = {cast} i64 %0 to {ty}");
        "%9".to_string()
    };
    let cases: Vec<String> = (0..n)
        .map(|i| format!("{}: bb{}", value(i), arm(i)))
        .collect();
    let _ = writeln!(
        s,
        "    switch {scrutinee} [ {} default: bb1 ]",
        cases.join(" ")
    );
    let join = arms + 2;
    let _ = writeln!(s, "bb1:\n    %10 = const i64 -1\n    br bb{join}(%10)");
    for j in 0..arms {
        let _ = writeln!(
            s,
            "bb{}:\n    %{} = const i64 {}\n    br bb{join}(%{})",
            j + 2,
            j + 11,
            j + 7,
            j + 11
        );
    }
    let _ = writeln!(
        s,
        "bb{join}(%{}: i64):\n    ret %{}\n}}",
        arms + 11,
        arms + 11
    );
    s
}

#[test]
fn deep_dominator_trees_and_huge_switches_compile_on_a_small_stack() {
    type ExecutionCase = (String, &'static str, Vec<(i64, i64)>);
    let cases: Vec<ExecutionCase> = vec![
        (
            checked_chain(20_000),
            "chain",
            vec![(0, 0), (3, 0), (255, 0)],
        ),
        (
            diamond_chain(20_000),
            "chain",
            vec![(0, 1), (5, 3), (-9, 2)],
        ),
        (
            sparse_switch(24_000, "i64", false),
            "sw",
            vec![(1_000_003, 0), (24_000 * 1_000_003, 0), (5, 0)],
        ),
        (
            sparse_switch(24_000, "i128", true),
            "sw",
            vec![(2_000_006, 0), (23_999 * 1_000_003, 0), (7, 0)],
        ),
        (
            sparse_switch(24_000, "i32", true),
            "sw",
            vec![(1_000_003, 0), (1_000_003 * 1000, 0), (8, 0)],
        ),
    ];
    for (text, name, inputs) in cases {
        let module = parse(&text);
        let m = module.clone();
        let bytes = on_small_stack(move || {
            wasm::compile_module_with_license(&m, &permit_unlicensed()).map_err(|e| e.to_string())
        })
        .unwrap_or_else(|e| panic!("{name}: {e}"));
        agrees(&module, &bytes, name, &inputs);
        let m = module.clone();
        on_small_stack(move || {
            wasm::compile_object_with_license(&m, &permit_unlicensed()).map_err(|e| e.to_string())
        })
        .unwrap_or_else(|e| panic!("{name} object: {e}"));
    }
}

// ---- 8. Local coalescing has no cliff ----

#[test]
fn large_functions_keep_few_locals() {
    for text in [
        sparse_switch(20_000, "i64", false),
        diamond_chain(7_000),
        checked_chain(8_000),
    ] {
        let module = parse(&text);
        let bytes = on_small_stack(move || {
            wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compile")
        });
        let locals = declared_locals(&bytes);
        assert!(locals < 64, "{locals} locals");
    }
}

/// `wide_u128_locals_refusal.rs` at the trust-ir level: `n` if-guarded
/// 128-bit updates, each in its own diamond. Every 128-bit value owns a frame
/// home; its address local is set where the value is written, so it lives
/// only as long as the value and the function coalesces to a handful of
/// locals (the address locals once stayed live for the whole body, one per
/// home, and the function needed more than the 50,000 engines accept).
fn guarded_wide(n: usize) -> String {
    let mut s = String::from(
        "functy.0 = (i64, i64) -> (i64)\n\nfn @g(functy.0) {\nbbentry(%a: i64, %k: i64):\n\
         %one = const i64 1\n    %zero = const i64 0\n    %w0 = sext i64 %a to i128\n\
         %c = const i128 6364136223846793005\n    br bbh0(%w0)\n",
    );
    for i in 0..n {
        let r = i % 61 + 1;
        let _ = write!(
            s,
            "bbh{i}(%x{i}: i128):\n    %sh{i} = const i64 {}\n    %t{i} = lshr i64 %k, %sh{i}\n\
             %b{i} = and i64 %t{i}, %one\n    %q{i} = icmp ne i64 %b{i}, %zero\n\
             condbr %q{i}, bbu{i}, bbh{}(%x{i})\n\
             bbu{i}:\n    %m{i} = mul i128 %x{i}, %c\n    %rr{i} = const i128 {r}\n\
             %s{i} = lshr i128 %x{i}, %rr{i}\n    %y{i} = xor i128 %m{i}, %s{i}\n    br bbh{}(%y{i})\n",
            i % 64,
            i + 1,
            i + 1
        );
    }
    let _ = writeln!(
        s,
        "bbh{n}(%x{n}: i128):\n    %r = trunc i128 %x{n} to i64\n    ret %r\n}}"
    );
    s
}

#[test]
fn guarded_wide_updates_keep_few_locals() {
    let module = parse(&guarded_wide(1_500));
    let bytes = wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compile");
    let locals = declared_locals(&bytes);
    assert!(locals < 100, "{locals} locals");
    agrees(
        &module,
        &bytes,
        "g",
        &[(3, 0), (-5, -1), (i64::MAX, 0x5555_5555_5555_5555)],
    );
}

// ---- 9. Many simultaneously live memory-carried values ----

/// `gen_live.py`: `n` 128-bit values all live until a final fold.
fn live_wide(n: usize) -> String {
    let mut s = String::from(
        "functy.0 = (i64, i64) -> (i64)\n\nfn @f(functy.0) {\nbbentry(%a: i64, %b: i64):\n\
         %w = sext i64 %a to i128\n    %v0 = sext i64 %b to i128\n",
    );
    for i in 1..=n {
        let _ = writeln!(s, "    %v{i} = add i128 %v{}, %w", i - 1);
    }
    let _ = writeln!(s, "    %x0 = xor i128 %v0, %v1");
    for i in 2..=n {
        let _ = writeln!(s, "    %x{} = xor i128 %x{}, %v{i}", i - 1, i - 2);
    }
    let _ = writeln!(s, "    %r = trunc i128 %x{} to i64\n    ret %r\n}}", n - 1);
    s
}

#[test]
fn many_simultaneously_live_homes_compile_without_quadratic_blowup() {
    // Exact interference (3,001 homes) and live hulls (past 16,384 homes);
    // every value is live at once, so the frame needs 16 bytes each.
    for n in [1_500, 9_000] {
        let module = parse(&live_wide(n));
        let start = std::time::Instant::now();
        let bytes =
            wasm::compile_module_with_policy_and_license(&module, &owned(16), &permit_unlicensed())
                .expect("compile");
        let took = start.elapsed();
        assert!(took.as_secs() < 60, "{n} live values took {took:?}");
        agrees(&module, &bytes, "f", &[(1, 2), (-987_654_321, 123_456_789)]);
    }
}

// ---- 10. Allocations in disjoint scopes ----

/// `frame_disjoint_scopes.rs` at the trust-ir level: two 600,000-byte arrays,
/// each dead before the next is made. Sharing one slot, the frame fits a
/// 1 MiB memory; one after the other it would not.
const DISJOINT: &str = r#"
type ty.0 = u8

functy.0 = (i64, i64) -> (i64)
functy.1 = (ptr, i64) -> (i64)

internal fn @touch(functy.1) {
bbentry(%p: ptr, %k: i64):
    %n = const i64 600000
    %m = urem i64 %k, %n
    %mi = trunc i64 %m to i32
    %pi = ptrtoint ptr %p to i32
    %ai = add i32 %pi, %mi
    %a = inttoptr i32 %ai to ptr
    %kb = trunc i64 %k to u8
    store u8 %kb, ptr %a
    %v = load u8, ptr %a
    %r = zext u8 %v to i64
    ret %r
}

fn @two_scopes(functy.0) {
bbentry(%k: i64, %b: i64):
    %x = alloca [ty.0 x 600000]
    %rx = call @func.0(%x, %k)
    %y = alloca [ty.0 x 600000]
    %one = const i64 1
    %k1 = add i64 %k, %one
    %ry = call @func.0(%y, %k1)
    %r = add i64 %rx, %ry
    ret %r
}

fn @overlapping(functy.0) {
bbentry(%k: i64, %b: i64):
    %x = alloca i64
    %y = alloca i64
    store i64 %k, ptr %x
    store i64 %b, ptr %y
    %vx = load i64, ptr %x
    %vy = load i64, ptr %y
    %c = const i64 1000
    %m = mul i64 %vx, %c
    %r = add i64 %m, %vy
    ret %r
}
"#;

#[test]
fn allocations_in_disjoint_scopes_share_frame_bytes() {
    let module = parse(DISJOINT);
    let bytes = closed_with(&module, &owned(16));
    agrees(
        &module,
        &bytes,
        "two_scopes",
        &[(3, 0), (599_999, 0), (1_000_000, 0)],
    );
    agrees(&module, &bytes, "overlapping", &[(3, 4), (-1, 7)]);
    // The frame is one array (plus bookkeeping), never two.
    let object = wasm::compile_object_with_license(&module, &permit_unlicensed()).expect("object");
    if let Some(linked) = link(&[&object]) {
        agrees(&module, &linked, "two_scopes", &[(3, 0), (123_456, 0)]);
    }
}

// ---- 11. Lifted and named wasm32-only refusals ----

/// `atomic128_wasm32.trust_ir`, extended to every read-modify-write.
fn atomic128(op: &str) -> String {
    format!(
        "functy.0 = (i64, i64) -> (i64)\n\n\
         fn @f(functy.0) {{\nbbentry(%a: i64, %b: i64):\n    %x = sext i64 %a to i128\n\
             %y = sext i64 %b to i128\n    %c = alloca i128\n    store i128 %x, ptr %c\n\
             %old = atomicrmw {op} seq_cst i128 ptr %c, %y\n\
             %now = atomic_load seq_cst i128, ptr %c\n\
             %got, %ok = cmpxchg i128 ptr %c, %now, %x seq_cst seq_cst\n\
             %seen = load i128, ptr %c\n    %s1 = add i128 %old, %got\n\
             %k = const i128 1000000\n    %s2 = mul i128 %s1, %k\n    %s3 = add i128 %s2, %seen\n\
             %okw = zext bool %ok to i128\n    %s4 = add i128 %s3, %okw\n\
             %hi = const i128 64\n    %h = ashr i128 %now, %hi\n    %s5 = xor i128 %s4, %h\n\
             %r = trunc i128 %s5 to i64\n    ret %r\n}}\n"
    )
}

#[test]
fn wide_atomics_and_zero_sized_enum_lanes_compile_and_closures_are_named() {
    let inputs = [(0, 0), (5, -7), (-1, 1), (i64::MAX, i64::MIN), (123, 123)];
    for op in [
        "xchg", "add", "sub", "and", "or", "xor", "max", "min", "umax", "umin",
    ] {
        let module = parse(&atomic128(op));
        let bytes = wasm::compile_module_with_license(&module, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("{op}: {e}"));
        agrees(&module, &bytes, "f", &inputs);
    }

    // `zst_enum_lane_wasm32.trust_ir`: lane 2 is `()` at different offsets
    // in the two variants, which a zero-sized lane cannot make ambiguous.
    let zst = parse(
        "enum @E repr(u8) { A(u8, ()) = 0, B(u64, ()) = 1 } id=0\n\n\
         functy.0 = (i64, i64) -> (i64)\n\n\
         fn @f(functy.0) {\nbbentry(%a: i64, %b: i64):\n    %e = const enum.0 { 0, 7, phantomdata }\n\
             %u = extractfield () %e, 2\n    %x = extractfield u8 %e, 1\n\
             %r = zext u8 %x to i64\n    ret %r\n}\n",
    );
    let bytes = wasm::compile_module_with_license(&zst, &permit_unlicensed())
        .expect("a zero-sized lane is not ambiguous");
    agrees(&zst, &bytes, "f", &[(0, 0)]);

    // `closure_wasm32.trust_ir`: refused by name.
    let closure = parse(
        "functy.0 = (i64, i64) -> (i64)\nfuncty.1 = (i64) -> (i64)\nfuncty.2 = (i64, i64) -> (i64)\n\n\
         closure_ty functy.1 { i64 }\n\n\
         fn @body(functy.2) {\nbbentry(%c: i64, %x: i64):\n    %t = const i64 10\n\
             %m = mul i64 %c, %t\n    %r = add i64 %m, %x\n    ret %r\n}\n\n\
         fn @f(functy.0) {\nbbentry(%a: i64, %b: i64):\n    %k = const closure.0 closure<func.0>{ 5 }\n\
             %c = insertfield closure.0 %k, 0, %a\n    %r = call_indirect %c(functy.1)(%b)\n    ret %r\n}\n",
    );
    for result in [
        wasm::compile_module_with_license(&closure, &permit_unlicensed()),
        wasm::compile_object_with_license(&closure, &permit_unlicensed()),
    ] {
        if let Err(WasmLowerError::InvalidTrustIr(refusal)) = &result {
            assert!(
                refusal.any(|error| matches!(
                    error,
                    trust_ir_build::ValidationError::UnlowerableForCodegen { .. }
                )),
                "{refusal}"
            );
            continue;
        }
        match result {
            Err(e) => assert!(e.to_string().contains("[TCG-WASM-CLOSURE]"), "{e}"),
            Ok(_) => panic!("a closure value compiled"),
        }
    }
}

/// A memory-carried lane (`i128`, a nested tuple) read through a pointer, then
/// overwritten through the same pointer by explicit stores and a callee
/// while the loaded value is still live. Each load must snapshot the bytes
/// at the read, not at the use. The lane once aliased the pointee instead (`let old = p.b; p.b =
/// n; f(old)` over a `&mut` struct with a `u128` field handed `f` the value
/// `n`, which made std's `RangeInclusive<u128>` reversed folds skip `end`).
const READ_THROUGH: &str = "\
functy.0 = (i64, i64) -> (i64)
functy.1 = (ptr, i128) -> ()

fn @bump(functy.1) {
bbentry(%p: ptr, %v: i128):
    %offset = const i32 16
    %field = gep inbounds u8, ptr %p, %offset
    store i128 %v, ptr %field
    ret
}

fn @insert(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = sext i64 %a to i128
    %y = sext i64 %b to i128
    %c = alloca (i128, i128, bool)
    %offset = const i32 16
    %field = gep inbounds u8, ptr %c, %offset
    store i128 %x, ptr %c
    store i128 %y, ptr %field
    %old = load i128, ptr %field
    %one = const i128 1
    %n = sub i128 %old, %one
    store i128 %n, ptr %field
    %t = const bool true
    %bool_offset = const i32 32
    %flag = gep inbounds u8, ptr %c, %bool_offset
    store bool %t, ptr %flag
    %now = load i128, ptr %field
    %k = const i128 1000
    %s = mul i128 %old, %k
    %s2 = add i128 %s, %now
    %r = trunc i128 %s2 to i64
    ret %r
}

fn @stored(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = sext i64 %a to i128
    %y = sext i64 %b to i128
    %c = alloca (i128, i128, bool)
    %offset = const i32 16
    %field = gep inbounds u8, ptr %c, %offset
    store i128 %x, ptr %c
    %old = load i128, ptr %c
    store i128 %y, ptr %c
    %now = load i128, ptr %c
    %k = const i128 1000
    %s = mul i128 %old, %k
    %s2 = add i128 %s, %now
    %r = trunc i128 %s2 to i64
    ret %r
}

fn @called(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = sext i64 %a to i128
    %y = sext i64 %b to i128
    %c = alloca (i128, i128, bool)
    %offset = const i32 16
    %field = gep inbounds u8, ptr %c, %offset
    store i128 %x, ptr %field
    %old = load i128, ptr %field
    call @func.0(%c, %y)
    %now = load i128, ptr %field
    %k = const i128 1000
    %s = mul i128 %old, %k
    %s2 = add i128 %s, %now
    %r = trunc i128 %s2 to i64
    ret %r
}

fn @nested(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = sext i64 %a to i128
    %y = sext i64 %b to i128
    %c = alloca (i64, (i128, i64))
    %offset = const i32 16
    %field = gep inbounds u8, ptr %c, %offset
    %in = const (i128, i64) { 0, 0 }
    %in1 = insertfield (i128, i64) %in, 0, %x
    store (i128, i64) %in1, ptr %field
    %old = load (i128, i64), ptr %field
    %in2 = insertfield (i128, i64) %in, 0, %y
    store (i128, i64) %in2, ptr %field
    %ow = extractfield i128 %old, 0
    %now = load (i128, i64), ptr %field
    %nw = extractfield i128 %now, 0
    %k = const i128 1000
    %s = mul i128 %ow, %k
    %s2 = add i128 %s, %nw
    %r = trunc i128 %s2 to i64
    ret %r
}
";

const LEGACY_READ_THROUGH: &str = "\
functy.0 = (i64, i64) -> (i64)
functy.1 = (ptr, i128) -> ()

fn @bump(functy.1) {
bbentry(%p: ptr, %v: i128):
    %w = insertfield (i128, i128, bool) %p, 1, %v
    ret
}

fn @insert(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = sext i64 %a to i128
    %y = sext i64 %b to i128
    %c = alloca (i128, i128, bool)
    %w0 = insertfield (i128, i128, bool) %c, 0, %x
    %w1 = insertfield (i128, i128, bool) %c, 1, %y
    %old = extractfield (i128, i128, bool) %c, 1
    %one = const i128 1
    %n = sub i128 %old, %one
    %w2 = insertfield (i128, i128, bool) %c, 1, %n
    %t = const bool true
    %w3 = insertfield (i128, i128, bool) %c, 2, %t
    %now = extractfield (i128, i128, bool) %c, 1
    %k = const i128 1000
    %s = mul i128 %old, %k
    %s2 = add i128 %s, %now
    %r = trunc i128 %s2 to i64
    ret %r
}

fn @stored(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = sext i64 %a to i128
    %y = sext i64 %b to i128
    %c = alloca (i128, i128, bool)
    %w0 = insertfield (i128, i128, bool) %c, 0, %x
    %old = extractfield (i128, i128, bool) %c, 0
    store i128 %y, ptr %c
    %now = extractfield (i128, i128, bool) %c, 0
    %k = const i128 1000
    %s = mul i128 %old, %k
    %s2 = add i128 %s, %now
    %r = trunc i128 %s2 to i64
    ret %r
}

fn @called(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = sext i64 %a to i128
    %y = sext i64 %b to i128
    %c = alloca (i128, i128, bool)
    %w1 = insertfield (i128, i128, bool) %c, 1, %x
    %old = extractfield (i128, i128, bool) %c, 1
    call @func.0(%c, %y)
    %now = extractfield (i128, i128, bool) %c, 1
    %k = const i128 1000
    %s = mul i128 %old, %k
    %s2 = add i128 %s, %now
    %r = trunc i128 %s2 to i64
    ret %r
}

fn @nested(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = sext i64 %a to i128
    %y = sext i64 %b to i128
    %c = alloca (i64, (i128, i64))
    %in = const (i128, i64) { 0, 0 }
    %in1 = insertfield (i128, i64) %in, 0, %x
    %w0 = insertfield (i64, (i128, i64)) %c, 1, %in1
    %old = extractfield (i64, (i128, i64)) %c, 1
    %in2 = insertfield (i128, i64) %in, 0, %y
    %w1 = insertfield (i64, (i128, i64)) %c, 1, %in2
    %ow = extractfield (i128, i64) %old, 0
    %now = extractfield (i64, (i128, i64)) %c, 1
    %nw = extractfield (i128, i64) %now, 0
    %k = const i128 1000
    %s = mul i128 %ow, %k
    %s2 = add i128 %s, %nw
    %r = trunc i128 %s2 to i64
    ret %r
}
";

#[test]
fn a_memory_carried_lane_read_through_a_pointer_is_a_copy_not_an_alias() {
    let invalid = parse(LEGACY_READ_THROUGH);
    for result in [
        wasm::compile_module_with_license(&invalid, &permit_unlicensed()),
        wasm::compile_object_with_license(&invalid, &permit_unlicensed()),
    ] {
        let err = result.expect_err("pointer-overloaded fields remain invalid");
        assert!(format!("{err:?}").contains("FieldAccessInvalid"), "{err}");
    }
    let module = parse(READ_THROUGH);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let bytes = wasm::compile_module_with_license(&module, &permit_unlicensed())
        .expect("read-through lanes compile");
    validate(&bytes);
    // Retain the independent arithmetic oracle: `old` is the loaded lane
    // before the overwrite, `now` after it.
    let inputs = [
        (0, 0),
        (5, -7),
        (-1, 1),
        (i64::MAX, i64::MIN),
        (123, 123),
        (1, 3),
    ];
    let expect = |name: &str, a: i64, b: i64| -> i64 {
        let (a, b) = (i128::from(a), i128::from(b));
        let (old, now) = match name {
            "insert" => (b, b - 1),
            _ => (a, b),
        };
        (old * 1000 + now) as i64
    };
    for name in ["insert", "stored", "called", "nested"] {
        let Some(got) = run_wasm(&bytes, name, &inputs) else {
            eprintln!("SKIP {name}: node is absent");
            continue;
        };
        for (&(a, b), got) in inputs.iter().zip(&got) {
            assert_eq!(*got, Some(expect(name, a, b)), "{name}({a}, {b})");
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
