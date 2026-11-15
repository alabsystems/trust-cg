// trust-cg-codegen/tests/wasm_p5_argpromo.rs - wasm32 lane: argument promotion
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Argument promotion in the trust-ir mid-end (`trust_cg_irmid`,
//! `passes/argpromo.rs`) on the wasm32 lane: a caller's frame slot passed to
//! a callee the inliner leaves (here every callee is in the producer's
//! never-inline side table) is passed as values to a clone that returns the
//! bytes it writes, and scalar replacement then removes the caller's frame.
//!
//! * the forms promoted: a read-only pointer and an out-pointer of one call
//!   (`pair`), typed scalar reads through a tuple
//!   pointer (`sum3`), an array passed by address (`agg`), an in-out pointer
//!   called twice (`bump`, the second call reads what the first copied out),
//!   writes through an integer address chain (`chain`) and a 128-bit field
//!   (`wide`);
//! * a slot whose address also reaches a block argument stays a pointer and
//!   the original callee stays called (`e_keep`, whose out-pointer alone is
//!   promoted: a second clone of `pair`), beside its clones;
//! * at O2 the linked object's promoted exports have no frame (no global
//!   access) and the evidence names the pass with no rollback or fallback;
//! * every form — O0 and O2 closed modules (whose callees are not hidden: a
//!   closed module has no emitter for hidden visibility, so nothing is
//!   promoted there), the sized closed module and the linked object — agrees
//!   with the trust-ir reference interpreter, run on
//!   the differential's view of the input (which reads a pointer passed for
//!   an aggregate as the aggregate's bytes), in node.
//!
//! Node is required to execute the wasm and `wasm-ld` (`WASM_LD`) to link the
//! object; the absence of either is a loud SKIP.
//!
//! The entries this test drives (`compile_object_with_evidence_license_options_hints`
//! with `WasmInlineHints`, `compile_module_with_evidence_policy_license_options`,
//! `compile_sized_closed_module_with_evidence_license_options`), `WasmOptOptions`,
//! the evidence it reads (`mid_end`) and `trust_ir_mid_tv::interpretable_module`
//! are provisional surfaces pending the owner's sign-off: this test follows
//! them if they change, and is not a contract for their shape.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{self, WasmInlineHints, WasmModulePolicy, WasmOptOptions};
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

const CALLEES: &[&str] = &[
    "pair.tcg.crate.00000000000000a1",
    "sum3.tcg.crate.00000000000000a2",
    "agg.tcg.crate.00000000000000a3",
    "bump.tcg.crate.00000000000000a4",
    "chain.tcg.crate.00000000000000a5",
    "wide.tcg.crate.00000000000000a6",
];

/// The exports promoted at O2 (every slot they pass dissolves).
const PROMOTED: &[&str] = &[
    "e_pair", "e_twice", "e_sum3", "e_agg", "e_bump", "e_chain", "e_wide",
];

const NAMES: &[&str] = &[
    "e_pair", "e_twice", "e_sum3", "e_agg", "e_bump", "e_chain", "e_wide", "e_keep",
];

const HEADER: &str = "module \"p5a\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
type ty.0 = i64\n\n\
functy.0 = (i64, i64) -> (i64)\n\
functy.1 = (ptr, ptr) -> ()\n\
functy.2 = (&(i32, f32, i64)) -> (i64)\n\
functy.3 = ([ty.0 x 2]) -> (i64)\n\
functy.4 = (ptr) -> ()\n\
functy.5 = (ptr, i64) -> ()\n\
functy.6 = (ptr) -> (i128)\n\n";

/// The callees, in function-index order (`func.0` .. `func.5`).
const CALLEE_BODIES: &str = "fn @pair.tcg.crate.00000000000000a1(functy.1) {
    ; #visibility: hidden
bbentry(%out: ptr, %in: ptr):
    %x = load i64, ptr %in
    %c8 = const i32 8
    %ip = gep inbounds u8, ptr %in, %c8
    %y = load i64, ptr %ip
    %s = add i64 %x, %y
    %t = xor i64 %x, %y
    store i64 %s, ptr %out
    %op = gep inbounds u8, ptr %out, %c8
    store i64 %t, ptr %op
    ret
}

fn @sum3.tcg.crate.00000000000000a2(functy.2) {
    ; #visibility: hidden
bbentry(%p: &(i32, f32, i64)):
    %a = load i32, ptr %p
    %four = const usize 4
    %bp = gep u8, ptr %p, %four
    %b = load f32, ptr %bp
    %eight = const usize 8
    %cp = gep u8, ptr %p, %eight
    %c = load i64, ptr %cp
    %aw = sext i32 %a to i64
    %bw = fptosi.sat f32 %b to i64
    %s = add i64 %aw, %bw
    %t = mul i64 %s, %c
    ret %t
}

fn @agg.tcg.crate.00000000000000a3(functy.3) {
    ; #visibility: hidden
bbentry(%v: [ty.0 x 2]):
    %zero = const usize 0
    %one = const usize 1
    %x = extractelement i64 %v, %zero
    %y = extractelement i64 %v, %one
    %m = mul i64 %x, %y
    %r = sub i64 %m, %x
    ret %r
}

fn @bump.tcg.crate.00000000000000a4(functy.4) {
    ; #visibility: hidden
bbentry(%p: ptr):
    %x = load i64, ptr %p
    %c1 = const i64 1
    %x1 = add i64 %x, %c1
    store i64 %x1, ptr %p
    %c8 = const i32 8
    %q = gep inbounds u8, ptr %p, %c8
    %y = load i32, ptr %q
    %y2 = add i32 %y, %y
    store i32 %y2, ptr %q
    ret
}

fn @chain.tcg.crate.00000000000000a5(functy.5) {
    ; #visibility: hidden
bbentry(%p: ptr, %x: i64):
    %pi = ptrtoint ptr %p to i32
    %c8 = const i32 8
    %qi = add i32 %pi, %c8
    %q = inttoptr i32 %qi to ptr
    store i64 %x, ptr %q
    %c3 = const i64 3
    %y = mul i64 %x, %c3
    store i64 %y, ptr %p
    ret
}

fn @wide.tcg.crate.00000000000000a6(functy.6) {
    ; #visibility: hidden
bbentry(%p: ptr):
    %v = load i128, ptr %p
    %c3 = const i128 3
    %m = mul i128 %v, %c3
    ret %m
}
";

/// The exported `(i64, i64) -> i64` callers: name and body after the entry
/// block's label.
const CALLERS: &[(&str, &str)] = &[
    (
        "e_pair",
        "    %in = alloca [ty.0 x 2], align 8
    %out = alloca [ty.0 x 2], align 8
    store i64 %a, ptr %in
    %c8 = const i32 8
    %in1 = gep inbounds u8, ptr %in, %c8
    store i64 %b, ptr %in1
    call @func.0(%out, %in)
    %s = load i64, ptr %out
    %out1 = gep inbounds u8, ptr %out, %c8
    %t = load i64, ptr %out1
    %c3 = const i64 3
    %t3 = mul i64 %t, %c3
    %r = sub i64 %s, %t3
    ret %r
",
    ),
    (
        "e_twice",
        "    %in = alloca [ty.0 x 2], align 8
    %out = alloca [ty.0 x 2], align 8
    store i64 %a, ptr %in
    %c8 = const i32 8
    %in1 = gep inbounds u8, ptr %in, %c8
    store i64 %b, ptr %in1
    call @func.0(%out, %in)
    %s = load i64, ptr %out
    %s2 = add i64 %s, %a
    store i64 %s2, ptr %in
    call @func.0(%out, %in)
    %out1 = gep inbounds u8, ptr %out, %c8
    %t = load i64, ptr %out1
    %u = load i64, ptr %out
    %r = xor i64 %t, %u
    ret %r
",
    ),
    (
        "e_sum3",
        "    %s = alloca [ty.0 x 2], align 8
    %a32 = trunc i64 %a to i32
    store i32 %a32, ptr %s
    %c4 = const i32 4
    %s4 = gep inbounds u8, ptr %s, %c4
    %bf = sitofp i64 %b to f32
    store f32 %bf, ptr %s4
    %c8 = const i32 8
    %s8 = gep inbounds u8, ptr %s, %c8
    %ab = mul i64 %a, %b
    store i64 %ab, ptr %s8
    %p = ptrtoptr ptr %s to &(i32, f32, i64)
    %r = call @func.1(%p)
    ret %r
",
    ),
    (
        "e_agg",
        "    %s = alloca [ty.0 x 2], align 8
    store i64 %a, ptr %s
    %c8 = const i32 8
    %s8 = gep inbounds u8, ptr %s, %c8
    %bb = add i64 %b, %b
    store i64 %bb, ptr %s8
    %value = load [ty.0 x 2], ptr %s
    %r = call @func.2(%value)
    ret %r
",
    ),
    (
        "e_bump",
        "    %s = alloca [ty.0 x 2], align 8
    store i64 %a, ptr %s
    %c8 = const i32 8
    %s8 = gep inbounds u8, ptr %s, %c8
    %b32 = trunc i64 %b to i32
    store i32 %b32, ptr %s8
    call @func.3(%s)
    call @func.3(%s)
    %x = load i64, ptr %s
    %y = load i32, ptr %s8
    %yw = sext i32 %y to i64
    %r = add i64 %x, %yw
    ret %r
",
    ),
    (
        "e_chain",
        "    %s = alloca [ty.0 x 2], align 8
    call @func.4(%s, %a)
    %x = load i64, ptr %s
    %c8 = const i32 8
    %s8 = gep inbounds u8, ptr %s, %c8
    %y = load i64, ptr %s8
    %xy = sub i64 %x, %y
    %r = xor i64 %xy, %b
    ret %r
",
    ),
    (
        "e_wide",
        "    %s = alloca i128, align 16
    %v = sext i64 %a to i128
    %c64 = const i128 64
    %sh = shl i128 %v, %c64
    %bz = zext i64 %b to i128
    %w = or i128 %sh, %bz
    store i128 %w, ptr %s
    %m = call @func.5(%s)
    %lo = trunc i128 %m to i64
    %hs = lshr i128 %m, %c64
    %hi = trunc i128 %hs to i64
    %r = xor i64 %lo, %hi
    ret %r
",
    ),
    (
        "e_keep",
        "    %in = alloca [ty.0 x 2], align 8
    %out = alloca [ty.0 x 2], align 8
    store i64 %a, ptr %in
    %c8 = const i32 8
    %in1 = gep inbounds u8, ptr %in, %c8
    store i64 %b, ptr %in1
    br bbcall(%in)
bbcall(%q: ptr):
    call @func.0(%out, %q)
    %s = load i64, ptr %out
    %out1 = gep inbounds u8, ptr %out, %c8
    %t = load i64, ptr %out1
    %r = add i64 %s, %t
    ret %r
",
    ),
];

/// Rename `%name` values and `bbname` blocks to the text format's numeric
/// spellings, per function, in order of first appearance.
fn number_names(text: &str) -> String {
    use std::collections::HashMap;
    use std::fmt::Write as _;
    let mut out = String::with_capacity(text.len());
    let mut values: HashMap<String, usize> = HashMap::new();
    let mut blocks: HashMap<String, usize> = HashMap::new();
    for line in text.lines() {
        if line.starts_with("fn ") {
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

/// The program; `hidden` keeps the callees' hidden visibility, which a
/// closed module refuses (it has no emitter for it), so a closed module's
/// callees are default-visibility symbols argument promotion leaves alone.
fn program_with(hidden: bool) -> Module {
    let mut text = String::from(HEADER);
    if hidden {
        text.push_str(CALLEE_BODIES);
    } else {
        text.push_str(&CALLEE_BODIES.replace("    ; #visibility: hidden\n", ""));
    }
    for (name, body) in CALLERS {
        text.push_str(&format!(
            "\nfn @{name}(functy.0) {{\nbbentry(%a: i64, %b: i64):\n{body}}}\n"
        ));
    }
    let text = number_names(&text);
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("the test program does not parse: {e}\n{text}"));
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "valid argument-promotion fixture: {errors:?}"
    );
    module
}

const ROWS: &[(i64, i64)] = &[
    (0, 0),
    (1, 2),
    (-3, 7),
    (40, -9),
    (1 << 40, 3),
    (-(1 << 33), (1 << 31) - 1),
    (i64::MAX, 1),
    (i64::MIN, -1),
    (123_456_789, 987_654),
];

fn interpret(view: &Module, name: &str, a: i64, b: i64) -> i64 {
    let f = view.function_by_name(name).expect("function");
    let args = [a, b].map(|v| InterpretValue::int(Ty::I64, i128::from(v)).expect("i64"));
    let out = Interpreter::with_module(view)
        .with_options(InterpretOptions {
            fuel: 100_000,
            max_call_depth: 16,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, args)
        .unwrap_or_else(|e| panic!("the interpreter runs {name}({a}, {b}): {e}"));
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => i.as_signed() as i64,
        other => panic!("{name} returned {other:?}"),
    }
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

fn scratch(tag: &str) -> PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("tcg_wasm_p5a_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Every export of `NAMES` on every row, in node; `None` when node is absent.
fn run(bytes: &[u8]) -> Option<Vec<Vec<i64>>> {
    let Some(node) = node() else {
        eprintln!("SKIP: node not found; the module was not executed");
        return None;
    };
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
    let dir = scratch("run");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let rows: Vec<String> = ROWS
        .iter()
        .map(|(a, b)| format!("[\"{a}\",\"{b}\"]"))
        .collect();
    let js = format!(
        "const fs = require('fs');\n\
         const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
         const imports = {{}};\n\
         for (const i of WebAssembly.Module.imports(m)) {{ imports[i.module] ??= {{}}; }}\n\
         const inst = new WebAssembly.Instance(m, imports);\n\
         const rows = [{}].map(([a, b]) => [BigInt(a), BigInt(b)]);\n\
         const out = {}.map((n) => rows.map(([a, b]) => inst.exports[n](a, b).toString()));\n\
         process.stdout.write(JSON.stringify(out));\n",
        rows.join(","),
        serde_json::to_string(NAMES).unwrap()
    );
    std::fs::write(dir.join("run.js"), js).unwrap();
    let out = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .output()
        .expect("run node");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.status.success(),
        "node failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let cols: Vec<Vec<String>> = serde_json::from_slice(&out.stdout).expect("node JSON");
    Some(
        cols.into_iter()
            .map(|c| c.into_iter().map(|v| v.parse().expect("i64")).collect())
            .collect(),
    )
}

fn assert_agrees(tag: &str, bytes: &[u8], view: &Module) {
    let Some(got) = run(bytes) else {
        return;
    };
    for (name, col) in NAMES.iter().zip(got) {
        let want: Vec<i64> = ROWS
            .iter()
            .map(|&(a, b)| interpret(view, name, a, b))
            .collect();
        assert_eq!(col, want, "{tag}: {name} disagrees with the interpreter");
    }
}

/// The global reads and writes in the body of export `name`.
fn global_accesses(bytes: &[u8], name: &str) -> usize {
    let mut index = None;
    let mut imported = 0u32;
    let mut bodies = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        match payload.expect("parse") {
            wasmparser::Payload::ImportSection(r) => {
                for import in r {
                    if matches!(import.expect("import").ty, wasmparser::TypeRef::Func(_)) {
                        imported += 1;
                    }
                }
            }
            wasmparser::Payload::ExportSection(r) => {
                for e in r {
                    let e = e.expect("export");
                    if e.name == name && e.kind == wasmparser::ExternalKind::Func {
                        index = Some(e.index);
                    }
                }
            }
            wasmparser::Payload::CodeSectionEntry(body) => bodies.push(body),
            _ => {}
        }
    }
    let index = (index.unwrap_or_else(|| panic!("no export {name}")) - imported) as usize;
    bodies[index]
        .get_operators_reader()
        .expect("ops")
        .into_iter()
        .filter(|op| {
            matches!(
                op,
                Ok(wasmparser::Operator::GlobalGet { .. } | wasmparser::Operator::GlobalSet { .. })
            )
        })
        .count()
}

fn options(level: OptLevel, mid_end: bool) -> WasmOptOptions {
    let mut options = WasmOptOptions::at(level);
    options.mid_end = mid_end;
    options
}

fn closed(module: &Module, opts: WasmOptOptions) -> (Vec<u8>, wasm::WasmCompileEvidence) {
    wasm::compile_module_with_evidence_policy_license_options(
        module,
        &WasmModulePolicy::closed(),
        &permit_unlicensed(),
        opts,
    )
    .expect("compile the closed module")
}

fn program() -> Module {
    program_with(true)
}

#[test]
fn closed_modules_agree_with_the_interpreter() {
    let module = program_with(false);
    let view = trust_cg_verify::trust_ir_mid_tv::interpretable_module(&module);
    let (o0, _) = closed(&module, options(OptLevel::O0, true));
    assert_agrees("O0", &o0, &view);
    for mid_end in [false, true] {
        let (o2, evidence) = closed(&module, options(OptLevel::O2, mid_end));
        assert!(
            evidence.local_emission.fallbacks.is_empty(),
            "{:?}",
            evidence.local_emission.fallbacks
        );
        if mid_end {
            assert_eq!(
                evidence.mid_end.rollback_count(),
                0,
                "{:?}",
                evidence.mid_end.rollbacks
            );
            assert!(
                evidence.mid_end.fallback.is_none(),
                "{:?}",
                evidence.mid_end.fallback
            );
        }
        assert_agrees(if mid_end { "O2" } else { "O2 lane-only" }, &o2, &view);
    }
    let (sized, _) = wasm::compile_sized_closed_module_with_evidence_license_options(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2, true),
    )
    .expect("compile the sized closed module");
    assert_agrees("sized O2", &sized, &view);
}

#[test]
fn the_object_passes_promoted_slots_by_value_and_links() {
    let module = program();
    let view = trust_cg_verify::trust_ir_mid_tv::interpretable_module(&module);
    let hints = WasmInlineHints {
        never_inline: CALLEES.iter().map(|s| s.to_string()).collect(),
        ..WasmInlineHints::default()
    };
    let (object, evidence) = wasm::compile_object_with_evidence_license_options_hints(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2, true),
        &hints,
    )
    .expect("compile the object");
    let mid = &evidence.mid_end;
    assert!(mid.applied, "{mid:?}");
    assert!(mid.fallback.is_none(), "{:?}", mid.fallback);
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    let argpromo = mid
        .passes
        .iter()
        .find(|p| p.name == "argpromo")
        .expect("argpromo");
    assert_eq!(
        argpromo.functions_changed,
        PROMOTED.len() + 1,
        "every caller, `e_keep` for its out-pointer alone: {argpromo:?}"
    );
    assert_eq!(
        argpromo.refinements,
        PROMOTED.len() + 3,
        "one site per caller, two in e_twice and e_bump: {argpromo:?}"
    );
    assert!(
        evidence.local_emission.fallbacks.is_empty(),
        "{:?}",
        evidence.local_emission.fallbacks
    );
    let Some(ld) = wasm_ld() else {
        eprintln!("SKIP: wasm-ld not found (set WASM_LD); the object was not linked");
        return;
    };
    let dir = scratch("link");
    std::fs::write(dir.join("m0.o"), &object).unwrap();
    let out = Command::new(&ld)
        .args([
            "--no-entry",
            "--export-dynamic",
            "--stack-first",
            "-z",
            "stack-size=1048576",
            "-o",
        ])
        .arg(dir.join("m.wasm"))
        .arg(dir.join("m0.o"))
        .output()
        .expect("run wasm-ld");
    assert!(
        out.status.success(),
        "wasm-ld refused the object: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let linked = std::fs::read(dir.join("m.wasm")).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    for name in PROMOTED {
        assert_eq!(
            global_accesses(&linked, name),
            0,
            "linked O2 `{name}` has no frame"
        );
    }
    assert!(
        global_accesses(&linked, "e_keep") > 0,
        "`e_keep`'s slot escapes to a block argument and keeps its frame"
    );
    assert_agrees("linked O2", &linked, &view);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
