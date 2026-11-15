// trust-cg-codegen/tests/wasm_p8_loops.rs - wasm32 lane: the loop passes
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The trust-ir mid-end's loop passes (`trust_cg_irmid`, P8 stage A) on the
//! wasm32 lane:
//!
//! * at O2 the counted reductions `sum` (a `u32` sum of the induction
//!   variable), `sum64` (a `u64` sum of its zero extension, through
//!   `add.overflow` with a dead flag) and `weighted` (an `!=` exit, a
//!   subtracted `3 * i` and a counter) are emitted without a `loop`, while
//!   `hoist` (a geometric accumulator) keeps its loop and loses its
//!   invariant parameter and product to loop-invariant code motion; at O0
//!   every function keeps its loop;
//! * the evidence names closed-form induction on the three reductions,
//!   invariant code motion on `hoist`, and no rollback;
//! * every form — O0 and O2, closed, sized and linked — agrees with the
//!   trust-ir reference interpreter in node;
//! * round 14's passes on a second program: `table` (a slot walked by a
//!   pointer from one past its end) and `bits` (a counted loop over the bits
//!   of an argument) are fully unrolled at O2, `table`'s slot dissolving
//!   with its loop; `rowsum` (a sum over a slot by index whose length,
//!   `7 - (n & 7)`, no interval derivation bounds)
//!   keeps its loop and its element address becomes a pointer induction
//!   variable; `twoslots` (a load of one observed slot in a loop that stores
//!   only to another) has the load hoisted by invariant code motion's tier
//!   (b); every form agrees with the interpreter.
//!
//! Node is required to execute the wasm and `wasm-ld` (`WASM_LD`) to link the
//! object; the absence of either is a loud SKIP.
//!
//! The entries this test drives (`compile_module_with_evidence_policy_license_options`,
//! `compile_sized_closed_module_with_evidence_license_options`,
//! `compile_object_with_evidence_license_options`), `WasmOptOptions::mid_end`
//! and the `mid_end` evidence it reads (`IrmidReport`'s pass statistics and
//! rollbacks, the pass names `loop_cf`, `licm`, `unroll` and `iv_sr`) are
//! provisional surfaces
//! pending the owner's sign-off: this test follows them if they change, and
//! is not a contract for their shape.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{self, WasmModulePolicy, WasmOptOptions};
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

const PROGRAM: &str = "module \"p8\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = (i32, i32) -> (i32)\n\n\
fn @sum(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = bitcast i32 %0 to u32\n\
\x20   %3 = bitcast i32 %1 to u32\n\
\x20   %4 = const u32 1023\n\
\x20   %5 = and u32 %2, %4\n\
\x20   %6 = and u32 %3, %4\n\
\x20   %7 = const u32 0\n\
\x20   br bb1(%7, %5)\n\
bb1(%10: u32, %11: u32):\n\
\x20   %12 = icmp ult u32 %11, %6\n\
\x20   condbr %12, bb2, bb3\n\
bb2:\n\
\x20   %13 = add u32 %10, %11\n\
\x20   %14 = const u32 1\n\
\x20   %15 = add u32 %11, %14\n\
\x20   br bb1(%13, %15)\n\
bb3:\n\
\x20   %16 = bitcast u32 %10 to i32\n\
\x20   ret %16\n\
}\n\n\
fn @sum64(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = bitcast i32 %0 to u32\n\
\x20   %3 = bitcast i32 %1 to u32\n\
\x20   %4 = const u32 1023\n\
\x20   %5 = and u32 %2, %4\n\
\x20   %6 = and u32 %3, %4\n\
\x20   %7 = const u64 0\n\
\x20   br bb1(%7, %5)\n\
bb1(%10: u64, %11: u32):\n\
\x20   %12 = icmp ult u32 %11, %6\n\
\x20   condbr %12, bb2, bb3\n\
bb2:\n\
\x20   %13 = zext u32 %11 to u64\n\
\x20   %14, %15 = add.overflow u64 %10, %13\n\
\x20   %16 = const u32 1\n\
\x20   %17 = add u32 %11, %16\n\
\x20   br bb1(%14, %17)\n\
bb3:\n\
\x20   %18 = const u64 2654435761\n\
\x20   %19 = mul u64 %10, %18\n\
\x20   %20 = const u64 32\n\
\x20   %21 = lshr u64 %19, %20\n\
\x20   %22 = xor u64 %19, %21\n\
\x20   %23 = trunc u64 %22 to i32\n\
\x20   ret %23\n\
}\n\n\
fn @weighted(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = const i32 255\n\
\x20   %3 = and i32 %0, %2\n\
\x20   %4 = add i32 %1, %3\n\
\x20   %5 = const i32 9\n\
\x20   br bb1(%1, %5, %5)\n\
bb1(%10: i32, %11: i32, %12: i32):\n\
\x20   %13 = icmp eq i32 %10, %4\n\
\x20   condbr %13, bb3, bb2\n\
bb2:\n\
\x20   %14 = const i32 3\n\
\x20   %15 = mul i32 %10, %14\n\
\x20   %16 = sub i32 %11, %15\n\
\x20   %17 = const i32 1\n\
\x20   %18 = add i32 %12, %17\n\
\x20   %19 = const i32 1\n\
\x20   %20 = add i32 %10, %19\n\
\x20   br bb1(%20, %16, %18)\n\
bb3:\n\
\x20   %21 = const i32 65536\n\
\x20   %22 = mul i32 %12, %21\n\
\x20   %23 = xor i32 %11, %22\n\
\x20   ret %23\n\
}\n\n\
fn @hoist(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = const i32 63\n\
\x20   %3 = and i32 %0, %2\n\
\x20   %4 = const i32 0\n\
\x20   br bb1(%4, %4, %1)\n\
bb1(%10: i32, %11: i32, %12: i32):\n\
\x20   %13 = icmp slt i32 %10, %3\n\
\x20   condbr %13, bb2, bb3\n\
bb2:\n\
\x20   %14 = const i32 7\n\
\x20   %15 = mul i32 %12, %14\n\
\x20   %16 = xor i32 %10, %15\n\
\x20   %17 = const i32 3\n\
\x20   %18 = mul i32 %11, %17\n\
\x20   %19 = add i32 %18, %16\n\
\x20   %20 = const i32 1\n\
\x20   %21 = add i32 %10, %20\n\
\x20   br bb1(%21, %19, %12)\n\
bb3:\n\
\x20   ret %11\n\
}\n";

const NAMES: &[&str] = &["sum", "sum64", "weighted", "hoist"];

/// Round 14's loops (module docs).
const PROGRAM_R14: &str = "module \"p8r14\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = (i32, i32) -> (i32)\n\n\
type ty.0 = i32\n\n\
fn @table(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 4], align 4\n\
\x20   store i32 %0, ptr %2\n\
\x20   %3 = const i32 4\n\
\x20   %4 = gep inbounds u8, ptr %2, %3\n\
\x20   store i32 %1, ptr %4\n\
\x20   %5 = const i32 8\n\
\x20   %6 = gep inbounds u8, ptr %2, %5\n\
\x20   %7 = const i32 3\n\
\x20   store i32 %7, ptr %6\n\
\x20   %8 = const i32 12\n\
\x20   %9 = gep inbounds u8, ptr %2, %8\n\
\x20   %30 = const i32 5\n\
\x20   store i32 %30, ptr %9\n\
\x20   %10 = ptrtoint ptr %2 to i32\n\
\x20   %11 = const i32 16\n\
\x20   %12 = add i32 %10, %11\n\
\x20   %13 = const i32 0\n\
\x20   br bb1(%12, %13)\n\
bb1(%20: i32, %21: i32):\n\
\x20   %22 = icmp eq i32 %20, %10\n\
\x20   condbr %22, bb3, bb2\n\
bb2:\n\
\x20   %23 = const i32 -4\n\
\x20   %24 = add i32 %20, %23\n\
\x20   %25 = inttoptr i32 %24 to ptr\n\
\x20   %26 = load i32, ptr %25\n\
\x20   %27 = const i32 31\n\
\x20   %28 = mul i32 %21, %27\n\
\x20   %29 = xor i32 %28, %26\n\
\x20   br bb1(%24, %29)\n\
bb3:\n\
\x20   ret %21\n\
}\n\n\
fn @bits(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = const i32 0\n\
\x20   br bb1(%2, %1)\n\
bb1(%10: i32, %11: i32):\n\
\x20   %12 = const i32 8\n\
\x20   %13 = icmp slt i32 %10, %12\n\
\x20   condbr %13, bb2, bb3\n\
bb2:\n\
\x20   %14 = const i32 31\n\
\x20   %15 = and i32 %10, %14\n\
\x20   %16 = lshr i32 %0, %15\n\
\x20   %17 = const i32 1\n\
\x20   %18 = and i32 %16, %17\n\
\x20   %19 = const i32 3\n\
\x20   %20 = mul i32 %11, %19\n\
\x20   %21 = add i32 %20, %18\n\
\x20   %22 = add i32 %10, %17\n\
\x20   br bb1(%22, %21)\n\
bb3:\n\
\x20   ret %11\n\
}\n\n\
fn @rowsum(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 8], align 4\n\
\x20   store i32 %0, ptr %2\n\
\x20   %40 = const i32 4\n\
\x20   %41 = gep inbounds u8, ptr %2, %40\n\
\x20   store i32 %1, ptr %41\n\
\x20   %42 = const i32 8\n\
\x20   %43 = gep inbounds u8, ptr %2, %42\n\
\x20   store i32 %0, ptr %43\n\
\x20   %44 = const i32 12\n\
\x20   %45 = gep inbounds u8, ptr %2, %44\n\
\x20   store i32 %1, ptr %45\n\
\x20   %46 = const i32 16\n\
\x20   %47 = gep inbounds u8, ptr %2, %46\n\
\x20   store i32 %0, ptr %47\n\
\x20   %48 = const i32 20\n\
\x20   %49 = gep inbounds u8, ptr %2, %48\n\
\x20   store i32 %1, ptr %49\n\
\x20   %50 = const i32 24\n\
\x20   %51 = gep inbounds u8, ptr %2, %50\n\
\x20   store i32 %0, ptr %51\n\
\x20   %52 = const i32 28\n\
\x20   %53 = gep inbounds u8, ptr %2, %52\n\
\x20   store i32 %1, ptr %53\n\
\x20   %3 = const i32 7\n\
\x20   %60 = and i32 %1, %3\n\
\x20   %4 = sub i32 %3, %60\n\
\x20   %5 = const i32 0\n\
\x20   br bb1(%5, %5)\n\
bb1(%10: i32, %11: i32):\n\
\x20   %12 = icmp slt i32 %10, %4\n\
\x20   condbr %12, bb2, bb3\n\
bb2:\n\
\x20   %13 = ptrtoint ptr %2 to i32\n\
\x20   %14 = const i32 4\n\
\x20   %15 = mul i32 %10, %14\n\
\x20   %16 = add i32 %13, %15\n\
\x20   %17 = inttoptr i32 %16 to ptr\n\
\x20   %18 = load i32, ptr %17\n\
\x20   %19 = add i32 %11, %18\n\
\x20   %20 = const i32 1\n\
\x20   %21 = add i32 %10, %20\n\
\x20   br bb1(%21, %19)\n\
bb3:\n\
\x20   ret %11\n\
}\n\n\
fn @twoslots(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca i32, align 4\n\
\x20   %3 = alloca i32, align 4\n\
\x20   store i32 %0, ptr %2\n\
\x20   store i32 %1, ptr %3\n\
\x20   %30 = ptrtoint ptr %2 to i32\n\
\x20   %31 = ptrtoint ptr %3 to i32\n\
\x20   %32 = icmp eq i32 %30, %31\n\
\x20   %4 = const i32 15\n\
\x20   %5 = and i32 %1, %4\n\
\x20   %6 = const i32 0\n\
\x20   br bb1(%6)\n\
bb1(%10: i32):\n\
\x20   %11 = load i32, ptr %2\n\
\x20   %12 = icmp slt i32 %10, %5\n\
\x20   condbr %12, bb2, bb3\n\
bb2:\n\
\x20   %13 = load i32, ptr %3\n\
\x20   %14 = mul i32 %13, %11\n\
\x20   %15 = add i32 %14, %10\n\
\x20   store i32 %15, ptr %3\n\
\x20   %16 = const i32 1\n\
\x20   %17 = add i32 %10, %16\n\
\x20   br bb1(%17)\n\
bb3:\n\
\x20   %18 = load i32, ptr %3\n\
\x20   %19 = select i32 %32, %0, %18\n\
\x20   ret %19\n\
}\n";

const NAMES_R14: &[&str] = &["table", "bits", "rowsum", "twoslots"];

const ROWS: &[(i64, i64)] = &[
    (0, 0),
    (1, 2),
    (5, 1000),
    (1000, 5),
    (63, 64),
    (-1, -1),
    (1023, 0),
    (0, 1023),
    (-2_000_000_000, 77),
    (300, -300),
];

fn program() -> Module {
    trust_ir::parser::parse_module(PROGRAM).expect("parse the test program")
}

fn options(level: OptLevel) -> WasmOptOptions {
    WasmOptOptions {
        level,
        mid_end: true,
    }
}

fn closed(module: &Module, level: OptLevel) -> (Vec<u8>, wasm::WasmCompileEvidence) {
    wasm::compile_module_with_evidence_policy_license_options(
        module,
        &WasmModulePolicy::closed(),
        &permit_unlicensed(),
        options(level),
    )
    .expect("compile the closed module")
}

fn interpret(module: &Module, name: &str, a: i64, b: i64) -> i64 {
    let f = module.function_by_name(name).expect("function");
    let args = [a, b].map(|v| InterpretValue::int(Ty::I32, i128::from(v)).expect("i32"));
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 10_000_000,
            max_call_depth: 64,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, args)
        .unwrap_or_else(|e| panic!("{name}({a}, {b}) is refused by the interpreter: {e:?}"));
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => i64::from(i.as_signed() as i32),
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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_p8_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run `name(a, b)` for every row in node; `None` when node is absent.
fn run(bytes: &[u8], name: &str) -> Option<Vec<i64>> {
    let Some(node) = node() else {
        eprintln!("SKIP: node not found; the module was not executed");
        return None;
    };
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
    let dir = scratch("run");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let rows: Vec<String> = ROWS.iter().map(|(a, b)| format!("[{a},{b}]")).collect();
    let js = format!(
        "const fs = require('fs');\n\
         const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
         const imports = {{}};\n\
         for (const i of WebAssembly.Module.imports(m)) {{ imports[i.module] ??= {{}}; }}\n\
         const inst = new WebAssembly.Instance(m, imports);\n\
         const out = [{}].map(([a, b]) => inst.exports['{name}'](a, b));\n\
         process.stdout.write(JSON.stringify(out));\n",
        rows.join(",")
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
    Some(serde_json::from_slice(&out.stdout).expect("node JSON"))
}

fn assert_agrees(tag: &str, bytes: &[u8], module: &Module) {
    assert_agrees_on(tag, bytes, module, NAMES);
}

fn assert_agrees_on(tag: &str, bytes: &[u8], module: &Module, names: &[&str]) {
    for &name in names {
        let want: Vec<i64> = ROWS
            .iter()
            .map(|&(a, b)| interpret(module, name, a, b))
            .collect();
        if let Some(got) = run(bytes, name) {
            assert_eq!(got, want, "{tag}: {name} disagrees with the interpreter");
        }
    }
}

/// The `loop` instructions in the body of export `name`.
fn loops(bytes: &[u8], name: &str) -> usize {
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
    let body = bodies.swap_remove(index);
    body.get_operators_reader()
        .expect("ops")
        .into_iter()
        .filter(|op| matches!(op.as_ref().expect("op"), wasmparser::Operator::Loop { .. }))
        .count()
}

fn pass_changed(evidence: &wasm::WasmCompileEvidence, pass: &str) -> usize {
    evidence
        .mid_end
        .passes
        .iter()
        .find(|p| p.name == pass)
        .map_or(0, |p| p.functions_changed)
}

#[test]
fn counted_reductions_close_and_invariant_code_moves() {
    let module = program();
    let (o0, _) = closed(&module, OptLevel::O0);
    for &name in NAMES {
        assert_eq!(loops(&o0, name), 1, "O0 `{name}` keeps its loop");
    }
    assert_agrees("O0", &o0, &module);

    let (o2, evidence) = closed(&module, OptLevel::O2);
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    assert_eq!(pass_changed(&evidence, "loop_cf"), 3, "{:?}", mid.passes);
    assert!(pass_changed(&evidence, "licm") >= 1, "{:?}", mid.passes);
    for name in ["sum", "sum64", "weighted"] {
        assert_eq!(loops(&o2, name), 0, "O2 `{name}` has no loop left");
    }
    assert_eq!(loops(&o2, "hoist"), 1, "O2 `hoist` keeps its loop");
    assert_agrees("O2", &o2, &module);

    let (sized, _) = wasm::compile_sized_closed_module_with_evidence_license_options(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2),
    )
    .expect("compile the sized closed module");
    assert_agrees("sized O2", &sized, &module);
}

#[test]
fn the_object_lane_closes_and_links() {
    let module = program();
    let (object, evidence) = wasm::compile_object_with_evidence_license_options(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2),
    )
    .expect("compile the object");
    assert!(evidence.mid_end.applied);
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
    for name in ["sum", "sum64", "weighted"] {
        assert_eq!(loops(&linked, name), 0, "linked O2 `{name}`");
    }
    assert_agrees("linked O2", &linked, &module);
}

#[test]
fn constant_trip_loops_unroll_and_element_addresses_strength_reduce() {
    let module = trust_ir::parser::parse_module(PROGRAM_R14).expect("parse the round-14 program");
    let (o0, _) = closed(&module, OptLevel::O0);
    for &name in NAMES_R14 {
        assert_eq!(loops(&o0, name), 1, "O0 `{name}` keeps its loop");
    }
    assert_agrees_on("O0", &o0, &module, NAMES_R14);

    let (o2, evidence) = closed(&module, OptLevel::O2);
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    assert_eq!(pass_changed(&evidence, "unroll"), 2, "{:?}", mid.passes);
    assert_eq!(pass_changed(&evidence, "iv_sr"), 1, "{:?}", mid.passes);
    assert!(pass_changed(&evidence, "licm") >= 1, "{:?}", mid.passes);
    for name in ["table", "bits"] {
        assert_eq!(loops(&o2, name), 0, "O2 `{name}` is unrolled");
    }
    for name in ["rowsum", "twoslots"] {
        assert_eq!(loops(&o2, name), 1, "O2 `{name}` keeps its loop");
    }
    // `table`'s slot dissolves: one of the four functions keeps no frame.
    assert!(mid.allocas_after < mid.allocas_before, "{mid:?}");
    assert_agrees_on("O2", &o2, &module, NAMES_R14);

    let (sized, _) = wasm::compile_sized_closed_module_with_evidence_license_options(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2),
    )
    .expect("compile the sized closed module");
    assert_agrees_on("sized O2", &sized, &module, NAMES_R14);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
