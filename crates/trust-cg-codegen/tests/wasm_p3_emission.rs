// trust-cg-codegen/tests/wasm_p3_emission.rs - wasm32 lane: the validated local emission pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The local emission pass (`wasm/opt.rs`) on real lowered functions:
//!
//! * every function of a corpus of hand-written programs (loops with
//!   loop-carried values, calls, memory, wide integers, floats, switches), of
//!   random reducible CFGs (the CFG fuzzer's generator) and of random
//!   irreducible CFGs with memory-carried values is emitted with a rewritten
//!   body the per-segment translation validator accepted — no function falls
//!   back — in a closed module and in a relocatable object;
//! * the rewritten modules validate and agree with the trust-ir reference
//!   interpreter in node, closed and linked;
//! * the evidence reports the pass and keeps the compile's verdict at
//!   `missing_evidence`: the validator relates two wasm bodies of one
//!   function, not the module to its trust-ir;
//! * O1 and O3 emit the default (O2) bytes, and O0 does not run the pass: it
//!   emits every baseline body, says so in its evidence, and agrees with the
//!   interpreter too;
//! * a GEP's address addition folds into a memarg offset under the no-wrap
//!   premise `trust_cg_verify::wasm_nowrap_premise` re-derives from the
//!   trust-ir function, and an integer address chain never does;
//! * the control cleanup (`wasm/opt/control.rs`) is accepted by its validator
//!   wherever it changes a body of these corpora (no refusal), and every
//!   control mutant of a baseline body the validator accepts validates and
//!   computes what the original computes in node.
//!
//! The summary's `control_*`, `nowrap_*` and `tv_premised_folds` fields and
//! `wasm_local_tv::validate_control` are provisional surfaces
//! (docs/wasm32_perf_roadmap.md, "Pending owner sign-off").
//!
//! Node is required to execute the wasm and `wasm-ld` (`WASM_LD`) to link
//! objects; the absence of either is a loud SKIP.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm;
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

#[allow(dead_code)]
#[path = "../examples/wasm_cfg_fuzz.rs"]
mod cfg_fuzz;

const HEADER: &str = "module \"p3\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n";

fn parse(body: &str) -> Module {
    let text = format!("{HEADER}{body}");
    trust_ir::parser::parse_module(&text).unwrap_or_else(|e| {
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

fn scratch(tag: &str) -> PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("tcg_wasm_p3_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn validate(bytes: &[u8]) {
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
}

/// The parameter/result width of an export.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum W {
    I32,
    I64,
}

impl W {
    fn ty(self) -> Ty {
        match self {
            W::I32 => Ty::I32,
            W::I64 => Ty::I64,
        }
    }
}

/// The interpreter's answer for `name(args)`, or `None` when the reference
/// execution refuses the input. Runs on the target-free copy of the module.
fn interpret(module: &Module, name: &str, w: W, args: &[i64]) -> Option<i64> {
    let f = module.function_by_name(name).expect("function");
    let args: Vec<InterpretValue> = args
        .iter()
        .map(|&v| InterpretValue::int(w.ty(), i128::from(v)).expect("int value"))
        .collect();
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 50_000_000,
            max_call_depth: 256,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, args)
        .ok()?;
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => Some(match w {
            W::I32 => i64::from(i.as_signed() as i32),
            W::I64 => i.as_signed() as i64,
        }),
        other => panic!("{name} returned {other:?}"),
    }
}

/// One export to run: its name, width and argument rows.
struct Export {
    name: String,
    w: W,
    calls: Vec<Vec<i64>>,
}

/// Run every export over its rows in one instance; `None` is a trap. `None`
/// for the whole table when node is absent.
fn run_wasm(bytes: &[u8], exports: &[Export]) -> Option<Vec<Vec<Option<i64>>>> {
    let Some(node) = node() else {
        eprintln!("SKIP: node not found; the rewritten module was not executed");
        return None;
    };
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
              const table = JSON.parse(fs.readFileSync(process.argv[3]));\n\
              const out = table.map(([name, w, calls]) => { const f = inst.exports[name]; \
                return calls.map((args) => { try { \
                  return String(f(...args.map((a) => w === 'i64' ? BigInt(a) : Number(a)))); } \
                catch (e) { if (e instanceof WebAssembly.RuntimeError) return null; throw e; } }); });\n\
              process.stdout.write(JSON.stringify(out));\n";
    std::fs::write(dir.join("run.js"), js).unwrap();
    let table: Vec<(String, &str, Vec<Vec<String>>)> = exports
        .iter()
        .map(|e| {
            (
                e.name.clone(),
                if e.w == W::I64 { "i64" } else { "i32" },
                e.calls
                    .iter()
                    .map(|c| c.iter().map(i64::to_string).collect())
                    .collect(),
            )
        })
        .collect();
    std::fs::write(
        dir.join("table.json"),
        serde_json::to_string(&table).unwrap(),
    )
    .unwrap();
    let run = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .arg(dir.join("table.json"))
        .output()
        .expect("run node");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "node failed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let got: Vec<Vec<Option<String>>> = serde_json::from_slice(&run.stdout).expect("node JSON");
    Some(
        got.into_iter()
            .map(|col| {
                col.into_iter()
                    .map(|v| v.map(|s| s.parse::<i64>().unwrap()))
                    .collect()
            })
            .collect(),
    )
}

/// Link relocatable objects into a runnable module (every definition
/// exported). `None` (a loud SKIP) when no linker is available.
fn link(object: &[u8]) -> Option<Vec<u8>> {
    let Some(ld) = wasm_ld() else {
        eprintln!("SKIP: wasm-ld not found (set WASM_LD); link not executed");
        return None;
    };
    let dir = scratch("link");
    std::fs::write(dir.join("m0.o"), object).unwrap();
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
    Some(linked)
}

/// Compile `module` closed and as an object; require every function to be
/// emitted with a validated rewrite; run both forms against the
/// interpreter. Returns the closed compile's pass summary.
fn check(tag: &str, module: &Module, exports: &[Export]) -> wasm::WasmLocalOptSummary {
    check_with(tag, module, exports, true)
}

/// [`check`], with the trust-ir mid-end on or off (`mid_end`): a fixture that
/// carries values through frame slots for the emission pass to rewrite is
/// lowered as given, since the mid-end's store forwarding would remove the
/// slots.
fn check_with(
    tag: &str,
    module: &Module,
    exports: &[Export],
    mid_end: bool,
) -> wasm::WasmLocalOptSummary {
    // The reference execution: on the module as given, or on its
    // target-free copy when the interpreter declines the wasm32 pin.
    let mut free = module.clone();
    free.target_info = None;
    let want: Vec<Vec<Option<i64>>> = exports
        .iter()
        .map(|e| {
            e.calls
                .iter()
                .map(|args| {
                    let v = interpret(module, &e.name, e.w, args)
                        .or_else(|| interpret(&free, &e.name, e.w, args));
                    assert!(
                        v.is_some(),
                        "{tag}: {}{args:?} is refused by the interpreter",
                        e.name
                    );
                    v
                })
                .collect()
        })
        .collect();

    let license = permit_unlicensed();
    let options = |level| wasm::WasmOptOptions { level, mid_end };
    let closed_at = |level| {
        wasm::compile_module_with_evidence_policy_license_options(
            module,
            &wasm::WasmModulePolicy::closed(),
            &license,
            options(level),
        )
    };
    let object_at = |level| {
        wasm::compile_object_with_evidence_license_options(module, &license, options(level))
    };
    let (closed, evidence) =
        closed_at(OptLevel::O2).unwrap_or_else(|e| panic!("{tag}: compile_module: {e}"));
    let summary = evidence.local_emission.clone();
    assert_eq!(
        summary.fallback_count(),
        0,
        "{tag}: functions fell back: {summary:?}"
    );
    assert!(
        summary.control_refusals.is_empty(),
        "{tag}: control cleanups refused: {summary:?}"
    );
    assert!(
        summary.optimized > 0,
        "{tag}: nothing optimized: {summary:?}"
    );
    assert_eq!(
        summary.optimized + summary.unchanged,
        summary.functions,
        "{tag}: {summary:?}"
    );
    assert!(evidence.ran.contains(&"wasm_local_emission_tv"), "{tag}");
    assert_eq!(evidence.verdict.as_str(), "missing_evidence", "{tag}");
    assert!(
        evidence.not_run.contains(&"translation_validation"),
        "{tag}"
    );
    let json = evidence.to_json();
    assert_eq!(
        json["local_emission"]["optimized"].as_u64(),
        Some(summary.optimized as u64)
    );
    validate(&closed);

    let (object, obj_evidence) =
        object_at(OptLevel::O2).unwrap_or_else(|e| panic!("{tag}: compile_object: {e}"));
    let obj = &obj_evidence.local_emission;
    assert_eq!(obj.fallback_count(), 0, "{tag}: object fell back: {obj:?}");
    assert!(
        obj.control_refusals.is_empty(),
        "{tag}: object control cleanups refused: {obj:?}"
    );
    assert!(obj.optimized > 0, "{tag}: object: {obj:?}");

    // The level selects the pass: O1 and O3 emit the default (O2) bytes; O0
    // emits every baseline body, records that the pass did not run, and
    // runs too.
    for level in [OptLevel::O1, OptLevel::O3] {
        let (bytes, _) = closed_at(level).unwrap_or_else(|e| panic!("{tag}: {level:?}: {e}"));
        assert_eq!(bytes, closed, "{tag}: {level:?}");
        let (bytes, _) =
            object_at(level).unwrap_or_else(|e| panic!("{tag}: {level:?} object: {e}"));
        assert_eq!(bytes, object, "{tag}: {level:?} object");
    }
    let (closed_o0, evidence_o0) =
        closed_at(OptLevel::O0).unwrap_or_else(|e| panic!("{tag}: O0: {e}"));
    let (object_o0, obj_evidence_o0) =
        object_at(OptLevel::O0).unwrap_or_else(|e| panic!("{tag}: O0 object: {e}"));
    for e in [&evidence_o0, &obj_evidence_o0] {
        assert!(!e.local_emission.enabled, "{tag}: O0 ran the pass");
        assert_eq!(e.local_emission.functions, 0, "{tag}");
        assert!(!e.ran.contains(&"wasm_local_emission_tv"), "{tag}");
        assert_eq!(e.to_json()["local_emission"]["enabled"], false, "{tag}");
    }
    assert!(evidence.local_emission.enabled, "{tag}");
    assert_ne!(closed_o0, closed, "{tag}: the pass rewrote nothing at O2");
    assert_ne!(
        object_o0, object,
        "{tag}: the pass rewrote nothing in the object"
    );
    validate(&closed_o0);

    if let Some(got) = run_wasm(&closed, exports) {
        assert_eq!(
            got, want,
            "{tag}: the closed module disagrees with the interpreter"
        );
    }
    if let Some(linked) = link(&object)
        && let Some(got) = run_wasm(&linked, exports)
    {
        assert_eq!(
            got, want,
            "{tag}: the linked object disagrees with the interpreter"
        );
    }
    if let Some(got) = run_wasm(&closed_o0, exports) {
        assert_eq!(
            got, want,
            "{tag}: the O0 module disagrees with the interpreter"
        );
    }
    if let Some(linked) = link(&object_o0)
        && let Some(got) = run_wasm(&linked, exports)
    {
        assert_eq!(
            got, want,
            "{tag}: the linked O0 object disagrees with the interpreter"
        );
    }
    summary
}

const PROGRAMS: &str = r#"functy.0 = (i64, i64) -> (i64)
functy.1 = (i64) -> (i64)

internal fn @step(functy.1) {
bb0(%0: i64):
    %1 = const i64 3
    %2 = mul i64 %0, %1
    %3 = const i64 1
    %4 = add i64 %2, %3
    ret %4
}

fn @collatz(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = const i64 0
    %3 = const i64 1
    %40 = const i64 2
    %41 = const i64 255
    %42 = and i64 %0, %41
    %43 = add i64 %42, %40
    br bb1(%43, %2)
bb1(%4: i64, %5: i64):
    %6 = icmp sle i64 %4, %3
    condbr %6, bb5, bb2
bb2:
    %7 = and i64 %4, %3
    %8 = icmp eq i64 %7, %2
    condbr %8, bb3, bb4
bb3:
    %9 = sdiv i64 %4, %40
    %10 = add i64 %5, %3
    br bb1(%9, %10)
bb4:
    %11 = call @func.0(%4)
    %12 = add i64 %5, %3
    br bb1(%11, %12)
bb5:
    %13 = mul i64 %5, %1
    %14 = add i64 %13, %4
    ret %14
}

fn @wide(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = sext i64 %0 to i128
    %3 = sext i64 %1 to i128
    %4 = mul i128 %2, %3
    %5 = const i128 1000003
    %6 = add i128 %4, %5
    %7 = const i128 7
    %8 = srem i128 %6, %7
    %9 = xor i128 %6, %8
    %10 = trunc i128 %9 to i64
    ret %10
}

fn @floats(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = sitofp i64 %0 to f64
    %3 = sitofp i64 %1 to f64
    %4 = const i64 0
    %5 = const i64 1
    %6 = const i64 6
    br bb1(%2, %4)
bb1(%7: f64, %8: i64):
    %9 = icmp slt i64 %8, %6
    condbr %9, bb2, bb3
bb2:
    %10 = fmul f64 %7, %3
    %11 = fadd f64 %10, %2
    %12 = add i64 %8, %5
    br bb1(%11, %12)
bb3:
    %13 = fptosi.sat f64 %7 to i64
    ret %13
}

fn @frame(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = alloca i64
    %3 = alloca i64
    store i64 %0, ptr %2
    store i64 %1, ptr %3
    %4 = const i64 0
    %5 = const i64 1
    %6 = const i64 5
    br bb1(%4)
bb1(%7: i64):
    %8 = icmp slt i64 %7, %6
    condbr %8, bb2, bb3
bb2:
    %9 = load i64, ptr %2
    %10 = load i64, ptr %3
    %11 = add i64 %9, %10
    store i64 %10, ptr %2
    store i64 %11, ptr %3
    %12 = add i64 %7, %5
    br bb1(%12)
bb3:
    %13 = load i64, ptr %3
    ret %13
}

fn @dispatch(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = trunc i64 %0 to i32
    %3 = const i32 3
    %4 = and i32 %2, %3
    switch %4 [ 0: bb1 1: bb2 2: bb3 default: bb4 ]
bb1:
    %5 = add i64 %0, %1
    br bb5(%5)
bb2:
    %6 = sub i64 %0, %1
    br bb5(%6)
bb3:
    %7 = mul i64 %0, %1
    br bb5(%7)
bb4:
    %8 = xor i64 %0, %1
    br bb5(%8)
bb5(%9: i64):
    %10 = const i64 9
    %11 = add i64 %9, %10
    ret %11
}
"#;

fn rows(pairs: &[(i64, i64)]) -> Vec<Vec<i64>> {
    pairs.iter().map(|&(a, b)| vec![a, b]).collect()
}

const PAIRS: &[(i64, i64)] = &[
    (0, 0),
    (1, 2),
    (7, -3),
    (-5, 11),
    (27, 1),
    (97, 3),
    (255, -255),
    (i64::MAX, 2),
    (i64::MIN, -1),
    (123_456_789, 987_654_321),
];

#[test]
fn hand_written_programs_are_emitted_with_validated_rewrites() {
    let module = parse(PROGRAMS);
    let exports: Vec<Export> = ["collatz", "wide", "floats", "frame", "dispatch"]
        .iter()
        .map(|n| Export {
            name: n.to_string(),
            w: W::I64,
            calls: rows(PAIRS),
        })
        .collect();
    let summary = check("programs", &module, &exports);
    assert!(
        summary.declared_locals_after < summary.declared_locals_before,
        "{summary:?}"
    );
    assert!(summary.copies_deleted > 0, "{summary:?}");
    assert!(
        summary.code_bytes_after < summary.code_bytes_before,
        "{summary:?}"
    );
}

/// Narrow values through memory, a small aggregate copied between frame
/// slots, and field reads: the segment rewrites (stackify, narrow masks,
/// memarg folding under the closed module's stack guard, small copies) all
/// apply, and the validator accepts each function.
const STAGE_B: &str = r#"struct @S { : i64 @0, : u8 @8, : i16 @10 } size=16 align=8 id=0

global @bias i64 = 3

functy.0 = (i64, i64) -> (i64)

fn @narrow(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = trunc i64 %0 to u8
    %3 = trunc i64 %1 to u8
    %4 = alloca u8
    store u8 %2, ptr %4
    %5 = load u8, ptr %4
    %6 = add u8 %5, %3
    %7 = zext u8 %6 to i64
    ret %7
}

fn @copy(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = trunc i64 %1 to u8
    %3 = trunc i64 %0 to i16
    %4 = make_aggregate struct.0 (%0, %2, %3)
    %5 = alloca struct.0
    %6 = alloca struct.0
    store struct.0 %4, ptr %5
    %7 = load struct.0, ptr %5
    store struct.0 %7, ptr %6
    %8 = load struct.0, ptr %6
    %9 = extractfield i64 %8, 0
    %10 = extractfield u8 %8, 1
    %11 = extractfield i16 %8, 2
    %12 = zext u8 %10 to i64
    %13 = sext i16 %11 to i64
    %14 = add i64 %9, %12
    %15 = add i64 %14, %13
    %16 = global_addr @global.0
    %17 = load i64, ptr %16
    %18 = add i64 %15, %17
    ret %18
}

fn @masks(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = trunc i64 %0 to u8
    %3 = trunc i64 %1 to u8
    %4 = alloca u8
    store u8 %2, ptr %4
    %5 = load u8, ptr %4
    %6 = and u8 %5, %3
    %7 = or u8 %5, %3
    %8 = xor u8 %6, %7
    %20 = const u8 2
    %9 = lshr u8 %8, %20
    %10 = zext u8 %9 to i64
    %11 = trunc i64 %1 to i16
    %12 = alloca i16
    store i16 %11, ptr %12
    %13 = load i16, ptr %12
    %14 = sext i16 %13 to i64
    %15 = add i64 %10, %14
    %16 = alloca i64
    %17 = alloca i64
    store i64 %15, ptr %16
    store i64 %0, ptr %17
    ret %15
}
"#;

#[test]
fn stage_b_rewrites_are_emitted_with_validated_rewrites() {
    let module = parse(STAGE_B);
    let exports: Vec<Export> = ["narrow", "copy", "masks"]
        .iter()
        .map(|n| Export {
            name: n.to_string(),
            w: W::I64,
            calls: rows(PAIRS),
        })
        .collect();
    let summary = check_with("stage b", &module, &exports, false);
    eprintln!("stage b: {summary:?}");
    assert!(summary.stackified > 0, "{summary:?}");
    assert!(summary.offsets_folded > 0, "{summary:?}");
    assert!(summary.tv_offsets_folded > 0, "{summary:?}");
    assert!(summary.tv_facts_checked > 0, "{summary:?}");
    assert_eq!(
        summary.copies_expanded, summary.tv_copies_expanded,
        "{summary:?}"
    );
    assert!(summary.copies_expanded > 0, "{summary:?}");
    assert!(summary.masks_removed > 0, "{summary:?}");
}

/// GEPs with constant indices from a pointer nothing bounds (one loaded
/// from a frame slot), each used once, beside an integer address chain
/// (`ptrtoint`/`add`/`inttoptr`) to other bytes of the same buffer and a
/// scaled GEP: the emission pass folds the GEPs' additions into memarg
/// offsets under their no-wrap premises (round 14 stage B), never the
/// chain's.
const PREMISE: &str = r#"type ty.0 = i64

functy.0 = (i64, i64) -> (i64)

fn @fields(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = alloca [ty.0 x 6]
    %3 = alloca ptr
    store ptr %2, ptr %3
    %4 = load ptr, ptr %3
    %5 = const usize 8
    %6 = gep u8, ptr %4, %5
    store i64 %0, ptr %6
    %7 = const usize 16
    %8 = gep u8, ptr %4, %7
    store i64 %1, ptr %8
    %28 = const usize 8
    %9 = gep u8, ptr %4, %28
    %10 = load i64, ptr %9
    %29 = const usize 16
    %11 = gep u8, ptr %4, %29
    %12 = load i64, ptr %11
    %13 = sub i64 %10, %12
    %14 = ptrtoint ptr %4 to i32
    %15 = const i32 24
    %16 = add i32 %14, %15
    %17 = inttoptr i32 %16 to ptr
    store i64 %13, ptr %17
    %18 = const usize 3
    %19 = gep i64, ptr %4, %18
    %20 = load i64, ptr %19
    %21 = const usize 32
    %22 = gep u8, ptr %4, %21
    %23 = trunc i64 %0 to u16
    store u16 %23, ptr %22
    %30 = const usize 32
    %24 = gep u8, ptr %4, %30
    %25 = load u16, ptr %24
    %26 = zext u16 %25 to i64
    %27 = add i64 %20, %26
    ret %27
}
"#;

#[test]
fn premised_gep_folds_are_emitted_with_validated_rewrites() {
    use trust_cg_verify::wasm_cfg_proofs::{Imm, decode_body, decode_module};
    let module = parse(PREMISE);
    let exports = vec![Export {
        name: "fields".to_string(),
        w: W::I64,
        calls: rows(PAIRS),
    }];
    let summary = check_with("premise", &module, &exports, false);
    eprintln!("premise: {summary:?}");
    assert!(summary.nowrap_premises >= 7, "{summary:?}");
    assert!(summary.nowrap_refusals.is_empty(), "{summary:?}");
    assert!(summary.tv_premised_folds >= 4, "{summary:?}");
    // The emitted accesses: the GEPs' offsets folded, the chain's 24 still
    // an `i32.add` before an access at offset 0.
    let options = wasm::WasmOptOptions {
        level: OptLevel::O2,
        mid_end: false,
    };
    let (bytes, _) = wasm::compile_module_with_evidence_policy_license_options(
        &module,
        &wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
        options,
    )
    .expect("compiles");
    let view = decode_module(&bytes).expect("decodes");
    let body = &view.code[0].body;
    let insts = decode_body(&body[..body.len() - 1], 0).expect("decodes");
    let offsets: Vec<u32> = insts
        .iter()
        .filter_map(|x| match x.imm {
            Imm::MemArg { offset, .. } if (0x28..=0x3e).contains(&x.opcode) => Some(offset),
            _ => None,
        })
        .collect();
    for k in [8, 16, 32] {
        assert!(offsets.contains(&k), "offset {k} not folded: {offsets:?}");
    }
    assert!(
        !offsets.contains(&24),
        "the integer chain was folded: {offsets:?}"
    );
    assert!(
        insts
            .windows(2)
            .any(|w| w[0].opcode == 0x41 && w[0].imm == Imm::Int(24) && w[1].opcode == 0x6a),
        "the integer chain's addition is gone"
    );
}

/// Many values computed from the parameters, two calls, then values computed
/// from the parameters again: single-use stackify could carry those late
/// trees' parameter reads across the calls' result writes, which the
/// pressure condition weighs. Whatever candidate is selected must validate
/// and run as the interpreter does.
const PRESSURE: &str = r#"functy.0 = (i64, i64) -> (i64)
functy.1 = (i64) -> (i64)

internal fn @step(functy.1) {
bb0(%0: i64):
    %1 = const i64 3
    %2 = mul i64 %0, %1
    ret %2
}

fn @spread(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = add i64 %0, %1
    %3 = mul i64 %0, %1
    %4 = sub i64 %0, %1
    %5 = xor i64 %0, %1
    %6 = call @func.0(%4)
    %7 = call @func.0(%5)
    %8 = add i64 %6, %7
    %9 = xor i64 %8, %2
    %10 = add i64 %9, %3
    %11 = or i64 %0, %1
    %12 = and i64 %0, %1
    %13 = sub i64 %11, %12
    %14 = icmp slt i64 %0, %1
    %15 = select i64 %14, %13, %10
    %16 = add i64 %15, %10
    ret %16
}
"#;

#[test]
fn pressure_limited_stackify_is_emitted_with_validated_rewrites() {
    let module = parse(PRESSURE);
    let exports = vec![Export {
        name: "spread".to_string(),
        w: W::I64,
        calls: rows(PAIRS),
    }];
    let summary = check("pressure", &module, &exports);
    assert!(summary.stackified > 0, "{summary:?}");
    assert!(
        summary.declared_locals_after < summary.declared_locals_before,
        "{summary:?}"
    );
}

#[test]
fn random_reducible_cfgs_are_emitted_with_validated_rewrites() {
    for seed in 0..6u64 {
        let mut module = cfg_fuzz::build_fuzz_module(seed.wrapping_mul(0x9E37_79B9) ^ 0x5EED, 12);
        module.target_info = Some(wasm::wasm32_target_info());
        let exports: Vec<Export> = (0..12)
            .map(|i| Export {
                name: format!("f{i}"),
                w: W::I32,
                calls: vec![
                    vec![0, 0, 0, 0],
                    vec![1, -2, 3, -4],
                    vec![17, 5, -9, 100],
                    vec![-1000, 999, 0, 7],
                    vec![i64::from(i32::MAX), 1, i64::from(i32::MIN), 2],
                ],
            })
            .collect();
        check(&format!("fuzz seed {seed}"), &module, &exports);
    }
}

/// Random CFGs over `n` loop blocks (often irreducible, so lowered as a
/// dispatch loop), each block computing through an `Alloca` and a
/// memory-carried struct (the generator of `wasm_r6_lane.rs`).
fn random_cfg(seed: u64, n: u64) -> String {
    struct Rng(u64);
    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }
    }
    assert!(n > 0);
    // One ring successor keeps all generated blocks reachable; random
    // secondary edges, operations, seeds and the full node census remain.
    let mut r = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    let head = |k: u64| 3 * k - 2;
    let mut v = 10u64;
    let mut nv = || {
        v += 1;
        format!("%{v}")
    };
    let mut out = String::from(
        "struct @S { : i64 @0, : i64 @8 } size=16 align=8 id=0\n\n\
         functy.0 = (i64, i64) -> (i64)\n\nfn @f(functy.0) {\nbb0(%0: i64, %1: i64):\n",
    );
    let (fuel, s0, z, c) = (nv(), nv(), nv(), nv());
    let (t1, t2) = (1 + r.below(n), 1 + r.below(n));
    out += &format!(
        "    {fuel} = const i64 {}\n    {s0} = make_aggregate struct.0 (%0, %1)\n\
         \x20   {z} = const i64 0\n    {c} = icmp slt i64 %1, {z}\n\
         \x20   condbr {c}, bb{}(%0, {fuel}, {s0}), bb{}(%1, {fuel}, {s0})\n",
        3 + r.below(38),
        head(t1),
        head(t2)
    );
    for k in 1..=n {
        let (x, fu, s) = (nv(), nv(), nv());
        let (one, f2, kk, y, f0, y2, a, ld, s2, zz, done) = (
            nv(),
            nv(),
            nv(),
            nv(),
            nv(),
            nv(),
            nv(),
            nv(),
            nv(),
            nv(),
            nv(),
        );
        let op = ["add", "mul", "xor", "sub"][r.below(4) as usize];
        out += &format!(
            "bb{}({x}: i64, {fu}: i64, {s}: struct.0):\n\
             \x20   {one} = const i64 1\n    {f2} = sub i64 {fu}, {one}\n\
             \x20   {kk} = const i64 {}\n    {y} = {op} i64 {x}, {kk}\n\
             \x20   {f0} = extractfield i64 {s}, 0\n    {y2} = add i64 {y}, {f0}\n\
             \x20   {a} = alloca i64\n    store i64 {y2}, ptr {a}\n    {ld} = load i64, ptr {a}\n\
             \x20   {s2} = make_aggregate struct.0 ({ld}, {x})\n\
             \x20   {zz} = const i64 0\n    {done} = icmp sle i64 {f2}, {zz}\n\
             \x20   condbr {done}, bb{}, bb{}\n",
            head(k),
            r.below(19) as i64 - 9,
            3 * k - 1,
            3 * k
        );
        let (f1, rr) = (nv(), nv());
        out += &format!(
            "bb{}:\n    {f1} = extractfield i64 {s2}, 1\n    {rr} = xor i64 {ld}, {f1}\n    ret {rr}\n",
            3 * k - 1
        );
        out += &format!("bb{}:\n", 3 * k);
        let choice = r.below(3);
        let arms = 1 + r.below(4);
        let mut t = || head(1 + r.below(n));
        match choice {
            0 => {
                let _random_target = t();
                out += &format!("    br bb{}({ld}, {f2}, {s2})\n", head(k % n + 1));
            }
            1 => {
                let (m, q, cc) = (nv(), nv(), nv());
                let (_random_target, tb, modulus) =
                    (t(), t(), 2 + ((k * 31 + seed * 17) ^ (seed >> 3)) % 4);
                let ta = head(k % n + 1);
                out += &format!(
                    "    {m} = const i64 {modulus}\n    {q} = srem i64 {ld}, {m}\n\
                     \x20   {cc} = icmp eq i64 {q}, {zz}\n\
                     \x20   condbr {cc}, bb{ta}({ld}, {f2}, {s2}), bb{tb}({x}, {f2}, {s})\n"
                );
            }
            _ => {
                let (q2, q3, q4) = (nv(), nv(), nv());
                let cases: Vec<String> = (0..arms)
                    .map(|i| format!("{i}: bb{}({ld}, {f2}, {s2})", t()))
                    .collect();
                let _random_target = t();
                let d = head(k % n + 1);
                out += &format!(
                    "    {q2} = trunc i64 {ld} to i32\n    {q3} = const i32 3\n\
                     \x20   {q4} = and i32 {q2}, {q3}\n\
                     \x20   switch {q4} [ {} default: bb{d}({x}, {f2}, {s2}) ]\n",
                    cases.join(" ")
                );
            }
        }
    }
    out + "}\n"
}

#[test]
fn random_irreducible_cfgs_with_memory_are_emitted_with_validated_rewrites() {
    for seed in 1..=8u64 {
        let module = parse(&random_cfg(seed, 3 + seed % 5));
        let exports = [Export {
            name: "f".to_string(),
            w: W::I64,
            calls: rows(PAIRS),
        }];
        check(&format!("irreducible seed {seed}"), &module, &exports);
    }
}

// ---- The validator's own soundness, spot-checked by execution ----

/// `module` with defined function `def`'s instruction bytes (its trailing
/// `end` included) replaced by `expr`.
fn with_body(module: &[u8], def: usize, expr: &[u8]) -> Vec<u8> {
    let mut section: Option<(std::ops::Range<usize>, u32)> = None;
    let mut bodies: Vec<std::ops::Range<usize>> = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(module) {
        match payload.expect("parse") {
            wasmparser::Payload::CodeSectionStart { range, size, .. } => {
                section = Some((range, size));
            }
            wasmparser::Payload::CodeSectionEntry(body) => bodies.push(body.range()),
            _ => {}
        }
    }
    let (range, size) = section.expect("a code section");
    let leb = |v: u64| {
        let mut out = Vec::new();
        let mut v = v;
        loop {
            let b = (v & 0x7f) as u8;
            v >>= 7;
            if v == 0 {
                out.push(b);
                return out;
            }
            out.push(b | 0x80);
        }
    };
    let header = 1 + leb(u64::from(size)).len();
    let view = trust_cg_verify::wasm_cfg_proofs::decode_module(module).expect("decodes");
    let mut content = leb(bodies.len() as u64);
    for (i, b) in bodies.iter().enumerate() {
        let entry: Vec<u8> = if i == def {
            let locals_end = view.code[i].body_offset;
            let mut e = module[b.start..locals_end].to_vec();
            e.extend_from_slice(expr);
            e
        } else {
            module[b.clone()].to_vec()
        };
        content.extend(leb(entry.len() as u64));
        content.extend(entry);
    }
    let mut out = module[..range.start - header].to_vec();
    out.push(10);
    out.extend(leb(content.len() as u64));
    out.extend(content);
    out.extend_from_slice(&module[range.end..]);
    out
}

struct ViewTypes<'a>(&'a trust_cg_verify::wasm_cfg_proofs::WasmModuleView);

impl trust_cg_verify::wasm_local_tv::TvTypes for ViewTypes<'_> {
    fn func(&self, index: u32) -> Option<trust_cg_verify::wasm_cfg_proofs::FuncSig> {
        self.0.sig_of_func(index).cloned()
    }
    fn type_at(&self, index: u32) -> Option<trust_cg_verify::wasm_cfg_proofs::FuncSig> {
        self.0.types.get(index as usize).cloned()
    }
    fn global(&self, index: u32) -> Option<trust_cg_verify::wasm_cfg_proofs::ValKind> {
        self.0.globals.get(index as usize).copied()
    }
}

/// `(operands, results)` of the simple value instructions the mutant test's
/// tree swap walks over; `None` for every other instruction.
fn arity(op: u8) -> Option<(usize, usize)> {
    Some(match op {
        0x20 | 0x23 | 0x41..=0x44 => (0, 1),
        0x22 | 0x28..=0x35 | 0x45 | 0x50 | 0x67..=0x69 | 0x79..=0x7b | 0xa7..=0xc4 => (1, 1),
        0x46..=0x4f | 0x51..=0x66 | 0x6a..=0x78 | 0x7c..=0x8a | 0x92..=0x98 | 0xa0..=0xa6 => (2, 1),
        0x8b..=0x91 | 0x99..=0x9f => (1, 1),
        _ => return None,
    })
}

/// Mutate emitted bodies — a `local.get` redirected to another local of its
/// type, a constant changed, the two operand trees of an `i32` binary
/// operator swapped (`sp - 32` becomes `32 - sp`), two adjacent operand
/// producers of one type swapped, or a `global.get` moved
/// across a `drop` of a value of its type — and validate each mutant against
/// the body it came from with the identity image. Every mutant the validator
/// ACCEPTS must compute what the original computes: each is spliced into the
/// module and run against the original's results. The subjects are random
/// CFGs (no memory) and the hand-written and stage-B programs (frames, so
/// the stack-pointer protocol's `global.get`/`global.set`). Mutants are
/// validated without premises, so the premise corpus here exercises only
/// the premise-free relation; the premise path's mutants are
/// `wasm/opt/premise_mutants_tests.rs` (a unit test, which reaches the
/// lowering's own bodies and premises).
#[test]
fn every_mutant_the_validator_accepts_behaves_like_the_original() {
    use trust_cg_verify::wasm_cfg_proofs::{Imm, ValKind, decode_body};
    use trust_cg_verify::wasm_local_tv::{
        LocalImage, ResidualPolicy, TvBody, TvRequest, validate as tv_validate,
    };
    let mut subjects: Vec<(String, Module, Vec<Export>)> = Vec::new();
    for seed in 0..3u64 {
        let mut module = cfg_fuzz::build_fuzz_module(seed ^ 0xC0FFEE, 8);
        module.target_info = Some(wasm::wasm32_target_info());
        let exports: Vec<Export> = (0..8)
            .map(|i| Export {
                name: format!("f{i}"),
                w: W::I32,
                calls: vec![
                    vec![0, 0, 0, 0],
                    vec![1, -2, 3, -4],
                    vec![17, 5, -9, 100],
                    vec![-1000, 999, 0, 7],
                ],
            })
            .collect();
        subjects.push((format!("fuzz seed {seed}"), module, exports));
    }
    for (tag, text, names) in [
        (
            "programs",
            PROGRAMS,
            &["collatz", "wide", "floats", "frame", "dispatch"][..],
        ),
        ("stage b", STAGE_B, &["narrow", "copy", "masks"][..]),
        ("premise", PREMISE, &["fields"][..]),
    ] {
        let exports = names
            .iter()
            .map(|n| Export {
                name: n.to_string(),
                w: W::I64,
                calls: rows(PAIRS),
            })
            .collect();
        subjects.push((tag.to_string(), parse(text), exports));
    }
    let (mut tried, mut accepted, mut executed) = (0usize, 0usize, 0usize);
    let (mut swaps, mut global_moves) = (0usize, 0usize);
    for (subject, (tag, module, exports)) in subjects.iter().enumerate() {
        let bytes =
            wasm::compile_module_with_license(module, &permit_unlicensed()).expect("compiles");
        let view = trust_cg_verify::wasm_cfg_proofs::decode_module(&bytes).expect("decodes");
        let original = run_wasm(&bytes, exports);
        let mut rng = 0x9E37_79B9_7F4A_7C15u64 ^ subject as u64;
        let mut next = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };
        for (def, entry) in view.code.iter().enumerate() {
            let func = view.imported_funcs + def;
            let sig = view.sig_of_func(func as u32).expect("signature").clone();
            let code = &entry.body[..entry.body.len() - 1];
            let insts = decode_body(code, 0).expect("decodes");
            let n = sig.params.len() + entry.locals.len();
            let ty = |l: usize| -> ValKind {
                if l < sig.params.len() {
                    sig.params[l]
                } else {
                    entry.locals[l - sig.params.len()]
                }
            };
            // The type a no-operand producer pushes.
            let produced =
                |x: &trust_cg_verify::wasm_cfg_proofs::DecodedInst| match (x.opcode, &x.imm) {
                    (0x20, Imm::Index(l)) if (*l as usize) < n => Some(ty(*l as usize)),
                    (0x23, Imm::Index(g)) => view.globals.get(*g as usize).copied(),
                    (0x41, _) => Some(ValKind::I32),
                    (0x42, _) => Some(ValKind::I64),
                    _ => None,
                };
            let bytes_of = |i: usize| &code[insts[i].offset..insts[i].offset + insts[i].size];
            // The first instruction of the one-value expression tree ending
            // just before `end` (simple value instructions only).
            let tree_start = |end: usize| -> Option<usize> {
                let mut need = 1usize;
                let mut i = end;
                while need > 0 {
                    i = i.checked_sub(1)?;
                    let (pops, pushes) = arity(insts[i].opcode)?;
                    need = (need + pops).checked_sub(pushes)?;
                }
                Some(i)
            };
            let image: Vec<LocalImage> = (0..n as u32).map(LocalImage::Local).collect();
            // Random instructions, plus every `global.get` and the four
            // after it (the stack-pointer protocol is rare among random
            // picks).
            let mut picks: Vec<usize> = (0..32)
                .map(|_| (next() % insts.len() as u64) as usize)
                .collect();
            for (i, x) in insts.iter().enumerate() {
                if x.opcode == 0x23 {
                    picks.extend(i..(i + 5).min(insts.len()));
                }
            }
            for k in picks {
                let x = &insts[k];
                // (first byte replaced, end of the replaced range, new bytes)
                let (from, to, replacement): (usize, usize, Vec<u8>) = match (x.opcode, &x.imm) {
                    (0x20, Imm::Index(l)) if next() % 3 != 0 => {
                        let same: Vec<usize> = (0..n)
                            .filter(|&o| o != *l as usize && ty(o) == ty(*l as usize))
                            .collect();
                        if same.is_empty() {
                            continue;
                        }
                        let o = same[(next() % same.len() as u64) as usize];
                        let mut r = vec![0x20];
                        let mut v = o as u64;
                        loop {
                            let b = (v & 0x7f) as u8;
                            v >>= 7;
                            if v == 0 {
                                r.push(b);
                                break;
                            }
                            r.push(b | 0x80);
                        }
                        (x.offset, x.offset + x.size, r)
                    }
                    (0x41, Imm::Int(v)) if next() % 3 != 0 => {
                        let v = (*v as i32).wrapping_add(1 + (next() % 3) as i32);
                        let mut r = vec![0x41];
                        let mut v = i64::from(v);
                        loop {
                            let b = (v & 0x7f) as u8;
                            v >>= 7;
                            let done = (v == 0 && b & 0x40 == 0) || (v == -1 && b & 0x40 != 0);
                            r.push(if done { b } else { b | 0x80 });
                            if done {
                                break;
                            }
                        }
                        (x.offset, x.offset + x.size, r)
                    }
                    (0x46..=0x4f | 0x6a..=0x78, _) => {
                        // An i32 binary operator's two operand trees swapped.
                        let Some(right) = tree_start(k) else { continue };
                        let Some(left) = tree_start(right) else {
                            continue;
                        };
                        swaps += 1;
                        global_moves +=
                            usize::from(insts[left..k].iter().any(|y| y.opcode == 0x23));
                        let (l, r) = (insts[left].offset, insts[right].offset);
                        let mut v = code[r..x.offset].to_vec();
                        v.extend_from_slice(&code[l..r]);
                        (l, x.offset, v)
                    }
                    _ if k >= 1
                        && produced(x).is_some()
                        && produced(x) == produced(&insts[k - 1])
                        && bytes_of(k) != bytes_of(k - 1) =>
                    {
                        // Two producers of one type swapped: operand order.
                        swaps += 1;
                        global_moves +=
                            usize::from(x.opcode == 0x23 || insts[k - 1].opcode == 0x23);
                        let mut r = bytes_of(k).to_vec();
                        r.extend_from_slice(bytes_of(k - 1));
                        (insts[k - 1].offset, x.offset + x.size, r)
                    }
                    (0x23, _)
                        if k >= 2
                            && insts[k - 1].opcode == 0x1a
                            && produced(&insts[k - 2]).is_some()
                            && produced(&insts[k - 2]) == produced(x) =>
                    {
                        // `p; drop; global.get` -> `p; global.get; drop`.
                        global_moves += 1;
                        let mut r = bytes_of(k).to_vec();
                        r.push(0x1a);
                        (insts[k - 1].offset, x.offset + x.size, r)
                    }
                    _ => continue,
                };
                let mut mutant = code[..from].to_vec();
                mutant.extend(&replacement);
                mutant.extend(&code[to..]);
                if mutant == code {
                    continue;
                }
                tried += 1;
                let verdict = tv_validate(&TvRequest {
                    params: &sig.params,
                    pre: TvBody {
                        locals: &entry.locals,
                        code,
                        relocs: &[],
                    },
                    post: TvBody {
                        locals: &entry.locals,
                        code: &mutant,
                        relocs: &[],
                    },
                    image: &image,
                    facts: &[],
                    types: &ViewTypes(&view),
                    residual: ResidualPolicy::Refuse,
                    max_work: 1 << 24,
                });
                if verdict.is_err() {
                    continue;
                }
                accepted += 1;
                let Some(want) = &original else { continue };
                mutant.push(0x0b);
                let patched = with_body(&bytes, def, &mutant);
                // Every mutation keeps every operand's type.
                validate(&patched);
                let got = run_wasm(&patched, exports).expect("node ran the original");
                assert_eq!(
                    &got, want,
                    "{tag}, function {func}: an accepted mutant at instruction {k} \
                     changed the results"
                );
                executed += 1;
            }
        }
    }
    eprintln!(
        "mutants: {tried} tried ({swaps} swaps, {global_moves} moving a global.get), \
         {accepted} accepted, {executed} executed"
    );
    assert!(tried > 100, "too few mutants were generated: {tried}");
    assert!(swaps > 10, "too few operand swaps were generated: {swaps}");
    assert!(global_moves > 0, "no global.get was moved");
    assert!(accepted < tried, "the validator accepted every mutant");
}

// ---- The control cleanup ----

/// The control cleanup runs on the hand-written programs and random CFGs:
/// branches, `return`s and blocks are removed, every cleanup is accepted
/// (`check` requires no refusal), and the cleaned modules agree with the
/// interpreter (`check` runs them).
#[test]
fn control_cleanup_is_validated_and_removes_branches() {
    let mut rules: std::collections::BTreeMap<String, usize> = Default::default();
    let mut cleaned = 0usize;
    let mut states = 0usize;
    let mut add = |s: &wasm::WasmLocalOptSummary| {
        cleaned += s.control_cleaned;
        states += s.tv_control_states;
        for (k, v) in &s.control_rewrites {
            *rules.entry(k.clone()).or_default() += v;
        }
    };
    let module = parse(PROGRAMS);
    let exports: Vec<Export> = ["collatz", "wide", "floats", "frame", "dispatch"]
        .iter()
        .map(|n| Export {
            name: n.to_string(),
            w: W::I64,
            calls: rows(PAIRS),
        })
        .collect();
    add(&check("control programs", &module, &exports));
    for seed in 0..4u64 {
        let mut module = cfg_fuzz::build_fuzz_module(seed ^ 0xC7_0001, 10);
        module.target_info = Some(wasm::wasm32_target_info());
        let exports: Vec<Export> = (0..10)
            .map(|i| Export {
                name: format!("f{i}"),
                w: W::I32,
                calls: vec![vec![0, 0, 0, 0], vec![1, -2, 3, -4], vec![17, 5, -9, 100]],
            })
            .collect();
        add(&check(&format!("control fuzz {seed}"), &module, &exports));
    }
    for seed in 1..=4u64 {
        let module = parse(&random_cfg(seed, 3 + seed % 5));
        let exports = [Export {
            name: "f".to_string(),
            w: W::I64,
            calls: rows(PAIRS),
        }];
        add(&check(
            &format!("control irreducible {seed}"),
            &module,
            &exports,
        ));
    }
    eprintln!("control cleanup: {cleaned} functions, {states} states, {rules:?}");
    assert!(cleaned > 0, "no function was cleaned");
    assert!(states > 0);
    assert!(rules.get("br").copied().unwrap_or(0) > 0, "{rules:?}");
    assert!(rules.get("return").copied().unwrap_or(0) > 0, "{rules:?}");
    assert!(rules.get("block").copied().unwrap_or(0) > 0, "{rules:?}");
}

/// Structure of a decoded body: the matching `end` of every opener and the
/// innermost opener enclosing every instruction (`usize::MAX`: the function).
fn structure(insts: &[trust_cg_verify::wasm_cfg_proofs::DecodedInst]) -> (Vec<usize>, Vec<usize>) {
    let n = insts.len();
    let (mut end_of, mut parent) = (vec![usize::MAX; n], vec![usize::MAX; n]);
    let mut stack: Vec<usize> = Vec::new();
    for (i, x) in insts.iter().enumerate() {
        parent[i] = stack.last().copied().unwrap_or(usize::MAX);
        match x.opcode {
            0x02..=0x04 => stack.push(i),
            0x0b => {
                if let Some(o) = stack.pop() {
                    end_of[o] = i;
                }
            }
            _ => {}
        }
    }
    (end_of, parent)
}

fn uleb(v: u64) -> Vec<u8> {
    let mut out = Vec::new();
    let mut v = v;
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            return out;
        }
        out.push(b | 0x80);
    }
}

/// Mutate the control of baseline (O0) bodies — a `br`, `br_if` (as `drop`)
/// or `return` deleted, a branch depth moved by one, a `block` or `loop`
/// unwrapped with and without renumbering the branches inside it, an `else`
/// deleted, a run of straight-line code deleted, a `br 0` inserted before an
/// `end` — and validate each mutant against its original with
/// `validate_control`. Every mutant the validator ACCEPTS must validate and
/// compute what the original computes in node.
#[test]
fn every_control_mutant_the_validator_accepts_behaves_like_the_original() {
    use trust_cg_verify::wasm_cfg_proofs::{Imm, decode_body};
    use trust_cg_verify::wasm_local_tv::{ControlTvRequest, TvBody, validate_control};
    let mut subjects: Vec<(String, Module, Vec<Export>)> = Vec::new();
    for seed in 0..8u64 {
        let mut module = cfg_fuzz::build_fuzz_module(seed ^ 0xC0FFEE, 8);
        module.target_info = Some(wasm::wasm32_target_info());
        let exports: Vec<Export> = (0..8)
            .map(|i| Export {
                name: format!("f{i}"),
                w: W::I32,
                calls: vec![
                    vec![0, 0, 0, 0],
                    vec![1, -2, 3, -4],
                    vec![17, 5, -9, 100],
                    vec![-1000, 999, 0, 7],
                ],
            })
            .collect();
        subjects.push((format!("fuzz seed {seed}"), module, exports));
    }
    for seed in 1..=8u64 {
        let exports = vec![Export {
            name: "f".to_string(),
            w: W::I64,
            calls: rows(PAIRS),
        }];
        subjects.push((
            format!("irreducible {seed}"),
            parse(&random_cfg(seed, 3 + seed % 5)),
            exports,
        ));
    }
    let names = ["collatz", "wide", "floats", "frame", "dispatch"];
    subjects.push((
        "programs".to_string(),
        parse(PROGRAMS),
        names
            .iter()
            .map(|n| Export {
                name: n.to_string(),
                w: W::I64,
                calls: rows(PAIRS),
            })
            .collect(),
    ));
    let license = permit_unlicensed();
    let (mut tried, mut accepted, mut executed) = (0usize, 0usize, 0usize);
    for (subject, (tag, module, exports)) in subjects.iter().enumerate() {
        let (bytes, _) = wasm::compile_module_with_evidence_policy_license_options(
            module,
            &wasm::WasmModulePolicy::closed(),
            &license,
            wasm::WasmOptOptions {
                level: OptLevel::O0,
                mid_end: true,
            },
        )
        .expect("compiles at O0");
        let view = trust_cg_verify::wasm_cfg_proofs::decode_module(&bytes).expect("decodes");
        let original = run_wasm(&bytes, exports);
        let mut rng = 0xD1B5_4A32_D192_ED03u64 ^ subject as u64;
        let mut next = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };
        for (def, entry) in view.code.iter().enumerate() {
            let func = view.imported_funcs + def;
            let sig = view.sig_of_func(func as u32).expect("signature").clone();
            let code = &entry.body[..entry.body.len() - 1];
            let insts = decode_body(code, 0).expect("decodes");
            if insts.is_empty() {
                continue;
            }
            let (end_of, parent) = structure(&insts);
            let bytes_of =
                |i: usize| code[insts[i].offset..insts[i].offset + insts[i].size].to_vec();
            // Re-encode with `drop` deleted instructions and `with`
            // replacing some; branch depths renumbered over deleted openers
            // when `renumber`.
            let rebuild = |drop: &[usize], with: &[(usize, Vec<u8>)], renumber: bool| -> Vec<u8> {
                let mut out = Vec::new();
                for (i, x) in insts.iter().enumerate() {
                    if drop.contains(&i) {
                        continue;
                    }
                    if let Some((_, r)) = with.iter().find(|(k, _)| *k == i) {
                        out.extend(r);
                        continue;
                    }
                    let depth = |d: u32| -> u32 {
                        if !renumber {
                            return d;
                        }
                        let (mut o, mut k) = (parent[i], 0u32);
                        for _ in 0..d {
                            if o == usize::MAX {
                                return d;
                            }
                            if !drop.contains(&o) {
                                k += 1;
                            }
                            o = parent[o];
                        }
                        k
                    };
                    match &x.imm {
                        Imm::Depth(d) => {
                            out.push(x.opcode);
                            out.extend(uleb(u64::from(depth(*d))));
                        }
                        Imm::Table { targets, default } => {
                            out.push(0x0e);
                            out.extend(uleb(targets.len() as u64));
                            for t in targets {
                                out.extend(uleb(u64::from(depth(*t))));
                            }
                            out.extend(uleb(u64::from(depth(*default))));
                        }
                        _ => out.extend(bytes_of(i)),
                    }
                }
                out
            };
            // Plausible cleanups (a branch or return right before an `end`
            // or `else` deleted, a construct unwrapped and renumbered, the
            // instruction after a transfer deleted), then random mutations.
            let transfer = |op: u8| matches!(op, 0x00 | 0x0c | 0x0e | 0x0f);
            let mut plans: Vec<(usize, u64)> = Vec::new();
            for (k, x) in insts.iter().enumerate() {
                let before_end = insts
                    .get(k + 1)
                    .is_none_or(|y| matches!(y.opcode, 0x05 | 0x0b));
                if matches!(x.opcode, 0x0c | 0x0f) && before_end {
                    plans.push((k, 0));
                }
                if matches!(x.opcode, 0x02 | 0x03) {
                    plans.push((k, 6));
                }
                if k > 0 && transfer(insts[k - 1].opcode) && !matches!(x.opcode, 0x05 | 0x0b) {
                    plans.push((k, 7));
                }
            }
            for _ in 0..24 {
                plans.push(((next() % insts.len() as u64) as usize, next() % 6));
            }
            for (k, kind) in plans {
                let x = &insts[k];
                let mutant = match (kind, x.opcode) {
                    (0, 0x0c | 0x0f) => rebuild(&[k], &[], false),
                    (0, 0x0d) => rebuild(&[], &[(k, vec![0x1a])], false),
                    (1, 0x0c | 0x0d) => {
                        let Imm::Depth(d) = x.imm else { continue };
                        let d = if next() % 2 == 0 {
                            d + 1
                        } else {
                            d.saturating_sub(1)
                        };
                        let mut r = vec![x.opcode];
                        r.extend(uleb(u64::from(d)));
                        rebuild(&[], &[(k, r)], false)
                    }
                    (2, 0x02 | 0x03) if end_of[k] != usize::MAX => {
                        rebuild(&[k, end_of[k]], &[], next() % 2 == 0)
                    }
                    (3, 0x05) => rebuild(&[k], &[], false),
                    (4, op) if !matches!(op, 0x00 | 0x02..=0x05 | 0x0b..=0x0f) => {
                        let mut run = vec![k];
                        let mut j = k + 1;
                        while j < insts.len()
                            && !matches!(insts[j].opcode, 0x00 | 0x02..=0x05 | 0x0b..=0x0f)
                            && next() % 2 == 0
                        {
                            run.push(j);
                            j += 1;
                        }
                        rebuild(&run, &[], false)
                    }
                    (5, 0x05 | 0x0b) => {
                        let mut r = vec![0x0c, 0x00];
                        r.extend(bytes_of(k));
                        rebuild(&[], &[(k, r)], false)
                    }
                    (6, _) if end_of[k] != usize::MAX => rebuild(&[k, end_of[k]], &[], true),
                    (7, _) => {
                        // The whole run up to the `else` or `end` closing
                        // the frame, nested constructs included.
                        let (mut j, mut depth) = (k, 0usize);
                        while j < insts.len() {
                            match insts[j].opcode {
                                0x05 | 0x0b if depth == 0 => break,
                                0x02..=0x04 => depth += 1,
                                0x0b => depth -= 1,
                                _ => {}
                            }
                            j += 1;
                        }
                        rebuild(&(k..j).collect::<Vec<_>>(), &[], false)
                    }
                    _ => continue,
                };
                if mutant == code {
                    continue;
                }
                tried += 1;
                let verdict = validate_control(&ControlTvRequest {
                    results: sig.results.len(),
                    pre: TvBody {
                        locals: &entry.locals,
                        code,
                        relocs: &[],
                    },
                    post: TvBody {
                        locals: &entry.locals,
                        code: &mutant,
                        relocs: &[],
                    },
                    types: &ViewTypes(&view),
                    max_work: 1 << 24,
                });
                if verdict.is_err() {
                    continue;
                }
                accepted += 1;
                let mut body = mutant.clone();
                body.push(0x0b);
                let patched = with_body(&bytes, def, &body);
                validate(&patched);
                let Some(want) = &original else { continue };
                let got = run_wasm(&patched, exports).expect("node ran the original");
                assert_eq!(
                    &got, want,
                    "{tag}, function {func}: an accepted control mutant at instruction {k} \
                     changed the results"
                );
                executed += 1;
            }
        }
    }
    eprintln!("control mutants: {tried} tried, {accepted} accepted, {executed} executed");
    assert!(
        tried > 100,
        "too few control mutants were generated: {tried}"
    );
    assert!(
        accepted >= 10,
        "the validator accepted too few control mutants: {accepted}"
    );
    assert!(
        accepted < tried,
        "the validator accepted every control mutant"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
/// These hand-written backend fixtures carry no source proof. Their explicit
/// legacy test policy must never change either production default.
#[test]
fn legacy_fixtures_remain_unlicensed_by_default() {
    let module = parse(
        "functy.0 = (i32) -> (i32)\n\nfn @legacy(functy.0) {\nbb0(%0: i32):\n    ret %0\n}\n",
    );
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "valid legacy fixture: {errors:?}");
    let policy = trust_cg_codegen::CodegenLicensePolicy::default();
    for result in [
        wasm::compile_module_with_license(&module, &policy),
        wasm::compile_object_with_license(&module, &policy),
    ] {
        let error =
            result.expect_err("an unlicensed fixture must not acquire production authority");
        assert!(
            error.to_string().contains("carries no codegen license"),
            "{error}"
        );
    }
}

fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
