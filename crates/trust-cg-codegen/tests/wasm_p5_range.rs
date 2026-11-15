// trust-cg-codegen/tests/wasm_p5_range.rs - wasm32 lane: the range rules
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The range rules in the trust-ir mid-end (`trust_cg_irmid`, P5 stage C) on
//! the wasm32 lane:
//!
//! * at O2 a bounds check its masked index decides (`(x & 63) < 64`) and an
//!   overflow check two bytes cannot trip (a saturating add) leave no branch
//!   in the emitted body, while an undecided check (`(x & 127) < 64`) keeps
//!   its branch; at O0 every check is emitted;
//! * the evidence names the pass on the two functions it changed and no
//!   rollback;
//! * every form — O0 and O2, closed, sized and linked — agrees with the
//!   trust-ir reference interpreter in node;
//! * in loops (`LOOPS`), a 4 x 4 nest's bounds check `i * 4 + k < 16` and
//!   its step's overflow check fold under the induction ranges, a scan's
//!   bounds check `i < len` folds under its loop test (`icmp_implied`) and
//!   its step's overflow check under the induction range, and a `switch` on
//!   `x & 1` loses its default: at O2 none of their panic arms (each
//!   returning its own sentinel) is emitted, at O0 all are, and every form
//!   agrees with the interpreter.
//!
//! Node is required to execute the wasm and `wasm-ld` (`WASM_LD`) to link the
//! object; the absence of either is a loud SKIP.
//!
//! The entries this test drives (`compile_module_with_evidence_policy_license_options`,
//! `compile_sized_closed_module_with_evidence_license_options`,
//! `compile_object_with_evidence_license_options`), `WasmOptOptions::mid_end`
//! and the `mid_end` evidence it reads (`IrmidReport`'s pass statistics,
//! the range pass's rule keys and rollbacks) are provisional surfaces
//! pending the owner's sign-off: this test follows them if they change, and
//! is not a contract for their shape.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{self, WasmModulePolicy, WasmOptOptions};
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

const PROGRAM: &str = "module \"p5c\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = (i32, i32) -> (i32)\n\n\
fn @table(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = bitcast i32 %0 to u32\n\
\x20   %3 = const u32 63\n\
\x20   %4 = and u32 %2, %3\n\
\x20   %5 = zext u32 %4 to usize\n\
\x20   %6 = const usize 64\n\
\x20   %7 = icmp ult usize %5, %6\n\
\x20   condbr %7, bb1, bb2\n\
bb1:\n\
\x20   %8 = bitcast u32 %4 to i32\n\
\x20   %9 = mul i32 %8, %1\n\
\x20   ret %9\n\
bb2:\n\
\x20   %10 = const i32 -1\n\
\x20   ret %10\n\
}\n\n\
fn @sat(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = trunc i32 %0 to u8\n\
\x20   %3 = trunc i32 %1 to u8\n\
\x20   %4 = zext u8 %2 to u32\n\
\x20   %5 = zext u8 %3 to u32\n\
\x20   %6, %7 = add.overflow u32 %4, %5\n\
\x20   %8 = const u32 4294967295\n\
\x20   %9 = select u32 %7, %8, %6\n\
\x20   %10 = const bool false\n\
\x20   %11 = icmp eq bool %7, %10\n\
\x20   condbr %11, bb1, bb2\n\
bb1:\n\
\x20   %12 = bitcast u32 %9 to i32\n\
\x20   ret %12\n\
bb2:\n\
\x20   %13 = const i32 -2\n\
\x20   ret %13\n\
}\n\n\
fn @keep(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = bitcast i32 %0 to u32\n\
\x20   %3 = const u32 127\n\
\x20   %4 = and u32 %2, %3\n\
\x20   %5 = zext u32 %4 to usize\n\
\x20   %6 = const usize 64\n\
\x20   %7 = icmp ult usize %5, %6\n\
\x20   condbr %7, bb1, bb2\n\
bb1:\n\
\x20   %8 = bitcast u32 %4 to i32\n\
\x20   %9 = add i32 %8, %1\n\
\x20   ret %9\n\
bb2:\n\
\x20   %10 = const i32 -1\n\
\x20   ret %10\n\
}\n";

const NAMES: &[&str] = &["table", "sat", "keep"];

const ROWS: &[(i64, i64)] = &[
    (0, 0),
    (1, 2),
    (63, 3),
    (64, 9),
    (100, 10),
    (-1, 15),
    (255, 255),
    (200, 100),
    (-129, 7),
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
            fuel: 1_000_000,
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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_p5c_{tag}_{}_{n}", std::process::id()));
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

/// The conditional control instructions (`if`, `br_if`, `br_table`) in the
/// body of export `name`.
fn branches(bytes: &[u8], name: &str) -> usize {
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
        .filter(|op| {
            matches!(
                op.as_ref().expect("op"),
                wasmparser::Operator::If { .. }
                    | wasmparser::Operator::BrIf { .. }
                    | wasmparser::Operator::BrTable { .. }
            )
        })
        .count()
}

#[test]
fn decided_checks_leave_no_branch_and_an_undecided_one_keeps_it() {
    let module = program();
    let (o0, _) = closed(&module, OptLevel::O0);
    for &name in NAMES {
        assert!(branches(&o0, name) > 0, "O0 `{name}` emits its check");
    }
    assert_agrees("O0", &o0, &module);

    let (o2, evidence) = closed(&module, OptLevel::O2);
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    let range = mid
        .passes
        .iter()
        .find(|p| p.name == "range")
        .expect("range");
    assert_eq!(range.functions_changed, 2, "{range:?}");
    assert_eq!(range.refinements, 0, "every range rewrite is exact");
    for name in ["table", "sat"] {
        assert_eq!(branches(&o2, name), 0, "O2 `{name}` has no check left");
    }
    assert!(
        branches(&o2, "keep") > 0,
        "O2 `keep` keeps its undecided check"
    );
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
fn the_object_lane_folds_and_links() {
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
    for name in ["table", "sat"] {
        assert_eq!(branches(&linked, name), 0, "linked O2 `{name}`");
    }
    assert_agrees("linked O2", &linked, &module);
}

/// Loops in the bridge's shape. Each panic arm returns a sentinel no other
/// code produces: `nest` 99999 (bounds) and 88888 (overflow), `scan` 77777
/// (bounds) and 66666 (overflow), `sw` 55555 (the `switch` default).
const LOOPS: &str = "module \"p5c_loops\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = (i32, i32) -> (i32)\n\n\
fn @nest(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = const u32 0\n\
\x20   %3 = bitcast i32 %0 to u32\n\
\x20   br bb1(%2, %3)\n\
bb1(%4: u32, %5: u32):\n\
\x20   %6 = const u32 4\n\
\x20   %7 = icmp ult u32 %4, %6\n\
\x20   condbr %7, bb2, bb7\n\
bb2:\n\
\x20   %8 = const u32 1\n\
\x20   %9, %10 = add.overflow u32 %4, %8\n\
\x20   condbr %10, bb9, bb10\n\
bb10:\n\
\x20   %11 = const u32 0\n\
\x20   br bb3(%4, %11, %5)\n\
bb3(%12: u32, %13: u32, %14: u32):\n\
\x20   %15 = const u32 4\n\
\x20   %16 = icmp ult u32 %13, %15\n\
\x20   condbr %16, bb4, bb6\n\
bb4:\n\
\x20   %17 = const u32 4\n\
\x20   %18 = mul u32 %12, %17\n\
\x20   %19 = add u32 %18, %13\n\
\x20   %20 = const u32 16\n\
\x20   %21 = icmp ult u32 %19, %20\n\
\x20   condbr %21, bb5, bb8\n\
bb5:\n\
\x20   %22 = const u32 31\n\
\x20   %23 = mul u32 %14, %22\n\
\x20   %24 = add u32 %23, %19\n\
\x20   %25 = const u32 1\n\
\x20   %26 = add u32 %13, %25\n\
\x20   br bb3(%12, %26, %24)\n\
bb6:\n\
\x20   br bb1(%9, %14)\n\
bb7:\n\
\x20   %27 = bitcast u32 %5 to i32\n\
\x20   %28 = add i32 %27, %1\n\
\x20   ret %28\n\
bb8:\n\
\x20   %29 = const i32 99999\n\
\x20   ret %29\n\
bb9:\n\
\x20   %30 = const i32 88888\n\
\x20   ret %30\n\
}\n\n\
fn @scan(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = bitcast i32 %0 to u32\n\
\x20   %3 = const u32 255\n\
\x20   %4 = and u32 %2, %3\n\
\x20   %5 = const u32 0\n\
\x20   %6 = bitcast i32 %1 to u32\n\
\x20   br bb1(%5, %6)\n\
bb1(%7: u32, %8: u32):\n\
\x20   %9 = icmp ult u32 %7, %4\n\
\x20   condbr %9, bb2, bb5\n\
bb2:\n\
\x20   %10 = icmp ult u32 %7, %4\n\
\x20   condbr %10, bb3, bb4\n\
bb3:\n\
\x20   %11 = const u32 1\n\
\x20   %12, %13 = add.overflow u32 %7, %11\n\
\x20   condbr %13, bb6, bb7\n\
bb7:\n\
\x20   %14 = const u32 3\n\
\x20   %15 = mul u32 %8, %14\n\
\x20   %16 = add u32 %15, %7\n\
\x20   br bb1(%12, %16)\n\
bb4:\n\
\x20   %17 = const i32 77777\n\
\x20   ret %17\n\
bb6:\n\
\x20   %18 = const i32 66666\n\
\x20   ret %18\n\
bb5:\n\
\x20   %19 = bitcast u32 %8 to i32\n\
\x20   ret %19\n\
}\n\n\
fn @sw(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = const i32 1\n\
\x20   %3 = and i32 %0, %2\n\
\x20   switch %3 [ 0: bb1 1: bb2 default: bb3 ]\n\
bb1:\n\
\x20   %4 = add i32 %1, %0\n\
\x20   ret %4\n\
bb2:\n\
\x20   %5 = sub i32 %1, %0\n\
\x20   ret %5\n\
bb3:\n\
\x20   %6 = const i32 55555\n\
\x20   ret %6\n\
}\n";

const LOOP_NAMES: &[&str] = &["nest", "scan", "sw"];

const SENTINELS: &[i64] = &[99999, 88888, 77777, 66666, 55555];

/// The `i32.const` immediates in the code section.
fn constants(bytes: &[u8]) -> Vec<i64> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::CodeSectionEntry(body) = payload.expect("parse") {
            for op in body.get_operators_reader().expect("ops") {
                if let wasmparser::Operator::I32Const { value } = op.expect("op") {
                    out.push(i64::from(value));
                }
            }
        }
    }
    out
}

#[test]
fn loop_bounds_and_overflow_checks_fold_under_induction_ranges() {
    let module = trust_ir::parser::parse_module(LOOPS).expect("parse the loops");
    let (o0, _) = closed(&module, OptLevel::O0);
    let o0_constants = constants(&o0);
    for sentinel in SENTINELS {
        assert!(
            o0_constants.contains(sentinel),
            "O0 emits panic arm {sentinel}"
        );
    }
    assert_agrees_on("loops O0", &o0, &module, LOOP_NAMES);

    let (o2, evidence) = closed(&module, OptLevel::O2);
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    let range = mid
        .passes
        .iter()
        .find(|p| p.name == "range")
        .expect("range");
    assert_eq!(range.functions_changed, 3, "{range:?}");
    assert_eq!(range.refinements, 0, "every range rewrite is exact");
    for (rule, at_least) in [
        ("icmp", 1),
        ("icmp_implied", 1),
        ("add_overflow", 2),
        ("switch", 1),
        ("param_interval", 3),
    ] {
        assert!(
            range.rules.get(rule).copied().unwrap_or(0) >= at_least,
            "{rule}: {range:?}"
        );
    }
    let o2_constants = constants(&o2);
    for sentinel in SENTINELS {
        assert!(
            !o2_constants.contains(sentinel),
            "O2 drops panic arm {sentinel}"
        );
    }
    assert_agrees_on("loops O2", &o2, &module, LOOP_NAMES);

    let (sized, _) = wasm::compile_sized_closed_module_with_evidence_license_options(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2),
    )
    .expect("compile the sized closed module");
    assert_agrees_on("loops sized O2", &sized, &module, LOOP_NAMES);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
