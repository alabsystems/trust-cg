// trust-cg-codegen/tests/wasm_p5_inline.rs - wasm32 lane: inlining before scalar replacement
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Call-site inlining in the trust-ir mid-end (`trust_cg_irmid`, P5 stage B)
//! on the wasm32 lane:
//!
//! * at O2 a caller whose slot escaped only through a small out-pointer
//!   callee (`init`) inlines it, and scalar replacement then promotes the
//!   slot: the caller's body makes no call and touches no global (no frame),
//!   where at O0 it calls and carves a frame;
//! * a callee returning from two blocks (`pick`) is spliced and the call
//!   disappears;
//! * a callee the producer's side table names (`#[inline(never)]`, here
//!   `kept`) stays a call on the object route, and the same object without
//!   the hint inlines it;
//! * an allocating callee (`leaf`) is inlined into a caller that does not
//!   recur (`once`) and stays a call in one on a cycle of direct calls
//!   (`walk`), whose every level would otherwise hold its slot;
//! * the evidence names the pass and no rollback;
//! * every form — O0 and O2, closed, sized and linked — agrees with the
//!   trust-ir reference interpreter in node.
//!
//! Node is required to execute the wasm and `wasm-ld` (`WASM_LD`) to link the
//! object; the absence of either is a loud SKIP.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{self, WasmInlineHints, WasmModulePolicy, WasmOptOptions};
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

const PROGRAM: &str = "module \"p5i\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
type ty.0 = i32\n\n\
functy.0 = (i32, i32) -> (i32)\n\
functy.1 = (ptr, i32, i32) -> ()\n\n\
internal fn @init(functy.1) {\n\
bb0(%0: ptr, %1: i32, %2: i32):\n\
\x20   %3 = const i32 4\n\
\x20   %4 = gep inbounds u8, ptr %0, %3\n\
\x20   store i32 %1, ptr %0\n\
\x20   %5 = mul i32 %1, %2\n\
\x20   store i32 %5, ptr %4\n\
\x20   ret\n\
}\n\n\
fn @pair(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 2], align 4\n\
\x20   call @func.0(%2, %0, %1)\n\
\x20   %3 = const i32 4\n\
\x20   %4 = gep inbounds u8, ptr %2, %3\n\
\x20   %5 = load i32, ptr %2\n\
\x20   %6 = load i32, ptr %4\n\
\x20   %7 = sub i32 %6, %5\n\
\x20   ret %7\n\
}\n\n\
fn @pick(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = icmp slt i32 %0, %1\n\
\x20   condbr %2, bb1, bb2\n\
bb1:\n\
\x20   %3 = sub i32 %1, %0\n\
\x20   ret %3\n\
bb2:\n\
\x20   ret %0\n\
}\n\n\
fn @sel(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = call @func.2(%0, %1)\n\
\x20   %3 = call @func.2(%1, %2)\n\
\x20   %4 = add i32 %2, %3\n\
\x20   ret %4\n\
}\n\n\
internal fn @kept(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = xor i32 %0, %1\n\
\x20   ret %2\n\
}\n\n\
fn @hinted(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = call @func.4(%0, %1)\n\
\x20   %3 = add i32 %2, %1\n\
\x20   ret %3\n\
}\n";

const NAMES: &[&str] = &["pair", "pick", "sel", "hinted"];

const ROWS: &[(i64, i64)] = &[(0, 0), (1, 2), (7, 3), (-5, 9), (100, 10), (3, 0), (-1, 15)];

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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_p5i_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run `name(a, b)` for every row in node; `None` when node is absent.
fn run(bytes: &[u8], name: &str) -> Option<Vec<i64>> {
    run_rows(bytes, name, ROWS)
}

/// Run `name(a, b)` for every row of `rows` in node.
fn run_rows(bytes: &[u8], name: &str, rows: &[(i64, i64)]) -> Option<Vec<i64>> {
    let Some(node) = node() else {
        eprintln!("SKIP: node not found; the module was not executed");
        return None;
    };
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
    let dir = scratch("run");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let rows: Vec<String> = rows.iter().map(|(a, b)| format!("[{a},{b}]")).collect();
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
    for &name in NAMES {
        let want: Vec<i64> = ROWS
            .iter()
            .map(|&(a, b)| interpret(module, name, a, b))
            .collect();
        if let Some(got) = run(bytes, name) {
            assert_eq!(got, want, "{tag}: {name} disagrees with the interpreter");
        }
    }
}

/// The body of export `name` and its parameter count.
fn exported_body<'a>(bytes: &'a [u8], name: &str) -> (wasmparser::FunctionBody<'a>, u32) {
    let mut index = None;
    let mut imported = 0u32;
    let mut params: Vec<u32> = Vec::new();
    let mut types: Vec<u32> = Vec::new();
    let mut bodies = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        match payload.expect("parse") {
            wasmparser::Payload::TypeSection(r) => {
                for group in r {
                    for ty in group.expect("type").into_types() {
                        params.push(match ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(f) => f.params().len() as u32,
                            _ => 0,
                        });
                    }
                }
            }
            wasmparser::Payload::ImportSection(r) => {
                for import in r {
                    if matches!(import.expect("import").ty, wasmparser::TypeRef::Func(_)) {
                        imported += 1;
                    }
                }
            }
            wasmparser::Payload::FunctionSection(r) => {
                for f in r {
                    types.push(f.expect("func"));
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
    (bodies.swap_remove(index), params[types[index] as usize])
}

/// The global reads and writes in the body of export `name`.
fn global_accesses(bytes: &[u8], name: &str) -> (usize, usize) {
    let (body, _) = exported_body(bytes, name);
    let (mut gets, mut sets) = (0, 0);
    for op in body.get_operators_reader().expect("ops").into_iter() {
        match op.expect("op") {
            wasmparser::Operator::GlobalGet { .. } => gets += 1,
            wasmparser::Operator::GlobalSet { .. } => sets += 1,
            _ => {}
        }
    }
    (gets, sets)
}

/// The direct calls in the body of export `name`.
fn calls(bytes: &[u8], name: &str) -> usize {
    let (body, _) = exported_body(bytes, name);
    body.get_operators_reader()
        .expect("ops")
        .into_iter()
        .filter(|op| matches!(op, Ok(wasmparser::Operator::Call { .. })))
        .count()
}

#[test]
fn an_inlined_out_pointer_callee_leaves_no_frame_and_no_call() {
    let module = program();
    let (o0, _) = closed(&module, OptLevel::O0);
    assert_eq!(calls(&o0, "pair"), 1);
    let (gets, sets) = global_accesses(&o0, "pair");
    assert!(gets > 0 && sets > 0, "O0 `pair` carves a frame");
    assert_eq!(calls(&o0, "sel"), 2);
    assert_agrees("O0", &o0, &module);

    let (o2, evidence) = closed(&module, OptLevel::O2);
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    let inline = mid
        .passes
        .iter()
        .find(|p| p.name == "inline")
        .expect("inline");
    assert_eq!(inline.functions_changed, 3, "{inline:?}");
    assert_eq!(
        inline.refinements, 4,
        "init once, pick twice, kept once: {inline:?}"
    );
    for name in ["pair", "sel", "hinted"] {
        assert_eq!(calls(&o2, name), 0, "O2 `{name}` calls nothing");
    }
    assert_eq!(
        global_accesses(&o2, "pair"),
        (0, 0),
        "O2 `pair` has no prologue, epilogue, stack-pointer update or stack guard"
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
fn the_object_lane_honours_the_never_inline_side_table_and_links() {
    let module = program();
    let hints = WasmInlineHints {
        never_inline: ["kept".to_string()].into_iter().collect(),
        ..WasmInlineHints::default()
    };
    let (object, evidence) = wasm::compile_object_with_evidence_license_options_hints(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2),
        &hints,
    )
    .expect("compile the object");
    assert!(evidence.mid_end.applied);
    let inline = evidence
        .mid_end
        .passes
        .iter()
        .find(|p| p.name == "inline")
        .expect("inline");
    assert_eq!(inline.refinements, 3, "`kept` stays called: {inline:?}");
    let (_, unhinted) = wasm::compile_object_with_evidence_license_options(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2),
    )
    .expect("compile the object without hints");
    let inline = unhinted
        .mid_end
        .passes
        .iter()
        .find(|p| p.name == "inline")
        .expect("inline");
    assert_eq!(inline.refinements, 4, "{inline:?}");
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
    assert_eq!(
        calls(&linked, "hinted"),
        1,
        "the hinted callee stays a call"
    );
    assert_eq!(calls(&linked, "pair"), 0);
    assert_eq!(
        global_accesses(&linked, "pair"),
        (0, 0),
        "linked O2 `pair` has no frame"
    );
    assert_agrees("linked O2", &linked, &module);
}

/// `leaf` allocates; `walk` reaches itself and calls `leaf` only at its base;
/// `once` calls it from a caller that does not recur.
const RECURSIVE: &str = "module \"p5r\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
type ty.0 = i32\n\n\
functy.0 = (i32, i32) -> (i32)\n\n\
internal fn @leaf(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 16], align 4\n\
\x20   %3 = const i32 15\n\
\x20   %4 = and i32 %0, %3\n\
\x20   %5 = const i32 4\n\
\x20   %6 = mul i32 %4, %5\n\
\x20   %7 = gep inbounds u8, ptr %2, %6\n\
\x20   store i32 %1, ptr %7\n\
\x20   %8 = load i32, ptr %7\n\
\x20   %9 = xor i32 %8, %0\n\
\x20   ret %9\n\
}\n\n\
fn @walk(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = const i32 15\n\
\x20   %3 = and i32 %0, %2\n\
\x20   %4 = const i32 0\n\
\x20   %5 = icmp eq i32 %3, %4\n\
\x20   condbr %5, bb1, bb2\n\
bb1:\n\
\x20   %6 = call @func.0(%0, %1)\n\
\x20   ret %6\n\
bb2:\n\
\x20   %7 = const i32 1\n\
\x20   %8 = sub i32 %3, %7\n\
\x20   %9 = xor i32 %1, %3\n\
\x20   %10 = call @func.1(%8, %9)\n\
\x20   %11 = add i32 %10, %3\n\
\x20   ret %11\n\
}\n\n\
fn @once(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = call @func.0(%1, %0)\n\
\x20   %3 = add i32 %2, %0\n\
\x20   ret %3\n\
}\n";

#[test]
fn an_allocating_callee_stays_a_call_in_a_recursive_caller() {
    let module = trust_ir::parser::parse_module(RECURSIVE).expect("parse the test program");
    let (o2, evidence) = closed(&module, OptLevel::O2);
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    let inline = mid
        .passes
        .iter()
        .find(|p| p.name == "inline")
        .expect("inline");
    assert_eq!(inline.refinements, 1, "`leaf` into `once` only: {inline:?}");
    assert_eq!(calls(&o2, "once"), 0, "the caller that does not recur");
    assert_eq!(
        calls(&o2, "walk"),
        2,
        "`walk` keeps its own call and the call of `leaf`"
    );
    let rows: &[(i64, i64)] = &[(0, 5), (1, 2), (7, 3), (15, -9), (31, 10), (-1, 15)];
    for (tag, bytes) in [("O0", closed(&module, OptLevel::O0).0), ("O2", o2)] {
        for name in ["walk", "once"] {
            let want: Vec<i64> = rows
                .iter()
                .map(|&(a, b)| interpret(&module, name, a, b))
                .collect();
            if let Some(got) = run_rows(&bytes, name, rows) {
                assert_eq!(got, want, "{tag}: {name} disagrees with the interpreter");
            }
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
