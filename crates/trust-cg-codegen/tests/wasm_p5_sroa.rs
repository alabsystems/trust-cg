// trust-cg-codegen/tests/wasm_p5_sroa.rs - wasm32 lane: scalar replacement and frame elision
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Scalar replacement in the trust-ir mid-end (`trust_cg_irmid`, P5 stage A)
//! on the wasm32 lane, and the frame elision it enables:
//!
//! * at O0 every function with a slot carves a shadow-stack frame (it reads
//!   and writes `__stack_pointer`);
//! * at O2 a function whose slots the mid-end promotes — a loop-carried
//!   accumulator and a field joined at a diamond, a signedness view and a
//!   float's bits (stage A); a pointer slot holding a slot's address, the
//!   bridge's field writes and reads through a slot, and a word copied over
//!   narrower fields (stage D) — keeps no frame: its body touches no global
//!   at all (no prologue, epilogue, stack-pointer update or stack guard),
//!   while a function whose slot is observed (its address read as an
//!   integer) keeps its frame;
//! * the frame-bounds guard (`wasm::frame_bounds`) accepts that frame's
//!   emitted body against the size its prologue carves, and refuses the same
//!   body with a frame access moved past it;
//! * the evidence names the pass, the promoted allocations and no rollback;
//! * every form — O0 and O2, closed, sized and linked — agrees with the
//!   trust-ir reference interpreter in node.
//!
//! Node is required to execute the wasm and `wasm-ld` (`WASM_LD`) to link the
//! object; the absence of either is a loud SKIP.
//!
//! The entries this test drives (`compile_module_with_evidence_policy_license_options`,
//! `compile_sized_closed_module_with_evidence_license_options`,
//! `compile_object_with_evidence_license_options`), `WasmOptOptions::mid_end`
//! and the `mid_end` evidence it reads (`IrmidReport`'s pass statistics and
//! allocation counts) are provisional surfaces pending the owner's sign-off:
//! this test follows them if they change, and is not a contract for their
//! shape.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::frame_bounds::{self, FrameShape};
use trust_cg_codegen::wasm::{self, WasmModulePolicy, WasmOptOptions};
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

const PROGRAM: &str = "module \"p5\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
type ty.0 = i32\n\n\
functy.0 = (i32, i32) -> (i32)\n\n\
fn @acc(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 2], align 4\n\
\x20   %3 = const i32 4\n\
\x20   %4 = gep inbounds u8, ptr %2, %3\n\
\x20   %30 = alloca i32\n\
\x20   %31 = const i32 0\n\
\x20   store i32 %31, ptr %30\n\
\x20   store i32 %0, ptr %2\n\
\x20   store i32 %1, ptr %4\n\
\x20   %5 = icmp slt i32 %0, %1\n\
\x20   condbr %5, bb1, bb2\n\
bb1:\n\
\x20   store i32 %1, ptr %2\n\
\x20   br bb3\n\
bb2:\n\
\x20   br bb3\n\
bb3:\n\
\x20   %32 = const i32 15\n\
\x20   %33 = and i32 %1, %32\n\
\x20   br bb4(%31)\n\
bb4(%34: i32):\n\
\x20   %35 = icmp slt i32 %34, %33\n\
\x20   condbr %35, bb5, bb6\n\
bb5:\n\
\x20   %36 = load i32, ptr %30\n\
\x20   %37 = load i32, ptr %2\n\
\x20   %38 = add i32 %36, %37\n\
\x20   store i32 %38, ptr %30\n\
\x20   %39 = const i32 1\n\
\x20   %40 = add i32 %34, %39\n\
\x20   br bb4(%40)\n\
bb6:\n\
\x20   %6 = load i32, ptr %2\n\
\x20   %7 = load i32, ptr %4\n\
\x20   %8 = load i32, ptr %30\n\
\x20   %9 = add i32 %6, %7\n\
\x20   %10 = add i32 %9, %8\n\
\x20   ret %10\n\
}\n\n\
fn @view(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca i32\n\
\x20   %3 = bitcast i32 %0 to u32\n\
\x20   store u32 %3, ptr %2\n\
\x20   %4 = load i32, ptr %2\n\
\x20   %5 = alloca f32\n\
\x20   %6 = sitofp i32 %1 to f32\n\
\x20   store f32 %6, ptr %5\n\
\x20   %7 = load i32, ptr %5\n\
\x20   %8 = xor i32 %4, %7\n\
\x20   ret %8\n\
}\n\n\
fn @keep(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca i32\n\
\x20   store i32 %0, ptr %2\n\
\x20   %3 = alloca ptr\n\
\x20   store ptr %2, ptr %3\n\
\x20   %4 = load ptr, ptr %3\n\
\x20   %5 = load i32, ptr %4\n\
\x20   %7 = ptrtoint ptr %4 to i32\n\
\x20   %8 = sub i32 %7, %7\n\
\x20   %9 = add i32 %5, %8\n\
\x20   %6 = add i32 %9, %1\n\
\x20   ret %6\n\
}\n\n\
fn @ptrs(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca i32\n\
\x20   %3 = alloca ptr\n\
\x20   store i32 %0, ptr %2\n\
\x20   %4 = ptrtoptr ptr %2 to &i32\n\
\x20   store &i32 %4, ptr %3\n\
\x20   %5 = load *const i32, ptr %3\n\
\x20   %6 = load i32, ptr %5\n\
\x20   %7 = sub i32 %6, %1\n\
\x20   ret %7\n\
}\n\n\
fn @thru(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 2], align 4\n\
\x20   %3 = const i32 4\n\
\x20   %4 = gep inbounds u8, ptr %2, %3\n\
\x20   store i32 %1, ptr %4\n\
\x20   store i32 %0, ptr %2\n\
\x20   %5 = load i32, ptr %4\n\
\x20   %6 = load i32, ptr %2\n\
\x20   %7 = mul i32 %6, %5\n\
\x20   ret %7\n\
}\n\n\
fn @parts(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca i64, align 8\n\
\x20   store i32 %0, ptr %2\n\
\x20   %3 = const i32 4\n\
\x20   %4 = gep inbounds u8, ptr %2, %3\n\
\x20   store i32 %1, ptr %4\n\
\x20   %5 = load i64, ptr %2\n\
\x20   %6 = alloca i64, align 8\n\
\x20   store i64 %5, ptr %6\n\
\x20   %7 = gep inbounds u8, ptr %6, %3\n\
\x20   %8 = load i32, ptr %7\n\
\x20   %9 = load u16, ptr %6\n\
\x20   %10 = zext u16 %9 to i32\n\
\x20   %11 = sub i32 %10, %8\n\
\x20   ret %11\n\
}\n";

const NAMES: &[&str] = &["acc", "view", "keep", "ptrs", "thru", "parts"];

const ROWS: &[(i64, i64)] = &[(0, 0), (1, 2), (7, 3), (-5, 9), (100, 10), (3, 0), (-1, 15)];

fn program() -> Module {
    let module = trust_ir::parser::parse_module(PROGRAM).expect("parse the test program");
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "valid scalar-replacement fixture: {errors:?}"
    );
    module
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
    // The interpreter reads the bridge's field access through a pointer as
    // a type error; `thru` stores `b` and `a` into its two lanes and returns
    // their product, as the lane executes it.
    if name == "thru" {
        return i64::from((a as i32).wrapping_mul(b as i32));
    }
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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_p5_{tag}_{}_{n}", std::process::id()));
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

/// Frame size and base local of a body whose prologue is `global.get;
/// local.set s; local.get s; i32.const F; i32.sub; [i32.const -a; i32.and;]
/// local.tee b`, or the same with `local.set s; local.get s` merged into
/// `local.tee s` by the emission pass.
fn prologue_frame(ops: &[wasmparser::Operator<'_>]) -> Option<FrameShape> {
    use wasmparser::Operator as O;
    let (size, rest) = match ops {
        [
            O::GlobalGet { .. },
            O::LocalSet { .. },
            O::LocalGet { .. },
            O::I32Const { value },
            O::I32Sub,
            rest @ ..,
        ]
        | [
            O::GlobalGet { .. },
            O::LocalTee { .. },
            O::I32Const { value },
            O::I32Sub,
            rest @ ..,
        ] => (u32::try_from(*value).ok()?, rest),
        _ => return None,
    };
    let base_local = match rest {
        [O::LocalTee { local_index }, ..]
        | [
            O::I32Const { .. },
            O::I32And,
            O::LocalTee { local_index },
            ..,
        ] => *local_index,
        _ => return None,
    };
    Some(FrameShape { size, base_local })
}

/// The frame of export `name` of the closed module `bytes`, its parameter
/// count, its declared local count, its instruction bytes, and the position
/// in them of the offset immediate of each `i32` load and store.
fn framed_body(bytes: &[u8], name: &str) -> (FrameShape, u32, usize, Vec<u8>, Vec<usize>) {
    let (body, params) = exported_body(bytes, name);
    let mut locals = 0usize;
    for l in body.get_locals_reader().expect("locals") {
        locals += l.expect("local").0 as usize;
    }
    let mut reader = body.get_operators_reader().expect("ops");
    let start = reader.original_position();
    let mut ops = Vec::new();
    let mut at = Vec::new();
    while !reader.eof() {
        at.push(reader.original_position() - start);
        ops.push(reader.read().expect("op"));
    }
    let frame = prologue_frame(&ops).unwrap_or_else(|| panic!("`{name}` has no frame prologue"));
    let code = bytes[start..body.range().end].to_vec();
    let mut offsets = Vec::new();
    for (op, &at) in ops.iter().zip(&at) {
        if let wasmparser::Operator::I32Load { memarg }
        | wasmparser::Operator::I32Store { memarg } = op
        {
            // Opcode, alignment and offset, each one byte here.
            assert!(memarg.align < 64 && memarg.offset < 64, "{op:?}");
            offsets.push(at + 2);
        }
    }
    (frame, params, locals, code, offsets)
}

#[test]
fn promoted_slots_leave_no_frame_and_an_escaped_slot_keeps_its_own() {
    let module = program();
    let (o0, _) = closed(&module, OptLevel::O0);
    for &name in NAMES {
        let (gets, sets) = global_accesses(&o0, name);
        assert!(
            gets > 0 && sets > 0,
            "O0 `{name}` carves a frame: {gets} global.get, {sets} global.set"
        );
    }
    assert_agrees("O0", &o0, &module);

    let (o2, evidence) = closed(&module, OptLevel::O2);
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    let sroa = mid.passes.iter().find(|p| p.name == "sroa").expect("sroa");
    assert!(sroa.functions_changed >= 5, "{sroa:?}");
    assert_eq!(mid.allocas_before, 11);
    assert_eq!(
        mid.allocas_after, 1,
        "only `keep`'s observed slot stays: {mid:?}"
    );
    for name in ["acc", "view", "ptrs", "thru", "parts"] {
        assert_eq!(
            global_accesses(&o2, name),
            (0, 0),
            "O2 `{name}` has no prologue, epilogue, stack-pointer update or stack guard"
        );
    }
    let (gets, sets) = global_accesses(&o2, "keep");
    assert!(
        gets > 0 && sets > 0,
        "the observed slot keeps `keep`'s frame: {gets} global.get, {sets} global.set"
    );
    // The guard accepts `keep`'s emitted frame, and refuses each of its
    // memory accesses (all of them address the observed slot, which is the
    // whole frame) moved to the first byte past the frame.
    let (frame, params, locals, code, offsets) = framed_body(&o2, "keep");
    assert!(frame.size > 0 && frame.size < 64, "{frame:?}");
    assert_eq!(
        frame_bounds::check(&code, params, locals, frame, &Default::default()),
        Ok(())
    );
    assert!(!offsets.is_empty(), "`keep` accesses its slot");
    for at in offsets {
        let mut outside = code.clone();
        outside[at] = frame.size as u8;
        let err = frame_bounds::check(&outside, params, locals, frame, &Default::default())
            .expect_err("an access past the frame");
        assert!(err.contains(&format!("[{}, ", frame.size)), "{err}");
    }
    assert!(evidence.ran.contains(&"optimization_pipeline"));
    assert_eq!(evidence.verdict.as_str(), "missing_evidence");
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
fn the_object_lane_promotes_and_links() {
    let module = program();
    let (object, evidence) = wasm::compile_object_with_evidence_license_options(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2),
    )
    .expect("compile the object");
    assert!(evidence.mid_end.applied);
    assert_eq!(evidence.mid_end.allocas_after, 1);
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
    for name in ["acc", "view", "ptrs", "thru", "parts"] {
        assert_eq!(
            global_accesses(&linked, name),
            (0, 0),
            "linked O2 `{name}` has no frame"
        );
    }
    assert_agrees("linked O2", &linked, &module);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}

#[test]
fn pointer_operand_field_access_remains_refused() {
    let invalid = PROGRAM.replace("%5 = load i32, ptr %4", "%5 = extractfield i32 %2, 1");
    let module = trust_ir::parser::parse_module(&invalid).expect("malformed fixture parses");
    for result in [
        wasm::compile_module_with_license(&module, &permit_unlicensed()),
        wasm::compile_object_with_license(&module, &permit_unlicensed()),
    ] {
        let error =
            result.expect_err("field extraction cannot reinterpret a pointer as an aggregate");
        assert!(
            format!("{error:?}").contains("FieldAccessInvalid"),
            "{error}"
        );
    }
}
