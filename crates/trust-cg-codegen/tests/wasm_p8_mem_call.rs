// trust-cg-codegen/tests/wasm_p8_mem_call.rs - wasm32 lane: memory library calls inlined
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The C memory library calls the rustc bridge emits for `ptr::copy`,
//! `ptr::swap`, `copy_nonoverlapping` and `write_bytes` (`memmove`,
//! `memcpy`, `memset` declarations with a constant count, and a `memmove`
//! of a run-time count, which stays a call: the default profile withholds
//! the run-time-count widening, OD-165's merge boundary) on the wasm32
//! lane:
//!
//! * at O2 the mid-end's memory-call rewrite (`mem_call`) turns each into
//!   the trust-ir instruction, the lane emits a copy of at most 32 bytes as
//!   `memory.copy` of its constant count without the zero-count guard, and
//!   the emission pass expands it into loads and stores: no call to the
//!   imported library function is left, no copy of at most 32 bytes keeps
//!   its `memory.copy`, and a fill and a longer copy keep their bulk
//!   operation under its zero-count guard; at O0 every call stays a call;
//! * every form agrees with the trust-ir reference interpreter, which runs
//!   the source in the mid-end differential's view (the declarations given
//!   the C library's bodies), on an overlapping `memmove` up by one byte and
//!   down by three, an unaligned `memcpy`, a `memset` of the argument's low
//!   byte, `ptr::swap`'s shape, a run-time count (which stays a call at
//!   O2) and a 40-byte copy (which keeps its `memory.copy`);
//!   node supplies the imported functions over the module's memory and
//!   counts their calls.
//!
//! Node is required to execute the wasm; its absence is a loud SKIP.
//!
//! The entry this test drives (`compile_module_with_evidence_policy_license_options`),
//! `WasmOptOptions::mid_end`, the `mid_end` evidence it reads (the pass
//! name `mem_call`) and `trust_cg_verify::trust_ir_mid_tv::interpretable_module`
//! are provisional surfaces pending the owner's sign-off: this test follows
//! them if they change, and is not a contract for their shape.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{
    self, WasmFuncImportPolicy, WasmMemoryPolicy, WasmModulePolicy, WasmOptOptions,
};
use trust_cg_verify::trust_ir_mid_tv::interpretable_module;
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

/// The five-word slot every function fills from its arguments, operates on
/// and folds into its result.
fn function(name: &str, op: &str) -> String {
    format!(
        "fn @{name}(functy.2) {{\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32), align 4\n\
\x20   store i32 %0, ptr %2\n\
\x20   %3 = const usize 4\n\
\x20   %4 = gep u8, ptr %2, %3\n\
\x20   store i32 %1, ptr %4\n\
\x20   %5 = const usize 8\n\
\x20   %6 = gep u8, ptr %2, %5\n\
\x20   %7 = xor i32 %0, %1\n\
\x20   store i32 %7, ptr %6\n\
\x20   %8 = const usize 12\n\
\x20   %9 = gep u8, ptr %2, %8\n\
\x20   %10 = add i32 %0, %1\n\
\x20   store i32 %10, ptr %9\n\
\x20   %50 = const usize 16\n\
\x20   %51 = gep u8, ptr %2, %50\n\
\x20   %52 = mul i32 %0, %1\n\
\x20   store i32 %52, ptr %51\n\
{op}\
\x20   %19 = load i32, ptr %2\n\
\x20   %20 = load i32, ptr %4\n\
\x20   %21 = load i32, ptr %6\n\
\x20   %22 = load i32, ptr %9\n\
\x20   %53 = load i32, ptr %51\n\
\x20   %23 = const i32 31\n\
\x20   %24 = mul i32 %19, %23\n\
\x20   %25 = xor i32 %24, %20\n\
\x20   %26 = mul i32 %25, %23\n\
\x20   %27 = xor i32 %26, %21\n\
\x20   %28 = mul i32 %27, %23\n\
\x20   %29 = xor i32 %28, %22\n\
\x20   %54 = mul i32 %29, %23\n\
\x20   %55 = xor i32 %54, %53\n\
\x20   ret %55\n\
}}\n\n"
    )
}

/// `callee(slot + to, slot + from, count)` (`memset`'s second argument is
/// the low byte of `%1`).
fn op(callee: u32, to: u32, from: u32, count: &str) -> String {
    let second = if callee == 2 {
        "\x20   %16 = copy i32 %1\n".to_string()
    } else {
        format!(
            "\x20   %13 = const usize {from}\n\
\x20   %14 = gep u8, ptr %2, %13\n\
\x20   %16 = ptrtoptr ptr %14 to *const u8\n"
        )
    };
    let dst = if callee == 2 {
        "\x20   %15 = copy ptr %12\n"
    } else {
        "\x20   %15 = ptrtoptr ptr %12 to *mut u8\n"
    };
    format!(
        "\x20   %11 = const usize {to}\n\
\x20   %12 = gep u8, ptr %2, %11\n\
{second}{dst}\
{count}\
\x20   %18 = call @func.{callee}(%15, %16, %17)\n"
    )
}

fn constant(n: u32) -> String {
    format!("\x20   %17 = const u32 {n}\n")
}

/// The functions: name, the operation, whether the O2 lane keeps a call
/// (the run-time count) and whether it keeps a `memory.copy` (over 32
/// bytes).
fn cases() -> Vec<(&'static str, String, bool, bool)> {
    let runtime = "\x20   %30 = bitcast i32 %1 to u32\n\
\x20   %31 = const u32 15\n\
\x20   %17 = and u32 %30, %31\n"
        .to_string();
    let swap = "\x20   %40 = load i32, ptr %4\n\
\x20   %41 = ptrtoptr ptr %4 to *mut u32\n\
\x20   %42 = ptrtoptr ptr %6 to *const u32\n\
\x20   %43 = const u32 1\n\
\x20   %44 = const u32 4\n\
\x20   %45 = mul u32 %43, %44\n\
\x20   %47 = ptrtoptr *mut u32 %41 to *mut u8\n\
\x20   %48 = ptrtoptr *const u32 %42 to *const u8\n\
\x20   %46 = call @func.0(%47, %48, %45)\n\
\x20   store i32 %40, ptr %6\n"
        .to_string();
    vec![
        ("up", op(0, 1, 0, &constant(7)), false, false),
        ("down", op(0, 0, 3, &constant(12)), false, false),
        ("unaligned", op(1, 5, 11, &constant(4)), false, false),
        ("fill", op(2, 3, 0, &constant(9)), false, false),
        ("swap", swap, false, false),
        ("runtime", op(0, 2, 0, &runtime), true, false),
        ("wide", op(0, 4, 0, &constant(40)), false, true),
    ]
}

fn program() -> Module {
    let mut text = String::from(
        "module \"p8m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = (*mut u8, *const u8, u32) -> (*mut u8)\n\
functy.1 = (ptr, i32, u32) -> (ptr)\n\
functy.2 = (i32, i32) -> (i32)\n\n\
fn @memmove(functy.0) {\n}\n\n\
fn @memcpy(functy.0) {\n}\n\n\
fn @memset(functy.1) {\n}\n\n",
    );
    for (name, op, _, _) in cases() {
        text.push_str(&function(name, &op));
    }
    trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("parse the test program: {e}\n{text}"))
}

const ROWS: &[(i64, i64)] = &[
    (0, 0),
    (1, 2),
    (5, 1000),
    (1000, 5),
    (-1, -1),
    (0x1234_5678, 0x0abc_def0),
    (-2_000_000_000, 77),
    (300, -300),
];

fn policy() -> WasmModulePolicy {
    WasmModulePolicy {
        memory: WasmMemoryPolicy::Owned {
            pages: 2,
            export: Some("memory".to_string()),
        },
        func_imports: WasmFuncImportPolicy::FromModule("host".to_string()),
        ..WasmModulePolicy::closed()
    }
}

fn compile(module: &Module, level: OptLevel) -> (Vec<u8>, wasm::WasmCompileEvidence) {
    wasm::compile_module_with_evidence_policy_license_options(
        module,
        &policy(),
        &permit_unlicensed(),
        WasmOptOptions {
            level,
            mid_end: true,
        },
    )
    .expect("compile the module")
}

/// The source run in the mid-end differential's view, where the library
/// declarations have the C library's bodies.
fn interpret(view: &Module, name: &str, a: i64, b: i64) -> i64 {
    let f = view.function_by_name(name).expect("function");
    let args = [a, b].map(|v| InterpretValue::int(Ty::I32, i128::from(v)).expect("i32"));
    let out = Interpreter::with_module(view)
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

fn scratch(tag: &str) -> PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("tcg_wasm_p8m_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run `name(a, b)` for every row in node, with the library functions
/// supplied over the module's memory: the results and the number of library
/// calls made. `None` when node is absent.
fn run(bytes: &[u8], name: &str) -> Option<(Vec<i64>, u64)> {
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
         let inst = null; let calls = 0;\n\
         const bytes = () => new Uint8Array(inst.exports.memory.buffer);\n\
         const host = {{\n\
           memmove: (d, s, n) => {{ calls++; bytes().copyWithin(d >>> 0, s >>> 0, (s >>> 0) + (n >>> 0)); return d; }},\n\
           memcpy: (d, s, n) => {{ calls++; bytes().copyWithin(d >>> 0, s >>> 0, (s >>> 0) + (n >>> 0)); return d; }},\n\
           memset: (d, c, n) => {{ calls++; bytes().fill(c & 255, d >>> 0, (d >>> 0) + (n >>> 0)); return d; }},\n\
         }};\n\
         inst = new WebAssembly.Instance(m, {{ host }});\n\
         const out = [{}].map(([a, b]) => inst.exports['{name}'](a, b));\n\
         process.stdout.write(JSON.stringify([out, calls]));\n",
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

/// The opcodes of export `name`'s body counted.
#[derive(Default)]
struct Ops {
    calls: usize,
    copies: usize,
    fills: usize,
    /// Bulk operations inside an `if` (the zero-count guard).
    guarded: usize,
}

fn body_ops(bytes: &[u8], name: &str) -> Ops {
    use wasmparser::{ExternalKind, Operator, Parser, Payload};
    let mut imported = 0u32;
    let mut export = None;
    let mut bodies = Vec::new();
    for payload in Parser::new(0).parse_all(bytes) {
        match payload.expect("parse") {
            Payload::ImportSection(r) => {
                for import in r {
                    if matches!(import.expect("import").ty, wasmparser::TypeRef::Func(_)) {
                        imported += 1;
                    }
                }
            }
            Payload::ExportSection(r) => {
                for e in r {
                    let e = e.expect("export");
                    if e.name == name && e.kind == ExternalKind::Func {
                        export = Some(e.index);
                    }
                }
            }
            Payload::CodeSectionEntry(body) => bodies.push(body),
            _ => {}
        }
    }
    let index = export.expect("the export") - imported;
    let body = &bodies[index as usize];
    let mut ops = Ops::default();
    // The open structured blocks, `true` for an `if`.
    let mut open: Vec<bool> = Vec::new();
    for op in body.get_operators_reader().expect("operators") {
        let in_if = open.contains(&true);
        match op.expect("operator") {
            Operator::Call { .. } => ops.calls += 1,
            Operator::Block { .. } | Operator::Loop { .. } => open.push(false),
            Operator::If { .. } => open.push(true),
            Operator::End => {
                open.pop();
            }
            Operator::MemoryCopy { .. } => {
                ops.copies += 1;
                ops.guarded += usize::from(in_if);
            }
            Operator::MemoryFill { .. } => {
                ops.fills += 1;
                ops.guarded += usize::from(in_if);
            }
            _ => {}
        }
    }
    ops
}

#[test]
fn memory_library_calls_with_constant_counts_become_loads_and_stores() {
    let module = program();
    let view = interpretable_module(&module);
    let (o2, evidence) = compile(&module, OptLevel::O2);
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    let changed = mid
        .passes
        .iter()
        .filter(|p| p.name == "mem_call")
        .map(|p| p.functions_changed)
        .sum::<usize>();
    assert_eq!(changed, 6, "every constant-count call is rewritten");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    let (o0, _) = compile(&module, OptLevel::O0);
    for (name, _, keeps_call, keeps_copy) in cases() {
        let want: Vec<i64> = ROWS
            .iter()
            .map(|&(a, b)| interpret(&view, name, a, b))
            .collect();
        let ops = body_ops(&o2, name);
        assert_eq!(ops.calls > 0, keeps_call, "{name}: calls at O2");
        assert_eq!(ops.copies > 0, keeps_copy, "{name}: memory.copy at O2");
        assert_eq!(ops.fills > 0, name == "fill", "{name}: memory.fill at O2");
        assert_eq!(
            ops.guarded,
            ops.copies + ops.fills,
            "{name}: every bulk operation left at O2 keeps its zero-count guard"
        );
        assert!(body_ops(&o0, name).calls > 0, "{name}: O0 keeps its call");
        for (tag, bytes) in [("O2", &o2), ("O0", &o0)] {
            if let Some((got, library_calls)) = run(bytes, name) {
                assert_eq!(got, want, "{tag}: {name} disagrees with the interpreter");
                let expect_calls = tag == "O0" || keeps_call;
                assert_eq!(
                    library_calls > 0,
                    expect_calls,
                    "{tag}: {name} made {library_calls} library calls"
                );
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
