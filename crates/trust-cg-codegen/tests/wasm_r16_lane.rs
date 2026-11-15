// trust-cg-codegen/tests/wasm_r16_lane.rs - wasm32 lane: round-16 mid-end rewrites
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The rustc bridge's shapes the round-16 mid-end rewrites, on the wasm32
//! lane at O2, each executed by node and compared with the trust-ir
//! reference interpreter (the source run in the mid-end differential's
//! view, where plain accesses have alignment 1). Fill-call fixtures instead
//! keep their external calls and use the explicitly supplied TEST host's
//! store loop as their execution oracle, not an invented production body:
//!
//! * `fill`: `[0u32; 20]` through `__trustcg_array_fill_i32` becomes
//!   an external call; `fill7` (`[7u32; 20]`) also keeps its call. Neither
//!   name authenticates a fill-helper contract;
//! * `packed`: a 15-byte packed struct built in a frame slot and copied byte
//!   by byte into another loses every byte load of the copy (its fields are
//!   stored into the destination);
//! * `loopcall`: a callee returning through the bridge's
//!   explicit signedness `bitcast` is spliced into its caller's loop, with no
//!   inlined callee withheld for a validation finding;
//! * `iter`: an iterator's `(index, len)` built in one slot, copied as one
//!   word into another and stepped in a loop through a `select` of its own
//!   reload leaves memory.
//!
//! At O0 every helper call stays. Node is required to execute the wasm; its
//! absence is a loud SKIP.
//!
//! The entry this test drives (`compile_module_with_evidence_policy_license_options`),
//! `WasmOptOptions::mid_end`, the `mid_end` evidence it reads (the pass
//! names `fill_call`, `byte_copy` and `retype_copy`, `passes_withheld`) and
//! `trust_cg_verify::trust_ir_mid_tv::interpretable_module` are provisional
//! surfaces pending the owner's sign-off: this test follows them if they
//! change, and is not a contract for their shape.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{
    self, WasmFuncImportPolicy, WasmMemoryPolicy, WasmModulePolicy, WasmOptOptions,
};
use trust_cg_verify::trust_ir_mid_tv::interpretable_module;
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

const FILL: &str = "fn @fill(functy.1) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 20], align 4\n\
\x20   store i32 %0, ptr %2\n\
\x20   %3 = const i64 VALUE\n\
\x20   %4 = const i32 20\n\
\x20   call @func.0(%2, %3, %4)\n\
\x20   %5 = const usize 12\n\
\x20   %6 = gep u8, ptr %2, %5\n\
\x20   store i32 %1, ptr %6\n\
\x20   %7 = load i32, ptr %2\n\
\x20   %8 = load i32, ptr %6\n\
\x20   %9 = const usize 76\n\
\x20   %10 = gep u8, ptr %2, %9\n\
\x20   %11 = load i32, ptr %10\n\
\x20   %12 = add i32 %7, %8\n\
\x20   %13 = add i32 %12, %11\n\
\x20   %14 = xor i32 %13, %0\n\
\x20   ret %14\n\
}\n\n";

fn packed() -> String {
    let mut copy = String::new();
    for i in 0..15u32 {
        let n = 100 + 5 * i;
        copy.push_str(&format!(
            "\x20   %{n} = const usize {i}\n\x20   %{a} = gep u8, ptr %2, %{n}\n\
             \x20   %{l} = load i8, ptr %{a}\n\x20   %{b} = gep u8, ptr %3, %{n}\n\
             \x20   store i8 %{l}, ptr %{b}\n",
            a = n + 1,
            l = n + 2,
            b = n + 3,
        ));
    }
    format!(
        "fn @packed(functy.1) {{\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.1 x 15], align 1\n\
\x20   %3 = alloca [ty.1 x 16], align 4\n\
\x20   %4 = trunc i32 %0 to u8\n\
\x20   store u8 %4, ptr %2\n\
\x20   %5 = const usize 1\n\
\x20   %6 = gep u8, ptr %2, %5\n\
\x20   store i32 %1, ptr %6\n\
\x20   %7 = const usize 5\n\
\x20   %8 = gep u8, ptr %2, %7\n\
\x20   %9 = trunc i32 %0 to i16\n\
\x20   store i16 %9, ptr %8\n\
\x20   %10 = const usize 7\n\
\x20   %11 = gep u8, ptr %2, %10\n\
\x20   %12 = sext i32 %1 to i64\n\
\x20   store i64 %12, ptr %11\n\
{copy}\
\x20   %20 = const u8 90\n\
\x20   %21 = const usize 15\n\
\x20   %22 = gep u8, ptr %3, %21\n\
\x20   store u8 %20, ptr %22\n\
\x20   %23 = load i32, ptr %3\n\
\x20   %24 = const usize 4\n\
\x20   %25 = gep u8, ptr %3, %24\n\
\x20   %26 = load i32, ptr %25\n\
\x20   %27 = const usize 8\n\
\x20   %28 = gep u8, ptr %3, %27\n\
\x20   %29 = load i32, ptr %28\n\
\x20   %30 = const usize 12\n\
\x20   %31 = gep u8, ptr %3, %30\n\
\x20   %32 = load i32, ptr %31\n\
\x20   %33 = xor i32 %23, %26\n\
\x20   %34 = mul i32 %33, %29\n\
\x20   %35 = add i32 %34, %32\n\
\x20   ret %35\n\
}}\n\n"
    )
}

const LOOPCALL: &str = "fn @g(functy.2) {\n\
bb0(%0: i32):\n\
\x20   %1 = const i32 3\n\
\x20   %2 = mul i32 %0, %1\n\
\x20   %3 = bitcast i32 %2 to u32\n\
\x20   ret %3\n\
}\n\n\
fn @loopcall(functy.1) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = const i32 0\n\
\x20   %3 = const u32 0\n\
\x20   %20 = const i32 15\n\
\x20   %21 = and i32 %0, %20\n\
\x20   br bb1(%2, %3)\n\
bb1(%4: i32, %5: u32):\n\
\x20   %6 = icmp slt i32 %4, %21\n\
\x20   condbr %6, bb2, bb3\n\
bb2:\n\
\x20   %7 = add i32 %4, %1\n\
\x20   %8 = call @func.1(%7)\n\
\x20   %9 = add u32 %5, %8\n\
\x20   %10 = const i32 1\n\
\x20   %11 = add i32 %4, %10\n\
\x20   br bb1(%11, %9)\n\
bb3:\n\
\x20   %12 = bitcast u32 %5 to i32\n\
\x20   ret %12\n\
}\n\n";

const ITER: &str = "fn @iter(functy.1) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 2], align 8\n\
\x20   %40 = const i32 0\n\
\x20   store i32 %40, ptr %2\n\
\x20   %3 = const usize 4\n\
\x20   %4 = gep u8, ptr %2, %3\n\
\x20   %41 = const i32 7\n\
\x20   %5 = and i32 %0, %41\n\
\x20   store i32 %5, ptr %4\n\
\x20   %6 = alloca i64, align 8\n\
\x20   %7 = load i64, ptr %2\n\
\x20   store i64 %7, ptr %6\n\
\x20   %10 = gep u8, ptr %6, %3\n\
\x20   br bb1(%1)\n\
bb1(%8: i32):\n\
\x20   %9 = load i32, ptr %6\n\
\x20   %11 = load i32, ptr %10\n\
\x20   %12 = icmp slt i32 %9, %11\n\
\x20   %13 = const i32 1\n\
\x20   %14 = add i32 %9, %13\n\
\x20   %15 = select i32 %12, %14, %9\n\
\x20   store i32 %15, ptr %6\n\
\x20   condbr %12, bb2, bb3\n\
bb2:\n\
\x20   %42 = const i32 31\n\
\x20   %16 = mul i32 %8, %42\n\
\x20   %17 = add i32 %16, %9\n\
\x20   br bb1(%17)\n\
bb3:\n\
\x20   ret %8\n\
}\n";

/// `(name, keeps a helper call at O2)`.
const CASES: &[(&str, bool)] = &[
    ("fill", true),
    ("fill7", true),
    ("packed", false),
    ("loopcall", false),
    ("iter", false),
];

fn program() -> Module {
    let text = format!(
        "module \"r16\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
type ty.0 = i32\n\ntype ty.1 = u8\n\n\
functy.0 = (ptr, i64, i32) -> ()\n\
functy.1 = (i32, i32) -> (i32)\n\
functy.2 = (i32) -> (u32)\n\n\
fn @__trustcg_array_fill_i32(functy.0) {{\n}}\n\n\
{LOOPCALL}{}{}{}{ITER}",
        FILL.replace("VALUE", "0"),
        FILL.replace("@fill(", "@fill7(").replace("VALUE", "7"),
        packed(),
    );
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

/// The source run in the mid-end differential's view.
fn interpret(view: &Module, name: &str, a: i64, b: i64) -> i64 {
    let f = view.function_by_name(name).expect("function");
    let args = [a, b].map(|v| InterpretValue::int(Ty::I32, i128::from(v as i32)).expect("i32"));
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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_r16_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run `name(a, b)` for every row in node, with the bridge's fill helper
/// supplied over the module's memory as the helper's loop: the results and
/// the number of helper calls made. `None` when node is absent.
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
         const host = {{\n\
           __trustcg_array_fill_i32: (d, v, n) => {{ calls++;\n\
             const view = new DataView(inst.exports.memory.buffer);\n\
             for (let i = 0; i < n; i++) view.setInt32((d >>> 0) + 4 * i, Number(BigInt.asIntN(32, v)), true); }},\n\
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
    fills: usize,
    byte_loads: usize,
    memory: usize,
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
    for op in body.get_operators_reader().expect("operators") {
        match op.expect("operator") {
            Operator::Call { .. } => ops.calls += 1,
            Operator::MemoryFill { .. } => ops.fills += 1,
            Operator::I32Load8S { .. } | Operator::I32Load8U { .. } => {
                ops.byte_loads += 1;
                ops.memory += 1;
            }
            Operator::I32Store8 { .. } => ops.memory += 1,
            Operator::I32Load { .. }
            | Operator::I64Load { .. }
            | Operator::I32Load16S { .. }
            | Operator::I32Load16U { .. }
            | Operator::I32Store { .. }
            | Operator::I64Store { .. }
            | Operator::I32Store16 { .. }
            | Operator::MemoryCopy { .. } => ops.memory += 1,
            _ => {}
        }
    }
    ops
}

fn changed(evidence: &wasm::WasmCompileEvidence, pass: &str) -> usize {
    evidence
        .mid_end
        .passes
        .iter()
        .filter(|p| p.name == pass)
        .map(|p| p.functions_changed)
        .sum()
}

#[test]
fn round_16_shapes_lose_their_calls_and_byte_traffic_and_agree() {
    let module = program();
    let view = interpretable_module(&module);
    let (o2, evidence) = compile(&module, OptLevel::O2);
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    // No callee or pass is withheld for a validation finding. The owned
    // memory's fixed size withholds the passes that add static data
    // (constant-table promotion and the CRC-table rewrite), and missing
    // implementation custody withholds fill calls (OD-155) and comparison
    // calls (OD-164) independently of their operands.
    assert!(
        mid.passes_withheld
            .keys()
            .all(|k| matches!(*k, "ctp" | "crc_table" | "fill_call" | "mem_cmp")),
        "{:?}",
        mid.passes_withheld
    );
    assert_eq!(changed(&evidence, "fill_call"), 0);
    assert!(mid.passes_withheld["fill_call"].contains("source-bound helper"));
    assert!(changed(&evidence, "byte_copy") >= 1);
    // The input already spells its signedness view as a valid bitcast.
    // The legacy copy normalizer is checked separately below.
    let (o0, _) = compile(&module, OptLevel::O0);
    for &(name, keeps_call) in CASES {
        let want: Vec<i64> = ROWS
            .iter()
            .map(|&(a, b)| match name {
                // These are expectations for the explicit test host in run,
                // not a source semantics claim about an arbitrary import.
                "fill" => i64::from((b as i32) ^ (a as i32)),
                "fill7" => i64::from((b as i32).wrapping_add(14) ^ (a as i32)),
                _ => interpret(&view, name, a, b),
            })
            .collect();
        let ops = body_ops(&o2, name);
        assert_eq!(ops.calls > 0, keeps_call, "{name}: calls at O2");
        assert_eq!(ops.fills, 0, "{name}: no unauthenticated memory.fill at O2");
        if name == "packed" {
            // The two byte stores left are the `u8` field and the guard byte.
            assert_eq!(ops.byte_loads, 0, "{name}: byte loads at O2");
            assert!(
                ops.memory <= 10,
                "{name}: {} memory operations at O2",
                ops.memory
            );
        }
        if name == "iter" {
            assert_eq!(ops.memory, 0, "{name}: memory operations at O2");
        }
        if name.starts_with("fill") || name == "loopcall" {
            assert!(body_ops(&o0, name).calls > 0, "{name}: O0 keeps its call");
        }
        for (tag, bytes) in [("O2", &o2), ("O0", &o0)] {
            if let Some((got, helper_calls)) = run(bytes, name) {
                assert_eq!(got, want, "{tag}: {name} disagrees with the interpreter");
                let expect_calls = name.starts_with("fill") && (tag == "O0" || keeps_call);
                assert_eq!(
                    helper_calls > 0,
                    expect_calls,
                    "{tag}: {name} made {helper_calls} helper calls"
                );
            }
        }
    }
}

#[test]
fn a_named_external_fill_keeps_the_actual_no_op_host_call() {
    // Ordinary generic IR: the import has no captured bridge helper body.
    // A no-op host is a legitimate implementation of this declaration.
    let module = trust_ir::parser::parse_module(
        "module \"foreign-fill\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = (ptr, i64, i32) -> ()\nfuncty.1 = () -> (i32)\n\n\
         fn @__trustcg_array_fill_i32(functy.0) {\n}\n\n\
         fn @probe(functy.1) {\nbb0():\n\
         \x20   %0 = alloca i32, align 4\n\
         \x20   %1 = const i32 0\n\
         \x20   store i32 %1, ptr %0\n\
         \x20   %2 = const i64 16843009\n\
         \x20   %3 = const i32 1\n\
         \x20   call @func.0(%0, %2, %3)\n\
         \x20   %4 = load i32, ptr %0\n\
         \x20   ret %4\n}\n",
    )
    .expect("parse the genuine arbitrary-import fixture");
    let snapshot = module.clone();
    let mut outputs = Vec::new();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let (bytes, evidence) = compile(&module, level);
        let ops = body_ops(&bytes, "probe");
        assert_eq!(ops.calls, 1, "{level:?}: the external call must remain");
        assert_eq!(ops.fills, 0, "{level:?}: no assumed fill may be emitted");
        assert_eq!(changed(&evidence, "fill_call"), 0);
        if level != OptLevel::O0 {
            assert!(evidence.mid_end.passes_withheld["fill_call"].contains("source-bound helper"));
        }
        wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
            .validate_all(&bytes)
            .expect("the actual emitted module validates");
        outputs.push((level, bytes));
    }
    assert_eq!(
        module, snapshot,
        "compilation preserves the complete source"
    );
    let Some(node) = node() else {
        eprintln!(
            "NOT_EXECUTED: node unavailable; O0-O3 call-retention controls ran, no host execution credit"
        );
        return;
    };
    let dir = scratch("foreign-fill");
    let script = "const fs = require('fs');\n\
                  let calls = 0;\n\
                  const host = { __trustcg_array_fill_i32: (_d, _v, _n) => { calls++; } };\n\
                  const bytes = fs.readFileSync(process.argv[2]);\n\
                  const inst = new WebAssembly.Instance(new WebAssembly.Module(bytes), { host });\n\
                  process.stdout.write(JSON.stringify([inst.exports.probe(), calls]));\n";
    std::fs::write(dir.join("run.js"), script).unwrap();
    for (level, bytes) in outputs {
        std::fs::write(dir.join("m.wasm"), bytes).unwrap();
        let result = Command::new(&node)
            .arg(dir.join("run.js"))
            .arg(dir.join("m.wasm"))
            .output()
            .expect("execute the actual no-op host fixture");
        assert!(
            result.status.success(),
            "{level:?}: node failed: {}",
            String::from_utf8_lossy(&result.stderr)
        );
        let observed: [i64; 2] =
            serde_json::from_slice(&result.stdout).expect("actual result and host-call count");
        assert_eq!(
            observed,
            [0, 1],
            "{level:?}: preserve the real host operation"
        );
        eprintln!("EXECUTED: {level:?} arbitrary no-op host returned0 and was called once");
    }
    let _ = std::fs::remove_dir_all(dir);
}

/// These hand-built backend fixtures carry no source proof. The explicit
/// legacy policy exercises lowering without changing production admission.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}

/// The obsolete cross-signed Copy is refused at production ingestion. The
/// existing low-level normalizer still has its independently checked rewrite;
/// its success does not license compiling that malformed input directly.
#[test]
fn malformed_copy_is_refused_and_its_low_level_rewrite_stays_checked() {
    let mut legacy = program();
    let g = legacy
        .functions
        .iter_mut()
        .find(|f| f.name == "g")
        .expect("g");
    let mut changed = 0;
    for node in g.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let trust_ir::Inst::Cast {
            op: trust_ir::CastOp::Bitcast,
            src_ty: Ty::I32,
            dst_ty: Ty::U32,
            operand,
        } = &node.inst
        {
            node.inst = trust_ir::Inst::Copy {
                ty: Ty::U32,
                operand: *operand,
            };
            changed += 1;
        }
    }
    assert_eq!(changed, 1, "exactly the legacy signedness-view instruction");
    for result in [
        wasm::compile_module_with_license(&legacy, &permit_unlicensed()),
        wasm::compile_object_with_license(&legacy, &permit_unlicensed()),
    ] {
        let error = result.expect_err("cross-signed Copy remains invalid at ingestion");
        assert!(
            format!("{error:?}").contains("OperandTypeMismatch"),
            "{error}"
        );
    }
    let (normalized, report) =
        trust_cg_irmid::optimize_module(&legacy, &trust_cg_irmid::MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(
        report
            .passes
            .iter()
            .any(|p| p.name == "retype_copy" && p.functions_changed >= 1),
        "{report:?}"
    );
    assert!(trust_ir_build::validate_module(&normalized).is_empty());
}
