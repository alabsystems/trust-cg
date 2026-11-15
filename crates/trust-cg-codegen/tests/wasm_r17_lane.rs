// trust-cg-codegen/tests/wasm_r17_lane.rs - wasm32 lane: round-17 mid-end rewrites
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The rustc bridge's loop shapes the round-17 mid-end rewrites, on the
//! wasm32 lane at O2 (a closed module sized for what it emits, so a new
//! read-only table may be laid out), each executed by node and compared
//! with the trust-ir reference interpreter on the source:
//!
//! * `zip`: `min_zip2`'s zip of a `k % 5`-element prefix of a 4-element
//!   array with another (the prefix's length a pointer difference, the trip
//!   count their minimum, the exit test `Zip::next`'s niche) is unrolled to
//!   its bound of 4: no loop, no memory access and no `select` is left;
//! * `crc`: the bit-serial CRC-32 step over one byte becomes one load from
//!   a 256-entry table and no branch;
//! * `ri`: a `RangeInclusive<u8>` loop's `switch` on its exhausted-flag
//!   `select` becomes a branch on the select's condition (no `br_table`).
//!
//! At O0 the module keeps every loop. Node is required to execute the wasm;
//! its absence is a loud SKIP.
//!
//! The entry this test drives (`compile_sized_closed_module_with_evidence_license_options`),
//! `WasmOptOptions`, the `mid_end` evidence it reads (the pass names
//! `bounded_unroll`, `select_branch` and `crc_table`, `globals_added`) are
//! provisional surfaces pending the owner's sign-off: this test follows them
//! if they change, and is not a contract for their shape.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{self, WasmOptOptions};
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

/// `zip(k, _)`: `acc = acc * 100 + a[i] + b[i]` over `zip(a[..k % 5], b)`
/// with `a = [1u16, 2, 3, 4]` and `b = [10u64, 20, 30, 40]`, in the shape the
/// bridge leaves once the `Zip`'s state is in values.
const ZIP: &str = "fn @zip(functy.0) {\n\
bb0(%1: i32, %2: i32):\n\
\x20   %47 = alloca [ty.0 x 4], align 2\n\
\x20   %48 = alloca [ty.1 x 4], align 8\n\
\x20   %64 = const u16 1\n\
\x20   store u16 %64, ptr %47\n\
\x20   %65 = const u16 2\n\
\x20   %66 = const i32 2\n\
\x20   %71 = gep inbounds u8, ptr %47, %66\n\
\x20   store u16 %65, ptr %71\n\
\x20   %72 = const u16 3\n\
\x20   %73 = const i32 4\n\
\x20   %78 = gep inbounds u8, ptr %47, %73\n\
\x20   store u16 %72, ptr %78\n\
\x20   %79 = const u16 4\n\
\x20   %80 = const i32 6\n\
\x20   %85 = gep inbounds u8, ptr %47, %80\n\
\x20   store u16 %79, ptr %85\n\
\x20   %86 = const u64 10\n\
\x20   store u64 %86, ptr %48\n\
\x20   %87 = const u64 20\n\
\x20   %88 = const i32 8\n\
\x20   %93 = gep inbounds u8, ptr %48, %88\n\
\x20   store u64 %87, ptr %93\n\
\x20   %94 = const u64 30\n\
\x20   %95 = const i32 16\n\
\x20   %100 = gep inbounds u8, ptr %48, %95\n\
\x20   store u64 %94, ptr %100\n\
\x20   %101 = const u64 40\n\
\x20   %102 = const i32 24\n\
\x20   %107 = gep inbounds u8, ptr %48, %102\n\
\x20   store u64 %101, ptr %107\n\
\x20   %108 = const u32 0\n\
\x20   %111 = const u32 5\n\
\x20   %109 = bitcast i32 %1 to u32\n\
\x20   %110 = urem u32 %109, %111\n\
\x20   %174 = ptrtoint ptr %47 to i32\n\
\x20   %175 = bitcast u32 %110 to i32\n\
\x20   %176 = const i32 2\n\
\x20   %177 = mul i32 %175, %176\n\
\x20   %178 = add i32 %174, %177\n\
\x20   %179 = inttoptr i32 %178 to ptr\n\
\x20   %483 = ptrtoint ptr %179 to i32\n\
\x20   %485 = ptrtoint ptr %47 to i32\n\
\x20   %486 = sub i32 %483, %485\n\
\x20   %487 = const i32 2\n\
\x20   %488 = udiv i32 %486, %487\n\
\x20   %498 = bitcast i32 %488 to u32\n\
\x20   %228 = ptrtoint ptr %48 to i32\n\
\x20   %231 = const i32 32\n\
\x20   %232 = add i32 %228, %231\n\
\x20   %233 = inttoptr i32 %232 to ptr\n\
\x20   %509 = ptrtoint ptr %233 to i32\n\
\x20   %511 = ptrtoint ptr %48 to i32\n\
\x20   %512 = sub i32 %509, %511\n\
\x20   %513 = const i32 8\n\
\x20   %514 = udiv i32 %512, %513\n\
\x20   %524 = bitcast i32 %514 to u32\n\
\x20   %526 = icmp ult u32 %524, %498\n\
\x20   condbr %526, bb37, bb36\n\
bb36:\n\
\x20   br bb38(%498)\n\
bb37:\n\
\x20   br bb38(%524)\n\
bb38(%528: u32):\n\
\x20   %544 = const i32 0\n\
\x20   %547 = bitcast u32 %528 to i32\n\
\x20   br bb1(%108, %544)\n\
bb1(%369: u32, %557: i32):\n\
\x20   %385 = icmp ult i32 %557, %547\n\
\x20   %388 = ptrtoint ptr %47 to i32\n\
\x20   %390 = const i32 2\n\
\x20   %391 = mul i32 %557, %390\n\
\x20   %392 = add i32 %388, %391\n\
\x20   %393 = inttoptr i32 %392 to ptr\n\
\x20   %402 = ptrtoint ptr %48 to i32\n\
\x20   %404 = const i32 8\n\
\x20   %405 = mul i32 %557, %404\n\
\x20   %406 = add i32 %402, %405\n\
\x20   %407 = inttoptr i32 %406 to ptr\n\
\x20   %408 = const i32 1\n\
\x20   %409 = add i32 %557, %408\n\
\x20   %410 = select i32 %385, %409, %557\n\
\x20   %411 = const i32 0\n\
\x20   %412 = inttoptr i32 %411 to ptr\n\
\x20   %413 = select ptr %385, %393, %412\n\
\x20   %464 = ptrtoint ptr %413 to i32\n\
\x20   %467 = ptrtoint ptr %407 to i32\n\
\x20   %421 = inttoptr i32 %464 to ptr\n\
\x20   %422 = ptrtoint ptr %421 to u64\n\
\x20   %423 = const u64 0\n\
\x20   %425 = icmp eq u64 %422, %423\n\
\x20   %426 = trunc u64 %422 to i32\n\
\x20   %429 = const i32 1\n\
\x20   %430 = select i32 %425, %426, %429\n\
\x20   switch %430 [ 0: bb4 1: bb3 default: bb2 ]\n\
bb4:\n\
\x20   %445 = bitcast u32 %369 to i32\n\
\x20   ret %445\n\
bb3:\n\
\x20   %465 = inttoptr i32 %464 to ptr\n\
\x20   %466 = inttoptr i32 %467 to ptr\n\
\x20   %437 = const u32 100\n\
\x20   %436 = mul u32 %369, %437\n\
\x20   %438 = load u16, ptr %465\n\
\x20   %439 = zext u16 %438 to u32\n\
\x20   %440 = add u32 %436, %439\n\
\x20   %441 = load u64, ptr %466\n\
\x20   %442 = trunc u64 %441 to u32\n\
\x20   %443 = add u32 %440, %442\n\
\x20   br bb1(%443, %410)\n\
bb2:\n\
\x20   %444 = const i32 0\n\
\x20   ret %444\n\
}\n\n";

/// `crc(state, byte)`: one CRC-32 step with the eight rounds in a loop.
const CRC: &str = "fn @crc(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = bitcast i32 %0 to u32\n\
\x20   %3 = bitcast i32 %1 to u32\n\
\x20   %4 = const u32 255\n\
\x20   %5 = and u32 %3, %4\n\
\x20   %6 = xor u32 %2, %5\n\
\x20   %7 = and u32 %6, %4\n\
\x20   %8 = const u32 0\n\
\x20   br bb1(%7, %8)\n\
bb1(%10: u32, %11: u32):\n\
\x20   %12 = const u32 8\n\
\x20   %13 = icmp ult u32 %11, %12\n\
\x20   condbr %13, bb2, bb5\n\
bb2:\n\
\x20   %14 = const u32 1\n\
\x20   %15 = and u32 %10, %14\n\
\x20   %16 = lshr u32 %10, %14\n\
\x20   %17 = const u32 3988292384\n\
\x20   %18 = xor u32 %17, %16\n\
\x20   %19 = const u32 0\n\
\x20   %20 = icmp ne u32 %15, %19\n\
\x20   condbr %20, bb3, bb4\n\
bb3:\n\
\x20   br bb6(%18)\n\
bb4:\n\
\x20   br bb6(%16)\n\
bb6(%21: u32):\n\
\x20   %22 = add u32 %11, %14\n\
\x20   br bb1(%21, %22)\n\
bb5:\n\
\x20   %23 = lshr u32 %2, %12\n\
\x20   %24 = xor u32 %10, %23\n\
\x20   %25 = bitcast u32 %24 to i32\n\
\x20   ret %25\n\
}\n\n";

/// `ri(a, _)`: `acc = acc * 3 + i` over `i` in `(a as u8).saturating_sub(3)
/// ..= a as u8`, `RangeInclusive<u8>`'s state in values and its test a
/// `switch` on the `zext` of a `select` of 1 and 0.
const RI: &str = "fn @ri(functy.0) {\n\
bb0(%1: i32, %2: i32):\n\
\x20   %15 = trunc i32 %1 to u8\n\
\x20   %16 = const u8 3\n\
\x20   %17, %18 = sub.overflow u8 %15, %16\n\
\x20   %20 = const u8 0\n\
\x20   %19 = select u8 %18, %20, %17\n\
\x20   %22 = const u32 0\n\
\x20   %121 = const i8 0\n\
\x20   br bb1(%22, %121, %19)\n\
bb1(%63: u32, %122: i8, %123: u8):\n\
\x20   %80 = const i8 0\n\
\x20   %81 = icmp ne i8 %122, %80\n\
\x20   %82 = icmp ule u8 %123, %15\n\
\x20   %83 = const bool false\n\
\x20   %84 = select bool %81, %83, %82\n\
\x20   %85 = icmp ult u8 %123, %15\n\
\x20   %86 = const u8 1\n\
\x20   %87 = add u8 %123, %86\n\
\x20   %88 = select u8 %85, %87, %123\n\
\x20   %89 = select u8 %84, %88, %123\n\
\x20   %90 = const i8 1\n\
\x20   %91 = select bool %85, %83, %84\n\
\x20   %92 = select i8 %91, %90, %122\n\
\x20   %93 = const u8 1\n\
\x20   %94 = const u8 0\n\
\x20   %95 = select u8 %84, %93, %94\n\
\x20   %104 = zext u8 %95 to i32\n\
\x20   switch %104 [ 0: bb4 default: bb3 ]\n\
bb4:\n\
\x20   %113 = bitcast u32 %63 to i32\n\
\x20   ret %113\n\
bb3:\n\
\x20   %110 = const u32 3\n\
\x20   %109 = mul u32 %63, %110\n\
\x20   %111 = zext u8 %123 to u32\n\
\x20   %112 = add u32 %109, %111\n\
\x20   br bb1(%112, %92, %89)\n\
}\n";

const NAMES: &[&str] = &["zip", "crc", "ri"];

fn program() -> Module {
    let text = format!(
        "module \"r17\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
type ty.0 = u16\n\ntype ty.1 = u64\n\n\
functy.0 = (i32, i32) -> (i32)\n\n\
{ZIP}{CRC}{RI}"
    );
    trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("parse the test program: {e}\n{text}"))
}

const ROWS: &[(i64, i64)] = &[
    (0, 0),
    (1, 2),
    (2, 0xff),
    (3, 0x80),
    (4, 7),
    (5, 1000),
    (9, -1),
    (1000, 5),
    (-1, -1),
    (0x1234_5678, 0x0abc_def0),
    (-2_000_000_000, 77),
    (300, -300),
];

fn compile(module: &Module, level: OptLevel) -> (Vec<u8>, wasm::WasmCompileEvidence) {
    wasm::compile_sized_closed_module_with_evidence_license_options(
        module,
        &permit_unlicensed(),
        WasmOptOptions {
            level,
            mid_end: true,
        },
    )
    .expect("compile the module")
}

/// The source run in the reference interpreter.
fn interpret(module: &Module, name: &str, a: i64, b: i64) -> i64 {
    let f = module.function_by_name(name).expect("function");
    let args = [a, b].map(|v| InterpretValue::int(Ty::I32, i128::from(v as i32)).expect("i32"));
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

fn scratch(tag: &str) -> PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("tcg_wasm_r17_{tag}_{}_{n}", std::process::id()));
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
         const inst = new WebAssembly.Instance(m, {{}});\n\
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

/// The opcodes of export `name`'s body counted.
#[derive(Default, Debug)]
struct Ops {
    loops: usize,
    branches: usize,
    tables: usize,
    loads: usize,
    stores: usize,
    selects: usize,
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
            Operator::Loop { .. } => ops.loops += 1,
            Operator::If { .. } | Operator::BrIf { .. } => ops.branches += 1,
            Operator::BrTable { .. } => ops.tables += 1,
            Operator::Select | Operator::TypedSelect { .. } => ops.selects += 1,
            Operator::I32Load { .. }
            | Operator::I64Load { .. }
            | Operator::I32Load8S { .. }
            | Operator::I32Load8U { .. }
            | Operator::I32Load16S { .. }
            | Operator::I32Load16U { .. } => ops.loads += 1,
            Operator::I32Store { .. }
            | Operator::I64Store { .. }
            | Operator::I32Store8 { .. }
            | Operator::I32Store16 { .. } => ops.stores += 1,
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
fn round_17_loop_shapes_lose_their_loops_and_agree() {
    let module = program();
    let (o2, evidence) = compile(&module, OptLevel::O2);
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    // Only the passes withheld for missing implementation custody (OD-155,
    // OD-164), never one withheld for a validation finding.
    assert_eq!(
        mid.passes_withheld.keys().copied().collect::<Vec<_>>(),
        ["fill_call", "mem_cmp"],
        "{:?}",
        mid.passes_withheld
    );
    for pass in ["bounded_unroll", "select_branch", "crc_table"] {
        assert!(changed(&evidence, pass) >= 1, "{pass}");
    }
    assert_eq!(mid.globals_added, 1, "one CRC table");
    let (o0, _) = compile(&module, OptLevel::O0);
    for &name in NAMES {
        let want: Vec<i64> = ROWS
            .iter()
            .map(|&(a, b)| interpret(&module, name, a, b))
            .collect();
        let ops = body_ops(&o2, name);
        match name {
            "zip" => {
                assert_eq!(ops.loops, 0, "{name}: {ops:?}");
                assert_eq!(ops.loads + ops.stores + ops.selects, 0, "{name}: {ops:?}");
            }
            "crc" => {
                assert_eq!(ops.loops, 0, "{name}: {ops:?}");
                assert_eq!(ops.loads, 1, "{name}: {ops:?}");
                assert_eq!(ops.branches + ops.tables, 0, "{name}: {ops:?}");
            }
            _ => assert_eq!(ops.tables, 0, "{name}: {ops:?}"),
        }
        assert!(body_ops(&o0, name).loops > 0, "{name}: O0 keeps its loop");
        for (tag, bytes) in [("O2", &o2), ("O0", &o0)] {
            if let Some(got) = run(bytes, name) {
                assert_eq!(got, want, "{tag}: {name} disagrees with the interpreter");
            }
        }
    }
}

/// These hand-built backend fixtures carry no source proof. The explicit
/// legacy policy exercises lowering without changing production admission.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
