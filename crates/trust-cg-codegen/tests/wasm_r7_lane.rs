// trust-cg-codegen/tests/wasm_r7_lane.rs - wasm32 lane: rebased pointers, zero-sized allocations, entry staging, precise pins
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Regressions for the wasm32 lane's frame analysis, each pinned with the
//! trust-ir input that exposed it and checked against the trust-ir reference
//! interpreter (or an exact value / a frame size):
//!
//! * a pointer rebuilt with `ptrtoint` / `add` / `inttoptr` at a displacement
//!   outside its allocation (which the interpreter resolves into a
//!   neighbour) pins the allocation, in straight-line code, through a stored
//!   marker and in a strong callee; a loop `Alloca` probed that way gets
//!   fresh storage on every execution; the same probes at a displacement
//!   inside the allocation still share bytes;
//! * every live allocation, a zero-sized one included, has an address of
//!   its own;
//! * a function whose only frame need would be staging for two or more
//!   by-address entry parameters compiles (the caller binds them; nothing
//!   stages them), closed and as a linked object;
//! * a pointer-carried extract of a memory-carried lane is a copy that a
//!   later allocation does not overwrite;
//! * the rustc bridge's bounds-checked indexing through rebuilt pointers
//!   (an index checked below a constant, a length parameter or a
//!   loop-carried copy of it, or bounded by a remainder) keeps sharing,
//!   while an index past the argument or a length longer than the
//!   allocation pins it;
//! * a check bounds a rebuilt pointer only by values that cannot have been
//!   rebound since it was built: a length a branch back to the entry block
//!   rebinds (in the checking callee or in a function that passes it on)
//!   and an index a loop rebinds after the displacement crossed its back
//!   edge both leave the allocation pinned;
//! * calls to the C library's `memset` / `memcpy` keep their pointer
//!   arguments unpinned, but an address handed to them as data is a capture.
//!
//! Node is required to execute the wasm and `wasm-ld` (`WASM_LD`) to link
//! objects; the absence of either is a loud SKIP.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::wasm;
use trust_ir::{
    InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty, parser,
};

const HEADER: &str = "module \"r7\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n";

fn parse(text: &str) -> Module {
    parser::parse_module(text).unwrap_or_else(|e| {
        let numbered: String = text
            .lines()
            .enumerate()
            .map(|(i, l)| format!("{:4} {l}\n", i + 1))
            .collect();
        panic!("test module failed to parse: {e}\n{numbered}")
    })
}

/// Parse a module body under [`HEADER`].
fn module(body: &str) -> Module {
    parse(&format!("{HEADER}{body}"))
}

/// The lane alone, without the trust-ir mid-end: these fixtures pin the
/// lane's frame decisions on slots the mid-end's store forwarding and
/// dead-slot removal would otherwise remove (a slot only stored to, or read
/// back right after its store).
fn lane_only(m: &Module) -> Result<Vec<u8>, wasm::WasmLowerError> {
    wasm::compile_module_with_evidence_policy_license_options(
        m,
        &wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
        wasm::WasmOptOptions {
            level: trust_cg_codegen::pipeline::OptLevel::O2,
            mid_end: false,
        },
    )
    .map(|(bytes, _)| bytes)
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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_r7_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn validate(bytes: &[u8]) {
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
}

/// The scalar parameter/result width of a test export.
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

    fn js(self) -> &'static str {
        match self {
            W::I32 => "i32",
            W::I64 => "i64",
        }
    }
}

/// The interpreter's answer for `name(args)` (every parameter of width `w`),
/// or `None` when the reference execution refuses the input.
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
        InterpretValueKind::Int(i) => Some(i.as_signed() as i64),
        other => panic!("{name} returned {other:?}"),
    }
}

/// Run export `name` over `calls` (in order, in ONE instance); `None` is a
/// trap. `None` for the whole column when node is absent.
fn run_wasm(bytes: &[u8], name: &str, w: W, calls: &[Vec<i64>]) -> Option<Vec<Option<i64>>> {
    let Some(node) = node() else {
        eprintln!("SKIP: node not found; {name} not executed");
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
              const f = inst.exports[process.argv[3]];\n\
              const big = process.argv[4] === 'i64';\n\
              const calls = JSON.parse(fs.readFileSync(process.argv[5]));\n\
              const out = calls.map((args) => { try { \
                return String(f(...args.map((a) => big ? BigInt(a) : Number(a)))); } \
              catch (e) { if (e instanceof WebAssembly.RuntimeError) return null; throw e; } });\n\
              process.stdout.write(JSON.stringify(out));\n";
    std::fs::write(dir.join("run.js"), js).unwrap();
    let calls: Vec<Vec<String>> = calls
        .iter()
        .map(|c| c.iter().map(i64::to_string).collect())
        .collect();
    std::fs::write(
        dir.join("calls.json"),
        serde_json::to_string(&calls).unwrap(),
    )
    .unwrap();
    let run = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .arg(name)
        .arg(w.js())
        .arg(dir.join("calls.json"))
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
/// exported). `None` (a loud SKIP) when no linker is available.
fn link(objects: &[&[u8]]) -> Option<Vec<u8>> {
    let Some(ld) = wasm_ld() else {
        eprintln!("SKIP: wasm-ld not found (set WASM_LD); link not executed");
        return None;
    };
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

/// Export `name` of `bytes` agrees with the interpreter on every call, and
/// the interpreter defines every call (a must-agree input, not UB). Returns
/// the number of checks (0 when node is absent).
fn agrees(module: &Module, bytes: &[u8], name: &str, w: W, calls: &[Vec<i64>]) -> usize {
    validate(bytes);
    let Some(got) = run_wasm(bytes, name, w, calls) else {
        return 0;
    };
    for (args, got) in calls.iter().zip(&got) {
        let want = interpret(module, name, w, args);
        assert!(want.is_some(), "{name}{args:?}: the interpreter refuses it");
        assert_eq!(
            *got, want,
            "{name}{args:?}: wasm {got:?}, interpreter {want:?}"
        );
    }
    calls.len()
}

fn singles(values: &[i64]) -> Vec<Vec<i64>> {
    values.iter().map(|&v| vec![v]).collect()
}

const I32_VALUES: &[i64] = &[
    i32::MIN as i64,
    -1000,
    -7,
    -1,
    0,
    1,
    2,
    5,
    7,
    255,
    65536,
    i32::MAX as i64,
];

/// The frame size the prologue of export `name` of a closed module reserves
/// (0 when the function has no frame).
fn frame_size(bytes: &[u8], name: &str) -> i32 {
    let mut index = None;
    let mut imported = 0u32;
    let mut bodies = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        match payload.expect("parse") {
            wasmparser::Payload::ImportSection(r) => {
                for i in r {
                    if matches!(i.expect("import").ty, wasmparser::TypeRef::Func(_)) {
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
    let index = index.unwrap_or_else(|| panic!("no export {name}")) - imported;
    let body = &bodies[index as usize];
    let ops: Vec<wasmparser::Operator<'_>> = body
        .get_operators_reader()
        .expect("ops")
        .into_iter()
        .take(4)
        .map(|o| o.expect("op"))
        .collect();
    // `local.set s; local.get s` may be merged into `local.tee s` by the
    // emission pass.
    match ops.as_slice() {
        [
            wasmparser::Operator::GlobalGet { .. },
            wasmparser::Operator::LocalSet { .. },
            wasmparser::Operator::LocalGet { .. },
            wasmparser::Operator::I32Const { value },
        ]
        | [
            wasmparser::Operator::GlobalGet { .. },
            wasmparser::Operator::LocalTee { .. },
            wasmparser::Operator::I32Const { value },
            ..,
        ] => *value,
        _ => 0,
    }
}

// ---- 1. A pointer rebuilt from an integer past its allocation ----

/// `min.trust_ir`: A1 (`%3`) is probed at A1-4 through `inttoptr`, which the
/// interpreter resolves into the neighbour `%1`; the probe reads 4, and
/// `%1 + 4 + 4` rebuilds A1 exactly. A2 (`%9`) is allocated after the last
/// data-flow use of A1, so sharing A1's bytes with A2 reads 12345.
const OOB_LOAD: &str = r#"functy.0 = (i32) -> (i32)

fn @f(functy.0) {
bb0(%0: i32):
    %1 = alloca i64
    %2 = const i64 17179869184
    store i64 %2, ptr %1
    %3 = alloca i32
    store i32 %0, ptr %3
    %4 = ptrtoint ptr %3 to i32
    %5 = const i32 4
    %6 = sub i32 %4, %5
    %7 = inttoptr i32 %6 to ptr
    %8 = load i32, ptr %7
    %9 = alloca i32
    %10 = const i32 12345
    store i32 %10, ptr %9
    %11 = ptrtoint ptr %1 to i32
    %12 = add i32 %11, %8
    %13 = add i32 %12, %5
    %14 = inttoptr i32 %13 to ptr
    %15 = load i32, ptr %14
    ret %15
}
"#;

/// `min_store.trust_ir`: a marker stored at A1-4 lands in `%1`; reading it
/// back selects the offset that rebuilds A1.
const OOB_STORE: &str = r#"functy.0 = (i32) -> (i32)

fn @f(functy.0) {
bb0(%0: i32):
    %1 = alloca i64
    %2 = const i64 0
    store i64 %2, ptr %1
    %3 = alloca i32
    store i32 %0, ptr %3
    %4 = ptrtoint ptr %3 to i32
    %5 = const i32 4
    %6 = sub i32 %4, %5
    %7 = inttoptr i32 %6 to ptr
    %8 = const i32 -559038737
    store i32 %8, ptr %7
    %9 = alloca i32
    %10 = const i32 12345
    store i32 %10, ptr %9
    %11 = load i32, ptr %1
    %12 = icmp eq i32 %11, %8
    %13 = const i32 0
    %14 = select i32 %12, %13, %5
    %15 = ptrtoint ptr %1 to i32
    %16 = add i32 %15, %14
    %17 = add i32 %16, %5
    %18 = inttoptr i32 %17 to ptr
    %19 = load i32, ptr %18
    ret %19
}
"#;

/// `min_loop.trust_ir`: the loop `Alloca` `%6` is probed in its first
/// execution; the second execution must not reuse the first's bytes.
const OOB_LOOP: &str = r#"functy.0 = (i32) -> (i32)

fn @f(functy.0) {
bb0(%0: i32):
    %1 = alloca i64
    %2 = const i64 17179869184
    store i64 %2, ptr %1
    %3 = const i32 0
    br bb1(%3, %3)
bb1(%4: i32, %5: i32):
    %6 = alloca i32
    %7 = add i32 %0, %4
    store i32 %7, ptr %6
    %8 = const i32 4
    %9 = icmp eq i32 %4, %3
    condbr %9, bb2, bb3
bb2:
    %10 = ptrtoint ptr %6 to i32
    %11 = sub i32 %10, %8
    %12 = inttoptr i32 %11 to ptr
    %13 = load i32, ptr %12
    %14 = const i32 1
    br bb1(%14, %13)
bb3:
    %15 = ptrtoint ptr %1 to i32
    %16 = add i32 %15, %5
    %17 = add i32 %16, %8
    %18 = inttoptr i32 %17 to ptr
    %19 = load i32, ptr %18
    ret %19
}
"#;

/// `min_callee.trust_ir`: a strong callee probes its argument at -4.
const OOB_CALLEE: &str = r#"functy.0 = (ptr) -> (i32)
functy.1 = (i32) -> (i32)

fn @probe(functy.0) {
bb0(%0: ptr):
    %1 = ptrtoint ptr %0 to i32
    %2 = const i32 4
    %3 = sub i32 %1, %2
    %4 = inttoptr i32 %3 to ptr
    %5 = load i32, ptr %4
    ret %5
}

fn @f(functy.1) {
bb0(%0: i32):
    %1 = alloca i64
    %2 = const i64 17179869184
    store i64 %2, ptr %1
    %3 = alloca i32
    store i32 %0, ptr %3
    %4 = call @func.0(%3)
    %5 = alloca i32
    %6 = const i32 12345
    store i32 %6, ptr %5
    %7 = ptrtoint ptr %1 to i32
    %8 = add i32 %7, %4
    %9 = const i32 4
    %10 = add i32 %8, %9
    %11 = inttoptr i32 %10 to ptr
    %12 = load i32, ptr %11
    ret %12
}
"#;

#[test]
fn a_pointer_rebuilt_past_its_allocation_keeps_the_allocation() {
    let mut checks = 0;
    for (label, text, alone) in [
        ("load", OOB_LOAD, 24),
        ("store", OOB_STORE, 24),
        ("callee", OOB_CALLEE, 24),
    ] {
        let m = module(text);
        let closed = lane_only(&m).unwrap_or_else(|e| panic!("{label}: {e}"));
        // `%1`, A1 and A2 each in bytes of their own (8 each).
        assert_eq!(frame_size(&closed, "f"), alone, "{label}: A1 shares bytes");
        checks += agrees(&m, &closed, "f", W::I32, &singles(I32_VALUES));
        // With the mid-end, which may remove the slots, the program still agrees.
        let optimized = wasm::compile_module_with_license(&m, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("{label}: {e}"));
        checks += agrees(&m, &optimized, "f", W::I32, &singles(I32_VALUES));
    }
    eprintln!("rebuilt pointers: {checks} checks agree");
}

/// The control: the same probes at displacement 0 stay inside A1, which
/// then shares its bytes with A2 (and the loop `Alloca` keeps one slot) in
/// the lane alone. With the mid-end, which may fold the zero displacement
/// and remove the slots, the module still validates (the second probe reads
/// at the argument's displacement, so the interpreter defines no result to
/// compare for most arguments).
#[test]
fn a_pointer_rebuilt_inside_its_allocation_still_shares() {
    for (label, text, shared) in [
        ("load", OOB_LOAD, 16),
        ("store", OOB_STORE, 16),
        ("callee", OOB_CALLEE, 16),
        ("loop", OOB_LOOP, 16),
    ] {
        let zero = |v: &str| format!("%50 = const i32 0\n    {v} = sub i32 ");
        let inside = text
            .replace("%6 = sub i32 %4, %5", &format!("{}%4, %50", zero("%6")))
            .replace("%3 = sub i32 %1, %2", &format!("{}%1, %50", zero("%3")))
            .replace("%11 = sub i32 %10, %8", &format!("{}%10, %50", zero("%11")));
        assert_ne!(inside, text);
        let m = module(&inside);
        let closed = lane_only(&m).unwrap_or_else(|e| panic!("{label}: {e}"));
        validate(&closed);
        assert_eq!(
            frame_size(&closed, "f"),
            shared,
            "{label}: no longer shares"
        );
        let optimized = wasm::compile_module_with_license(&m, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("{label}: {e}"));
        validate(&optimized);
    }
}

/// `min_loop.trust_ir`: the probe of the first execution of the loop
/// `Alloca` leaves it at a displacement that may resolve elsewhere, so every
/// execution gets fresh storage (carved from the shadow stack: the frame
/// holds `%1` only). Which bytes the probe then reads depends on the layout
/// (the interpreter's own layout defines it), so the result is not compared.
#[test]
fn a_loop_alloca_probed_past_its_allocation_gets_fresh_storage() {
    let m = module(OOB_LOOP);
    let closed = wasm::compile_module_with_license(&m, &permit_unlicensed()).expect("loop");
    validate(&closed);
    assert_eq!(frame_size(&closed, "f"), 8);
}

// ---- 2. Zero-sized allocations ----

/// `zst.trust_ir`: the interpreter gives every live allocation, a
/// zero-sized one included, an address of its own.
const ZST: &str = r#"type ty.0 = i32

functy.0 = (i32) -> (i32)
functy.1 = (ptr) -> ()

global @g ptr

fn @sink(functy.1) {
bb0(%0: ptr):
    %1 = global_addr @global.0
    store ptr %0, ptr %1
    ret
}

fn @two_zst(functy.0) {
bb0(%0: i32):
    %1 = alloca [ty.0 x 0]
    %2 = alloca [ty.0 x 0]
    %3 = ptrtoint ptr %1 to i32
    %4 = ptrtoint ptr %2 to i32
    %5 = icmp eq i32 %3, %4
    %6 = zext bool %5 to i32
    ret %6
}

fn @zst_vs_word(functy.0) {
bb0(%0: i32):
    %1 = alloca [ty.0 x 0]
    %2 = alloca i32
    store i32 %0, ptr %2
    %3 = ptrtoint ptr %1 to i32
    %4 = ptrtoint ptr %2 to i32
    %5 = icmp eq i32 %3, %4
    %6 = zext bool %5 to i32
    ret %6
}

fn @zst_loop(functy.0) {
bb0(%0: i32):
    %1 = const i32 0
    %2 = alloca [ty.0 x 0]
    %3 = ptrtoint ptr %2 to i32
    br bb1(%1, %1)
bb1(%4: i32, %5: i32):
    %6 = alloca [ty.0 x 0]
    call @func.0(%6)
    %7 = ptrtoint ptr %6 to i32
    %8 = icmp eq i32 %7, %3
    %9 = zext bool %8 to i32
    %10 = add i32 %5, %9
    %11 = const i32 1
    %12 = add i32 %4, %11
    %13 = const i32 3
    %14 = icmp ult i32 %12, %13
    condbr %14, bb1(%12, %10), bb2
bb2:
    ret %10
}
"#;

#[test]
fn zero_sized_allocations_have_addresses_of_their_own() {
    let m = module(ZST);
    let closed = wasm::compile_module_with_license(&m, &permit_unlicensed()).expect("zst");
    let mut checks = 0;
    for name in ["two_zst", "zst_vs_word", "zst_loop"] {
        checks += agrees(&m, &closed, name, W::I32, &singles(&[0, 1, 7]));
    }
    eprintln!("zero-sized allocations: {checks} checks agree");
}

// ---- 3. Two by-address aggregate entry parameters need no frame ----

const TWO_AGG: &str = r#"struct @S0 { : i64 @0, : i64 @8 } size=16 align=8 repr=c id=0

functy.0 = (struct.0, struct.0) -> (i64)
functy.1 = (i64, i64) -> (i64)

fn @pick(functy.0) {
bb0(%0: struct.0, %1: struct.0):
    %2 = extractfield i64 %0, 0
    %3 = extractfield i64 %1, 1
    %4 = const i64 3
    %5 = mul i64 %2, %4
    %6 = xor i64 %5, %3
    ret %6
}
"#;

const TWO_AGG_CALLER: &str = r#"
fn @e0(functy.1) {
bb0(%0: i64, %1: i64):
    %2 = make_aggregate struct.0 (%0, %1)
    %3 = make_aggregate struct.0 (%1, %0)
    %4 = call @func.0(%2, %3)
    ret %4
}
"#;

#[test]
fn two_by_address_entry_parameters_compile_without_a_frame() {
    let helper = module(TWO_AGG);
    let closed = wasm::compile_module_with_license(&helper, &permit_unlicensed())
        .expect("closed helper-only module");
    validate(&closed);
    let object = wasm::compile_object_with_license(&helper, &permit_unlicensed())
        .expect("helper-only object");
    let caller = module(&format!(
        "{}{TWO_AGG_CALLER}",
        TWO_AGG.replace(
            "fn @pick(functy.0) {\nbb0",
            "fn @pick(functy.0) {\n}\n\nfn @unused_pick(functy.0) {\nbb0"
        )
    ));
    let caller_object =
        wasm::compile_object_with_license(&caller, &permit_unlicensed()).expect("caller object");
    let reference = module(&format!("{TWO_AGG}{TWO_AGG_CALLER}"));
    let calls: Vec<Vec<i64>> = [(5, 7), (0, -1), (i64::MIN, 3), (100, i64::MAX)]
        .iter()
        .map(|&(a, b)| vec![a, b])
        .collect();
    let closed_ref = wasm::compile_module_with_license(&reference, &permit_unlicensed())
        .expect("closed reference");
    let mut checks = agrees(&reference, &closed_ref, "e0", W::I64, &calls);
    if let Some(linked) = link(&[&object, &caller_object]) {
        checks += agrees(&reference, &linked, "e0", W::I64, &calls);
    }
    eprintln!("two by-address entry parameters: {checks} checks agree");
}

// ---- 4. A pointer-carried extract of a memory-carried lane is a copy ----

/// `xf_slot.trust_ir`: lane 0 of `%1` (a `u128`) is read through the
/// pointer, then `%4` is allocated and written; the extracted value is the
/// argument whatever `%4`'s placement.
const XF_SLOT: &str = r#"functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = alloca (u128, u32)
    %2 = zext u32 %0 to u128
    store u128 %2, ptr %1
    %3 = load u128, ptr %1
    %4 = alloca (u128, u32)
    %5 = const u128 999
    store u128 %5, ptr %4
    %6 = trunc u128 %3 to u32
    ret %6
}
"#;

#[test]
fn a_pointer_carried_extract_is_not_overwritten_by_a_later_allocation() {
    let invalid = module(&XF_SLOT.replace(
        "%3 = load u128, ptr %1",
        "%3 = extractfield (u128, u32) %1, 0",
    ));
    let error = wasm::compile_module_with_license(&invalid, &permit_unlicensed())
        .expect_err("a pointer is not an aggregate field operand");
    assert!(
        format!("{error:?}").contains("FieldAccessInvalid"),
        "{error}"
    );
    let m = module(XF_SLOT);
    let closed = wasm::compile_module_with_license(&m, &permit_unlicensed()).expect("xf_slot");
    validate(&closed);
    let calls = singles(&[0, 5, 77, 65536, i64::from(i32::MAX)]);
    let Some(got) = run_wasm(&closed, "f", W::I32, &calls) else {
        return;
    };
    let want: Vec<Option<i64>> = calls.iter().map(|c| Some(c[0])).collect();
    assert_eq!(got, want);
}

// ---- 5. Bounds-checked accesses through rebuilt pointers still share ----

/// The rustc bridge's shapes: every projection rebuilds the pointer with
/// `ptrtoint` / `add` / `inttoptr`, an index is checked below its slice's
/// length first, and a slice is passed as `(pointer, length)`. `@touch`
/// writes `p[k % len]` and reads it and `p[len - 1]` back; `@e` fills two
/// 4 KiB arrays in disjoint scopes, writes one element of each directly and
/// hands each to `@touch` with `LEN` (`{len}` below). With `LEN` = the
/// array's size every rebuilt pointer provably stays inside its array, so
/// the arrays share bytes.
fn slices(len: u32, (last, limit): (&str, &str)) -> Module {
    module(&format!(
        r#"type ty.0 = u8

functy.0 = (ptr, i32, i32) -> (i32)
functy.1 = (i32) -> (i32)

fn @touch(functy.0) {{
bb0(%0: ptr, %1: i32, %2: i32):
    %3 = const i32 0
    %4 = icmp eq i32 %1, %3
    condbr %4, bb9, bb1
bb1:
    %5 = urem i32 %2, %1
    %6 = icmp ult i32 %5, %1
    condbr %6, bb2, bb9
bb2:
    %7 = ptrtoint ptr %0 to i32
    %8 = add i32 %7, %5
    %9 = inttoptr i32 %8 to ptr
    %10 = trunc i32 %2 to u8
    store u8 %10, ptr %9
    %11 = const i32 1
    %22 = add i32 %1, %11
    %12 = {last}
    %13 = icmp ult i32 %12, {limit}
    condbr %13, bb3, bb9
bb3:
    %14 = ptrtoint ptr %0 to i32
    %15 = add i32 %14, %12
    %16 = inttoptr i32 %15 to ptr
    %17 = load u8, ptr %16
    %18 = zext u8 %17 to i32
    %19 = load u8, ptr %9
    %20 = zext u8 %19 to i32
    %21 = add i32 %18, %20
    ret %21
bb9:
    unreachable
}}

fn @e(functy.1) {{
bb0(%0: i32):
    %1 = alloca [ty.0 x 4096]
    %2 = const u8 3
    %3 = const usize 4096
    memset ptr %1, %2, %3
    %4 = const i32 4096
    %5 = urem i32 %0, %4
    %6 = icmp ult i32 %5, %4
    condbr %6, bb1, bb9
bb1:
    %7 = ptrtoint ptr %1 to i32
    %8 = add i32 %7, %5
    %9 = inttoptr i32 %8 to ptr
    %10 = const u8 9
    store u8 %10, ptr %9
    %11 = const i32 {len}
    %12 = call @func.0(%1, %11, %0)
    %13 = alloca [ty.0 x 4096]
    %14 = const u8 5
    memset ptr %13, %14, %3
    %15 = const i32 7
    %16 = xor i32 %0, %15
    %17 = call @func.0(%13, %11, %16)
    %18 = const i32 3
    %19 = mul i32 %17, %18
    %20 = add i32 %12, %19
    ret %20
bb9:
    unreachable
}}
"#
    ))
}

/// `p[len - 1]`, checked against `len`.
const LAST_IN_BOUNDS: (&str, &str) = ("sub i32 %1, %11", "%1");
/// `p[len]`, one past the end: checked against `len + 1` only.
const LAST_PAST_END: (&str, &str) = ("copy i32 %1", "%22");

#[test]
fn bounds_checked_rebuilt_pointers_keep_sharing() {
    let calls = singles(&[0, 1, 5, 4095, 4096, 100_000, -1, i64::from(i32::MIN)]);
    let m = slices(4096, LAST_IN_BOUNDS);
    let closed = wasm::compile_module_with_license(&m, &permit_unlicensed()).expect("slices");
    let frame = frame_size(&closed, "e");
    assert!(
        frame < 2 * 4096,
        "the frame is {frame} bytes; the two arrays no longer share"
    );
    let checks = agrees(&m, &closed, "e", W::I32, &calls);
    eprintln!("bounds-checked slices: frame {frame}, {checks} checks agree");
}

#[test]
fn a_rebuilt_pointer_past_the_argument_pins_it() {
    // `p[len]` with the check `len < len + 1`: one past the array, which the
    // interpreter resolves into whatever allocation follows (or refuses).
    let past = slices(4096, LAST_PAST_END);
    let closed = wasm::compile_module_with_license(&past, &permit_unlicensed()).expect("past");
    assert!(frame_size(&closed, "e") >= 2 * 4096, "p[len] shares");
    // A length longer than the array: `p[k % len]` and `p[len - 1]` may
    // leave it.
    let long = slices(8192, LAST_IN_BOUNDS);
    let closed = wasm::compile_module_with_license(&long, &permit_unlicensed()).expect("long");
    assert!(frame_size(&closed, "e") >= 2 * 4096, "a long slice shares");
}

// ---- 6. The C library's bulk-memory functions keep no pointer ----

/// `slice::fill` and `copy_from_slice` call the C library's `memset` and
/// `memcpy`, which another object defines. Two 4 KiB arrays in disjoint
/// scopes: `A` is filled and read back, `B` is filled, half of it copied
/// within itself, and read back through the pointer `memcpy` returns.
/// `{fill}` is `memset`'s fill argument.
fn libc_caller(fill: &str, bodies: bool) -> Module {
    let (memset, memcpy) = if bodies {
        (LIBC_MEMSET, LIBC_MEMCPY)
    } else {
        ("fn @memset(functy.0) {\n}\n", "fn @memcpy(functy.1) {\n}\n")
    };
    module(&format!(
        r#"type ty.0 = u8

functy.0 = (ptr, i32, usize) -> (ptr)
functy.1 = (ptr, ptr, usize) -> (ptr)
functy.2 = (i32) -> (i32)

{memset}
{memcpy}
fn @e(functy.2) {{
bb0(%0: i32):
    %1 = alloca [ty.0 x 4096]
    %2 = const usize 4096
    %20 = ptrtoint ptr %1 to i32
    %3 = call @func.0(%1, {fill}, %2)
    %4 = ptrtoint ptr %1 to i32
    %5 = const i32 100
    %6 = add i32 %4, %5
    %7 = inttoptr i32 %6 to ptr
    %8 = load u8, ptr %7
    %9 = zext u8 %8 to i32
    %10 = alloca [ty.0 x 4096]
    %11 = const i32 1
    %12 = add i32 %0, %11
    %13 = call @func.0(%10, %12, %2)
    %14 = ptrtoint ptr %10 to i32
    %15 = const i32 2048
    %16 = add i32 %14, %15
    %17 = inttoptr i32 %16 to ptr
    %18 = const u8 77
    store u8 %18, ptr %17
    %19 = const usize 16
    %21 = call @func.1(%10, %17, %19)
    %22 = ptrtoint ptr %21 to i32
    %23 = const i32 3
    %24 = add i32 %22, %23
    %25 = inttoptr i32 %24 to ptr
    %26 = load u8, ptr %25
    %27 = zext u8 %26 to i32
    %28 = load u8, ptr %21
    %29 = zext u8 %28 to i32
    %30 = const i32 1000
    %31 = mul i32 %29, %30
    %32 = add i32 %9, %27
    %33 = add i32 %32, %31
    ret %33
}}
"#
    ))
}

const LIBC_MEMSET: &str = "fn @memset(functy.0) {\n\
bb0(%0: ptr, %1: i32, %2: usize):\n\
    %3 = trunc i32 %1 to u8\n\
    memset ptr %0, %3, %2\n\
    ret %0\n\
}\n";

const LIBC_MEMCPY: &str = "fn @memcpy(functy.1) {\n\
bb0(%0: ptr, %1: ptr, %2: usize):\n\
    memcopy ptr %0, ptr %1, %2\n\
    ret %0\n\
}\n";

#[test]
fn the_c_librarys_bulk_memory_functions_do_not_pin_their_arguments() {
    let caller = libc_caller("%0", false);
    let object =
        wasm::compile_object_with_license(&caller, &permit_unlicensed()).expect("caller object");
    let library = module(&format!(
        "functy.0 = (ptr, i32, usize) -> (ptr)\nfuncty.1 = (ptr, ptr, usize) -> (ptr)\n\n\
         {LIBC_MEMSET}\n{LIBC_MEMCPY}"
    ));
    let library =
        wasm::compile_object_with_license(&library, &permit_unlicensed()).expect("library object");
    let reference = libc_caller("%0", true);
    let Some(linked) = link(&[&object, &library]) else {
        return;
    };
    let frame = frame_size(&linked, "e");
    assert!(
        frame < 2 * 4096,
        "the frame is {frame} bytes; memset/memcpy pinned the arrays"
    );
    let checks = agrees(&reference, &linked, "e", W::I32, &singles(I32_VALUES));
    eprintln!("C library bulk memory: frame {frame}, {checks} checks agree");
    // An address handed to `memset` as its fill byte reaches memory: pinned.
    let leaked = libc_caller("%20", false);
    let object =
        wasm::compile_object_with_license(&leaked, &permit_unlicensed()).expect("leaked fill");
    let Some(linked) = link(&[&object, &library]) else {
        return;
    };
    assert!(
        frame_size(&linked, "e") >= 2 * 4096,
        "an address fill shares"
    );
}

/// `q13_len.rs` at `-C opt-level=2`: the callee's loop carries the slice
/// length in a block parameter and checks every index against that copy.
const LOOP_SUM: &str = r#"type ty.0 = u8

functy.0 = (ptr, i32) -> (i32)
functy.1 = (i32) -> (i32)

fn @sum_all(functy.0) {
bb0(%0: ptr, %1: i32):
    %2 = const i32 0
    %3 = copy i32 %1
    br bb1(%2, %3, %2)
bb1(%4: i32, %5: i32, %6: i32):
    %7 = icmp ult i32 %6, %5
    condbr %7, bb3, bb4
bb3:
    %9 = ptrtoint ptr %0 to i32
    %10 = add i32 %9, %6
    %11 = inttoptr i32 %10 to ptr
    %12 = load u8, ptr %11
    %13 = zext u8 %12 to i32
    %14 = add i32 %4, %13
    %15 = const i32 512
    %16 = add i32 %6, %15
    br bb1(%14, %5, %16)
bb4:
    ret %4
}

fn @e(functy.1) {
bb0(%0: i32):
    %1 = alloca [ty.0 x 4096]
    %2 = trunc i32 %0 to u8
    %3 = const usize 4096
    memset ptr %1, %2, %3
    %4 = const i32 4096
    %5 = call @func.0(%1, %4)
    %6 = alloca [ty.0 x 4096]
    %7 = const u8 1
    memset ptr %6, %7, %3
    %8 = call @func.0(%6, %4)
    %9 = add i32 %5, %8
    ret %9
}
"#;

#[test]
fn a_loop_carried_copy_of_the_length_still_bounds_the_index() {
    let m = module(LOOP_SUM);
    let closed = wasm::compile_module_with_license(&m, &permit_unlicensed()).expect("loop sum");
    let frame = frame_size(&closed, "e");
    assert!(frame < 2 * 4096, "the frame is {frame} bytes");
    agrees(&m, &closed, "e", W::I32, &singles(&[0, 1, 255, 256, -1]));
}

/// A callee that checks `%2 < %1` against its CURRENT length, where a branch
/// back to its entry block rebinds the length to `u32::MAX`: the caller's
/// length 1 does not bound the probe at displacement -4, which the
/// interpreter resolves into A1.
const REENTERED_CALLEE: &str = r#"functy.0 = (ptr, i32, i32) -> (i32)
functy.1 = (i32) -> (i32)

fn @probe(functy.0) {
bb0(%0: ptr, %1: i32, %2: i32):
    %3 = icmp ult i32 %2, %1
    condbr %3, bb1, bb2
bb1:
    %4 = ptrtoint ptr %0 to i32
    %5 = add i32 %4, %2
    %6 = inttoptr i32 %5 to ptr
    %7 = load i32, ptr %6
    ret %7
bb2:
    %8 = const i32 -1
    br bb0(%0, %8, %2)
}

fn @f(functy.1) {
bb0(%0: i32):
    %1 = alloca i64
    %2 = const i64 17179869184
    store i64 %2, ptr %1
    %3 = alloca i32
    store i32 %0, ptr %3
    %20 = const i32 1
    %21 = const i32 -4
    %4 = call @func.0(%3, %20, %21)
    %5 = alloca i32
    %6 = const i32 12345
    store i32 %6, ptr %5
    %7 = ptrtoint ptr %1 to i32
    %8 = add i32 %7, %4
    %9 = const i32 4
    %10 = add i32 %8, %9
    %11 = inttoptr i32 %10 to ptr
    %12 = load i32, ptr %11
    ret %12
}
"#;

/// The caller-side form: `@mid` re-enters its own entry block with the length
/// rebound to `u32::MAX` and only then hands it to a checking `@probe` that
/// is never re-entered; `@f` passes length 1.
const REENTERED_MIDDLE: &str = r#"functy.0 = (ptr, i32, i32) -> (i32)
functy.1 = (ptr, i32, i32, i32) -> (i32)
functy.2 = (i32) -> (i32)

fn @probe(functy.0) {
bb0(%0: ptr, %1: i32, %2: i32):
    %3 = icmp ult i32 %2, %1
    condbr %3, bb1, bb2
bb1:
    %4 = ptrtoint ptr %0 to i32
    %5 = add i32 %4, %2
    %6 = inttoptr i32 %5 to ptr
    %7 = load i32, ptr %6
    ret %7
bb2:
    %8 = const i32 0
    ret %8
}

fn @mid(functy.1) {
bb0(%0: ptr, %1: i32, %2: i32, %3: i32):
    %4 = const i32 0
    %5 = icmp eq i32 %3, %4
    condbr %5, bb1, bb2
bb1:
    %6 = call @func.0(%0, %1, %2)
    ret %6
bb2:
    %7 = const i32 -1
    br bb0(%0, %7, %2, %4)
}

fn @f(functy.2) {
bb0(%0: i32):
    %1 = alloca i64
    %2 = const i64 17179869184
    store i64 %2, ptr %1
    %3 = alloca i32
    store i32 %0, ptr %3
    %20 = const i32 1
    %21 = const i32 -4
    %22 = const i32 1
    %4 = call @func.1(%3, %20, %21, %22)
    %5 = alloca i32
    %6 = const i32 12345
    store i32 %6, ptr %5
    %7 = ptrtoint ptr %1 to i32
    %8 = add i32 %7, %4
    %9 = const i32 4
    %10 = add i32 %8, %9
    %11 = inttoptr i32 %10 to ptr
    %12 = load i32, ptr %11
    ret %12
}
"#;

/// A length check binds a callee's length parameter only while no branch
/// re-enters the entry block: the callee that checks a rebound length, and a
/// middle function that rebinds the length before passing it on, both pin
/// A3 (each of `%1`, A3 and A5 in 8 bytes of its own); without the
/// re-entry (and called straight through) the middle function's need still
/// translates to the caller's constant length, and A3 shares with A5.
#[test]
fn a_length_rebound_by_reentering_the_entry_block_does_not_bound_the_index() {
    let mut checks = 0;
    for (label, text, frame) in [
        ("re-entered callee", REENTERED_CALLEE.to_owned(), 24),
        ("re-entered middle", REENTERED_MIDDLE.to_owned(), 24),
        (
            "middle without re-entry",
            REENTERED_MIDDLE
                .replace("    br bb0(%0, %7, %2, %4)", "    ret %7")
                .replace("%22 = const i32 1", "%22 = const i32 0"),
            16,
        ),
    ] {
        let m = module(&text);
        let closed = lane_only(&m).unwrap_or_else(|e| panic!("{label}: {e}"));
        assert_eq!(frame_size(&closed, "f"), frame, "{label}: frame");
        checks += agrees(&m, &closed, "f", W::I32, &singles(I32_VALUES));
        // With the mid-end, which may remove the slots, the program still agrees.
        let optimized = wasm::compile_module_with_license(&m, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("{label}: {e}"));
        checks += agrees(&m, &optimized, "f", W::I32, &singles(I32_VALUES));
    }
    eprintln!("re-entered lengths: {checks} checks agree");
}

/// A displacement `A3 + %7` crosses the back edge into `%6` while the loop
/// rebinds `%7` (from -4 to 0); the exit checks the NEW `%7 < 4`, which says
/// nothing of the -4 `%6` was built from, so the probe through `%6` reads
/// A1's high word and A3 must not share with A19.
const STALE_INDEX: &str = r#"functy.0 = (i32) -> (i32)

fn @f(functy.0) {
bb0(%0: i32):
    %1 = alloca i64
    %2 = const i64 17179869184
    store i64 %2, ptr %1
    %3 = alloca i32
    store i32 %0, ptr %3
    %4 = const i32 0
    %5 = const i32 -4
    br bb1(%4, %5, %4)
bb1(%6: i32, %7: i32, %8: i32):
    %9 = ptrtoint ptr %3 to i32
    %10 = add i32 %9, %7
    %11 = const i32 1
    %12 = add i32 %8, %11
    %13 = const i32 4
    %14 = add i32 %7, %13
    %15 = icmp eq i32 %8, %11
    condbr %15, bb2, bb1(%10, %14, %12)
bb2:
    %16 = icmp ult i32 %7, %13
    condbr %16, bb3, bb9
bb3:
    %17 = inttoptr i32 %6 to ptr
    %18 = load i32, ptr %17
    %19 = alloca i32
    %20 = const i32 12345
    store i32 %20, ptr %19
    %21 = ptrtoint ptr %1 to i32
    %22 = add i32 %21, %18
    %23 = add i32 %22, %13
    %24 = inttoptr i32 %23 to ptr
    %25 = load i32, ptr %24
    ret %25
bb9:
    unreachable
}
"#;

/// The precision control: the index is checked before the pointer is built,
/// and the pointer crosses a forward edge into a block its index's
/// definition dominates, so the probe stays inside A1 and A1 shares with A9.
const CHECKED_INDEX_FORWARD: &str = r#"functy.0 = (i32) -> (i32)

fn @f(functy.0) {
bb0(%0: i32):
    %1 = alloca i32
    store i32 %0, ptr %1
    %2 = const i32 1
    %3 = icmp ult i32 %0, %2
    condbr %3, bb1, bb2
bb1:
    %4 = ptrtoint ptr %1 to i32
    %5 = add i32 %4, %0
    br bb3(%5)
bb2:
    ret %0
bb3(%6: i32):
    %7 = inttoptr i32 %6 to ptr
    %8 = load i32, ptr %7
    %9 = alloca i32
    %10 = const i32 12345
    store i32 %10, ptr %9
    %11 = load i32, ptr %9
    %12 = add i32 %8, %11
    ret %12
}
"#;

/// A displacement carried into a block parameter keeps its index only when
/// the index cannot have been rebound since: around a loop it is unknown
/// (A3 is pinned, with or without a check of the rebound index), across a
/// forward edge the index's definition dominates it stays bounded (A1
/// shares with A9).
#[test]
fn a_displacement_carried_around_a_loop_is_not_bounded_by_the_next_index() {
    // Both outcomes reach the access, so this is not a bounds guard;
    // retain every block under strict source admission.
    let unguarded = STALE_INDEX.replace("bb9:\n    unreachable", "bb9:\n    br bb3");
    assert_ne!(unguarded, STALE_INDEX);
    let mut checks = 0;
    for (label, text, frame) in [
        ("checked rebound index", STALE_INDEX.to_owned(), 24),
        ("unchecked", unguarded, 24),
        ("forward edge", CHECKED_INDEX_FORWARD.to_owned(), 8),
    ] {
        let m = module(&text);
        let closed = lane_only(&m).unwrap_or_else(|e| panic!("{label}: {e}"));
        assert_eq!(frame_size(&closed, "f"), frame, "{label}: frame");
        checks += agrees(&m, &closed, "f", W::I32, &singles(I32_VALUES));
        // With the mid-end, which may remove the slots, the program still agrees.
        let optimized = wasm::compile_module_with_license(&m, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("{label}: {e}"));
        checks += agrees(&m, &optimized, "f", W::I32, &singles(I32_VALUES));
    }
    eprintln!("carried displacements: {checks} checks agree");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
