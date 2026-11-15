// trust-cg-codegen/tests/wasm_r17b_lane.rs - wasm32 lane: round-17 stage-B calls and aggregates
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Typed forms of the bridge call and aggregate workloads the round-17 stage-B
//! mid-end rewrites, on the wasm32 lane at O2, each executed by node and
//! compared with the trust-ir reference interpreter running the source in
//! the mid-end differential's view (the C library declarations are given
//! their bodies; aggregate loads and values are explicit):
//!
//! * `env`: a closure whose `[u32 x 1]` environment is loaded from the
//!   caller's slot and whose `[u8 x 1]` result is loaded from its own slot
//!   returns that value and is spliced into the caller's loop (no call);
//! * `iter`: a slice-iterator step views its two thin pointers as `ptr`
//!   for comparison and updates the first tuple field (no call);
//! * `niche`: a callee copying eight constant bytes by a `memcopy` of a
//!   `usize` count and testing `const i8 -2` (the byte 0xfe) is spliced (no call);
//! * `eq3`: `memcmp(a, b, 3) == 0` keeps its call of the imported `memcmp`:
//!   the default profile withholds the comparison-call rewrite, since a
//!   declaration's name and prototype do not authenticate the C library's
//!   comparison (OD-164);
//! * `copyrt`: `memcpy` of a run-time count keeps its call of the imported
//!   `memcpy`: the default profile withholds the run-time-count widening of
//!   the memory-call rewrite (OD-165's merge boundary);
//! * `packed1` and `packed2`: a packed `[u8 x 15]` by-value parameter, which
//!   its callee copies into a slot lane by lane and reads three fields of,
//!   is read through its address by a clone: the clone loads three fields
//!   and stores nothing.
//!
//! At O0 every call stays a call. trust-ir's validator reports no finding on
//! the O2 mid-end's output that the input lacks (the lane would fall back
//! otherwise: no pass is withheld for a finding and nothing falls back;
//! the fill-call and comparison-call rewrites are withheld for custody,
//! OD-155 and OD-164). Node is required
//! to execute the wasm; its absence is a loud SKIP. The callees are hidden,
//! so the module is an object linked by `wasm-ld`.
//!
//! The object is linked by `wasm-ld` (`WASM_LD`), the library functions
//! imported; the absence of `wasm-ld` is a loud SKIP too.
//!
//! The entry this test drives (`compile_object_with_evidence_license_options_hints`
//! with `WasmInlineHints`), `WasmOptOptions`, the `mid_end` evidence it reads (the pass names
//! `inline`, `lane_load`, `respell`, `mem_call`, `mem_cmp` and `byaddr`) and
//! `trust_cg_verify::trust_ir_mid_tv::{interpretable_module, interpretable}`
//! are provisional surfaces pending the owner's sign-off: this test follows
//! them if they change, and is not a contract for their shape.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{self, WasmInlineHints, WasmOptOptions};
use trust_cg_verify::trust_ir_mid_tv::{interpretable, interpretable_module};
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

/// The declarations (`func.0` `memcmp`, `func.1` `memcpy`) and the hidden
/// callees (`func.2` the closure, `func.3` the slice step, `func.4` the
/// niche filler, `func.5` the packed reader).
fn callees() -> String {
    let mut copy = String::new();
    for j in 0..15 {
        copy.push_str(&format!(
            "\x20   %{index} = const usize {j}\n\
             \x20   %{x} = extractelement u8 %0, %{index}\n\
             \x20   %{y} = gep u8, ptr %10, %{index}\n\
             \x20   store u8 %{x}, ptr %{y}\n",
            index = 100 + 3 * j,
            x = 101 + 3 * j,
            y = 102 + 3 * j,
        ));
    }
    format!(
        "fn @memcmp(functy.0) {{\n}}\n\n\
fn @memcpy(functy.1) {{\n}}\n\n\
fn @clo(functy.2) {{\n\
\x20   ; #visibility: hidden\n\
bb0(%0: [ty.1 x 1], %1: u32):\n\
\x20   %2 = alloca [ty.0 x 1], align 1\n\
\x20   %10 = const usize 0\n\
\x20   %3 = extractelement u32 %0, %10\n\
\x20   %4 = mul u32 %3, %1\n\
\x20   %5 = trunc u32 %4 to u8\n\
\x20   store u8 %5, ptr %2\n\
\x20   %6 = load [ty.0 x 1], ptr %2\n\
\x20   ret %6\n\
}}\n\n\
fn @step(functy.3) {{\n\
\x20   ; #visibility: hidden\n\
bb0(%0: &mut (*const u32, *const u32)):\n\
\x20   %14 = load (*const u32, *const u32), ptr %0\n\
\x20   %1 = extractfield *const u32 %14, 0\n\
\x20   %2 = extractfield *const u32 %14, 1\n\
\x20   %3 = ptrtoptr *const u32 %1 to ptr\n\
\x20   %4 = ptrtoptr *const u32 %2 to ptr\n\
\x20   %5 = icmp eq ptr %3, %4\n\
\x20   condbr %5, bb1, bb2\n\
bb1:\n\
\x20   %6 = const u32 0\n\
\x20   ret %6\n\
bb2:\n\
\x20   %7 = load u32, ptr %3\n\
\x20   %8 = const usize 4\n\
\x20   %9 = gep u8, ptr %3, %8\n\
\x20   %10 = ptrtoptr ptr %9 to *const u32\n\
\x20   store *const u32 %10, ptr %0\n\
\x20   %12 = const u32 1\n\
\x20   %13 = or u32 %7, %12\n\
\x20   ret %13\n\
}}\n\n\
fn @fill(functy.4) {{\n\
\x20   ; #visibility: hidden\n\
bb0(%0: ptr, %1: u32):\n\
\x20   %2 = global_addr @global.0\n\
\x20   %3 = const usize 8\n\
\x20   memcopy ptr %0, ptr %2, %3\n\
\x20   %4 = const i8 -2\n\
\x20   %5 = trunc u32 %1 to i8\n\
\x20   %6 = icmp eq i8 %5, %4\n\
\x20   %7 = zext bool %6 to u8\n\
\x20   %8 = const usize 8\n\
\x20   %9 = gep u8, ptr %0, %8\n\
\x20   store u8 %7, ptr %9\n\
\x20   ret\n\
}}\n\n\
fn @sumpk.tcg.crate.0123456789abcdef(functy.5) {{\n\
\x20   ; #visibility: hidden\n\
bb0(%0: [ty.0 x 15]):\n\
\x20   %10 = alloca [ty.0 x 15], align 1\n\
{copy}\
\x20   %60 = const i32 1\n\
\x20   %61 = gep inbounds u8, ptr %10, %60\n\
\x20   %62 = load u64, ptr %61\n\
\x20   %63 = const i32 11\n\
\x20   %64 = gep inbounds u8, ptr %10, %63\n\
\x20   %65 = load u32, ptr %64\n\
\x20   %66 = const i32 9\n\
\x20   %67 = gep inbounds u8, ptr %10, %66\n\
\x20   %68 = load u16, ptr %67\n\
\x20   %69 = trunc u64 %62 to u32\n\
\x20   %70 = const u64 32\n\
\x20   %71 = lshr u64 %62, %70\n\
\x20   %72 = trunc u64 %71 to u32\n\
\x20   %73 = zext u16 %68 to u32\n\
\x20   %74 = xor u32 %69, %72\n\
\x20   %75 = add u32 %74, %65\n\
\x20   %76 = mul u32 %75, %73\n\
\x20   ret %76\n\
}}\n\n"
    )
}

/// The exported functions, each `(i32, i32) -> i32`.
fn exports() -> String {
    // A 16-byte slot holding `a`, `b`, `a ^ b`, `a + b` (`%2`), the shared
    // prefix of `iter`, `eq3`, `copyrt` and the packed callers.
    let slot = "\x20   %2 = alloca [ty.1 x 4], align 4\n\
\x20   %3 = bitcast i32 %0 to u32\n\
\x20   %4 = bitcast i32 %1 to u32\n\
\x20   store u32 %3, ptr %2\n\
\x20   %5 = const usize 4\n\
\x20   %6 = gep u8, ptr %2, %5\n\
\x20   store u32 %4, ptr %6\n\
\x20   %7 = const usize 8\n\
\x20   %8 = gep u8, ptr %2, %7\n\
\x20   %9 = xor u32 %3, %4\n\
\x20   store u32 %9, ptr %8\n\
\x20   %11 = const usize 12\n\
\x20   %12 = gep u8, ptr %2, %11\n\
\x20   %13 = add u32 %3, %4\n\
\x20   store u32 %13, ptr %12\n";
    let packed = |name: &str, shift: u32| {
        format!(
            "fn @{name}(functy.6) {{\n\
bb0(%0: i32, %1: i32):\n\
{slot}\
\x20   %14 = const u32 {shift}\n\
\x20   %15 = shl u32 %9, %14\n\
\x20   store u32 %15, ptr %12\n\
\x20   %90 = load [ty.0 x 15], ptr %2\n\
\x20   %16 = call @func.5(%90)\n\
\x20   %17 = bitcast u32 %16 to i32\n\
\x20   ret %17\n\
}}\n\n"
        )
    };
    format!(
        "fn @env(functy.6) {{\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.1 x 1], align 4\n\
\x20   %3 = bitcast i32 %0 to u32\n\
\x20   store u32 %3, ptr %2\n\
\x20   %4 = const u32 0\n\
\x20   %5 = bitcast i32 %1 to u32\n\
\x20   %6 = const u32 3\n\
\x20   %7 = and u32 %5, %6\n\
\x20   %8 = const u32 2\n\
\x20   %9 = add u32 %7, %8\n\
\x20   br bb1(%4, %4)\n\
bb1(%10: u32, %11: u32):\n\
\x20   %30 = load [ty.1 x 1], ptr %2\n\
\x20   %12 = call @func.2(%30, %10)\n\
\x20   %31 = const usize 0\n\
\x20   %13 = extractelement u8 %12, %31\n\
\x20   %14 = zext u8 %13 to u32\n\
\x20   %15 = const u32 7\n\
\x20   %16 = mul u32 %11, %15\n\
\x20   %17 = add u32 %16, %14\n\
\x20   %18 = const u32 1\n\
\x20   %19 = add u32 %10, %18\n\
\x20   %20 = icmp ult u32 %19, %9\n\
\x20   condbr %20, bb1(%19, %17), bb2\n\
bb2:\n\
\x20   %21 = bitcast u32 %17 to i32\n\
\x20   ret %21\n\
}}\n\n\
fn @iter(functy.6) {{\n\
bb0(%0: i32, %1: i32):\n\
{slot}\
\x20   %20 = alloca (*const u32, *const u32), align 4\n\
\x20   %21 = ptrtoptr ptr %2 to *const u32\n\
\x20   %22 = const u32 3\n\
\x20   %23 = and u32 %4, %22\n\
\x20   %24 = const u32 4\n\
\x20   %25 = mul u32 %23, %24\n\
\x20   %26 = bitcast u32 %25 to usize\n\
\x20   %27 = gep u8, ptr %2, %26\n\
\x20   %28 = ptrtoptr ptr %27 to *const u32\n\
\x20   store *const u32 %21, ptr %20\n\
\x20   %29 = const usize 4\n\
\x20   %30 = gep u8, ptr %20, %29\n\
\x20   store *const u32 %28, ptr %30\n\
\x20   %31 = const u32 0\n\
\x20   br bb1(%31)\n\
bb1(%32: u32):\n\
\x20   %33 = ptrtoptr ptr %20 to &mut (*const u32, *const u32)\n\
\x20   %34 = call @func.3(%33)\n\
\x20   %35 = const u32 31\n\
\x20   %36 = mul u32 %32, %35\n\
\x20   %37 = add u32 %36, %34\n\
\x20   %38 = const u32 0\n\
\x20   %39 = icmp ne u32 %34, %38\n\
\x20   condbr %39, bb1(%37), bb2\n\
bb2:\n\
\x20   %40 = bitcast u32 %37 to i32\n\
\x20   ret %40\n\
}}\n\n\
fn @niche(functy.6) {{\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.1 x 3], align 4\n\
\x20   %3 = bitcast i32 %0 to u32\n\
\x20   call @func.4(%2, %3)\n\
\x20   %4 = const usize 5\n\
\x20   %5 = gep u8, ptr %2, %4\n\
\x20   %6 = load u32, ptr %5\n\
\x20   %7 = bitcast i32 %1 to u32\n\
\x20   %8 = add u32 %6, %7\n\
\x20   %9 = bitcast u32 %8 to i32\n\
\x20   ret %9\n\
}}\n\n\
fn @eq3(functy.6) {{\n\
bb0(%0: i32, %1: i32):\n\
{slot}\
\x20   %14 = const usize 1\n\
\x20   %15 = gep u8, ptr %2, %14\n\
\x20   %16 = const i32 3\n\
\x20   %17 = call @func.0(%2, %6, %16)\n\
\x20   %18 = const i32 0\n\
\x20   %19 = icmp eq i32 %17, %18\n\
\x20   %20 = call @func.0(%15, %8, %16)\n\
\x20   %21 = icmp ne i32 %20, %18\n\
\x20   %22 = zext bool %19 to i32\n\
\x20   %23 = zext bool %21 to i32\n\
\x20   %24 = const i32 1\n\
\x20   %25 = shl i32 %23, %24\n\
\x20   %26 = or i32 %22, %25\n\
\x20   ret %26\n\
}}\n\n\
fn @copyrt(functy.6) {{\n\
bb0(%0: i32, %1: i32):\n\
{slot}\
\x20   %14 = const u32 3\n\
\x20   %15 = and u32 %4, %14\n\
\x20   %16 = const usize 1\n\
\x20   %17 = gep u8, ptr %2, %16\n\
\x20   %40 = ptrtoptr ptr %17 to *mut u8\n\
\x20   %41 = ptrtoptr ptr %6 to *const u8\n\
\x20   %18 = call @func.1(%40, %41, %15)\n\
\x20   %19 = load u32, ptr %2\n\
\x20   %20 = load u32, ptr %6\n\
\x20   %21 = load u32, ptr %8\n\
\x20   %22 = const u32 31\n\
\x20   %23 = mul u32 %19, %22\n\
\x20   %24 = xor u32 %23, %20\n\
\x20   %25 = mul u32 %24, %22\n\
\x20   %26 = xor u32 %25, %21\n\
\x20   %27 = bitcast u32 %26 to i32\n\
\x20   ret %27\n\
}}\n\n{}{}",
        packed("packed1", 3),
        packed("packed2", 5)
    )
}

const NAMES: &[&str] = &[
    "env", "iter", "niche", "eq3", "copyrt", "packed1", "packed2",
];

fn program() -> Module {
    let text = format!(
        "module \"r17b\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
type ty.0 = u8\n\ntype ty.1 = u32\n\n\
global internal align(1) @K [ty.0 x 8] = bytes<0102030405060708>\n\n\
functy.0 = (ptr, ptr, i32) -> (i32)\n\
functy.1 = (*mut u8, *const u8, u32) -> (*mut u8)\n\
functy.2 = ([ty.1 x 1], u32) -> ([ty.0 x 1])\n\
functy.3 = (&mut (*const u32, *const u32)) -> (u32)\n\
functy.4 = (ptr, u32) -> ()\n\
functy.5 = ([ty.0 x 15]) -> (u32)\n\
functy.6 = (i32, i32) -> (i32)\n\n\
{}{}",
        callees(),
        exports()
    );
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("parse the test program: {e}\n{text}"));
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "valid round-17 fixture: {errors:?}");
    module
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
    (0x0102_0304, 0x0102_0304),
    (0x00ff_00ff, 0x00ff_00fe),
];

/// The packed reader, in the producer's never-inline side table (as the
/// rustc bridge records an `#[inline(never)]` item).
const NEVER_INLINE: &str = "sumpk.tcg.crate.0123456789abcdef";

/// The object at `level` (the hidden callees need an object: a closed
/// module has no emitter for hidden visibility), linked by `wasm-ld` with
/// the library functions left undefined (imported from `env`); `None`
/// (a loud SKIP) without `wasm-ld`.
fn compile(module: &Module, level: OptLevel) -> Option<(Vec<u8>, wasm::WasmCompileEvidence)> {
    let hints = WasmInlineHints {
        never_inline: [NEVER_INLINE.to_string()].into_iter().collect(),
        ..WasmInlineHints::default()
    };
    let (object, evidence) = wasm::compile_object_with_evidence_license_options_hints(
        module,
        &permit_unlicensed(),
        WasmOptOptions {
            level,
            mid_end: true,
        },
        &hints,
    )
    .expect("compile the object");
    let Some(ld) = wasm_ld() else {
        eprintln!("SKIP: wasm-ld not found (set WASM_LD); the object was not linked");
        return None;
    };
    let dir = scratch("link");
    std::fs::write(dir.join("m0.o"), &object).unwrap();
    let out = Command::new(&ld)
        .args([
            "--no-entry",
            "--export-dynamic",
            "--allow-undefined",
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
    Some((linked, evidence))
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

/// The source run in the mid-end differential's view.
/// `eq3(a, b)` by hand: the slot holds `a`, `b`, `a ^ b` and `a + b`
/// little-endian; bit 0 is `memcmp(slot, slot + 4, 3) == 0`, bit 1 is
/// `memcmp(slot + 1, slot + 8, 3) != 0`.
fn eq3_reference(a: i64, b: i64) -> i64 {
    let (a, b) = (a as i32 as u32, b as i32 as u32);
    let mut slot = [0u8; 16];
    slot[0..4].copy_from_slice(&a.to_le_bytes());
    slot[4..8].copy_from_slice(&b.to_le_bytes());
    slot[8..12].copy_from_slice(&(a ^ b).to_le_bytes());
    slot[12..16].copy_from_slice(&a.wrapping_add(b).to_le_bytes());
    let eq = slot[0..3] == slot[4..7];
    let ne = slot[1..4] != slot[8..11];
    i64::from(eq) | (i64::from(ne) << 1)
}

fn interpret(view: &Module, name: &str, a: i64, b: i64) -> i64 {
    let f = view.function_by_name(name).expect("function");
    let viewed = interpretable(view, f).unwrap_or_else(|| f.clone());
    let args = [a, b].map(|v| InterpretValue::int(Ty::I32, i128::from(v as i32)).expect("i32"));
    let out = Interpreter::with_module(view)
        .with_options(InterpretOptions {
            fuel: 10_000_000,
            max_call_depth: 64,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_function(&viewed, args)
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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_r17b_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run `name(a, b)` for every row in node, the library functions supplied
/// over the module's memory: the results and the number of library calls.
/// `None` when node is absent.
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
           memcpy: (d, s, n) => {{ calls++; bytes().copyWithin(d >>> 0, s >>> 0, (s >>> 0) + (n >>> 0)); return d; }},\n\
           memcmp: (a, b, n) => {{ calls++; const m = bytes(); for (let i = 0; i < (n >>> 0); i++) {{ const x = m[(a >>> 0) + i], y = m[(b >>> 0) + i]; if (x !== y) return x - y; }} return 0; }},\n\
         }};\n\
         inst = new WebAssembly.Instance(m, {{ env: host }});\n\
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

/// The opcodes of a function's body counted (by export name, or the body
/// of the function a call in it names when `callee` is set).
#[derive(Default, Debug)]
struct Ops {
    calls: Vec<u32>,
    loads: usize,
    stores: usize,
    copies: usize,
}

fn bodies(bytes: &[u8]) -> (u32, std::collections::HashMap<String, u32>, Vec<Ops>) {
    use wasmparser::{ExternalKind, Operator, Parser, Payload};
    let mut imported = 0u32;
    let mut exports = std::collections::HashMap::new();
    let mut out = Vec::new();
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
                    if e.kind == ExternalKind::Func {
                        exports.insert(e.name.to_string(), e.index);
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                let mut ops = Ops::default();
                for op in body.get_operators_reader().expect("operators") {
                    match op.expect("operator") {
                        Operator::Call { function_index } => ops.calls.push(function_index),
                        Operator::I32Load { .. }
                        | Operator::I64Load { .. }
                        | Operator::F32Load { .. }
                        | Operator::F64Load { .. }
                        | Operator::I32Load8S { .. }
                        | Operator::I32Load8U { .. }
                        | Operator::I32Load16S { .. }
                        | Operator::I32Load16U { .. } => ops.loads += 1,
                        Operator::I32Store { .. }
                        | Operator::I64Store { .. }
                        | Operator::I32Store8 { .. }
                        | Operator::I32Store16 { .. } => ops.stores += 1,
                        Operator::MemoryCopy { .. } => ops.copies += 1,
                        _ => {}
                    }
                }
                out.push(ops);
            }
            _ => {}
        }
    }
    (imported, exports, out)
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
fn round_17_stage_b_calls_and_aggregates_lose_their_calls_and_agree() {
    let module = program();
    let view = interpretable_module(&module);
    let Some((o2, evidence)) = compile(&module, OptLevel::O2) else {
        return;
    };
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    assert_eq!(
        mid.passes_withheld.keys().copied().collect::<Vec<_>>(),
        ["fill_call", "mem_cmp"],
        "{:?}",
        mid.passes_withheld
    );
    assert!(mid.fallback.is_none(), "{:?}", mid.fallback);
    for pass in ["inline", "lane_load", "byaddr"] {
        assert!(changed(&evidence, pass) >= 1, "{pass}: {mid:#?}");
    }
    // Typed inputs already spell pointer comparisons and byte counts at
    // their required types. The invalid legacy forms are checked below.
    assert_eq!(changed(&evidence, "respell"), 0);
    assert_eq!(changed(&evidence, "mem_cmp"), 0);
    assert_eq!(changed(&evidence, "mem_call"), 0);
    let Some((o0, _)) = compile(&module, OptLevel::O0) else {
        return;
    };
    let (imported, exports, ops) = bodies(&o2);
    let (o0_imported, o0_exports, o0_ops) = bodies(&o0);
    for &name in NAMES {
        // The differential's view gives `memcmp` no body (OD-164's merge
        // boundary), so `eq3`'s reference is computed here.
        let want: Vec<i64> = ROWS
            .iter()
            .map(|&(a, b)| match name {
                "eq3" => eq3_reference(a, b),
                _ => interpret(&view, name, a, b),
            })
            .collect();
        let body = &ops[(exports[name] - imported) as usize];
        if name.starts_with("packed") {
            // One call, of the clone, which loads three fields and stores
            // nothing.
            let [callee] = body.calls.as_slice() else {
                panic!("{name}: {body:?}");
            };
            let clone = &ops[(callee - imported) as usize];
            assert_eq!(
                (clone.loads, clone.stores),
                (3, 0),
                "{name}'s callee: {clone:?}"
            );
        } else if name == "eq3" || name == "copyrt" {
            // The withheld rewrites' calls stay calls of the imports.
            assert!(!body.calls.is_empty(), "{name}: {body:?}");
            assert!(
                body.calls.iter().all(|callee| *callee < imported),
                "{name}: {body:?}"
            );
            assert_eq!(body.copies, 0, "{name}: no memory.copy");
        } else {
            assert!(body.calls.is_empty(), "{name}: {body:?}");
        }
        let o0_body = &o0_ops[(o0_exports[name] - o0_imported) as usize];
        assert!(!o0_body.calls.is_empty(), "{name}: O0 keeps its call");
        for (tag, bytes) in [("O2", &o2), ("O0", &o0)] {
            if let Some((got, library_calls)) = run(bytes, name) {
                assert_eq!(got, want, "{tag}: {name} disagrees with the interpreter");
                if tag == "O2" && (name == "eq3" || name == "copyrt") {
                    assert!(library_calls > 0, "{name}: the library call stays");
                } else if tag == "O2" {
                    assert_eq!(library_calls, 0, "{name}: no library call at O2");
                }
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

#[test]
fn legacy_pointer_comparison_stays_refused_and_its_normalizer_is_checked() {
    let mut legacy = program();
    let step = legacy
        .functions
        .iter_mut()
        .find(|f| f.name == "step")
        .unwrap();
    let mut rewritten = 0;
    for block in &mut step.blocks {
        let body = std::mem::take(&mut block.body);
        for mut node in body {
            if let trust_ir::Inst::ICmp { ty, lhs, rhs, .. } = &mut node.inst {
                assert_eq!(*ty, Ty::Ptr);
                *ty = Ty::PtrConst(Box::new(Ty::U32));
                // Respell's existing type table reads explicit copies, not
                // extractfield results. Preserve both pointer values while
                // putting the legacy comparison in its admitted input form.
                for (operand, result) in [(1, 15), (2, 16)] {
                    block.body.push(
                        trust_ir::InstrNode::new(trust_ir::Inst::Copy {
                            ty: ty.clone(),
                            operand: trust_ir::ValueId::new(operand),
                        })
                        .with_result(trust_ir::ValueId::new(result)),
                    );
                }
                *lhs = trust_ir::ValueId::new(15);
                *rhs = trust_ir::ValueId::new(16);
                rewritten += 1;
            }
            block.body.push(node);
        }
    }
    assert_eq!(rewritten, 1);
    let error = wasm::compile_object_with_license(&legacy, &permit_unlicensed())
        .expect_err("a typed-pointer comparison remains invalid at ingestion");
    assert!(
        format!("{error:?}").contains("ICmpRequiresIntegerOrPtr"),
        "{error}"
    );
    let (normalized, report) = trust_cg_irmid::optimize_module(
        &legacy,
        &trust_cg_irmid::MidConfig {
            never_inline: [NEVER_INLINE.to_owned()].into_iter().collect(),
            ..trust_cg_irmid::MidConfig::wasm32()
        },
    );
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(changed_report(&report, "respell") >= 1, "{report:#?}");
    assert!(trust_ir_build::validate_module(&normalized).is_empty());
}

fn changed_report(report: &trust_cg_irmid::IrmidReport, name: &str) -> usize {
    report
        .passes
        .iter()
        .filter(|p| p.name == name)
        .map(|p| p.functions_changed)
        .sum()
}
