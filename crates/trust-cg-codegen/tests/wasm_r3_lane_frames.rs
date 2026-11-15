// trust-cg-codegen/tests/wasm_r3_lane_frames.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Frame bounds of the wasm lane:
//!
//! * explicit typed field extraction, bitcasts and stores preserve the two
//!   8-byte lanes of an incoming by-value `(f64, f64)` aggregate, so a
//!   `repr(C) {f32, f64}` passed
//!   indirectly and returned through `sret` stays inside the frames that own
//!   it — checked by execution in modules whose memory ENDS at the initial
//!   stack pointer (a closed module; a `wasm-ld --stack-first` link with no
//!   data), where any byte at or above it traps, from the very first call;
//! * a lane access whose declared type moves a different number of bytes than
//!   the lane holds is refused by name instead of reading or writing past it;
//! * the frame-bounds guard (`wasm::frame_bounds`) refuses a body with a
//!   constant-offset access definitely outside its frame — including this
//!   lane's earlier lowering of the reinterpreting function — accepts every
//!   function this lane emits here, and lets through a path-correlated pointer
//!   join only partly outside the frame (which runs and agrees with the
//!   interpreter).
//!
//! The ABI functions retain the independent exact-value oracle
//! (`extern "C" fn fl(p: Fl, k: f32) -> Fl` computed in Rust); the
//! path-correlated join is checked against the interpreter. Malformed
//! pointer-overloaded field operations remain strict refusal controls.
//! Node is required to execute the wasm; its absence is a loud SKIP.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::wasm;
use trust_cg_codegen::wasm::frame_bounds::{self, FrameShape};
use trust_ir::{
    InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty, parser,
};

/// A typed wasm32 fixture for the bridge ABI of
///
/// ```text
/// #[repr(C)] struct Fl { x: f32, y: f64 }
/// extern "C" fn fl(p: Fl, k: f32) -> Fl { Fl { x: p.x * k, y: p.y - k as f64 } }
/// extern "C" fn cabi_float(a: f64, b: f32) -> f64 {
///     let r = fl(Fl { x: b, y: a }, 2.0); r.x as f64 + r.y
/// }
/// ```
///
/// (`fl` takes its `sret` pointer and a by-value `(f64, f64)` tuple,
/// explicitly bitcasts its two fields and stores them in `[i64 x 2]` lanes.) Before the lane-width fix, `cabi_float(0, 0)` trapped
/// on the first call of a fresh instance. The target line carries the
/// bridge's own aggregate-passing claim (`NativeC`, the default spelling): the
/// lane refuses an `unclassified` module that passes `(f64, f64)` by value.
const CABI: &str = r#"; TrustIr text format v1
module "r3"
target "wasm32-unknown-unknown" 4 little

functy.0 = (ptr, (f64, f64), f32) -> ()

functy.1 = (f64, f32) -> (f64)

type ty.0 = i64

fn @fl(functy.0) {
    ; #param_attrs 0: nonnull noalias sret
bb0(%8: ptr, %1: (f64, f64), %2: f32):
    %9 = alloca [ty.0 x 2], align 8
    %10 = alloca [ty.0 x 2], align 8
    %52 = extractfield f64 %1, 0
    %11 = bitcast f64 %52 to i64
    store i64 %11, ptr %10
    %53 = extractfield f64 %1, 1
    %13 = bitcast f64 %53 to i64
    %54 = const i32 8
    %55 = gep inbounds u8, ptr %10, %54
    store i64 %13, ptr %55
    %15 = load f32, ptr %10
    %16 = fmul f32 %15, %2
    %18 = const i32 8
    %20 = ptrtoint ptr %10 to i32
    %22 = add i32 %20, %18
    %23 = inttoptr i32 %22 to ptr
    %17 = load f64, ptr %23
    %24 = fpext f32 %2 to f64
    %25 = fsub f64 %17, %24
    store f32 %16, ptr %9
    %28 = ptrtoint ptr %9 to i32
    %30 = add i32 %28, %18
    %31 = inttoptr i32 %30 to ptr
    store f64 %25, ptr %31
    %38 = load i64, ptr %9
    store i64 %38, ptr %8
    %51 = load i64, ptr %31
    %41 = ptrtoint ptr %8 to i32
    %43 = add i32 %41, %18
    %44 = inttoptr i32 %43 to ptr
    store i64 %51, ptr %44
    ret
}

fn @cabi_float(functy.1) {
bb0(%1: f64, %2: f32):
    %8 = alloca [ty.0 x 2], align 8
    %9 = alloca [ty.0 x 2], align 8
    store f32 %2, ptr %9
    %10 = const i32 8
    %12 = ptrtoint ptr %9 to i32
    %14 = add i32 %12, %10
    %15 = inttoptr i32 %14 to ptr
    store f64 %1, ptr %15
    %16 = alloca [ty.0 x 2], align 8
    %23 = load i64, ptr %9
    store i64 %23, ptr %16
    %31 = load i64, ptr %15
    %55 = gep inbounds u8, ptr %16, %10
    store i64 %31, ptr %55
    %56 = load (f64, f64), ptr %16
    %33 = const f32 2.0
    call @func.0(%8, %56, %33)
    br bb1
bb1:
    %34 = load f32, ptr %8
    %35 = fpext f32 %34 to f64
    %38 = ptrtoint ptr %8 to i32
    %41 = add i32 %38, %10
    %42 = inttoptr i32 %41 to ptr
    %36 = load f64, ptr %42
    %43 = fadd f64 %35, %36
    ret %43
}

"#;

/// The two lanes `fl`'s entry copy reads, observed through typed extraction
/// and explicit bitcasts: lane `i` contains the bits of tuple element `i`.
const VIEW: &str = r#"; TrustIr text format v1
module "r3v"
target "wasm32-unknown-unknown" 4 little

functy.0 = (f64, f64) -> (i64)

type ty.0 = i64

fn @fl_view(functy.0) {
bb0(%1: f64, %2: f64):
    %3 = make_aggregate (f64, f64) (%1, %2)
    %9 = extractfield f64 %3, 0
    %4 = bitcast f64 %9 to i64
    %10 = extractfield f64 %3, 1
    %5 = bitcast f64 %10 to i64
    %6 = const i64 3
    %7 = mul i64 %5, %6
    %8 = xor i64 %4, %7
    ret %8
}
"#;

fn parse(text: &str) -> Module {
    parser::parse_module(text).unwrap_or_else(|e| panic!("test module failed to parse: {e}"))
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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_r3f_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn validate(bytes: &[u8]) {
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
}

/// Link a relocatable object as the rustc bridge's objects are linked
/// (`--stack-first`, every definition exported). `None` without a linker.
fn link(object: &[u8]) -> Option<Vec<u8>> {
    let ld = wasm_ld()?;
    let dir = scratch("link");
    std::fs::write(dir.join("m.o"), object).unwrap();
    let out = Command::new(&ld)
        .args(["--no-entry", "--export-dynamic", "--stack-first", "-o"])
        .arg(dir.join("m.wasm"))
        .arg(dir.join("m.o"))
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

/// The module's memory ends exactly at its initial stack pointer and holds
/// no data: every byte at or above the stack pointer is out of bounds, so an
/// access above a frame's allocation traps instead of landing in slack.
fn assert_memory_ends_at_initial_sp(bytes: &[u8]) {
    let mut memory_min = None;
    let mut sp = None;
    let mut data = 0usize;
    let mut imported_globals = 0u32;
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        match payload.expect("parse") {
            wasmparser::Payload::ImportSection(r) => {
                for imp in r {
                    if matches!(imp.expect("import").ty, wasmparser::TypeRef::Global(_)) {
                        imported_globals += 1;
                    }
                }
            }
            wasmparser::Payload::MemorySection(r) => {
                for m in r {
                    memory_min = Some(m.expect("memory").initial);
                }
            }
            wasmparser::Payload::GlobalSection(r) => {
                assert_eq!(imported_globals, 0, "a runnable module imports no global");
                if let Some(g) = r.into_iter().next() {
                    let g = g.expect("global");
                    let mut ops = g.init_expr.get_operators_reader();
                    if let Ok(wasmparser::Operator::I32Const { value }) = ops.read() {
                        sp = Some(value as u32);
                    }
                }
            }
            wasmparser::Payload::DataSection(r) => data += r.count() as usize,
            _ => {}
        }
    }
    let memory_min = memory_min.expect("a defined memory");
    let sp = sp.expect("a stack-pointer global initialized by a constant");
    assert_eq!(data, 0, "the module carries data above or below the stack");
    assert_eq!(
        u64::from(sp),
        memory_min * 65_536,
        "the initial stack pointer {sp} is not the end of memory ({memory_min} pages)"
    );
}

/// Run `(f64, f32) -> f64` export `name` over `inputs` in ONE fresh instance,
/// in order, so the first call sees the pristine stack. Results are f64 bit
/// patterns (`None` is a trap); `None` for the whole column without node.
fn run_f64_f32(bytes: &[u8], name: &str, inputs: &[(f64, f32)]) -> Option<Vec<Option<u64>>> {
    let node = node()?;
    let dir = scratch("run");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let js = "const fs = require('fs');\n\
              const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
              const inst = new WebAssembly.Instance(m, {});\n\
              const f = inst.exports[process.argv[3]];\n\
              const inputs = JSON.parse(fs.readFileSync(process.argv[4]));\n\
              const dv = new DataView(new ArrayBuffer(8));\n\
              const out = inputs.map(([a, b]) => { try { dv.setFloat64(0, f(a, b)); \
              return dv.getBigUint64(0).toString(); } \
              catch (e) { if (e instanceof WebAssembly.RuntimeError) return null; throw e; } });\n\
              process.stdout.write(JSON.stringify(out));\n";
    std::fs::write(dir.join("run.js"), js).unwrap();
    let json: Vec<String> = inputs
        .iter()
        .map(|(a, b)| format!("[{a:?},{b:?}]"))
        .collect();
    std::fs::write(dir.join("inputs.json"), format!("[{}]", json.join(","))).unwrap();
    let run = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .arg(name)
        .arg(dir.join("inputs.json"))
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
            .map(|v| v.map(|s| s.parse::<u64>().unwrap()))
            .collect(),
    )
}

/// `rustc`'s `cabi_float`: `fl(Fl { x: b, y: a }, 2.0)`, then `r.x as f64 + r.y`.
fn cabi_float(a: f64, b: f32) -> f64 {
    let x = b * 2.0;
    let y = a - f64::from(2.0f32);
    f64::from(x) + y
}

fn cabi_inputs() -> Vec<(f64, f32)> {
    // (0, 0) first: before the fix it trapped on exactly the first call.
    let fs: [f64; 7] = [0.0, 1.5, -2.25, 1e10, -0.0, 3.0e-3, 65_504.0];
    let gs: [f32; 6] = [0.0, 2.5, -1.0, 1.0e-3, 7.0, -0.0];
    fs.iter()
        .flat_map(|&a| gs.iter().map(move |&b| (a, b)))
        .collect()
}

/// Both runnable forms of `module`: the closed module and (with a linker) the
/// relocatable object linked `--stack-first`, each validated and each with
/// memory ending at its initial stack pointer.
fn runnable_forms(module: &Module) -> Vec<(&'static str, Vec<u8>)> {
    let closed = wasm::compile_module_with_license(module, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile_module: {e}"));
    validate(&closed);
    assert_memory_ends_at_initial_sp(&closed);
    let mut forms = vec![("closed", closed)];
    let object = wasm::compile_object_with_license(module, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile_object: {e}"));
    match link(&object) {
        Some(linked) => {
            validate(&linked);
            assert_memory_ends_at_initial_sp(&linked);
            forms.push(("object", linked));
        }
        None => eprintln!("SKIP object form: no wasm-ld (set WASM_LD)"),
    }
    forms
}

#[test]
fn indirect_repr_c_float_struct_stays_in_its_frames_from_the_first_call() {
    let module = parse(CABI);
    let inputs = cabi_inputs();
    let mut checks = 0;
    for (tag, bytes) in runnable_forms(&module) {
        let Some(got) = run_f64_f32(&bytes, "cabi_float", &inputs) else {
            eprintln!("SKIP cabi_float [{tag}]: node not on PATH");
            continue;
        };
        for (i, &(a, b)) in inputs.iter().enumerate() {
            let want = cabi_float(a, b).to_bits();
            assert_eq!(
                got[i],
                Some(want),
                "cabi_float({a:?}, {b:?}) [{tag}], call #{i} in one instance: want {:?}, \
                 wasm {:?}",
                f64::from_bits(want),
                got[i].map(f64::from_bits)
            );
            checks += 1;
        }
    }
    eprintln!("cabi_float: {checks} checks");
}

/// The reinterpreting extraction is typed as the DECLARED aggregate's lane
/// (an `i64`), not as the declared aggregate, and reads that lane's bits.
#[test]
fn reinterpreting_extract_is_the_declared_lane() {
    let module = parse(CABI);
    let fl = module.function_by_name("fl").expect("fl");
    let types = wasm::value_types(&module, fl).expect("typing");
    for v in [11u32, 13] {
        let id = trust_ir::ValueId::new(v);
        assert_eq!(types.get(&id), Some(&Ty::I64), "%{v} is the i64 lane");
    }
    let module = parse(VIEW);
    let view = module.function_by_name("fl_view").expect("fl_view");
    let types = wasm::value_types(&module, view).expect("typing");
    assert_eq!(types.get(&trust_ir::ValueId::new(4)), Some(&Ty::I64));
    // The lanes carry the argument's exact bits.
    let pairs: [(f64, f64); 4] = [(1.5, -2.0), (0.0, -0.0), (f64::MAX, 1e-300), (-7.25, 3.0)];
    let closed = wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compile");
    let Some(node) = node() else {
        eprintln!("SKIP fl_view: node not on PATH");
        return;
    };
    let dir = scratch("view");
    std::fs::write(dir.join("m.wasm"), &closed).unwrap();
    let js = "const fs = require('fs');\n\
              const inst = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[2])), {});\n\
              const pairs = JSON.parse(process.argv[3]);\n\
              process.stdout.write(JSON.stringify(pairs.map(([a, b]) => \
              BigInt.asUintN(64, inst.exports.fl_view(a, b)).toString())));\n";
    std::fs::write(dir.join("run.js"), js).unwrap();
    let arg: Vec<String> = pairs
        .iter()
        .map(|(a, b)| format!("[{a:?},{b:?}]"))
        .collect();
    let out = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .arg(format!("[{}]", arg.join(",")))
        .output()
        .expect("node");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let got: Vec<String> = serde_json::from_slice(&out.stdout).expect("json");
    for (i, (a, b)) in pairs.iter().enumerate() {
        let want = a.to_bits() ^ b.to_bits().wrapping_mul(3);
        assert_eq!(got[i], want.to_string(), "fl_view({a:?}, {b:?})");
    }
}

/// A lane whose declared type moves a different number of bytes than the
/// lane holds is refused by name — never read or written past the lane.
#[test]
fn a_lane_access_of_the_wrong_size_is_refused() {
    // Declared [i64 x 3] (24 bytes) over a 16-byte (f64, f64): neither the
    // field type nor a same-size reinterpretation.
    let wide_extract = r#"
functy.0 = ((f64, f64)) -> (i64)
type ty.0 = i64
fn @f(functy.0) {
bb0(%1: (f64, f64)):
    %2 = alloca [ty.0 x 3], align 8
    %3 = extractfield [ty.0 x 3] %1, 1
    %4 = insertfield [ty.0 x 3] %2, 0, %3
    %5 = load i64, ptr %2
    ret %5
}
"#;
    // A 16-byte value written through a pointer into an 8-byte lane.
    let wide_insert = r#"
functy.0 = (f64, f64) -> (i64)
type ty.0 = i64
fn @f(functy.0) {
bb0(%1: f64, %2: f64):
    %3 = make_aggregate (f64, f64) (%1, %2)
    %4 = alloca [ty.0 x 2], align 8
    %5 = insertfield [ty.0 x 2] %4, 1, %3
    %6 = load i64, ptr %4
    ret %6
}
"#;
    // A 24-byte aggregate built from a 16-byte one: the copy of the source
    // image would read 8 bytes past it.
    let short_source = r#"
functy.0 = (f64, f64) -> (i64)
type ty.0 = i64
fn @f(functy.0) {
bb0(%1: f64, %2: f64):
    %3 = make_aggregate (f64, f64) (%1, %2)
    %4 = const i64 7
    %5 = insertfield [ty.0 x 3] %3, 2, %4
    %6 = extractfield i64 %5, 2
    ret %6
}
"#;
    // A 16-byte value stored as one 8-byte array element.
    let wide_element = r#"
functy.0 = (f64, f64, i32) -> (i64)
type ty.0 = i64
fn @f(functy.0) {
bb0(%1: f64, %2: f64, %3: i32):
    %4 = make_aggregate (f64, f64) (%1, %2)
    %5 = const i64 0
    %6 = array_splat [ty.0 x 2] %5
    %7 = insertelement [ty.0 x 2] %6, %3, %4
    %8 = extractfield i64 %7, 0
    ret %8
}
"#;
    for (text, needle) in [
        (wide_extract, "OperandTypeMismatch"),
        (wide_insert, "OperandTypeMismatch"),
        (short_source, "OperandTypeMismatch"),
        (wide_element, "InvalidVectorElementOp"),
    ] {
        let module = parse(&format!(
            "; TrustIr text format v1\nmodule \"r3\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n{text}"
        ));
        for (form, result) in [
            (
                "closed",
                wasm::compile_module_with_license(&module, &permit_unlicensed()),
            ),
            (
                "object",
                wasm::compile_object_with_license(&module, &permit_unlicensed()),
            ),
        ] {
            let err = result.expect_err("an over-wide lane access must be refused");
            let msg = err.to_string();
            assert!(
                format!("{err:?}").contains(needle),
                "[{form}] refused for another reason: {msg}"
            );
        }
    }
}

// ---- The frame-bounds guard ----

/// Frame size and base local of a body whose prologue is
/// `global.get; local.set s; local.get s; i32.const F; i32.sub;
/// [i32.const -a; i32.and;] local.tee b`, or the same with its `local.set s;
/// local.get s` merged into `local.tee s` by the emission pass.
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
        ] => (*value as u32, rest),
        _ => return None,
    };
    let base_local = match rest {
        [O::LocalTee { local_index }, ..] => *local_index,
        [
            O::I32Const { .. },
            O::I32And,
            O::LocalTee { local_index },
            ..,
        ] => *local_index,
        _ => return None,
    };
    Some(FrameShape { size, base_local })
}

/// Every framed function of the CLOSED module `bytes` (locals not
/// coalesced below the coalescing threshold): its frame, parameter count,
/// declared local count and instruction bytes.
fn framed_bodies(bytes: &[u8]) -> Vec<(FrameShape, u32, usize, Vec<u8>)> {
    let mut types: Vec<u32> = Vec::new();
    let mut funcs: Vec<u32> = Vec::new();
    let mut out = Vec::new();
    let mut next = 0usize;
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        match payload.expect("parse") {
            wasmparser::Payload::TypeSection(r) => {
                for group in r {
                    for ty in group.expect("type").into_types() {
                        match ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(f) => {
                                types.push(f.params().len() as u32)
                            }
                            _ => types.push(0),
                        }
                    }
                }
            }
            wasmparser::Payload::FunctionSection(r) => {
                for f in r {
                    funcs.push(f.expect("func"));
                }
            }
            wasmparser::Payload::CodeSectionEntry(body) => {
                let params = types[funcs[next] as usize];
                next += 1;
                let mut locals = 0usize;
                for l in body.get_locals_reader().expect("locals") {
                    locals += l.expect("local").0 as usize;
                }
                let reader = body.get_operators_reader().expect("ops");
                let start = reader.original_position();
                let ops: Vec<wasmparser::Operator<'_>> = body
                    .get_operators_reader()
                    .expect("ops")
                    .into_iter()
                    .take(10)
                    .map(|o| o.expect("op"))
                    .collect();
                if let Some(frame) = prologue_frame(&ops) {
                    let end = body.range().end;
                    out.push((frame, params, locals, bytes[start..end].to_vec()));
                }
            }
            _ => {}
        }
    }
    out
}

/// This lane's EARLIER lowering of `fl` (captured from the closed module of
/// [`CABI`]'s bridge original before the lane-width fix): its entry copy
/// wrote the second 8-byte lane as a 16-byte `memory.copy` to frame bytes
/// `[24, 40)` of a 32-byte frame — 8 bytes into its caller's frame — and read
/// 8 bytes past the caller's 16-byte argument. 3 parameters, 51 declared
/// locals, frame base local 53.
const OLD_FL_BODY: &str = "23002134203441206b22352400203541006a2103203541106a210420012105200420\
054110fc0a000020042106200141086a2107200441086a20074110fc0a00002004210820042a020021092009200294\
210a4108210b2004210c200c210d200b210e200d200e6a210f200f211020102b030021112002bb211220112012a121\
132003200a38020041082114200321152015211620142117201620176a211820182119201920133903004100211a20\
03211b201b211c201a211d201c201d6a211e201e211f201f290300212041002121200021222022212320212124202320\
246a212520252126202620203703004108212720032128202821292027212a2029202a6a212b202b212c202c29030021\
2d4108212e2000212f202f2130202e2131203020316a2132203221332033202d370300203424000f000b";

/// A pointer block parameter that receives a 32-byte slot on one edge and an
/// 8-byte slot on the other, dereferenced at offset 24 only on the path where
/// it is the 32-byte slot (the shape of a Rust `if big { &mut a } else {
/// small.cast() }` at `-O2`). Well defined; the guard's flow-insensitive join
/// gives the parameter both offsets, and only one of them is outside the frame
/// at `+24`.
const PATH_CORRELATED: &str = r#"; TrustIr text format v1
module "m"
target "wasm32-unknown-unknown" 4 little

type ty.0 = i64

functy.0 = (i32) -> (i64)

fn @f(functy.0) {
bb0(%1: i32):
    %2 = alloca [ty.0 x 4], align 8
    %3 = alloca i64, align 8
    %4 = const i64 0
    store i64 %4, ptr %3
    %5 = const i32 1
    %6 = icmp eq i32 %1, %5
    condbr %6, bb1, bb2
bb1:
    %7 = const i32 1
    br bb3(%2, %7)
bb2:
    %8 = const i32 0
    br bb3(%3, %8)
bb3(%9: ptr, %10: i32):
    %11 = const i32 0
    %12 = icmp ne i32 %10, %11
    condbr %12, bb4, bb5
bb4:
    %13 = ptrtoint ptr %9 to i32
    %14 = const i32 24
    %15 = add i32 %13, %14
    %16 = inttoptr i32 %15 to ptr
    %17 = const i64 99
    store i64 %17, ptr %16
    %18 = load i64, ptr %16
    ret %18
bb5:
    %19 = load i64, ptr %9
    ret %19
}
"#;

/// The interpreter's answer for `(i32) -> i64` function `name`.
fn interpret_i32(module: &Module, name: &str, a: i32) -> Option<i64> {
    let f = module.function_by_name(name).expect("function");
    let arg = InterpretValue::int(Ty::I32, i128::from(a)).expect("i32 value");
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 1_000_000,
            max_call_depth: 64,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, vec![arg])
        .ok()?;
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => Some(i.as_signed() as i64),
        other => panic!("{name} returned {other:?}"),
    }
}

/// Run `(i32) -> i64` export `name` over `inputs` in ONE fresh instance, in
/// order (`None` is a trap); `None` for the whole column without node.
fn run_i32(bytes: &[u8], name: &str, inputs: &[i32]) -> Option<Vec<Option<i64>>> {
    let node = node()?;
    let dir = scratch("run_i32");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let js = "const fs = require('fs');\n\
              const inst = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[2])), {});\n\
              const f = inst.exports[process.argv[3]];\n\
              const out = JSON.parse(process.argv[4]).map((a) => { try { \
              return BigInt.asIntN(64, f(a)).toString(); } \
              catch (e) { if (e instanceof WebAssembly.RuntimeError) return null; throw e; } });\n\
              process.stdout.write(JSON.stringify(out));\n";
    std::fs::write(dir.join("run.js"), js).unwrap();
    let args: Vec<String> = inputs.iter().map(i32::to_string).collect();
    let run = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .arg(name)
        .arg(format!("[{}]", args.join(",")))
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

/// A path-correlated pointer join whose offset set is only PARTLY outside the
/// frame is not a definite violation: the guard lets it through, and the
/// function agrees with the interpreter in memory ending at the initial stack
/// pointer.
#[test]
fn a_path_correlated_pointer_join_compiles_and_agrees() {
    let module = parse(PATH_CORRELATED);
    let inputs = [1, 0, 1, 2, -1, 1, 7];
    let want: Vec<Option<i64>> = inputs
        .iter()
        .map(|&a| interpret_i32(&module, "f", a))
        .collect();
    assert_eq!(want[0], Some(99), "the interpreter runs the big-slot path");
    assert_eq!(want[1], Some(0), "the interpreter runs the small-slot path");
    for (form, bytes) in runnable_forms(&module) {
        let Some(got) = run_i32(&bytes, "f", &inputs) else {
            eprintln!("SKIP path-correlated execution: node not on PATH");
            return;
        };
        assert_eq!(got, want, "[{form}] f disagrees with the interpreter");
    }
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex"))
        .collect()
}

#[test]
fn the_guard_refuses_the_earlier_out_of_frame_lowering() {
    let code = unhex(OLD_FL_BODY);
    let frame = FrameShape {
        size: 32,
        base_local: 53,
    };
    let err = frame_bounds::check(&code, 3, 51, frame, &Default::default())
        .expect_err("the earlier lowering copies past its frame");
    assert!(
        err.contains("memory.copy destination") && err.contains("[24, 40)"),
        "{err}"
    );
    // The same body with the second lane copy narrowed to its 8 bytes (both
    // `i32.const 16` lengths of the entry copies become 8) is inside.
    let mut fixed = code.clone();
    let copy_len = [0x41, 0x10, 0xfc, 0x0a];
    let mut at = 0;
    while let Some(i) = fixed[at..]
        .windows(copy_len.len())
        .position(|w| w == copy_len)
    {
        fixed[at + i + 1] = 0x08;
        at += i + copy_len.len();
    }
    assert_eq!(
        frame_bounds::check(&fixed, 3, 51, frame, &Default::default()),
        Ok(())
    );
}

#[test]
fn the_guard_refuses_a_deliberate_out_of_frame_store() {
    // global.get 0; local.set 0; local.get 0; i32.const 16; i32.sub;
    // local.tee 1; global.set 0; local.get 1; i64.const 0; i64.store offset=16.
    let code = [
        0x23, 0x00, 0x21, 0x00, 0x20, 0x00, 0x41, 0x10, 0x6b, 0x22, 0x01, 0x24, 0x00, 0x20, 0x01,
        0x42, 0x00, 0x37, 0x03, 0x10, 0x0b,
    ];
    let frame = FrameShape {
        size: 16,
        base_local: 1,
    };
    let err = frame_bounds::check(&code, 0, 2, frame, &Default::default()).unwrap_err();
    assert!(err.contains("store") && err.contains("[16, 24)"), "{err}");
    // offset=8 is the frame's last eightbyte.
    let mut inside = code;
    inside[19] = 0x08;
    assert_eq!(
        frame_bounds::check(&inside, 0, 2, frame, &Default::default()),
        Ok(())
    );
}

/// Every framed function the lane emits for [`CABI`] passes the guard when
/// re-run on the final bytes, against the frame size and base local its
/// emitted prologue carves. This re-check runs after local coalescing, where a
/// merged local's offsets widen to unknown, so it is weaker than the guard
/// `lower_function` runs on the uncoalesced body.
#[test]
fn every_lowered_frame_passes_the_guard() {
    let module = parse(CABI);
    // Keep the frames this guard is meant to audit: the O2 mid-end can
    // eliminate their slots and inline `fl` into its caller.
    let (closed, _) = wasm::compile_module_with_evidence_policy_license_options(
        &module,
        &wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
        wasm::WasmOptOptions::at(trust_cg_codegen::pipeline::OptLevel::O0),
    )
    .expect("compile");
    let bodies = framed_bodies(&closed);
    assert!(bodies.len() >= 2, "fl and cabi_float carry frames");
    for (frame, params, locals, code) in bodies {
        frame_bounds::check(&code, params, locals, frame, &Default::default())
            .unwrap_or_else(|e| panic!("a lowered frame fails the guard: {e}"));
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
