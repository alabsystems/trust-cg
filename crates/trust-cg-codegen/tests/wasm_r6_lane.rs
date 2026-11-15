// trust-cg-codegen/tests/wasm_r6_lane.rs - wasm32 lane: link-replaceable callees, exposed addresses, runtime-count allocas, irreducible CFGs, exports
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Regressions for the wasm32 lane, each pinned with the trust-ir input that
//! exposed it and checked against the trust-ir reference interpreter (or an
//! exact value / a named refusal):
//!
//! * an object's `weak`, `weak_odr`, `linkonce` and `linkonce_odr` C
//!   definitions may be replaced at link time by foreign code that writes its
//!   by-address parameter (the C ABI's caller-made copy), so their callers
//!   pass a copy — the caller's value, a forwarded by-address parameter and a
//!   pooled constant all survive a replacement that writes its argument;
//! * an `Alloca` whose address bits escape the data flow (a branch on them, a
//!   table read or write indexed by them, after `ptrtoint` or a bitcast or
//!   transmute to an integer) is never given bytes another allocation
//!   reuses, in straight-line code or across loop iterations;
//! * nor is one whose address decides whether execution continues (an
//!   `assert` or `assume` on it, a division, shift, `GEP`, access or wide
//!   `inttoptr` that is UB or traps for some of its bits), also in a strong
//!   callee — checked by the frame size and by a sweep of the guessed address
//!   over the frame, since the interpreter's panic at its own address counts
//!   as agreement;
//! * an `Alloca` whose element count is known only at run time is carved
//!   from the shadow stack (and traps on a count the interpreter rejects);
//! * an irreducible CFG (a cycle with several entries) lowers as a dispatch
//!   loop that agrees with the interpreter, closed and linked, and passes the
//!   CFG structural invariant;
//! * a closed module leaves a module-local function unexported when another
//!   definition or export uses its name, instead of refusing the module;
//! * a use its definition does not dominate is refused by name;
//! * the new lowerings are deterministic.
//!
//! Node is required to execute the wasm and `wasm-ld` (`WASM_LD`) to link
//! objects; the absence of either is a loud SKIP.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::wasm::{self, WasmLowerError, WasmMemoryPolicy, WasmModulePolicy};
use trust_ir::{
    BlockId, Function, Inst, InterpretOptions, InterpretValue, InterpretValueKind, Interpreter,
    Module, Ty, parser,
};

const HEADER: &str = "module \"r6\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n";

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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_r6_{tag}_{}_{n}", std::process::id()));
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

/// Run export `name` over `calls` (in order, in ONE instance, so state such
/// as a pooled constant persists between calls); `None` is a trap. `None`
/// for the whole column when node is absent.
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

/// Export `name` of `bytes` agrees with the interpreter on every call.
/// Returns the number of checks (0 when node is absent).
fn agrees(module: &Module, bytes: &[u8], name: &str, w: W, calls: &[Vec<i64>]) -> usize {
    validate(bytes);
    let Some(got) = run_wasm(bytes, name, w, calls) else {
        return 0;
    };
    for (args, got) in calls.iter().zip(&got) {
        let want = interpret(module, name, w, args);
        assert_eq!(
            *got, want,
            "{name}{args:?}: wasm {got:?}, interpreter {want:?}"
        );
    }
    calls.len()
}

/// Every pair of `values`.
fn grid(values: &[i64]) -> Vec<Vec<i64>> {
    values
        .iter()
        .flat_map(|&a| values.iter().map(move |&b| vec![a, b]))
        .collect()
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
    6,
    255,
    65536,
    i32::MAX as i64,
];

const I64_VALUES: &[i64] = &[i64::MIN, -1000, -5, -1, 0, 1, 3, 7, 100, i64::MAX];

// ---- 1. Link-replaceable callees get a copy of a by-address argument ----

/// The strong replacement another object provides for `get(P)`: a C
/// definition `int get(P p) { int r = p.a; p.a = 99; return r; }` computes
/// exactly what the trust-ir body does and writes only its OWN by-value copy.
/// At the wasm level that copy is the address it receives, so it is spelled
/// here as a `ptr` parameter (the same wasm type, `(i32) -> i32`).
const STRONG_GET: &str = "functy.0 = (ptr) -> (i32)\n\n\
fn @get(functy.0) {\n\
bb0(%0: ptr):\n\
    %1 = load i32, ptr %0\n\
    %2 = const i32 99\n\
    store i32 %2, ptr %0\n\
    ret %1\n\
}\n";

/// `min.trust_ir` / `min_const.trust_ir` / the forwarded-parameter variant,
/// with `get` given `linkage` (`""` is a declaration of it).
fn weak_caller(linkage: &str) -> Module {
    let get = if linkage == "decl" {
        "fn @get(functy.0) {\n}\n".to_string()
    } else {
        format!(
            "{linkage} fn @get(functy.0) {{\nbb0(%0: struct.0):\n    %1 = extractfield i32 %0, 0\n    ret %1\n}}\n"
        )
    };
    module(&format!(
        "struct @P {{ : i32 @0, : i32 @4 }} size=8 align=4 repr=c id=0\n\n\
         functy.0 = (struct.0) -> (i32)\n\
         functy.1 = (i32) -> (i32)\n\n\
         {get}\n\
         fn @run(functy.1) {{\n\
         bb0(%0: i32):\n\
             %1 = make_aggregate struct.0 (%0, %0)\n\
             %2 = call @func.0(%1)\n\
             %3 = extractfield i32 %1, 0\n\
             ret %3\n\
         }}\n\n\
         fn @konst(functy.1) {{\n\
         bb0(%0: i32):\n\
             %1 = const struct.0 {{ 7, 7 }}\n\
             %2 = call @func.0(%1)\n\
             ret %2\n\
         }}\n\n\
         fn @fwd(functy.0) {{\n\
         bb0(%0: struct.0):\n\
             %1 = call @func.0(%0)\n\
             %2 = extractfield i32 %0, 0\n\
             ret %2\n\
         }}\n\n\
         fn @run_fwd(functy.1) {{\n\
         bb0(%0: i32):\n\
             %1 = make_aggregate struct.0 (%0, %0)\n\
             %2 = call @func.3(%1)\n\
             %3 = extractfield i32 %1, 0\n\
             %4 = add i32 %2, %3\n\
             ret %4\n\
         }}\n"
    ))
}

#[test]
fn a_link_replaceable_callee_never_writes_the_callers_argument() {
    let strong = wasm::compile_object_with_license(&module(STRONG_GET), &permit_unlicensed())
        .expect("strong get");
    let mut ran = 0;
    for linkage in [
        "weak",
        "weak_odr",
        "linkonce",
        "linkonce_odr",
        "internal",
        "decl",
    ] {
        let caller = weak_caller(linkage);
        let object = wasm::compile_object_with_license(&caller, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("{linkage} caller: {e}"));
        let Some(linked) = link(&[&object, &strong]) else {
            return;
        };
        validate(&linked);
        let calls: Vec<Vec<i64>> = [5, -3, 0, 1000].iter().map(|&x| vec![x]).collect();
        let Some(got) = run_wasm(&linked, "run", W::I32, &calls) else {
            return;
        };
        let want: Vec<Option<i64>> = calls.iter().map(|c| Some(c[0])).collect();
        assert_eq!(got, want, "{linkage}: run(x) must read back its own x");
        // A pooled constant must survive every call: `konst` returns field 0
        // of `{7, 7}` on each of them.
        let got = run_wasm(&linked, "konst", W::I32, &[vec![0], vec![0], vec![0]]).unwrap();
        assert_eq!(
            got,
            vec![Some(7); 3],
            "{linkage}: the pooled constant changed"
        );
        // A by-address parameter forwarded to `get` aliases the caller's
        // bytes; the replacement returns x and must leave x in place.
        let got = run_wasm(&linked, "run_fwd", W::I32, &calls).unwrap();
        let want: Vec<Option<i64>> = calls.iter().map(|c| Some(2 * c[0])).collect();
        assert_eq!(got, want, "{linkage}: a forwarded argument was written");
        ran += 1;
    }
    assert_eq!(ran, 6);
    // The closed module (no linker, the body is final) agrees with the
    // interpreter for every linkage.
    for linkage in ["weak", "weak_odr", "linkonce", "linkonce_odr"] {
        let caller = weak_caller(linkage);
        let bytes =
            wasm::compile_module_with_license(&caller, &permit_unlicensed()).expect("closed");
        let calls: Vec<Vec<i64>> = [5, -3].iter().map(|&x| vec![x]).collect();
        agrees(&caller, &bytes, "run", W::I32, &calls);
        agrees(&caller, &bytes, "run_fwd", W::I32, &calls);
    }
}

// ---- 2. An exposed address is a capture ----

/// `min_share.trust_ir`: A's address is rebuilt bit by bit through control
/// flow, B is allocated after the last data-flow use of A, and the load
/// through the rebuilt pointer must still read A.
const LAUNDER_SHARE: &str = r#"functy.0 = (i32, i32) -> (i32)

fn @launder_share(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = alloca i32
    store i32 %0, ptr %2
    %3 = ptrtoint ptr %2 to usize
    %4 = const usize 0
    br bb1(%4, %4)
bb1(%5: usize, %6: usize):
    %7 = const usize 32
    %8 = icmp ult usize %5, %7
    condbr %8, bb2, bb3
bb2:
    %9 = const usize 1
    %10 = shl usize %9, %5
    %11 = and usize %3, %10
    %12 = icmp ne usize %11, %4
    %13 = add usize %5, %9
    %14 = or usize %6, %10
    condbr %12, bb1(%13, %14), bb1(%13, %6)
bb3:
    %15 = inttoptr usize %6 to ptr
    %16 = alloca i32
    store i32 %1, ptr %16
    %17 = load i32, ptr %15
    ret %17
}
"#;

/// `min_loop.trust_ir`: the iteration-0 allocation's address leaves the
/// loop as a laundered integer in a header parameter.
const LOOP_REUSE: &str = r#"functy.0 = (i32, i32) -> (i32)
functy.1 = (usize) -> (usize)

internal fn @launder(functy.1) {
bb0(%0: usize):
    %1 = const usize 0
    br bb1(%1, %1)
bb1(%2: usize, %3: usize):
    %4 = const usize 32
    %5 = icmp ult usize %2, %4
    condbr %5, bb2, bb3
bb2:
    %6 = const usize 1
    %7 = shl usize %6, %2
    %8 = and usize %0, %7
    %9 = icmp ne usize %8, %1
    %10 = add usize %2, %6
    %11 = or usize %3, %7
    condbr %9, bb1(%10, %11), bb1(%10, %3)
bb3:
    ret %3
}

fn @loop_reuse(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = const usize 0
    br bb1(%0, %2)
bb1(%3: i32, %4: usize):
    %5 = alloca i32
    store i32 %3, ptr %5
    %6 = icmp eq usize %4, %2
    condbr %6, bb2, bb3
bb2:
    %7 = ptrtoint ptr %5 to usize
    %8 = call @func.0(%7)
    br bb1(%1, %8)
bb3:
    %9 = inttoptr usize %4 to ptr
    %10 = load i32, ptr %9
    ret %10
}
"#;

/// `probe_table.trust_ir`: a branch-free rebuild — each address byte is
/// looked up in an identity table, so no value is data-derived from it.
const LAUNDER_TABLE: &str = r#"type ty.0 = u8

functy.0 = (i32, i32) -> (i32)

fn @launder_table(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = alloca i32
    store i32 %0, ptr %2
    %3 = ptrtoint ptr %2 to usize
    %4 = alloca [ty.0 x 256]
    %5 = const usize 0
    br bb1(%5)
bb1(%6: usize):
    %7 = const usize 256
    %8 = icmp ult usize %6, %7
    condbr %8, bb2, bb3
bb2:
    %9 = gep u8, ptr %4, %6
    %10 = trunc usize %6 to u8
    store u8 %10, ptr %9
    %11 = const usize 1
    %12 = add usize %6, %11
    br bb1(%12)
bb3:
    %13 = const usize 255
    %14 = const usize 8
    %20 = and usize %3, %13
    %21 = gep u8, ptr %4, %20
    %22 = load u8, ptr %21
    %23 = zext u8 %22 to usize
    %30 = lshr usize %3, %14
    %31 = and usize %30, %13
    %32 = gep u8, ptr %4, %31
    %33 = load u8, ptr %32
    %34 = zext u8 %33 to usize
    %35 = shl usize %34, %14
    %40 = lshr usize %30, %14
    %41 = and usize %40, %13
    %42 = gep u8, ptr %4, %41
    %43 = load u8, ptr %42
    %44 = zext u8 %43 to usize
    %45 = shl usize %44, %14
    %46 = shl usize %45, %14
    %50 = lshr usize %40, %14
    %51 = and usize %50, %13
    %52 = gep u8, ptr %4, %51
    %53 = load u8, ptr %52
    %54 = zext u8 %53 to usize
    %55 = shl usize %54, %14
    %56 = shl usize %55, %14
    %57 = shl usize %56, %14
    %60 = or usize %23, %35
    %61 = or usize %60, %46
    %62 = or usize %61, %57
    %63 = inttoptr usize %62 to ptr
    %64 = alloca i32
    store i32 %1, ptr %64
    %65 = load i32, ptr %63
    ret %65
}
"#;

/// A write-based rebuild: each address byte marks a slot of a table (a
/// store through a pointer indexed by the address's bits), and a scan of the
/// table that branches only on loaded bytes rebuilds the address.
const LAUNDER_SCAN: &str = r#"type ty.0 = u8

functy.0 = (i32, i32) -> (i32)

fn @launder_scan(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = alloca i32
    store i32 %0, ptr %2
    %3 = alloca [ty.0 x 1024]
    %4 = const usize 0
    %5 = const usize 1
    %6 = const usize 1024
    %7 = const u8 0
    %8 = const u8 1
    br bb1(%4)
bb1(%9: usize):
    %10 = icmp ult usize %9, %6
    condbr %10, bb2, bb3
bb2:
    %11 = gep u8, ptr %3, %9
    store u8 %7, ptr %11
    %12 = add usize %9, %5
    br bb1(%12)
bb3:
    %13 = ptrtoint ptr %2 to usize
    %14 = const usize 255
    %15 = const usize 8
    %16 = const usize 256
    %20 = and usize %13, %14
    %21 = gep u8, ptr %3, %20
    store u8 %8, ptr %21
    %22 = lshr usize %13, %15
    %23 = and usize %22, %14
    %24 = add usize %23, %16
    %25 = gep u8, ptr %3, %24
    store u8 %8, ptr %25
    %26 = lshr usize %22, %15
    %27 = and usize %26, %14
    %28 = add usize %27, %16
    %29 = add usize %28, %16
    %30 = gep u8, ptr %3, %29
    store u8 %8, ptr %30
    %31 = lshr usize %26, %15
    %32 = and usize %31, %14
    %33 = add usize %32, %16
    %34 = add usize %33, %16
    %35 = add usize %34, %16
    %36 = gep u8, ptr %3, %35
    store u8 %8, ptr %36
    br bb4(%4, %4)
bb4(%40: usize, %41: usize):
    %42 = icmp ult usize %40, %6
    condbr %42, bb5, bb7
bb5:
    %43 = gep u8, ptr %3, %40
    %44 = load u8, ptr %43
    %45 = icmp eq u8 %44, %8
    %46 = add usize %40, %5
    condbr %45, bb6, bb4(%46, %41)
bb6:
    %47 = and usize %40, %14
    %48 = lshr usize %40, %15
    %49 = const usize 3
    %50 = shl usize %48, %49
    %51 = shl usize %47, %50
    %52 = or usize %41, %51
    br bb4(%46, %52)
bb7:
    %53 = inttoptr usize %41 to ptr
    %54 = alloca i32
    store i32 %1, ptr %54
    %55 = load i32, ptr %53
    ret %55
}
"#;

/// [`LAUNDER_SHARE`] with the address exposed by `transmute ptr -> u32`
/// (`probe_transmute.trust_ir`) or `bitcast`-free `ptrtoint` to `u32`.
fn launder_via(expose: &str) -> String {
    LAUNDER_SHARE
        .replace("launder_share", "launder_via")
        .replace("    %3 = ptrtoint ptr %2 to usize\n", expose)
}

/// `probe_addr_eq.trust_ir`: whether A's rebuilt address equals live B's —
/// it never does, since trust-ir allocations are disjoint while both live.
const ADDR_EQ: &str = r#"functy.0 = (i32, i32) -> (i32)

fn @addr_eq(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = alloca i32
    store i32 %0, ptr %2
    %3 = ptrtoint ptr %2 to usize
    %4 = const usize 0
    br bb1(%4, %4)
bb1(%5: usize, %6: usize):
    %7 = const usize 32
    %8 = icmp ult usize %5, %7
    condbr %8, bb2, bb3
bb2:
    %9 = const usize 1
    %10 = shl usize %9, %5
    %11 = and usize %3, %10
    %12 = icmp ne usize %11, %4
    %13 = add usize %5, %9
    %14 = or usize %6, %10
    condbr %12, bb1(%13, %14), bb1(%13, %6)
bb3:
    %16 = alloca i32
    store i32 %1, ptr %16
    %17 = ptrtoint ptr %16 to usize
    %18 = icmp eq usize %6, %17
    %19 = zext bool %18 to i32
    ret %19
}
"#;

#[test]
fn an_exposed_address_keeps_its_allocation() {
    let calls = grid(I32_VALUES);
    let mut checks = 0;
    let transmute =
        launder_via("    %30 = transmute ptr %2 to u32\n    %3 = bitcast u32 %30 to usize\n");
    let narrow = launder_via("    %30 = ptrtoint ptr %2 to u32\n    %3 = zext u32 %30 to usize\n");
    for (text, name) in [
        (LAUNDER_SHARE, "launder_share"),
        (LOOP_REUSE, "loop_reuse"),
        (LAUNDER_TABLE, "launder_table"),
        (LAUNDER_SCAN, "launder_scan"),
        (ADDR_EQ, "addr_eq"),
        (transmute.as_str(), "launder_via"),
        (narrow.as_str(), "launder_via"),
    ] {
        let m = module(text);
        let closed = wasm::compile_module_with_license(&m, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        checks += agrees(&m, &closed, name, W::I32, &calls);
        if let Some(linked) =
            link(&[&wasm::compile_object_with_license(&m, &permit_unlicensed()).expect("object")])
        {
            checks += agrees(&m, &linked, name, W::I32, &calls);
        }
    }
    if node().is_some() {
        assert!(checks > 0);
    }
}

// ---- 2b. A check that only some address bits pass is a capture ----
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

/// A probe: `A` (4 KiB) holds 7 and its address is compared against the
/// input `k` by `check`; `B` (4 KiB) is allocated after the last use of A's
/// address and holds `v`; the result is the word at address `k`. When `check`
/// lets execution continue only if `k` is A's address, the only defined
/// result is 7, so A must keep its bytes: `B` may not share them. `check`
/// reads `%4` (A's address as `usize`) and `%5` (`k` as `usize`). `@check`
/// (`func.0`) is a strong callee; `@addr_of` returns the address of a 4 KiB
/// array at the top of a frame, which locates the sweep.
fn bits_probe(check: &str, callee: &str) -> Module {
    module(&format!(
        "type ty.0 = i32\n\n\
         functy.0 = (i32, i32) -> (i32)\n\
         functy.1 = (usize, usize) -> ()\n\n\
         fn @check(functy.1) {{\n\
         bb0(%0: usize, %1: usize):\n\
         {callee}\
             ret\n\
         }}\n\n\
         fn @probe(functy.0) {{\n\
         bb0(%0: i32, %1: i32):\n\
             %2 = alloca [ty.0 x 1024]\n\
             %3 = const i32 7\n\
             store i32 %3, ptr %2\n\
             %4 = ptrtoint ptr %2 to usize\n\
             %5 = zext i32 %0 to usize\n\
         {check}\
             %7 = alloca [ty.0 x 1024]\n\
             store i32 %1, ptr %7\n\
             %8 = inttoptr usize %5 to ptr\n\
             %9 = load i32, ptr %8\n\
             ret %9\n\
         }}\n\n\
         fn @addr_of(functy.0) {{\n\
         bb0(%0: i32, %1: i32):\n\
             %2 = alloca [ty.0 x 1024]\n\
             %3 = const i32 7\n\
             store i32 %3, ptr %2\n\
             %4 = ptrtoint ptr %2 to usize\n\
             %5 = trunc usize %4 to i32\n\
             ret %5\n\
         }}\n"
    ))
}

/// The frame size the prologue of export `name` of a closed module reserves.
fn frame_size(bytes: &[u8], name: &str) -> i32 {
    let mut index = None;
    let mut bodies = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        match payload.expect("parse") {
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
    let body = &bodies[index.unwrap_or_else(|| panic!("no export {name}")) as usize];
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
        other => panic!("{name}: no frame prologue: {other:?}"),
    }
}

/// `probe(k, v)` for every `k` in `lo..hi` step 4, each call in a FRESH
/// instance (a trap leaves the stack pointer lowered, and the sweep relies
/// on the first frame's layout); `None` is a trap. `None` for the whole
/// sweep when node is absent.
fn sweep(bytes: &[u8], name: &str, lo: i64, hi: i64, v: i64) -> Option<Vec<(i64, Option<i64>)>> {
    let Some(node) = node() else {
        eprintln!("SKIP: node not found; {name} not swept");
        return None;
    };
    let dir = scratch("sweep");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let js = "const fs = require('fs');\n\
              const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
              const name = process.argv[3];\n\
              const [lo, hi, v] = [+process.argv[4], +process.argv[5], +process.argv[6]];\n\
              const out = [];\n\
              for (let k = lo; k < hi; k += 4) {\n\
                const f = new WebAssembly.Instance(m, {}).exports[name];\n\
                try { out.push([k, f(k, v)]); } \
                catch (e) { if (!(e instanceof WebAssembly.RuntimeError)) throw e; out.push([k, null]); }\n\
              }\n\
              process.stdout.write(JSON.stringify(out));\n";
    std::fs::write(dir.join("sweep.js"), js).unwrap();
    let run = Command::new(node)
        .arg(dir.join("sweep.js"))
        .arg(dir.join("m.wasm"))
        .arg(name)
        .args([lo, hi, v].map(|x| x.to_string()))
        .output()
        .expect("run node");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "node failed on {name}: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    Some(serde_json::from_slice(&run.stdout).expect("node JSON"))
}

/// Checks on A's address (`%4`) that pass for some of its bits only: a
/// wasm trap or trust-ir UB for the others. Past each, A's address is known,
/// so A is captured. `(label, check, callee body)`. A source `assert` (a Rust
/// panic since trust-ir v52) is refused before lowering
/// ([`a_source_assert_probe_is_refused_by_its_panic_kind`]); its capture rule
/// is the `assume` row's.
const BITS_CHECKS: &[(&str, &str, &str)] = &[
    (
        "assume",
        "    %6 = icmp eq usize %4, %5\n    assume %6\n",
        "",
    ),
    (
        "udiv",
        "    %6 = icmp eq usize %4, %5\n    %20 = zext bool %6 to usize\n    \
         %21 = const usize 1\n    %22 = udiv usize %21, %20\n",
        "",
    ),
    (
        "sdiv",
        "    %20 = sub usize %4, %5\n    %21 = const usize 2147483648\n    \
         %22 = add usize %20, %21\n    %23 = const usize 4294967295\n    \
         %24 = sdiv usize %22, %23\n",
        "",
    ),
    (
        "shift",
        "    %20 = sub usize %4, %5\n    %21 = const usize 1\n    %22 = shl usize %21, %20\n",
        "",
    ),
    (
        "load_bits",
        "    %6 = icmp eq usize %4, %5\n    %20 = zext bool %6 to usize\n    \
         %21 = mul usize %20, %5\n    %22 = inttoptr usize %21 to ptr\n    \
         %23 = load i32, ptr %22\n",
        "",
    ),
    (
        "gep_bits_index",
        "    %20 = sub usize %4, %5\n    %21 = inttoptr usize %5 to ptr\n    \
         %22 = gep u8, ptr %21, %20\n",
        "",
    ),
    (
        "gep_bits_base",
        "    %20 = xor usize %4, %5\n    %21 = inttoptr usize %20 to ptr\n    \
         %22 = const usize 1\n    %23 = gep u8, ptr %21, %22\n",
        "",
    ),
    (
        "wide_inttoptr",
        "    %20 = zext usize %4 to u64\n    %21 = zext usize %5 to u64\n    \
         %22 = sub u64 %20, %21\n    %23 = inttoptr u64 %22 to ptr\n",
        "",
    ),
    (
        "callee_assume",
        "    call @func.0(%4, %5)\n",
        "    %2 = icmp eq usize %0, %1\n    assume %2\n",
    ),
];

/// Uses of A's address that let every execution continue: A and B share.
const OFFSET_USES: &[(&str, &str, &str)] = &[
    (
        "independent_assume",
        "    %6 = icmp eq usize %5, %5\n    assume %6\n",
        "",
    ),
    (
        "offset_gep",
        "    %20 = const usize 4\n    %21 = gep u8, ptr %2, %20\n    %22 = load u8, ptr %21\n",
        "",
    ),
    (
        "callee_offset",
        "    call @func.0(%4, %5)\n",
        "    %2 = const usize 100\n    %3 = icmp ult usize %1, %2\n    assume %3\n",
    ),
];

/// The source-`assert` spellings of the probes above, which compiled (and
/// trapped) before trust-ir v52 named an assert's panic. Each stays a
/// fixture and must be refused by its panic kind at the shared admission
/// floor, never lowered to a generic trap. `(label, check, callee body)`.
const SOURCE_ASSERT_PROBES: &[(&str, &str, &str)] = &[
    (
        "assert",
        "    %6 = icmp eq usize %4, %5\n    assert %6\n",
        "",
    ),
    (
        "callee_assert",
        "    call @func.0(%4, %5)\n",
        "    %2 = icmp eq usize %0, %1\n    assert %2\n",
    ),
    (
        "independent_assert",
        "    %6 = icmp eq usize %5, %5\n    assert %6\n",
        "",
    ),
    (
        "callee_offset_assert",
        "    call @func.0(%4, %5)\n",
        "    %2 = const usize 100\n    %3 = icmp ult usize %1, %2\n    assert %3\n",
    ),
    (
        "bounds_check_assert",
        "    %20 = const usize 8\n    %6 = icmp ult usize %5, %20\n    \
         assert %6, bounds_check %5, %20\n",
        "",
    ),
];

/// A source `assert` is a Rust panic of a stated kind (trust-ir v52). The wasm
/// lane has no faithful panic route (payload, caller location, handler), so
/// the closed-module and object lanes refuse every probe by its kind instead
/// of trapping.
#[test]
fn a_source_assert_probe_is_refused_by_its_panic_kind() {
    for &(label, check, callee) in SOURCE_ASSERT_PROBES {
        let m = bits_probe(check, callee);
        let closed = wasm::compile_module_with_license(&m, &permit_unlicensed())
            .expect_err(label)
            .to_string();
        let object = wasm::compile_object_with_license(&m, &permit_unlicensed())
            .expect_err(label)
            .to_string();
        let expected = if label == "bounds_check_assert" {
            "panic_bounds_check"
        } else {
            "assert of unspecified panic kind"
        };
        for (lane, err) in [("closed", &closed), ("object", &object)] {
            assert!(
                err.contains(expected),
                "{label} ({lane} lane): refusal does not name the panic kind: {err}"
            );
        }
    }
}

/// An `assume`, division, shift, `GEP`, access or wide `inttoptr`
/// that stops execution for all but some of an address's bits exposes the
/// address, as a branch on them does: the allocation never shares bytes with
/// a later one, also when the check sits in a strong callee. The frame shows
/// the decision; where the check traps in wasm too, a sweep of `k` over the
/// frame (a fresh instance per call) shows every passing call reads A's 7.
#[test]
fn an_address_only_some_bits_pass_keeps_its_allocation() {
    const SLOT: i32 = 4096;
    for &(label, check, callee) in OFFSET_USES {
        let m = bits_probe(check, callee);
        let closed = lane_only(&m).unwrap_or_else(|e| panic!("{label}: {e}"));
        validate(&closed);
        let frame = frame_size(&closed, "probe");
        assert!(
            frame < 2 * SLOT,
            "{label}: the control's frame is {frame} bytes; A and B no longer share"
        );
    }
    let mut hits = 0;
    for &(label, check, callee) in BITS_CHECKS {
        let m = bits_probe(check, callee);
        let closed = lane_only(&m).unwrap_or_else(|e| panic!("{label}: {e}"));
        validate(&closed);
        let frame = frame_size(&closed, "probe");
        assert!(
            frame >= 2 * SLOT,
            "{label}: the frame is {frame} bytes; A shares bytes with B after a check \
             on its address"
        );
        if label != "udiv" {
            continue;
        }
        let Some(top) = run_wasm(&closed, "addr_of", W::I32, &[vec![0, 0]]) else {
            continue;
        };
        let top = top[0].expect("addr_of returns");
        let (lo, hi) = ((top - 3 * i64::from(SLOT)).max(0), top + i64::from(SLOT));
        let Some(got) = sweep(&closed, "probe", lo, hi, 9) else {
            continue;
        };
        let passed: Vec<(i64, i64)> = got.iter().filter_map(|&(k, r)| r.map(|r| (k, r))).collect();
        assert!(
            !passed.is_empty(),
            "{label}: no k in {lo}..{hi} passed the check; the sweep missed A"
        );
        for (k, r) in &passed {
            assert_eq!(*r, 7, "{label}: probe({k}, 9) read {r}, not A's 7");
        }
        hits += passed.len();
    }
    eprintln!("bits checks: {hits} sweep hits read A's 7");
}

// ---- 3. An `Alloca` with a runtime element count ----

/// `dyncount.trust_ir`: `alloca i32, count` with `count` in `1..=8`.
const DYNCOUNT: &str = r#"functy.0 = (i32, i32) -> (i32)

fn @dyncount(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = const i32 7
    %3 = and i32 %1, %2
    %4 = const i32 1
    %5 = add i32 %3, %4
    %6 = bitcast i32 %5 to u32
    %7 = zext u32 %6 to usize
    %8 = alloca i32, %7
    %9 = const usize 0
    %10 = gep i32, ptr %8, %9
    store i32 %0, ptr %10
    %11 = load i32, ptr %10
    ret %11
}
"#;

/// `dc2.trust_ir` retargeted to wasm32: `count` in `1..=64` elements are
/// filled and summed, with a second fixed allocation beside them and a
/// runtime-count allocation in a loop — every allocation stays disjoint.
const DYNSUM: &str = r#"functy.0 = (i64, i64) -> (i64)

fn @dynsum(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = const i64 63
    %3 = and i64 %1, %2
    %4 = const i64 1
    %5 = add i64 %3, %4
    %6 = alloca i64
    store i64 %0, ptr %6
    %7 = alloca i64, %5
    %8 = const i64 0
    br bb1(%8)
bb1(%9: i64):
    %10 = icmp slt i64 %9, %5
    condbr %10, bb2, bb3(%8, %8)
bb2:
    %11 = gep i64, ptr %7, %9
    %12 = mul i64 %9, %0
    store i64 %12, ptr %11
    %13 = add i64 %9, %4
    br bb1(%13)
bb3(%14: i64, %15: i64):
    %16 = icmp slt i64 %14, %5
    condbr %16, bb4, bb5
bb4:
    %17 = gep i64, ptr %7, %14
    %18 = load i64, ptr %17
    %19 = alloca i64, %5
    store i64 %18, ptr %19
    %20 = load i64, ptr %19
    %21 = add i64 %15, %20
    %22 = add i64 %14, %4
    br bb3(%22, %21)
bb5:
    %23 = load i64, ptr %6
    %24 = xor i64 %15, %23
    ret %24
}
"#;

/// The count straight from the input, at a signed, an unsigned and a
/// 128-bit type: a count at or below zero is undefined behaviour in the
/// interpreter and traps here; a count too large for memory traps too.
fn raw_count(conv: &str) -> Module {
    module(&format!(
        "functy.0 = (i64, i64) -> (i64)\n\n\
         fn @rawcount(functy.0) {{\n\
         bb0(%0: i64, %1: i64):\n\
         {conv}\
             %8 = alloca i16, %7\n\
             %10 = trunc i64 %0 to i16\n\
             store i16 %10, ptr %8\n\
             %11 = load i16, ptr %8\n\
             %12 = sext i16 %11 to i64\n\
             ret %12\n\
         }}\n"
    ))
}

#[test]
fn an_alloca_with_a_runtime_count_is_carved_from_the_stack() {
    let mut checks = 0;
    let m = module(DYNCOUNT);
    checks += agrees(
        &m,
        &wasm::compile_module_with_license(&m, &permit_unlicensed()).expect("dyncount"),
        "dyncount",
        W::I32,
        &grid(I32_VALUES),
    );
    let m = module(DYNSUM);
    let calls = grid(&[-3, 0, 1, 7, 62, 63, 64, 1000]);
    checks += agrees(
        &m,
        &wasm::compile_module_with_license(&m, &permit_unlicensed()).expect("dynsum"),
        "dynsum",
        W::I64,
        &calls,
    );
    if let Some(linked) =
        link(
            &[
                &wasm::compile_object_with_license(&m, &permit_unlicensed())
                    .expect("dynsum object"),
            ],
        )
    {
        checks += agrees(&m, &linked, "dynsum", W::I64, &calls);
    }
    let counts = [
        vec![5, 1],
        vec![5, 3],
        vec![-9, 0],
        vec![-9, -1],
        vec![7, 1 << 40],
        vec![7, i64::MIN],
    ];
    for (ty, conv) in [
        ("i64", "    %7 = copy i64 %1\n"),
        ("u32", "    %7 = trunc i64 %1 to u32\n"),
        ("i32", "    %7 = trunc i64 %1 to i32\n"),
        ("i128", "    %7 = sext i64 %1 to i128\n"),
        ("u128", "    %7 = zext i64 %1 to u128\n"),
    ] {
        let m = raw_count(conv);
        let bytes = wasm::compile_module_with_license(&m, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("{ty}: {e}"));
        checks += agrees(&m, &bytes, "rawcount", W::I64, &counts);
        // A zero (or, signed, negative) count and a count past the stack
        // trap rather than carve.
        if let Some(got) = run_wasm(&bytes, "rawcount", W::I64, &counts) {
            assert_eq!(got[0], Some(5), "{ty}");
            assert_eq!(got[2], None, "{ty}: a zero count must trap");
            assert_eq!(got[4], None, "{ty}: a 2^40 count must trap");
        }
    }
    if node().is_some() {
        assert!(checks > 0);
    }
}

// ---- 4. Irreducible control flow ----

/// `irr1.trust_ir`: the loop {bb1, bb2} is entered from bb0 at both blocks.
const IRR1: &str = r#"functy.0 = (i64, i64) -> (i64)

fn @f(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = const i64 0
    %3 = icmp slt i64 %0, %2
    %4 = const i64 7
    %5 = and i64 %1, %4
    condbr %3, bb1(%5, %0), bb2(%5, %1)
bb1(%6: i64, %7: i64):
    %8 = const i64 3
    %9 = mul i64 %7, %8
    %10 = const i64 1
    %11 = add i64 %9, %10
    br bb2(%6, %11)
bb2(%12: i64, %13: i64):
    %14 = const i64 5
    %15 = xor i64 %13, %14
    %16 = const i64 0
    %17 = icmp eq i64 %12, %16
    %18 = const i64 1
    %19 = sub i64 %12, %18
    condbr %17, bb3(%15), bb1(%19, %15)
bb3(%20: i64):
    ret %20
}
"#;

/// A deterministic xorshift stream.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A small per-block constant, independent of the branch stream.
fn ta_seed(k: u64, seed: u64) -> u64 {
    (k * 31 + seed * 17) ^ (seed >> 3)
}

/// A random CFG over `n` loop blocks (often irreducible). Each block `k`
/// carries `(x: i64, fuel: i64, s: struct.0)`, computes, writes and reads an
/// `Alloca`, and exits when its fuel runs out; otherwise it branches to
/// random blocks by `br`, `condbr` or `switch`, rebinding the memory-carried
/// struct on every edge. The entry enters at two random blocks; one successor
/// per node follows a ring so every generated block is source-reachable.
fn random_cfg(seed: u64, n: u64) -> String {
    let mut r = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    assert!(n > 0);
    // Block ids: 0 entry; loop block k (1..=n) is 3k-2, its exit 3k-1 and
    // its branch 3k.
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
                let (_random_target, tb, modulus) = (t(), t(), 2 + ((ta_seed(k, seed)) % 4));
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

/// Whether `func` has a cycle with more than one entry: a DFS back edge
/// whose target does not dominate its source.
fn is_irreducible(func: &Function) -> bool {
    let index = |b: BlockId| func.blocks.iter().position(|x| x.id == b).unwrap();
    let n = func.blocks.len();
    let succs: Vec<Vec<usize>> = func
        .blocks
        .iter()
        .map(|b| match &b.body.last().unwrap().inst {
            Inst::Br { target, .. } => vec![index(*target)],
            Inst::CondBr {
                then_target,
                else_target,
                ..
            } => vec![index(*then_target), index(*else_target)],
            Inst::Switch { default, cases, .. } => std::iter::once(index(*default))
                .chain(cases.iter().map(|c| index(c.target)))
                .collect(),
            _ => vec![],
        })
        .collect();
    let entry = index(func.entry);
    // Dominator sets by iteration to a fixpoint.
    let all: Vec<bool> = vec![true; n];
    let mut dom: Vec<Vec<bool>> = vec![all; n];
    dom[entry] = (0..n).map(|i| i == entry).collect();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (p, ss) in succs.iter().enumerate() {
        for &s in ss {
            preds[s].push(p);
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for b in (0..n).filter(|&b| b != entry) {
            let mut d: Vec<bool> = vec![true; n];
            for &p in &preds[b] {
                for i in 0..n {
                    d[i] &= dom[p][i];
                }
            }
            d[b] = true;
            if d != dom[b] {
                dom[b] = d;
                changed = true;
            }
        }
    }
    // Back edges of a DFS: edges to a block on the current path.
    let mut on_path = vec![false; n];
    let mut seen = vec![false; n];
    let mut stack: Vec<(usize, usize)> = vec![(entry, 0)];
    seen[entry] = true;
    on_path[entry] = true;
    while let Some(&mut (b, ref mut i)) = stack.last_mut() {
        if let Some(&s) = succs[b].get(*i) {
            *i += 1;
            if on_path[s] && !dom[b][s] {
                return true;
            }
            if !seen[s] {
                seen[s] = true;
                on_path[s] = true;
                stack.push((s, 0));
            }
        } else {
            on_path[b] = false;
            stack.pop();
        }
    }
    false
}

#[test]
fn an_irreducible_cfg_lowers_as_a_dispatch_loop() {
    let mut checks = 0;
    let irr = module(IRR1);
    assert!(is_irreducible(&irr.functions[0]));
    let (bytes, evidence) = wasm::compile_module_with_evidence_policy_and_license(
        &irr,
        &wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("irr1");
    assert!(
        evidence.cfg_structural.holds(),
        "{:?}",
        evidence.cfg_structural
    );
    let calls = grid(I64_VALUES);
    checks += agrees(&irr, &bytes, "f", W::I64, &calls);
    assert_eq!(interpret(&irr, "f", W::I64, &[-5, 3]), Some(-245));
    if let Some(linked) = link(&[
        &wasm::compile_object_with_license(&irr, &permit_unlicensed()).expect("irr1 object"),
    ]) {
        checks += agrees(&irr, &linked, "f", W::I64, &calls);
    }
    let inputs = grid(&[-9, -1, 0, 1, 4, 11, 1 << 33, i64::MIN]);
    let mut irreducible = 0;
    for seed in 1..=40u64 {
        let m = module(&random_cfg(seed, 2 + seed % 7));
        irreducible += usize::from(is_irreducible(&m.functions[0]));
        let (bytes, evidence) = wasm::compile_module_with_evidence_policy_and_license(
            &m,
            &wasm::WasmModulePolicy::closed(),
            &permit_unlicensed(),
        )
        .unwrap_or_else(|e| panic!("seed {seed}: {e}"));
        assert!(
            evidence.cfg_structural.holds(),
            "seed {seed}: {:?}",
            evidence.cfg_structural
        );
        checks += agrees(&m, &bytes, "f", W::I64, &inputs);
        let object = wasm::compile_object_with_license(&m, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("seed {seed}: {e}"));
        validate(&object);
    }
    assert!(
        irreducible >= 10,
        "the generator must exercise irreducible CFGs ({irreducible} of 40)"
    );
    if node().is_some() {
        assert!(checks > 0);
    }
}

// ---- 5. Closed-module exports ----

/// `dup_c2.trust_ir`: two internal `@foo`s beside an external `@foo` and an
/// internal global `@foo`. The trust-ir validator refuses two functions of
/// one name whatever their linkage. Keep that source refusal beside the
/// corresponding uniquely named positive, with every body and call retained.
const DUP_NAMES: &str = r#"functy.0 = (i32) -> (i32)

internal fn @foo(functy.0) {
bb0(%0: i32):
    %1 = const i32 1000
    %2 = add i32 %0, %1
    ret %2
}

internal fn @foo(functy.0) {
bb0(%0: i32):
    %1 = const i32 3
    %2 = mul i32 %0, %1
    ret %2
}

global internal @foo i32 = 55

fn @foo(functy.0) {
bb0(%0: i32):
    %1 = const i32 -1
    %2 = xor i32 %0, %1
    ret %2
}

fn @use3(functy.0) {
bb0(%0: i32):
    %1 = call @func.0(%0)
    %2 = call @func.1(%0)
    %3 = call @func.2(%0)
    %10 = global_addr @global.0
    %11 = load i32, ptr %10
    %4 = const i32 1000
    %5 = mul i32 %1, %4
    %6 = add i32 %5, %2
    %7 = mul i32 %6, %4
    %8 = add i32 %7, %3
    %9 = add i32 %8, %11
    ret %9
}
"#;

/// Retain all definitions, IDs, bodies and calls while giving distinct
/// definitions distinct source symbols, as current IR admission requires.
fn unique_names() -> String {
    DUP_NAMES
        .replacen("internal fn @foo(", "internal fn @foo_local0(", 1)
        .replacen("internal fn @foo(", "internal fn @foo_local1(", 1)
        .replace("global internal @foo", "global internal @foo_data")
}

fn exports(bytes: &[u8]) -> Vec<String> {
    let mut names = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let Ok(wasmparser::Payload::ExportSection(reader)) = payload {
            for export in reader {
                names.push(export.expect("export").name.to_string());
            }
        }
    }
    names.sort();
    names
}

#[test]
fn distinct_local_and_external_functions_keep_their_exports() {
    let invalid = module(DUP_NAMES);
    for result in [
        wasm::compile_module_with_license(&invalid, &permit_unlicensed()),
        wasm::compile_object_with_license(&invalid, &permit_unlicensed()),
    ] {
        let error = result.expect_err("duplicate source symbols remain invalid");
        assert!(
            format!("{error:?}").contains("DuplicateFunctionSymbol"),
            "{error}"
        );
    }
    let m = module(&unique_names());
    let bytes =
        wasm::compile_module_with_license(&m, &permit_unlicensed()).expect("distinct local names");
    assert_eq!(
        exports(&bytes),
        vec![
            "foo".to_string(),
            "foo_local0".to_string(),
            "foo_local1".to_string(),
            "use3".to_string()
        ]
    );
    let calls: Vec<Vec<i64>> = [0, 5, -7].iter().map(|&x| vec![x]).collect();
    agrees(&m, &bytes, "use3", W::I32, &calls);
    if let Some(got) = run_wasm(&bytes, "use3", W::I32, &[vec![0]]) {
        assert_eq!(got, vec![Some(1_000_000_054)]);
    }
    // `foo` is the external definition.
    if let Some(got) = run_wasm(&bytes, "foo", W::I32, &[vec![5]]) {
        assert_eq!(got, vec![Some(!5)]);
    }
    // A module-local function named like the memory export yields the name.
    let mem = module(
        "functy.0 = (i32) -> (i32)\n\n\
         internal fn @memory(functy.0) {\nbb0(%0: i32):\n    %1 = const i32 1000\n\
             %2 = add i32 %0, %1\n    ret %2\n}\n\n\
         fn @use1(functy.0) {\nbb0(%0: i32):\n    %1 = call @func.0(%0)\n    ret %1\n}\n",
    );
    let exporting = WasmModulePolicy {
        memory: WasmMemoryPolicy::Owned {
            pages: 1,
            export: Some("memory".to_string()),
        },
        ..WasmModulePolicy::closed()
    };
    let bytes =
        wasm::compile_module_with_policy_and_license(&mem, &exporting, &permit_unlicensed())
            .expect("memory-named local");
    assert_eq!(
        exports(&bytes),
        vec!["memory".to_string(), "use1".to_string()]
    );
    agrees(&mem, &bytes, "use1", W::I32, &calls);
    // Without the memory export it keeps its own export.
    let bytes = wasm::compile_module_with_license(&mem, &permit_unlicensed()).expect("closed");
    assert_eq!(
        exports(&bytes),
        vec!["memory".to_string(), "use1".to_string()]
    );
    // Two EXTERNAL definitions of one name are still refused by name.
    let twice = module(&DUP_NAMES.replace("internal fn @foo", "fn @foo"));
    match wasm::compile_module_with_license(&twice, &permit_unlicensed()) {
        Err(WasmLowerError::InvalidTrustIr(refusal)) => assert!(
            refusal.any(|error| matches!(
                error,
                trust_ir_build::ValidationError::DuplicateFunctionSymbol { .. }
            )),
            "{refusal}"
        ),
        other => panic!("two external `foo`s must be refused, got {other:?}"),
    }
}

// ---- 6. Non-dominated uses ----

/// `nonstrict.trust_ir`: `%4`, defined only on the `bb1` path, is used in
/// `bb4` under the same condition. The trust-ir validator rejects it
/// (`UseBeforeDefInBlock`); the lane refuses it by name on both entries.
const NONSTRICT: &str = r#"functy.0 = (i32, i32) -> (i32)

fn @nonstrict(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = const i32 0
    %3 = icmp slt i32 %0, %2
    condbr %3, bb1, bb2
bb1:
    %4 = mul i32 %0, %1
    br bb3
bb2:
    br bb3
bb3:
    condbr %3, bb4, bb5
bb4:
    ret %4
bb5:
    ret %1
}
"#;

#[test]
fn a_use_its_definition_does_not_dominate_is_refused_by_name() {
    let m = module(NONSTRICT);
    for result in [
        wasm::compile_module_with_license(&m, &permit_unlicensed()),
        wasm::compile_object_with_license(&m, &permit_unlicensed()),
    ] {
        if let Err(WasmLowerError::InvalidTrustIr(refusal)) = &result {
            assert!(
                refusal.any(|error| matches!(
                    error,
                    trust_ir_build::ValidationError::UseBeforeDefInBlock { .. }
                )),
                "{refusal}"
            );
            continue;
        }
        match result {
            Err(WasmLowerError::IllFormedSsa(msg)) => {
                assert!(msg.contains("does not dominate"), "{msg}")
            }
            other => panic!("expected an SSA refusal, got {other:?}"),
        }
    }
    // The same refusal inside an irreducible CFG, whose dominators are those
    // of EVERY edge: `%9` is defined in bb1 and used in bb3, and bb3 is also
    // reached through bb2 -> bb4 -> bb3. Over the DFS's forward edges alone
    // bb1 would look like bb3's dominator (bb4 -> bb3 is a back edge there).
    let irr = module(
        "functy.0 = (i64, i64) -> (i64)\n\nfn @g(functy.0) {\n\
         bb0(%0: i64, %1: i64):\n    %2 = const i64 0\n    %3 = icmp slt i64 %0, %2\n\
         \x20   condbr %3, bb1, bb2\n\
         bb1:\n    %9 = add i64 %1, %1\n    br bb3(%1)\n\
         bb2:\n    br bb4(%1)\n\
         bb3(%4: i64):\n    %5 = add i64 %4, %9\n    %6 = icmp eq i64 %5, %2\n\
         \x20   condbr %6, bb5, bb4(%5)\n\
         bb4(%7: i64):\n    br bb3(%7)\n\
         bb5:\n    ret %5\n}\n",
    );
    assert!(is_irreducible(&irr.functions[0]));
    for result in [
        wasm::compile_module_with_license(&irr, &permit_unlicensed()),
        wasm::compile_object_with_license(&irr, &permit_unlicensed()),
    ] {
        if let Err(WasmLowerError::InvalidTrustIr(refusal)) = &result {
            assert!(
                refusal.any(|error| matches!(
                    error,
                    trust_ir_build::ValidationError::UseBeforeDefInBlock { .. }
                )),
                "{refusal}"
            );
            continue;
        }
        match result {
            Err(WasmLowerError::IllFormedSsa(msg)) => {
                assert!(msg.contains("does not dominate"), "{msg}")
            }
            other => panic!("expected an SSA refusal, got {other:?}"),
        }
    }
}

// ---- 7. Determinism ----

#[test]
fn the_new_lowerings_always_compile_to_the_same_bytes() {
    let texts: Vec<String> = [IRR1, DYNSUM, LAUNDER_TABLE, LOOP_REUSE, DUP_NAMES]
        .iter()
        .map(|t| {
            if *t == DUP_NAMES {
                unique_names()
            } else {
                t.to_string()
            }
        })
        .chain((1..=6).map(|seed| random_cfg(seed, 5)))
        .collect();
    let compile_all = |texts: &[String]| -> Vec<(Vec<u8>, Vec<u8>)> {
        texts
            .iter()
            .map(|t| {
                let m = module(t);
                (
                    wasm::compile_module_with_license(&m, &permit_unlicensed()).expect("closed"),
                    wasm::compile_object_with_license(&m, &permit_unlicensed()).expect("object"),
                )
            })
            .collect()
    };
    let objects = || {
        ["weak", "linkonce_odr"]
            .iter()
            .map(|l| {
                wasm::compile_object_with_license(&weak_caller(l), &permit_unlicensed())
                    .expect("weak caller")
            })
            .collect::<Vec<_>>()
    };
    let first = compile_all(&texts);
    let first_objects = objects();
    for _ in 0..3 {
        assert!(
            compile_all(&texts) == first,
            "a recompile changed the bytes"
        );
        assert!(objects() == first_objects, "a recompile changed the bytes");
    }
    // A fresh thread has fresh hash-map seeds.
    let again = std::thread::spawn(move || (compile_all(&texts), objects()))
        .join()
        .expect("compile thread");
    assert!(again.0 == first, "a fresh thread changed the bytes");
    assert!(again.1 == first_objects, "a fresh thread changed the bytes");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
