// trust-cg-codegen/tests/wasm_p6_pair.rs - wasm32 lane: the 128-bit pair carrier
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The wasm lane's pair carrier for 128-bit integers (P6 stage A): at O1 and
//! above a 128-bit value whose every definition and use has a pair lowering
//! lives in two `i64` locals instead of a 16-byte home in the frame.
//!
//! * At O0 every function below that computes on 128-bit values carves a
//!   shadow-stack frame for their homes.
//! * At O2, with or without the trust-ir mid-end, the functions whose 128-bit
//!   values are all pairs — a loop-carried accumulator, a diamond join and a
//!   `select`, an irreducible cycle lowered as the dispatch loop, a 128-bit
//!   `switch`, the casts — keep no frame and touch no memory at all; with
//!   the mid-end, so does a loop over a 128-bit frame slot, which scalar
//!   replacement turns into a block parameter.
//! * Calls pass pairs as the two `i64` halves of the C ABI and take a 128-bit
//!   result back through a scratch `sret` slot; the division helper writes
//!   into a scratch slot; aggregates, stores and loads move a pair's 16-byte
//!   image; atomics on 128-bit values stay memory-based.
//! * A shift or rotate of a pair by a constant amount has its own sequence
//!   of constant half shifts at O2 (no `select`); O0 keeps the general one.
//! * The local emission pass's translation validation accepts every body:
//!   no function falls back.
//! * Every form — O0, O2 lane-only, O2 with the mid-end, the linked object —
//!   agrees with the trust-ir reference interpreter in node.
//!
//! Node is required to execute the wasm and `wasm-ld` (`WASM_LD`) to link
//! the object; the absence of either is a loud SKIP.
//!
//! The entries this test drives (`compile_module_with_evidence_policy_license_options`,
//! `compile_sized_closed_module_with_evidence_license_options`,
//! `compile_object_with_evidence_license_options`), `WasmOptOptions` and the
//! evidence it reads (`local_emission.enabled` / `fallbacks`, `mid_end`) are
//! provisional surfaces pending the owner's sign-off: this test follows them
//! if they change, and is not a contract for their shape.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{self, WasmModulePolicy, WasmOptOptions};
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

/// `%r` (a 128-bit value of type `t`) folded to an `i64`: `lo ^ hi * 31`.
fn fold(t: &str, r: &str) -> String {
    format!(
        "    %flo = trunc {t} {r} to u64\n    %fc64 = const {t} 64\n    \
         %fsh = lshr {t} {r}, %fc64\n    %fhi = trunc {t} %fsh to u64\n    \
         %fc31 = const u64 31\n    %fhm = mul u64 %fhi, %fc31\n    \
         %ff = xor u64 %flo, %fhm\n    %fout = bitcast u64 %ff to i64\n    ret %fout\n"
    )
}

const HEADER: &str = "module \"p6\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
struct @W { : u32 @0, : i128 @16 } size=32 align=16 id=0\n\n\
functy.0 = (i64, i64) -> (i64)\n\
functy.1 = (i128, u128) -> (i128)\n\
functy.2 = (i128, i64) -> (i128)\n\n";

/// Rustcc helpers, in function-index order (`func.0`, `func.1`).
const HELPERS: &str = "rustcc fn @mix(functy.1) {
bbentry(%x: i128, %y: u128):
    %yi = bitcast u128 %y to i128
    %m = mul i128 %x, %yi
    %c3 = const i128 3
    %t = add i128 %m, %c3
    ret %t
}

rustcc fn @doubling(functy.2) {
bbentry(%x: i128, %n: i64):
    %c0 = const i64 0
    %z = icmp sle i64 %n, %c0
    condbr %z, bbret, bbstep
bbstep:
    %c2 = const i128 2
    %x2 = mul i128 %x, %c2
    %c1 = const i64 1
    %n1 = sub i64 %n, %c1
    br bbentry(%x2, %n1)
bbret:
    ret %x
}
";

/// Where a function's 128-bit values are all pair-carried, so that it keeps
/// no frame and touches no memory.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Pure {
    /// At O2, with or without the mid-end.
    Lane,
    /// At O2 once the mid-end promoted its 128-bit slot.
    MidEnd,
    /// Never: it keeps memory by design.
    No,
}

/// The exported `(i64, i64) -> i64` functions: name, body (after the entry
/// block's label) and where every 128-bit value in it is pair-carried.
fn functions() -> Vec<(&'static str, String, Pure)> {
    vec![
        (
            "loop_acc",
            format!(
                "    %x = sext i64 %a to i128\n    %c31 = const i64 31\n    \
                 %n = and i64 %b, %c31\n    %zero = const i128 0\n    %i0 = const i64 0\n    \
                 br bbloop(%zero, %i0)\n\
                 bbloop(%acc: i128, %i: i64):\n    %done = icmp sge i64 %i, %n\n    \
                 condbr %done, bbexit, bbbody\n\
                 bbbody:\n    %k = const i128 170141183460469231731687303715884105727\n    \
                 %m = mul i128 %acc, %k\n    %s = add i128 %m, %x\n    \
                 %c1 = const i64 1\n    %i1 = add i64 %i, %c1\n    br bbloop(%s, %i1)\n\
                 bbexit:\n{}",
                fold("i128", "%acc")
            ),
            Pure::Lane,
        ),
        (
            "diamond",
            format!(
                "    %x = sext i64 %a to i128\n    %y = zext i64 %b to i128\n    \
                 %c = icmp slt i128 %x, %y\n    condbr %c, bbt, bbf\n\
                 bbt:\n    %p = sub i128 %y, %x\n    br bbj(%p, %x)\n\
                 bbf:\n    %q = mul i128 %x, %y\n    br bbj(%q, %y)\n\
                 bbj(%v: i128, %w: i128):\n    %c2 = icmp ugt i128 %v, %w\n    \
                 %r = select i128 %c2, %v, %w\n{}",
                fold("i128", "%r")
            ),
            Pure::Lane,
        ),
        (
            "dispatch",
            format!(
                "    %x = sext i64 %a to i128\n    %y = sext i64 %b to i128\n    \
                 %c15 = const i64 15\n    %n = and i64 %b, %c15\n    %z = const i64 0\n    \
                 %neg = icmp slt i64 %a, %z\n    condbr %neg, bbl(%x, %z), bbr(%y, %z)\n\
                 bbl(%u: i128, %i: i64):\n    %c3 = const i128 3\n    \
                 %u3 = mul i128 %u, %c3\n    %c1 = const i64 1\n    %i1 = add i64 %i, %c1\n    \
                 br bbr(%u3, %i1)\n\
                 bbr(%v: i128, %j: i64):\n    %c5 = const i128 5\n    \
                 %v5 = add i128 %v, %c5\n    %stop = icmp sge i64 %j, %n\n    \
                 condbr %stop, bbexit(%v5), bbl(%v5, %j)\n\
                 bbexit(%r: i128):\n{}",
                fold("i128", "%r")
            ),
            Pure::Lane,
        ),
        (
            "switch128",
            format!(
                "    %x = sext i64 %a to i128\n    %c3 = const i64 3\n    \
                 %k = and i64 %b, %c3\n    %kl = zext i64 %k to i128\n    \
                 %c1 = const i64 1\n    %kh = lshr i64 %k, %c1\n    %khw = zext i64 %kh to i128\n    \
                 %c64 = const i128 64\n    %khs = shl i128 %khw, %c64\n    \
                 %kk = or i128 %khs, %kl\n    \
                 switch %kk [ 0: bbz 1: bbo 18446744073709551618: bbt default: bbd ]\n\
                 bbz:\n    %r0 = add i128 %x, %x\n    br bbj(%r0)\n\
                 bbo:\n    %r1 = mul i128 %x, %x\n    br bbj(%r1)\n\
                 bbt:\n    %r2 = neg i128 %x\n    br bbj(%r2)\n\
                 bbd:\n    br bbj(%kk)\n\
                 bbj(%r: i128):\n{}",
                fold("i128", "%r")
            ),
            Pure::Lane,
        ),
        (
            "casts",
            format!(
                "    %x = sext i64 %a to i128\n    %u = bitcast i128 %x to u128\n    \
                 %c64 = const u128 64\n    %h = lshr u128 %u, %c64\n    \
                 %f = sitofp i128 %x to f64\n    %g = fptosi.sat f64 %f to i128\n    \
                 %d = sub i128 %g, %x\n    %du = bitcast i128 %d to u128\n    \
                 %bf = sitofp i64 %b to f32\n    %bu = fptoui.sat f32 %bf to u128\n    \
                 %s0 = xor u128 %du, %h\n    %s = add u128 %s0, %bu\n    \
                 %t = trunc u128 %s to u32\n    %tw = zext u32 %t to u128\n    \
                 %e = uitofp u128 %s to f32\n    %eb = bitcast f32 %e to u32\n    \
                 %ew = zext u32 %eb to u128\n    %c32 = const u128 32\n    \
                 %es = shl u128 %ew, %c32\n    %r0 = xor u128 %s, %es\n    \
                 %r = add u128 %r0, %tw\n{}",
                fold("u128", "%r")
            ),
            Pure::Lane,
        ),
        (
            "entry_loop",
            format!(
                "    %x = sext i64 %a to i128\n    %c7 = const i64 7\n    \
                 %n = and i64 %b, %c7\n    %r = call @func.1(%x, %n)\n{}",
                fold("i128", "%r")
            ),
            Pure::No,
        ),
        (
            "calls",
            format!(
                "    %x = sext i64 %a to i128\n    %y = zext i64 %b to u128\n    \
                 %r = call @func.0(%x, %y)\n    %c7 = const i128 7\n    \
                 %d = or i128 %r, %c7\n    %q = sdiv i128 %x, %d\n    \
                 %rm = srem i128 %r, %d\n    %s = add i128 %q, %rm\n{}",
                fold("i128", "%s")
            ),
            Pure::No,
        ),
        (
            "aggregates",
            format!(
                "    %x = sext i64 %a to i128\n    %w32 = trunc i64 %b to u32\n    \
                 %agg = make_aggregate struct.0 (%w32, %x)\n    %slot = alloca i128\n    \
                 %y = zext i64 %b to i128\n    %t = mul i128 %x, %y\n    \
                 store i128 %t, ptr %slot\n    %e = extractfield i128 %agg, 1\n    \
                 %l = load i128, ptr %slot\n    %s0 = xor i128 %e, %l\n    \
                 %ins = insertfield struct.0 %agg, 1, %s0\n    \
                 %e2 = extractfield i128 %ins, 1\n    %s = add i128 %e2, %s0\n{}",
                fold("i128", "%s")
            ),
            Pure::No,
        ),
        (
            "slot_loop",
            format!(
                "    %slot = alloca i128\n    %x = sext i64 %a to i128\n    \
                 store i128 %x, ptr %slot\n    %c15 = const i64 15\n    \
                 %n = and i64 %b, %c15\n    %i0 = const i64 0\n    br bbloop(%i0)\n\
                 bbloop(%i: i64):\n    %done = icmp sge i64 %i, %n\n    \
                 condbr %done, bbexit, bbbody\n\
                 bbbody:\n    %v = load i128, ptr %slot\n    %c3 = const i128 3\n    \
                 %m = mul i128 %v, %c3\n    %u = bitcast i128 %m to u128\n    \
                 store u128 %u, ptr %slot\n    %c1 = const i64 1\n    \
                 %i1 = add i64 %i, %c1\n    br bbloop(%i1)\n\
                 bbexit:\n    %r = load i128, ptr %slot\n{}",
                fold("i128", "%r")
            ),
            Pure::MidEnd,
        ),
        ("const_shifts", const_shifts(), Pure::Lane),
        (
            "atomics",
            format!(
                "    %slot = alloca i128\n    %x = sext i64 %a to i128\n    \
                 %y = zext i64 %b to i128\n    atomic_store seq_cst i128 %x, ptr %slot\n    \
                 %old = atomicrmw add seq_cst i128 ptr %slot, %y\n    \
                 %cur, %ok = cmpxchg i128 ptr %slot, %old, %y seq_cst seq_cst\n    \
                 %fin = atomic_load seq_cst i128, ptr %slot\n    \
                 %s0 = xor i128 %fin, %cur\n    %okw = zext bool %ok to i128\n    \
                 %c100 = const i128 100\n    %okb = shl i128 %okw, %c100\n    \
                 %s = or i128 %s0, %okb\n{}",
                fold("i128", "%s")
            ),
            Pure::No,
        ),
    ]
}

/// Every 128-bit shift and rotate by constant amounts on both sides of each
/// half boundary (and, for the rotates, amounts reduced modulo 128: 128, 191
/// and 255), of a signed and an unsigned value, folded by `xor`. trust-ir's
/// interpreter reads an amount of the shifted value's type.
fn const_shifts() -> String {
    let mut body = String::from(
        "    %x = sext i64 %a to i128\n    %yl = zext i64 %b to u128\n    \
         %ys = zext i64 %a to u128\n    %c64u = const u128 64\n    \
         %yh = shl u128 %ys, %c64u\n    %y = or u128 %yh, %yl\n    \
         %acc0 = bitcast u128 %y to i128\n",
    );
    let amounts: [u32; 11] = [0, 1, 7, 63, 64, 65, 70, 127, 128, 191, 255];
    let mut n = 0;
    for (ai, k) in amounts.iter().enumerate() {
        body.push_str(&format!(
            "    %ks{ai} = const i128 {k}\n    %ku{ai} = const u128 {k}\n"
        ));
        for (op, signed) in [
            ("shl", true),
            ("lshr", false),
            ("ashr", true),
            ("rotl", false),
            ("rotr", true),
        ] {
            // A shift by 128 or more is undefined behaviour in trust-ir; a
            // rotate reduces its amount modulo 128.
            if *k >= 128 && !op.starts_with("rot") {
                continue;
            }
            let (t, v, amount, view) = if signed {
                ("i128", "%x", format!("%ks{ai}"), format!("copy i128 %s{n}"))
            } else {
                (
                    "u128",
                    "%y",
                    format!("%ku{ai}"),
                    format!("bitcast u128 %s{n} to i128"),
                )
            };
            body.push_str(&format!(
                "    %s{n} = {op} {t} {v}, {amount}\n    %b{n} = {view}\n    \
                 %acc{} = xor i128 %acc{n}, %b{n}\n",
                n + 1
            ));
            n += 1;
        }
    }
    body + &fold("i128", &format!("%acc{n}"))
}

/// The `select`s in the body of export `name`.
fn selects(bytes: &[u8], name: &str) -> usize {
    exported_body(bytes, name)
        .get_operators_reader()
        .expect("ops")
        .into_iter()
        .filter(|op| {
            matches!(
                op.as_ref().expect("op"),
                wasmparser::Operator::Select | wasmparser::Operator::TypedSelect { .. }
            )
        })
        .count()
}

/// Rename `%name` values and `bbname` blocks to the text format's numeric
/// spellings, per function, in order of first appearance.
fn number_names(text: &str) -> String {
    use std::collections::HashMap;
    use std::fmt::Write as _;
    let mut out = String::with_capacity(text.len());
    let mut values: HashMap<String, usize> = HashMap::new();
    let mut blocks: HashMap<String, usize> = HashMap::new();
    for line in text.lines() {
        if line.starts_with("fn ") || line.starts_with("rustcc fn ") {
            values.clear();
            blocks.clear();
        }
        let bytes = line.as_bytes();
        let mut i = 0;
        let ident_end = |mut j: usize| {
            while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
                j += 1;
            }
            j
        };
        while i < bytes.len() {
            let word_start =
                i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_');
            if bytes[i] == b'%' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_alphabetic() {
                let end = ident_end(i + 1);
                let n = values.len();
                let id = *values.entry(line[i + 1..end].to_string()).or_insert(n);
                let _ = write!(out, "%{id}");
                i = end;
            } else if word_start
                && line[i..].starts_with("bb")
                && i + 2 < bytes.len()
                && bytes[i + 2].is_ascii_alphabetic()
            {
                let end = ident_end(i + 2);
                let n = blocks.len();
                let id = *blocks.entry(line[i + 2..end].to_string()).or_insert(n);
                let _ = write!(out, "bb{id}");
                i = end;
            } else {
                out.push(bytes[i] as char);
                i += 1;
            }
        }
        out.push('\n');
    }
    out
}

fn program() -> (Module, Vec<(&'static str, Pure)>) {
    let mut text = String::from(HEADER);
    text.push_str(HELPERS);
    let mut names = Vec::new();
    for (name, body, pure) in functions() {
        text.push_str(&format!(
            "\nfn @{name}(functy.0) {{\nbbentry(%a: i64, %b: i64):\n{body}}}\n"
        ));
        names.push((name, pure));
    }
    let text = number_names(&text);
    let module = trust_ir::parser::parse_module(&text).unwrap_or_else(|e| {
        let numbered: String = text
            .lines()
            .enumerate()
            .map(|(i, l)| format!("{:4} {l}\n", i + 1))
            .collect();
        panic!("the test program does not parse: {e}\n{numbered}")
    });
    (module, names)
}

fn options(level: OptLevel, mid_end: bool) -> WasmOptOptions {
    let mut options = WasmOptOptions::at(level);
    options.mid_end = mid_end;
    options
}

fn closed(module: &Module, opts: WasmOptOptions) -> (Vec<u8>, wasm::WasmCompileEvidence) {
    let (bytes, evidence) = wasm::compile_module_with_evidence_policy_license_options(
        module,
        &WasmModulePolicy::closed(),
        &permit_unlicensed(),
        opts,
    )
    .expect("compile the closed module");
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
    let verdict = trust_cg_verify::wasm_cfg_proofs::check_module_structure(&bytes);
    assert!(verdict.holds(), "CFG structural invariant: {verdict}");
    (bytes, evidence)
}

fn inputs() -> Vec<(i64, i64)> {
    let edges: [i64; 10] = [
        0,
        1,
        -1,
        2,
        -7,
        255,
        i32::MAX as i64,
        i32::MIN as i64,
        i64::MAX,
        i64::MIN,
    ];
    let mut out = Vec::new();
    for &a in &edges {
        for &b in &edges {
            out.push((a, b));
        }
    }
    let mut s: u64 = 0x2545_F491_4F6C_DD1D;
    let mut next = || {
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        s as i64
    };
    for _ in 0..60 {
        let (a, b) = (next(), next());
        out.push((a, b));
        out.push((a >> 33, b >> 50));
    }
    out
}

fn interpret(module: &Module, name: &str, a: i64, b: i64) -> Option<i64> {
    let f = module.function_by_name(name).expect("function");
    let args = [a, b].map(|v| InterpretValue::int(Ty::I64, i128::from(v)).expect("i64"));
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 1_000_000,
            max_call_depth: 64,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, args)
        .ok()?;
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => Some(i.as_signed() as i64),
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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_p6_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Every exported function on every input, in node; `None` when node is
/// absent.
fn run(bytes: &[u8], names: &[&str], inputs: &[(i64, i64)]) -> Option<Vec<Vec<Option<i64>>>> {
    let Some(node) = node() else {
        eprintln!("SKIP: node not found; the module was not executed");
        return None;
    };
    let dir = scratch("run");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let rows: Vec<String> = inputs
        .iter()
        .map(|(a, b)| format!("[\"{a}\",\"{b}\"]"))
        .collect();
    let js = format!(
        "const fs = require('fs');\n\
         const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
         const imports = {{}};\n\
         for (const i of WebAssembly.Module.imports(m)) {{ imports[i.module] ??= {{}}; }}\n\
         const inst = new WebAssembly.Instance(m, imports);\n\
         const rows = [{}].map(([a, b]) => [BigInt(a), BigInt(b)]);\n\
         const out = {}.map((n) => rows.map(([a, b]) => {{\n\
           try {{ return inst.exports[n](a, b).toString(); }} catch (e) {{ return null; }}\n\
         }}));\n\
         process.stdout.write(JSON.stringify(out));\n",
        rows.join(","),
        serde_json::to_string(names).unwrap()
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
    let cols: Vec<Vec<Option<String>>> = serde_json::from_slice(&out.stdout).expect("node JSON");
    Some(
        cols.into_iter()
            .map(|c| {
                c.into_iter()
                    .map(|v| v.map(|s| s.parse().expect("i64")))
                    .collect()
            })
            .collect(),
    )
}

/// Every function agrees with the interpreter on every input the interpreter
/// defines (and the interpreter defines most of them).
fn assert_agrees(tag: &str, bytes: &[u8], module: &Module, names: &[&str]) {
    let inputs = inputs();
    let Some(got) = run(bytes, names, &inputs) else {
        return;
    };
    let mut failures = Vec::new();
    for (name, col) in names.iter().zip(&got) {
        let mut defined = 0;
        for (&(a, b), have) in inputs.iter().zip(col) {
            let Some(want) = interpret(module, name, a, b) else {
                continue;
            };
            defined += 1;
            if *have != Some(want) {
                failures.push(format!(
                    "{name}({a}, {b}): interpreter {want}, wasm {have:?}"
                ));
            }
        }
        assert!(
            defined * 2 >= inputs.len(),
            "{tag}: the interpreter refused most inputs of {name}"
        );
    }
    assert!(
        failures.is_empty(),
        "{tag}: {} disagreements:\n{}",
        failures.len(),
        failures[..failures.len().min(30)].join("\n")
    );
}

/// The body of export `name`.
fn exported_body<'a>(bytes: &'a [u8], name: &str) -> wasmparser::FunctionBody<'a> {
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
    bodies.swap_remove(index)
}

/// Bytes of active data segments (the pooled constant images: the program
/// has no globals).
fn data_bytes(bytes: &[u8]) -> usize {
    let mut n = 0;
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::DataSection(r) = payload.expect("parse") {
            for d in r {
                n += d.expect("data").data.len();
            }
        }
    }
    n
}

/// `(global accesses, memory accesses, br_tables)` in the body of export
/// `name`.
fn shape(bytes: &[u8], name: &str) -> (usize, usize, usize) {
    use wasmparser::Operator as O;
    let body = exported_body(bytes, name);
    let (mut globals, mut memory, mut tables) = (0, 0, 0);
    for op in body.get_operators_reader().expect("ops").into_iter() {
        match op.expect("op") {
            O::GlobalGet { .. } | O::GlobalSet { .. } => globals += 1,
            O::I32Load { .. }
            | O::I64Load { .. }
            | O::I32Load8U { .. }
            | O::I32Load8S { .. }
            | O::I32Load16U { .. }
            | O::I32Load16S { .. }
            | O::I64Load8U { .. }
            | O::I64Load8S { .. }
            | O::I64Load16U { .. }
            | O::I64Load16S { .. }
            | O::I64Load32U { .. }
            | O::I64Load32S { .. }
            | O::I32Store { .. }
            | O::I64Store { .. }
            | O::I32Store8 { .. }
            | O::I32Store16 { .. }
            | O::I64Store8 { .. }
            | O::I64Store16 { .. }
            | O::I64Store32 { .. }
            | O::MemoryCopy { .. }
            | O::MemoryFill { .. } => memory += 1,
            O::BrTable { .. } => tables += 1,
            _ => {}
        }
    }
    (globals, memory, tables)
}

#[test]
fn pair_carried_functions_keep_no_frame_and_agree_with_the_interpreter() {
    let (module, functions) = program();
    let names: Vec<&str> = functions.iter().map(|(n, _)| *n).collect();

    let (o0, o0_evidence) = closed(&module, options(OptLevel::O0, true));
    assert!(!o0_evidence.local_emission.enabled);
    for &(name, _) in &functions {
        let (globals, memory, _) = shape(&o0, name);
        assert!(
            globals > 0 && memory > 0,
            "O0 `{name}` keeps its 128-bit values in a frame: {globals} global and {memory} \
             memory accesses"
        );
    }
    assert!(
        shape(&o0, "dispatch").2 > 0,
        "O0 `dispatch` is a dispatch loop"
    );
    assert!(
        selects(&o0, "const_shifts") > 0,
        "O0 `const_shifts` keeps the general shift sequence"
    );
    assert_agrees("O0", &o0, &module, &names);
    // O0 pools every 128-bit constant's image; a pair-carried one is two
    // `i64.const`s, so O2 lays out none.
    assert!(data_bytes(&o0) > 0, "O0 pools the 128-bit constants");

    for mid_end in [false, true] {
        let tag = if mid_end { "O2" } else { "O2 lane-only" };
        let (o2, evidence) = closed(&module, options(OptLevel::O2, mid_end));
        let summary = &evidence.local_emission;
        assert!(summary.enabled, "{tag}: {summary:?}");
        assert!(
            summary.fallbacks.is_empty(),
            "{tag}: the emission pass's validation fell back: {:?}",
            summary.fallbacks
        );
        for &(name, pure) in &functions {
            let (globals, memory, _) = shape(&o2, name);
            if pure == Pure::Lane || (mid_end && pure == Pure::MidEnd) {
                assert_eq!(
                    (globals, memory),
                    (0, 0),
                    "{tag} `{name}` carries every 128-bit value in pair locals: no frame and \
                     no memory access"
                );
            }
        }
        assert_eq!(data_bytes(&o2), 0, "{tag}: no pooled 128-bit constant");
        assert_eq!(
            selects(&o2, "const_shifts"),
            0,
            "{tag} `const_shifts` shifts by its constant amounts without the general form's \
             selects"
        );
        if !mid_end {
            assert!(
                shape(&o2, "dispatch").2 > 0,
                "{tag} `dispatch` is still a dispatch loop"
            );
            // `calls` keeps a frame only for the transient scratch slots of
            // its `sret` result and its two divisions.
            let (globals, _, _) = shape(&o2, "calls");
            assert!(globals > 0, "{tag} `calls` has a scratch frame");
        }
        assert_agrees(tag, &o2, &module, &names);
    }

    let (sized, _) = wasm::compile_sized_closed_module_with_evidence_license_options(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2, true),
    )
    .expect("compile the sized closed module");
    assert_agrees("sized O2", &sized, &module, &names);
}

#[test]
fn a_pair_carried_object_links_and_agrees() {
    let (module, functions) = program();
    let names: Vec<&str> = functions.iter().map(|(n, _)| *n).collect();
    // The object lane refuses a Rust-convention 128-bit signature at no link
    // boundary (two `i64` halves in, `sret` out, as rustc passes them); the
    // helpers are internal to the object either way.
    for mid_end in [false, true] {
        let (object, evidence) = wasm::compile_object_with_evidence_license_options(
            &module,
            &permit_unlicensed(),
            options(OptLevel::O2, mid_end),
        )
        .expect("compile the object");
        assert!(
            evidence.local_emission.fallbacks.is_empty(),
            "{:?}",
            evidence.local_emission.fallbacks
        );
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
        for &(name, pure) in &functions {
            if pure == Pure::Lane || (mid_end && pure == Pure::MidEnd) {
                assert_eq!(shape(&linked, name).0, 0, "linked O2 `{name}` has no frame");
            }
        }
        assert_agrees("linked O2", &linked, &module, &names);
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
