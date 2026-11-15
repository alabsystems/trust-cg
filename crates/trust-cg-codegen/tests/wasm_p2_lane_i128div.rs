// trust-cg-codegen/tests/wasm_p2_lane_i128div.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! 128-bit division and remainder in the wasm lane go through ONE trust-ir
//! helper per module (`wasm::divmod128_helper_name`), compiled by the lane
//! itself, with fast paths for 64-bit operands, a 64-bit divisor and a short
//! quotient.
//!
//! Pinned here:
//!
//! * every `udiv`/`urem`/`sdiv`/`srem` on `u128`/`i128`, run by node from a
//!   CLOSED module and from a LINKED relocatable object, computes what the
//!   trust-ir interpreter computes, over the edge classes (0, 1, all-ones,
//!   `MIN`, -1, powers of two and their neighbours at the 2^32 / 2^64 / 2^96
//!   boundaries, divisors larger than the dividend) and random operands of
//!   every bit length;
//! * on the inputs trust-ir leaves undefined (a zero divisor, `MIN / -1`),
//!   which the interpreter refuses, the lane still returns exactly what its
//!   earlier inline restoring loop returned (no trap is introduced);
//! * a closed module carries the helper once whatever the number of division
//!   sites; an object defines it as a weak hidden symbol, so several
//!   trust-cg objects (and an LLVM-compiled C object, when clang can target
//!   wasm32) link into one module with one copy and no symbol collision;
//! * a module that itself names the helper's symbol is refused as an object
//!   (`[TCG-WASM-SYMBOL]`). (`lower_function` without a provisioned helper
//!   fails closed: the lane's unit test
//!   `wide_division_calls_the_one_provisioned_helper`.)
//!
//! Node and `wasm-ld` ($WASM_LD) are needed for the execution legs; their
//! absence is a loud SKIP.

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::wasm;
use trust_ir::{
    InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty, parser,
};
use wasmparser::{KnownCustom, Linking, Name, Parser, Payload, SymbolInfo};

/// `WASM_SYM_BINDING_WEAK`.
const WEAK: u32 = 0x1;
/// `WASM_SYM_VISIBILITY_HIDDEN`.
const HIDDEN: u32 = 0x4;

const HEADER: &str = "; TrustIr text format v1\nmodule \"MOD\"\ntarget \"wasm32-unknown-unknown\" 4 \
                      little\n\nfuncty.0 = (i64, i64, i64, i64) -> (i64)\n\n";

/// `(name, trust-ir op, type, high half?)` of every division function.
fn division_functions(prefix: &str) -> Vec<(String, &'static str, &'static str, bool)> {
    let mut out = Vec::new();
    for (op, ty) in [
        ("udiv", "u128"),
        ("urem", "u128"),
        ("sdiv", "i128"),
        ("srem", "i128"),
    ] {
        for high in [false, true] {
            let half = if high { "hi" } else { "lo" };
            out.push((format!("{prefix}{op}_{half}"), op, ty, high));
        }
    }
    out
}

/// `n = ah:al`, `d = bh:bl`; return the low or high half of `n op d`.
fn division_body(name: &str, op: &str, ty: &str, high: bool) -> String {
    let fold = if high {
        format!("    %rs = lshr {ty} %r, %c64\n    %out = trunc {ty} %rs to i64\n")
    } else {
        format!("    %out = trunc {ty} %r to i64\n")
    };
    format!(
        "fn @{name}(functy.0) {{\nbb0(%0: i64, %1: i64, %2: i64, %3: i64):\n\
         %c64 = const {ty} 64\n\
         %nl = zext i64 %0 to {ty}\n    %nh0 = zext i64 %1 to {ty}\n    %nh = shl {ty} %nh0, %c64\n\
         %n = or {ty} %nh, %nl\n\
         %dl = zext i64 %2 to {ty}\n    %dh0 = zext i64 %3 to {ty}\n    %dh = shl {ty} %dh0, %c64\n\
         %d = or {ty} %dh, %dl\n\
         %r = {op} {ty} %n, %d\n{fold}    ret %out\n}}\n\n"
    )
}

/// Number `%name` values per function (the text format's `%N` spelling).
fn number_values(text: &str) -> String {
    use std::collections::HashMap;
    let mut out = String::new();
    let mut values: HashMap<String, usize> = HashMap::new();
    for line in text.lines() {
        if line.starts_with("fn ") {
            values.clear();
            // Parameters are `%0..%3`.
            for i in 0..4 {
                values.insert(i.to_string(), i);
            }
        }
        let bytes = line.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'%' {
                let mut j = i + 1;
                while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
                    j += 1;
                }
                let n = values.len();
                let id = *values.entry(line[i + 1..j].to_string()).or_insert(n);
                let _ = write!(out, "%{id}");
                i = j;
            } else {
                out.push(bytes[i] as char);
                i += 1;
            }
        }
        out.push('\n');
    }
    out
}

fn module_text(module_name: &str, prefix: &str, extra: &str) -> (String, Vec<String>) {
    let mut text = HEADER.replace("MOD", module_name);
    let mut names = Vec::new();
    for (name, op, ty, high) in division_functions(prefix) {
        text.push_str(&division_body(&name, op, ty, high));
        names.push(name);
    }
    text.push_str(extra);
    (number_values(&text), names)
}

fn parse(text: &str) -> Module {
    parser::parse_module(text).unwrap_or_else(|e| panic!("parse: {e}\n{text}"))
}

/// The lane's result for `n op d`, including the inputs trust-ir leaves
/// undefined: a zero divisor gives an all-ones quotient and the dividend as
/// remainder (signed: of the magnitudes, then negated), and `MIN / -1` gives
/// `MIN`, remainder 0 — what the inline restoring loop computed before the
/// helper replaced it.
fn reference(op: &str, n: u128, d: u128) -> u128 {
    match op {
        "udiv" => n.checked_div(d).unwrap_or(u128::MAX),
        "urem" => n.checked_rem(d).unwrap_or(n),
        "sdiv" | "srem" => {
            let (a, b) = (n as i128, d as i128);
            if b == 0 {
                if op == "srem" {
                    n
                } else if a < 0 {
                    1
                } else {
                    u128::MAX
                }
            } else if a == i128::MIN && b == -1 {
                if op == "srem" { 0 } else { n }
            } else if op == "sdiv" {
                (a / b) as u128
            } else {
                (a % b) as u128
            }
        }
        other => panic!("{other}"),
    }
}

/// Edge classes crossed, then random operands of random bit lengths.
fn inputs() -> Vec<(u128, u128)> {
    let mut edges: Vec<u128> = vec![0, 1, 2, 3, 7, 10, u128::MAX, u128::MAX - 1];
    for k in [31u32, 32, 33, 63, 64, 65, 95, 96, 127] {
        let p = 1u128 << k;
        edges.extend([p - 1, p, p + 1, p.wrapping_neg()]);
    }
    edges.extend([
        0xffff_ffff_0000_0001,
        0x8000_0000_0000_0001,
        0x8000_0000_ffff_ffff_ffff_ffff_ffff_ffff,
        0x1234_5678_9abc_def0_0fed_cba9_8765_4321,
    ]);
    let mut out = Vec::new();
    for &n in &edges {
        for &d in &edges {
            out.push((n, d));
        }
    }
    let mut s: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    for _ in 0..3000 {
        let operand = |next: &mut dyn FnMut() -> u64| {
            let bits = next() % 129;
            let v = (u128::from(next()) << 64) | u128::from(next());
            let v = if bits == 128 {
                v
            } else {
                v & ((1u128 << bits) - 1)
            };
            // Half of them negative, so signed division sees every sign pair.
            if next() & 1 == 1 { v.wrapping_neg() } else { v }
        };
        let n = operand(&mut next);
        let d = operand(&mut next);
        out.push((n, d));
    }
    out
}

fn halves(v: u128) -> [i64; 2] {
    [v as u64 as i64, (v >> 64) as u64 as i64]
}

fn interpret(module: &Module, name: &str, n: u128, d: u128) -> Option<i64> {
    let f = module.function_by_name(name).expect("function");
    let [nl, nh] = halves(n);
    let [dl, dh] = halves(d);
    let args: Vec<_> = [nl, nh, dl, dh]
        .iter()
        .map(|&v| InterpretValue::int(Ty::I64, i128::from(v)).unwrap())
        .collect();
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 100_000,
            max_call_depth: 8,
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
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|d| d.join("node"))
        .find(|p| p.is_file())
}

fn wasm_ld() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("WASM_LD").filter(|p| !p.is_empty()) {
        return Some(PathBuf::from(p));
    }
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|d| d.join("wasm-ld"))
        .find(|p| p.is_file())
}

fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_wasm_p2div_{tag}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run every `names` function on every input under node; `None` is a trap.
fn run(
    tag: &str,
    bytes: &[u8],
    names: &[String],
    inputs: &[(u128, u128)],
) -> Vec<Vec<Option<i64>>> {
    let node = node().expect("node");
    let dir = scratch(tag);
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    std::fs::write(
        dir.join("run.js"),
        "const fs = require('fs');\n\
         const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
         const inst = new WebAssembly.Instance(m, {});\n\
         const names = JSON.parse(fs.readFileSync(process.argv[3]));\n\
         const inputs = JSON.parse(fs.readFileSync(process.argv[4])).map(r => r.map(BigInt));\n\
         const out = names.map(n => inputs.map(a => { try { return inst.exports[n](...a).toString(); } catch (e) { return null; } }));\n\
         process.stdout.write(JSON.stringify(out));\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("names.json"),
        serde_json::to_string(names).unwrap(),
    )
    .unwrap();
    let rows: Vec<[String; 4]> = inputs
        .iter()
        .map(|&(n, d)| {
            let [a, b] = halves(n);
            let [c, e] = halves(d);
            [a.to_string(), b.to_string(), c.to_string(), e.to_string()]
        })
        .collect();
    std::fs::write(
        dir.join("inputs.json"),
        serde_json::to_string(&rows).unwrap(),
    )
    .unwrap();
    let out = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .arg(dir.join("names.json"))
        .arg(dir.join("inputs.json"))
        .output()
        .expect("run node");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.status.success(),
        "node failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let cols: Vec<Vec<Option<String>>> = serde_json::from_slice(&out.stdout).expect("node JSON");
    cols.into_iter()
        .map(|c| {
            c.into_iter()
                .map(|v| v.map(|s| s.parse().unwrap()))
                .collect()
        })
        .collect()
}

/// Compare node's columns with the interpreter (where it runs) and with the
/// lane's exact result everywhere. Returns (interpreter checks, UB checks).
fn compare(
    tag: &str,
    module: &Module,
    names: &[String],
    inputs: &[(u128, u128)],
    got: &[Vec<Option<i64>>],
) -> (usize, usize) {
    let (mut defined, mut undefined) = (0, 0);
    let mut failures = Vec::new();
    for (col, name) in got.iter().zip(names) {
        let op = ["udiv", "urem", "sdiv", "srem"]
            .into_iter()
            .find(|o| name.contains(&format!("{o}_")))
            .unwrap_or_else(|| panic!("op of {name}"));
        let high = name.ends_with("_hi");
        for (&(n, d), &wasm_v) in inputs.iter().zip(col) {
            let exact = halves(reference(op, n, d))[usize::from(high)];
            match interpret(module, name, n, d) {
                Some(want) => {
                    // The reference agrees with the interpreter wherever
                    // trust-ir defines the operation.
                    assert_eq!(
                        want, exact,
                        "reference vs interpreter: {name}({n:#x}, {d:#x})"
                    );
                    defined += 1;
                }
                None => undefined += 1,
            }
            if wasm_v != Some(exact) {
                failures.push(format!(
                    "{name}({n:#x}, {d:#x}): want {exact:#x}, wasm {wasm_v:?}"
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "[{tag}] {} divergences:\n{}",
        failures.len(),
        failures[..failures.len().min(40)].join("\n")
    );
    (defined, undefined)
}

fn validate(bytes: &[u8]) {
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("does not validate: {e}"));
    let verdict = trust_cg_verify::wasm_cfg_proofs::check_module_structure(bytes);
    assert!(verdict.holds(), "CFG structural invariant: {verdict}");
}

/// Defined-function count of a module (code-section bodies).
fn body_count(bytes: &[u8]) -> u32 {
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::CodeSectionStart { count, .. } = payload.expect("parse") {
            return count;
        }
    }
    0
}

/// `(name, flags)` of every function symbol of an object.
fn function_symbols(bytes: &[u8]) -> Vec<(String, u32)> {
    let mut out = Vec::new();
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::CustomSection(c) = payload.expect("parse")
            && let KnownCustom::Linking(linking) = c.as_known()
        {
            for sub in linking.subsections() {
                if let Linking::SymbolTable(map) = sub.expect("linking") {
                    for info in map {
                        if let SymbolInfo::Func { flags, name, .. } = info.expect("symbol") {
                            out.push((name.unwrap_or_default().to_string(), flags.bits()));
                        }
                    }
                }
            }
        }
    }
    out
}

/// Function names a linked module's `name` section gives, and its exports.
fn linked_names(bytes: &[u8]) -> (Vec<String>, Vec<String>) {
    let (mut names, mut exports) = (Vec::new(), Vec::new());
    for payload in Parser::new(0).parse_all(bytes) {
        match payload.expect("parse") {
            Payload::ExportSection(r) => {
                for e in r {
                    exports.push(e.expect("export").name.to_string());
                }
            }
            Payload::CustomSection(c) => {
                if let KnownCustom::Name(r) = c.as_known() {
                    for sub in r {
                        if let Name::Function(map) = sub.expect("name subsection") {
                            for n in map {
                                names.push(n.expect("name").name.to_string());
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    (names, exports)
}

fn link(tag: &str, objects: &[Vec<u8>]) -> Vec<u8> {
    let dir = scratch(tag);
    let mut cmd = Command::new(wasm_ld().expect("wasm-ld"));
    cmd.args(["--no-entry", "--export-dynamic"]);
    for (i, bytes) in objects.iter().enumerate() {
        let path = dir.join(format!("in{i}.o"));
        std::fs::write(&path, bytes).unwrap();
        cmd.arg(path);
    }
    let out = dir.join("out.wasm");
    let run = cmd.arg("-o").arg(&out).output().expect("run wasm-ld");
    assert!(
        run.status.success(),
        "wasm-ld failed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let bytes = std::fs::read(&out).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    bytes
}

/// The helper's symbol is reserved and pinned to the helper's text.
#[test]
fn helper_symbol_is_reserved_and_digest_pinned() {
    let name = wasm::divmod128_helper_name();
    let digest = name
        .strip_prefix("__tcg_divmod128_")
        .expect("reserved prefix");
    assert_eq!(digest.len(), 16, "{name}");
    assert!(digest.bytes().all(|b| b.is_ascii_hexdigit()), "{name}");
}

/// A closed module computes every 128-bit division exactly as the
/// interpreter (and, on undefined inputs, exactly as before), and carries
/// the helper ONCE for its eight division sites plus a ninth function with
/// four more.
#[test]
fn closed_module_agrees_with_the_interpreter_and_carries_one_helper() {
    let mix = "fn @mix(functy.0) {\nbb0(%0: i64, %1: i64, %2: i64, %3: i64):\n\
               %c1 = const u128 1\n    %a = zext i64 %0 to u128\n    %b0 = zext i64 %2 to u128\n\
               %b = or u128 %b0, %c1\n    %q = udiv u128 %a, %b\n    %r = urem u128 %a, %b\n\
               %sa = bitcast u128 %a to i128\n    %sb = bitcast u128 %b to i128\n\
               %sq = sdiv i128 %sa, %sb\n    %sr = srem i128 %sa, %sb\n\
               %x0 = xor u128 %q, %r\n    %sx = xor i128 %sq, %sr\n    %ux = bitcast i128 %sx to u128\n\
               %x = xor u128 %x0, %ux\n    %out = trunc u128 %x to i64\n    ret %out\n}\n";
    let (text, mut names) = module_text("p2div_closed", "c_", mix);
    let module = parse(&text);
    let bytes = wasm::compile_module_with_license(&module, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile: {e}"));
    validate(&bytes);
    assert_eq!(
        body_count(&bytes),
        names.len() as u32 + 2,
        "the closed module carries the eight division functions, `mix`, and ONE helper"
    );
    if node().is_none() {
        eprintln!("SKIP closed_module_agrees_with_the_interpreter: node not on PATH");
        return;
    }
    let inputs = inputs();
    let got = run("closed", &bytes, &names, &inputs);
    let (defined, undefined) = compare("closed", &module, &names, &inputs, &got);
    assert!(
        defined > 30_000 && undefined > 500,
        "{defined} / {undefined}"
    );
    // `mix` against the interpreter (its divisor is odd, so always defined).
    names = vec!["mix".to_string()];
    let got = run("closed_mix", &bytes, &names, &inputs);
    for (&(n, d), &v) in inputs.iter().zip(&got[0]) {
        assert_eq!(v, interpret(&module, "mix", n, d), "mix({n:#x}, {d:#x})");
    }
    eprintln!("closed: {defined} interpreter checks, {undefined} undefined-input checks agree");
}

/// The same functions through the relocatable-object lane, linked by
/// `wasm-ld`: the object DEFINES the helper as a weak hidden function, and
/// the linked module computes exactly what the closed one does.
#[test]
fn linked_object_agrees_with_the_interpreter() {
    let (text, names) = module_text("p2div_object", "o_", "");
    let module = parse(&text);
    let object = wasm::compile_object_with_license(&module, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("object: {e}"));
    let helper = wasm::divmod128_helper_name();
    let syms = function_symbols(&object);
    let found: Vec<_> = syms.iter().filter(|(n, _)| *n == helper).collect();
    assert_eq!(found.len(), 1, "one helper symbol in {syms:?}");
    assert_eq!(
        found[0].1,
        WEAK | HIDDEN,
        "the helper is a weak hidden DEFINITION"
    );
    if node().is_none() || wasm_ld().is_none() {
        eprintln!("SKIP linked_object_agrees_with_the_interpreter: needs node and wasm-ld");
        return;
    }
    let linked = link("object", &[object]);
    validate(&linked);
    let (_, exports) = linked_names(&linked);
    assert!(!exports.contains(&helper), "hidden: not exported");
    let inputs = inputs();
    let got = run("object", &linked, &names, &inputs);
    let (defined, undefined) = compare("object", &module, &names, &inputs, &got);
    eprintln!("object: {defined} interpreter checks, {undefined} undefined-input checks agree");
}

/// Two trust-cg objects that both divide 128-bit integers, plus an
/// LLVM-compiled C object calling into both, link into one module with ONE
/// helper copy and no duplicate-symbol error, and every function still
/// agrees.
#[test]
fn several_objects_link_with_one_helper_copy() {
    let (text_a, names_a) = module_text("p2div_a", "a_", "");
    let (text_b, names_b) = module_text("p2div_b", "b_", "");
    let (module_a, module_b) = (parse(&text_a), parse(&text_b));
    let obj_a = wasm::compile_object_with_license(&module_a, &permit_unlicensed()).unwrap();
    let obj_b = wasm::compile_object_with_license(&module_b, &permit_unlicensed()).unwrap();
    if node().is_none() || wasm_ld().is_none() {
        eprintln!("SKIP several_objects_link_with_one_helper_copy: needs node and wasm-ld");
        return;
    }
    let mut objects = vec![obj_a, obj_b];
    // An LLVM object beside them, when clang can target wasm32.
    let c_dir = scratch("c");
    let c_src = c_dir.join("c.c");
    std::fs::write(
        &c_src,
        "long long a_udiv_lo(long long, long long, long long, long long);\n\
         long long b_srem_hi(long long, long long, long long, long long);\n\
         static long long twice(long long x) { return x * 2; }\n\
         __attribute__((visibility(\"default\"))) long long c_mix(long long a, long long b) {\n\
           return twice(a_udiv_lo(a, 0, b | 1, 0)) ^ b_srem_hi(a, -1, b | 1, 0);\n\
         }\n",
    )
    .unwrap();
    let c_obj = c_dir.join("c.o");
    let llvm = Command::new("clang")
        .args(["--target=wasm32-unknown-unknown", "-O2", "-c"])
        .arg(&c_src)
        .arg("-o")
        .arg(&c_obj)
        .output();
    let with_c = match llvm {
        Ok(o) if o.status.success() => {
            objects.push(std::fs::read(&c_obj).unwrap());
            true
        }
        _ => {
            eprintln!(
                "SKIP the LLVM leg of several_objects_link_with_one_helper_copy: clang cannot target wasm32"
            );
            false
        }
    };
    let _ = std::fs::remove_dir_all(&c_dir);
    let linked = link("multi", &objects);
    validate(&linked);
    let helper = wasm::divmod128_helper_name();
    let (fnames, exports) = linked_names(&linked);
    assert_eq!(
        fnames.iter().filter(|n| **n == helper).count(),
        1,
        "one helper copy in the linked module: {fnames:?}"
    );
    assert!(!exports.contains(&helper));
    let inputs = inputs();
    let got_a = run("multi_a", &linked, &names_a, &inputs);
    compare("multi_a", &module_a, &names_a, &inputs, &got_a);
    let got_b = run("multi_b", &linked, &names_b, &inputs);
    compare("multi_b", &module_b, &names_b, &inputs, &got_b);
    if with_c {
        let node = node().unwrap();
        let dir = scratch("c_run");
        std::fs::write(dir.join("m.wasm"), &linked).unwrap();
        let js = "const fs = require('fs');\n\
                  const E = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[2])), {}).exports;\n\
                  const out = [];\n\
                  for (const a of [0n, 1n, 12345678901234n, -5n]) for (const b of [0n, 7n, 1000n]) out.push(E.c_mix(a, b).toString());\n\
                  process.stdout.write(JSON.stringify(out));\n";
        std::fs::write(dir.join("run.js"), js).unwrap();
        let out = Command::new(node)
            .arg(dir.join("run.js"))
            .arg(dir.join("m.wasm"))
            .output()
            .unwrap();
        let _ = std::fs::remove_dir_all(&dir);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let got: Vec<String> = serde_json::from_slice(&out.stdout).unwrap();
        let mut want = Vec::new();
        for a in [0i64, 1, 12_345_678_901_234, -5] {
            for b in [0i64, 7, 1000] {
                let d = u128::from((b | 1) as u64);
                let q = (u128::from(a as u64) / d) as u64 as i64;
                let n = ((-1i128 as u128) << 64 | u128::from(a as u64)) as i128;
                let r = ((n % d as i128) >> 64) as i64;
                want.push((q.wrapping_mul(2) ^ r).to_string());
            }
        }
        assert_eq!(got, want, "C caller through the linked trust-cg objects");
    }
}

/// An object whose module names the helper's symbol — as a function or as a
/// global, defined or declared — or any other name under the reserved
/// prefix is refused, WHETHER OR NOT the module divides: a frontend may put
/// the division and a definition that would replace the weak helper into
/// two different objects of one link (the bridge's per-function fallback).
#[test]
fn module_naming_the_helper_symbol_is_refused_as_an_object() {
    let helper = wasm::divmod128_helper_name();
    let own = format!(
        "fn @{helper}(functy.0) {{\nbb0(%0: i64, %1: i64, %2: i64, %3: i64):\n    ret %0\n}}\n"
    );
    let (text, _) = module_text("p2div_clash", "x_", &own);
    let err = wasm::compile_object_with_license(&parse(&text), &permit_unlicensed())
        .expect_err("helper-name clash");
    let msg = err.to_string();
    assert!(
        msg.contains("[TCG-WASM-SYMBOL]") && msg.contains(&helper),
        "{msg}"
    );

    let (mut text, _) = module_text("p2div_clash_g", "y_", "");
    text = text.replacen(
        "functy.0 =",
        &format!("global mut @{helper} u32 = 0\n\nfuncty.0 ="),
        1,
    );
    let err = wasm::compile_object_with_license(&parse(&text), &permit_unlicensed())
        .expect_err("helper-name global clash");
    assert!(err.to_string().contains("[TCG-WASM-SYMBOL]"), "{err}");

    // Without a 128-bit division this object carries no helper, but its
    // strong definition would still replace another object's weak copy.
    let text = number_values(&format!("{}{own}", HEADER.replace("MOD", "p2div_nodiv")));
    let err = wasm::compile_object_with_license(&parse(&text), &permit_unlicensed())
        .expect_err("reserved name without division");
    let msg = err.to_string();
    assert!(
        msg.contains("[TCG-WASM-SYMBOL]") && msg.contains(&helper),
        "{msg}"
    );

    // Any name under the prefix (another digest), with any linkage.
    let other = format!("{}0000000000000000", wasm::DIVMOD128_SYMBOL_PREFIX);
    assert_ne!(other, helper);
    let text = number_values(&format!(
        "{}fn @{other}(functy.0) {{\nbb0(%0: i64, %1: i64, %2: i64, %3: i64):\n    ret %0\n}}\n",
        HEADER.replace("MOD", "p2div_other")
    ));
    let err = wasm::compile_object_with_license(&parse(&text), &permit_unlicensed())
        .expect_err("other reserved name");
    assert!(err.to_string().contains("[TCG-WASM-SYMBOL]"), "{err}");

    // A body-less declaration of the helper would bind to another object's
    // hidden copy.
    let mut module = parse(&number_values(&format!(
        "{}{own}",
        HEADER.replace("MOD", "p2div_decl")
    )));
    module.functions[0].blocks.clear();
    let err = wasm::compile_object_with_license(&module, &permit_unlicensed())
        .expect_err("declaration of the helper");
    assert!(err.to_string().contains("[TCG-WASM-SYMBOL]"), "{err}");

    // A name that merely resembles the prefix is not reserved.
    let text = number_values(&format!(
        "{}fn @tcg_divmod128_x(functy.0) {{\nbb0(%0: i64, %1: i64, %2: i64, %3: i64):\n    ret %0\n}}\n",
        HEADER.replace("MOD", "p2div_free")
    ));
    wasm::compile_object_with_license(&parse(&text), &permit_unlicensed())
        .expect("an unreserved name compiles");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
