// trust-cg-codegen/tests/wasm_g3_lane_frames.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Frames, locals and the shadow stack of the wasm lane, against the trust-ir
//! reference interpreter (run by node for the wasm side) or exact expected
//! values:
//!
//! * a by-address aggregate ENTRY parameter that a branch back to the entry
//!   block rebinds lives in the callee's own frame — the caller's aggregate, a
//!   field of an enclosing aggregate, a pooled constant, and a second parameter
//!   bound to the same value are never written;
//! * an `Alloca` that runs repeatedly yields a fresh allocation each time
//!   whenever an earlier one's pointer may still be observed, and keeps one
//!   fixed slot when it provably cannot be (so a long loop does not grow the
//!   stack);
//! * in a closed module, a stack that would run into static data traps
//!   instead of overwriting it, also after an earlier trap left the stack
//!   pointer lowered;
//! * home slots are reused by liveness and the bridge's write-through
//!   `insertfield` owns no home, so frames stay near the program's live data;
//! * locals are reused by liveness, and a function no engine would compile is
//!   refused by name;
//! * a zero-byte `memcopy` / `memset` is a no-op even through a pointer past
//!   the end of memory (trust-ir defines it so; wasm's `memory.copy` /
//!   `memory.fill` would trap on the range end), while a nonzero count still
//!   copies and fills.
//!
//! Node is required to execute the wasm; its absence is a loud SKIP.

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::wasm;
use trust_ir::{
    InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty, parser,
};

const HEADER: &str = "; TrustIr text format v1\nmodule \"g3\"\ntarget \"wasm32-unknown-unknown\" 4 \
                      little\n\n";

/// Rename `%name` values and `bbname` blocks to the text format's numeric
/// spellings, per function, in order of first appearance.
fn number_names(text: &str) -> String {
    use std::collections::HashMap;
    let mut out = String::with_capacity(text.len());
    let mut values: HashMap<String, usize> = HashMap::new();
    let mut blocks: HashMap<String, usize> = HashMap::new();
    for line in text.lines() {
        if line.starts_with("fn ")
            || line.starts_with("internal fn ")
            || line.starts_with("rustcc fn ")
        {
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

fn parse(text: &str) -> Module {
    let text = number_names(text);
    parser::parse_module(&text).unwrap_or_else(|e| {
        let numbered: String = text
            .lines()
            .enumerate()
            .map(|(i, l)| format!("{:4} {l}\n", i + 1))
            .collect();
        panic!("test module failed to parse: {e}\n{numbered}")
    })
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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_g3_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn validate(bytes: &[u8]) {
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
}

/// The interpreter's answer for `(i64, i64) -> i64` function `name`, or `None`
/// when the reference execution refuses the input.
fn interpret(module: &Module, name: &str, a: i64, b: i64) -> Option<i64> {
    let f = module.function_by_name(name).expect("function");
    let arg = |v: i64| InterpretValue::int(Ty::I64, i128::from(v)).expect("i64 value");
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 50_000_000,
            max_call_depth: 256,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, vec![arg(a), arg(b)])
        .ok()?;
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => Some(i.as_signed() as i64),
        other => panic!("{name} returned {other:?}"),
    }
}

/// Run `(i64, i64) -> i64` export `name` over `inputs` in ONE instance, in
/// order (so a corruption one call leaves behind is seen by the next). `None`
/// is a trap. `None` for the whole column when node is absent.
fn run_wasm(bytes: &[u8], name: &str, inputs: &[(i64, i64)]) -> Option<Vec<Option<i64>>> {
    let node = node()?;
    let dir = scratch("run");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let js = "const fs = require('fs');\n\
              const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
              const inst = new WebAssembly.Instance(m, {});\n\
              const f = inst.exports[process.argv[3]];\n\
              const inputs = JSON.parse(fs.readFileSync(process.argv[4]));\n\
              const out = inputs.map(([a, b]) => { try { return f(BigInt(a), BigInt(b)).toString(); } \
              catch (e) { if (e instanceof WebAssembly.RuntimeError) return null; throw e; } });\n\
              process.stdout.write(JSON.stringify(out));\n";
    std::fs::write(dir.join("run.js"), js).unwrap();
    let pairs: Vec<[String; 2]> = inputs
        .iter()
        .map(|(a, b)| [a.to_string(), b.to_string()])
        .collect();
    std::fs::write(
        dir.join("inputs.json"),
        serde_json::to_string(&pairs).unwrap(),
    )
    .unwrap();
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
            .map(|v| v.map(|s| s.parse::<i64>().unwrap()))
            .collect(),
    )
}

/// Link a relocatable object into a runnable module (every definition
/// exported). `None` when no linker is available.
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

/// Seeded inputs: small edge values crossed.
fn inputs() -> Vec<(i64, i64)> {
    let edges: [i64; 10] = [0, 1, -1, 2, 3, 7, -8, 1000, i64::MAX, i64::MIN];
    edges
        .iter()
        .flat_map(|&a| edges.iter().map(move |&b| (a, b)))
        .collect()
}

/// Every named function agrees with the interpreter on every input, in the
/// closed module and (with a linker) through the relocatable-object lane.
/// Returns the number of checks.
fn assert_agrees(module: &Module, names: &[&str], inputs: &[(i64, i64)]) -> usize {
    let closed = wasm::compile_module_with_license(module, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile_module: {e}"));
    validate(&closed);
    let object = wasm::compile_object_with_license(&c_spelling(module), &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile_object: {e}"));
    let linked = link(&object);
    let mut checks = 0;
    for name in names {
        let want: Vec<Option<i64>> = inputs
            .iter()
            .map(|&(a, b)| interpret(module, name, a, b))
            .collect();
        assert!(
            want.iter().filter(|v| v.is_some()).count() * 2 >= inputs.len(),
            "the interpreter refused most inputs of {name}"
        );
        for (tag, bytes) in [("closed", Some(&closed)), ("object", linked.as_ref())] {
            let Some(bytes) = bytes else {
                eprintln!("SKIP {name} [{tag}]: no wasm-ld (set WASM_LD)");
                continue;
            };
            let Some(got) = run_wasm(bytes, name, inputs) else {
                eprintln!("SKIP {name} [{tag}]: node not on PATH");
                continue;
            };
            for (i, w) in want.iter().enumerate() {
                let Some(w) = w else { continue };
                checks += 1;
                assert_eq!(
                    got[i],
                    Some(*w),
                    "{name}{:?} [{tag}]: interpreter {w}, wasm {:?}",
                    inputs[i],
                    got[i]
                );
            }
        }
    }
    checks
}

/// The locals count and the prologue's frame size of export `name` of a
/// closed module.
fn function_shape(bytes: &[u8], name: &str) -> (u64, Option<i32>) {
    let mut index = None;
    let mut bodies = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        match payload.expect("parse") {
            wasmparser::Payload::ImportSection(_) => panic!("a closed module imports nothing"),
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
    let index = index.unwrap_or_else(|| panic!("no export {name}"));
    let body = &bodies[index as usize];
    let mut locals = 0u64;
    for l in body.get_locals_reader().expect("locals") {
        locals += u64::from(l.expect("local").0);
    }
    let ops: Vec<wasmparser::Operator<'_>> = body
        .get_operators_reader()
        .expect("ops")
        .into_iter()
        .take(4)
        .map(|o| o.expect("op"))
        .collect();
    // The prologue saves the stack pointer and subtracts the frame size; the
    // emission pass may merge its `local.set; local.get` into a `local.tee`.
    let frame = match ops.as_slice() {
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
        ] => Some(*value),
        _ => None,
    };
    (locals, frame)
}

// ---- A by-address entry parameter rebound by a branch back to the entry ----

const ENTRY_BACKEDGE: &str = r#"
struct @P { : i64 @0, : i64 @8 } size=16 align=8 id=0
struct @Q { : struct.0 @0, : i64 @16 } size=24 align=8 id=1
struct @W { : u128 @0, : u32 @16 } size=32 align=16 id=2

functy.0 = (i64, i64) -> (i64)
functy.1 = (struct.0, i64) -> (i64)
functy.2 = (struct.0, struct.0, i64) -> (i64)
functy.3 = (struct.2, i32) -> (u128)

fn @reenter(functy.1) {
bbentry(%p: struct.0, %n: i64):
    %zero = const i64 0
    %done = icmp eq i64 %n, %zero
    condbr %done, bbout, bbagain
bbagain:
    %one = const i64 1
    %m = sub i64 %n, %one
    %q = make_aggregate struct.0 (%n, %m)
    br bbentry(%q, %m)
bbout:
    %r = extractfield i64 %p, 0
    ret %r
}

fn @swap(functy.2) {
bbentry(%x: struct.0, %y: struct.0, %n: i64):
    %zero = const i64 0
    %done = icmp sle i64 %n, %zero
    condbr %done, bbout, bbagain
bbagain:
    %one = const i64 1
    %m = sub i64 %n, %one
    %x0 = extractfield i64 %x, 0
    %x1 = add i64 %x0, %one
    %xx = insertfield struct.0 %x, 0, %x1
    br bbentry(%y, %xx, %m)
bbout:
    %a = extractfield i64 %x, 0
    %b = extractfield i64 %y, 1
    %c7 = const i64 7
    %b7 = mul i64 %b, %c7
    %r = add i64 %a, %b7
    ret %r
}

fn @wideloop(functy.3) {
bbentry(%w: struct.2, %n: i32):
    %zero = const i32 0
    %done = icmp sle i32 %n, %zero
    condbr %done, bbout, bbagain
bbagain:
    %one = const i32 1
    %m = sub i32 %n, %one
    %v = extractfield u128 %w, 0
    %c5 = const u128 5
    %v5 = mul u128 %v, %c5
    %ww = insertfield struct.2 %w, 0, %v5
    br bbentry(%ww, %m)
bbout:
    %r = extractfield u128 %w, 0
    ret %r
}

fn @d_reenter(functy.0) {
bbentry(%a: i64, %b: i64):
    %c3 = const i64 3
    %n = and i64 %b, %c3
    %p = make_aggregate struct.0 (%a, %b)
    %r = call @func.0(%p, %n)
    %p0 = extractfield i64 %p, 0
    %p1 = extractfield i64 %p, 1
    %c31 = const i64 31
    %p131 = mul i64 %p1, %c31
    %s = xor i64 %p0, %p131
    %t = add i64 %s, %r
    ret %t
}

fn @d_swap(functy.0) {
bbentry(%a: i64, %b: i64):
    %c3 = const i64 3
    %n = and i64 %b, %c3
    %p = make_aggregate struct.0 (%a, %b)
    %q = make_aggregate struct.0 (%b, %a)
    %r = call @func.1(%p, %q, %n)
    %p0 = extractfield i64 %p, 0
    %q1 = extractfield i64 %q, 1
    %c1000 = const i64 1000
    %m = mul i64 %p0, %c1000
    %s = add i64 %m, %q1
    %t = xor i64 %s, %r
    ret %t
}

fn @d_self_alias(functy.0) {
bbentry(%a: i64, %b: i64):
    %c3 = const i64 3
    %n = and i64 %b, %c3
    %p = make_aggregate struct.0 (%a, %b)
    %r = call @func.1(%p, %p, %n)
    %p1 = extractfield i64 %p, 1
    %t = add i64 %r, %p1
    ret %t
}

fn @d_field_alias(functy.0) {
bbentry(%a: i64, %b: i64):
    %c3 = const i64 3
    %n = and i64 %b, %c3
    %p = make_aggregate struct.0 (%a, %b)
    %q = make_aggregate struct.1 (%p, %a)
    %f = extractfield struct.0 %q, 0
    %r = call @func.0(%f, %n)
    %g = extractfield struct.0 %q, 0
    %g1 = extractfield i64 %g, 1
    %g0 = extractfield i64 %g, 0
    %s = add i64 %g1, %r
    %t = xor i64 %s, %g0
    ret %t
}

fn @d_const_pool(functy.0) {
bbentry(%a: i64, %b: i64):
    %c3 = const i64 3
    %n = and i64 %b, %c3
    %c = const struct.0 { 11, 22 }
    %r = call @func.0(%c, %n)
    %c0 = extractfield i64 %c, 0
    %c1 = extractfield i64 %c, 1
    %c100 = const i64 100
    %m = mul i64 %c0, %c100
    %s = add i64 %m, %c1
    %t = add i64 %s, %r
    ret %t
}

fn @d_wide(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = zext i64 %a to u128
    %bi = trunc i64 %b to i32
    %c7 = const i32 7
    %n = and i32 %bi, %c7
    %nine = const u32 9
    %w = make_aggregate struct.2 (%x, %nine)
    %r = call @func.2(%w, %n)
    %w0 = extractfield u128 %w, 0
    %s = add u128 %r, %w0
    %t = trunc u128 %s to i64
    ret %t
}
"#;

/// The object lane refuses a `CallingConv::Rust` aggregate at a link
/// boundary (rustc's own Rust ABI for it differs from this lane's), while the
/// lane lowers the two conventions identically: the linked object is
/// compiled from the module's C spelling, and the interpreter keeps the
/// original.
fn c_spelling(module: &Module) -> Module {
    let mut m = module.clone();
    for f in &mut m.functions {
        f.calling_conv = trust_ir::CallingConv::C;
        for node in f.blocks.iter_mut().flat_map(|b| b.body.iter_mut()) {
            if let trust_ir::Inst::CallIndirect { calling_conv, .. } = &mut node.inst {
                *calling_conv = trust_ir::CallingConv::C;
            }
        }
    }
    m
}

#[test]
fn entry_backedge_by_address_parameters_never_write_the_callers_storage() {
    let module = parse(&format!("{HEADER}{ENTRY_BACKEDGE}"));
    let names = [
        "d_reenter",
        "d_swap",
        "d_self_alias",
        "d_field_alias",
        "d_const_pool",
        "d_wide",
    ];
    let checks = assert_agrees(&module, &names, &inputs());
    eprintln!("entry back-edge: {checks} checks agree");
}

/// The staged edge copy of a re-entered entry needs a frame even when nothing
/// else in the module does (it was refused for want of a stack pointer).
#[test]
fn a_reentered_entry_alone_provisions_its_frame() {
    let module = parse(&format!(
        "{HEADER}struct @P {{ : i32 @0, : i32 @4 }} size=8 align=4 id=0\n\n\
         functy.0 = (struct.0, struct.0, i32) -> (i32)\n\n\
         fn @swaploop(functy.0) {{\n\
         bbentry(%x: struct.0, %y: struct.0, %n: i32):\n\
         \x20   %zero = const i32 0\n\
         \x20   %done = icmp sle i32 %n, %zero\n\
         \x20   condbr %done, bbout, bbagain\n\
         bbagain:\n\
         \x20   %one = const i32 1\n\
         \x20   %m = sub i32 %n, %one\n\
         \x20   br bbentry(%y, %x, %m)\n\
         bbout:\n\
         \x20   %r = extractfield i32 %x, 0\n\
         \x20   ret %r\n\
         }}\n"
    ));
    validate(
        &wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("closed module"),
    );
    validate(&wasm::compile_object_with_license(&module, &permit_unlicensed()).expect("object"));
}

// ---- An Alloca that runs repeatedly ----

const LOOP_ALLOCAS: &str = r#"
type ty.0 = i32
type ty.1 = i64

global internal mut @table [ty.0 x 8]

functy.0 = (i64, i64) -> (i64)
functy.1 = (ptr, i64) -> ()
functy.2 = (ptr, i64) -> (i64)

fn @stash(functy.1) {
bbentry(%p: ptr, %i: i64):
    %base = global_addr @global.0
    %bi = ptrtoint ptr %base to i32
    %ii = trunc i64 %i to i32
    %c4 = const i32 4
    %off = mul i32 %ii, %c4
    %ai = add i32 %bi, %off
    %slot = inttoptr i32 %ai to ptr
    store ptr %p, ptr %slot
    ret
}

fn @touch(functy.2) {
bbentry(%p: ptr, %i: i64):
    store i64 %i, ptr %p
    %v = load i64, ptr %p
    %c3 = const i64 3
    %r = mul i64 %v, %c3
    ret %r
}

fn @first(functy.0) {
bbentry(%a: i64, %b: i64):
    %null = null ptr
    %zero = const i64 0
    br bbloop(%null, %zero)
bbloop(%prev: ptr, %i: i64):
    %cell = alloca i64
    %v = add i64 %a, %i
    store i64 %v, ptr %cell
    %again = icmp eq i64 %i, %zero
    condbr %again, bbnext, bbout
bbnext:
    %one = const i64 1
    br bbloop(%cell, %one)
bbout:
    %r = load i64, ptr %prev
    ret %r
}

fn @keep(functy.0) {
bbentry(%a: i64, %b: i64):
    %zero = const i64 0
    %null = null ptr
    br bbloop(%null, %null, %zero)
bbloop(%p1: ptr, %p2: ptr, %i: i64):
    %two = const i64 2
    %more = icmp slt i64 %i, %two
    condbr %more, bbbody, bbout
bbbody:
    %cell = alloca i64
    %v = add i64 %a, %i
    store i64 %v, ptr %cell
    %one = const i64 1
    %j = add i64 %i, %one
    br bbloop(%cell, %p1, %j)
bbout:
    %x = load i64, ptr %p1
    %y = load i64, ptr %p2
    %c1000 = const i64 1000
    %y1000 = mul i64 %y, %c1000
    %r = add i64 %x, %y1000
    ret %r
}

fn @distinct(functy.0) {
bbentry(%a: i64, %b: i64):
    %zero = const i64 0
    %outer = alloca i32
    br bbloop(%outer, %zero)
bbloop(%prev: ptr, %i: i64):
    %cell = alloca i32
    %again = icmp eq i64 %i, %zero
    condbr %again, bbnext, bbout
bbnext:
    %one = const i64 1
    br bbloop(%cell, %one)
bbout:
    %pa = ptrtoint ptr %prev to i32
    %pb = ptrtoint ptr %cell to i32
    %same = icmp eq i32 %pa, %pb
    %r = zext bool %same to i64
    ret %r
}

fn @captured(functy.0) {
bbentry(%a: i64, %b: i64):
    %zero = const i64 0
    br bbloop(%zero)
bbloop(%i: i64):
    %c3 = const i64 3
    %more = icmp slt i64 %i, %c3
    condbr %more, bbbody, bbout
bbbody:
    %cell = alloca i64
    %v = add i64 %a, %i
    store i64 %v, ptr %cell
    call @func.0(%cell, %i)
    %one = const i64 1
    %j = add i64 %i, %one
    br bbloop(%j)
bbout:
    %base = global_addr @global.0
    %s0 = load ptr, ptr %base
    %bi = ptrtoint ptr %base to i32
    %c8 = const i32 8
    %a2 = add i32 %bi, %c8
    %slot2 = inttoptr i32 %a2 to ptr
    %s2 = load ptr, ptr %slot2
    %x = load i64, ptr %s0
    %y = load i64, ptr %s2
    %c1000 = const i64 1000
    %y1000 = mul i64 %y, %c1000
    %r = add i64 %x, %y1000
    ret %r
}

fn @long_loop(functy.0) {
bbentry(%a: i64, %b: i64):
    %zero = const i64 0
    br bbloop(%zero, %zero)
bbloop(%i: i64, %acc: i64):
    %n = const i64 20000
    %more = icmp slt i64 %i, %n
    condbr %more, bbbody, bbout
bbbody:
    %cell = alloca [ty.1 x 64]
    %v = add i64 %a, %i
    %t = call @func.1(%cell, %v)
    %acc2 = add i64 %acc, %t
    %one = const i64 1
    %j = add i64 %i, %one
    br bbloop(%j, %acc2)
bbout:
    ret %acc
}
"#;

#[test]
fn a_repeated_alloca_is_fresh_while_earlier_pointers_are_observable() {
    let module = parse(&format!("{HEADER}{LOOP_ALLOCAS}"));
    let checks = assert_agrees(&module, &["first", "keep", "captured"], &inputs());
    eprintln!("repeated allocas: {checks} checks agree");
    // Two live executions of one Alloca never share an address.
    let closed = wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compile");
    if let Some(got) = run_wasm(&closed, "distinct", &[(0, 0), (5, 5)]) {
        assert_eq!(
            got,
            vec![Some(0), Some(0)],
            "two live allocations compare equal"
        );
    }
    assert_eq!(interpret(&module, "distinct", 0, 0), Some(0));
}

/// A repeated `Alloca` whose pointer only reaches a callee that does not keep
/// it keeps one slot: 20000 iterations of a 512-byte allocation would need
/// 10 MB of shadow stack otherwise, far beyond the module's.
#[test]
fn a_repeated_alloca_no_earlier_pointer_can_reach_keeps_one_slot() {
    let module = parse(&format!("{HEADER}{LOOP_ALLOCAS}"));
    let checks = assert_agrees(&module, &["long_loop"], &[(0, 0), (7, 1), (-3, 2)]);
    eprintln!("long loop: {checks} checks agree");
}

// ---- The closed module's stack meets its static data ----

const STACK_INTO_DATA: &str = r#"
type ty.0 = u8

global internal mut @big [ty.0 x 60000]
global internal mut @x i64 = 7

functy.0 = (i64, i64) -> (i64)

fn @rec(functy.0) {
bbentry(%n: i64, %t: i64):
    %buf = alloca [ty.0 x 1024]
    %fill = const u8 171
    %len = const usize 1024
    memset ptr %buf, %fill, %len
    %zero = const i64 0
    %deeper = icmp sgt i64 %n, %zero
    condbr %deeper, bbcall, bbbottom
bbcall:
    %one = const i64 1
    %m = sub i64 %n, %one
    %r = call @func.0(%m, %t)
    ret %r
bbbottom:
    %i1 = const i64 1
    %odd = and i64 %t, %i1
    %trap = icmp ne i64 %odd, %zero
    condbr %trap, bbtrap, bbok
bbtrap:
    %q = sdiv i64 %i1, %zero
    ret %q
bbok:
    %g = global_addr @global.1
    %v = load i64, ptr %g
    ret %v
}

fn @dive(functy.0) {
bbentry(%a: i64, %b: i64):
    %c63 = const i64 63
    %n = and i64 %a, %c63
    %r = call @func.0(%n, %b)
    ret %r
}
"#;

/// With 60 KB of static data under a one-page stack, a deep call chain (or a
/// frame left behind by a trap) must trap — never overwrite `@x` and return
/// something other than 7.
#[test]
fn a_closed_stack_that_meets_static_data_traps_instead_of_overwriting_it() {
    let module = parse(&format!("{HEADER}{STACK_INTO_DATA}"));
    let closed = wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compile");
    validate(&closed);
    for n in 0..3 {
        assert_eq!(interpret(&module, "dive", n, 0), Some(7));
    }
    // Shallow calls fit; an odd `b` traps in the deepest frame and leaves
    // every frame of the chain behind; deeper calls overflow. Every call on
    // the one instance returns 7 or traps.
    let mut calls = Vec::new();
    for round in 0..40i64 {
        calls.push((round % 4, 0));
        calls.push((round % 64, round & 1));
    }
    let Some(got) = run_wasm(&closed, "dive", &calls) else {
        eprintln!("SKIP a_closed_stack_that_meets_static_data_traps: node not on PATH");
        return;
    };
    assert_eq!(got[0], Some(7), "a shallow first call fits the stack");
    for (i, g) in got.iter().enumerate() {
        assert!(
            matches!(g, None | Some(7)),
            "dive{:?}: returned {g:?} — static data was overwritten",
            calls[i]
        );
    }
    assert!(got.iter().any(Option::is_none), "no call overflowed");
}

// ---- A block parameter read along an edge that does not rebind it ----

/// A `condbr` or `switch` rebinds its target's parameters only on the edge it
/// takes. Along the other edge (a loop exit that reads the header's aggregate
/// parameter) the old parameter stays live across the terminator, so a
/// temporary defined earlier in the block must not share its bytes. `walk`
/// is the same shape with the ENTRY block as the loop header (a by-address
/// entry parameter's home); `fuzz` is a generated loop with a `switch`, a
/// `condbr` back edge and an exit that reads the header's parameters.
const UNTAKEN_EDGE: &str = r#"
struct @P { : i64 @0, : i64 @8 } size=16 align=8 id=0

functy.0 = (i64, i64) -> (i64)
functy.1 = (struct.0, i64) -> (i64)

rustcc fn @walk(functy.1) {
bb0(%0: struct.0, %1: i64):
    %2 = const i64 100
    %3 = mul i64 %1, %2
    %4 = make_aggregate struct.0 (%1, %2)
    %5 = make_aggregate struct.0 (%3, %3)
    %6 = extractfield i64 %4, 1
    %7 = extractfield i64 %5, 0
    %8 = add i64 %7, %6
    %9 = make_aggregate struct.0 (%8, %1)
    %10 = const i64 1
    %11 = add i64 %1, %10
    %12 = const i64 3
    %13 = icmp slt i64 %1, %12
    condbr %13, bb0(%9, %11), bb1
bb1:
    %14 = extractfield i64 %0, 0
    %15 = extractfield i64 %0, 1
    %16 = const i64 1000
    %17 = mul i64 %14, %16
    %18 = add i64 %17, %15
    ret %18
}

fn @d_walk(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = make_aggregate struct.0 (%0, %1)
    %3 = const i64 0
    %4 = call @func.0(%2, %3)
    %5 = extractfield i64 %2, 0
    %6 = xor i64 %4, %5
    ret %6
}

fn @exit_reads(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = make_aggregate struct.0 (%0, %1)
    %3 = const i64 0
    br bb1(%2, %3)
bb1(%4: struct.0, %5: i64):
    %6 = const i64 100
    %7 = mul i64 %5, %6
    %21 = make_aggregate struct.0 (%5, %6)
    %8 = make_aggregate struct.0 (%7, %7)
    %22 = extractfield i64 %21, 1
    %9 = extractfield i64 %8, 0
    %10 = const i64 1
    %11 = add i64 %9, %22
    %12 = make_aggregate struct.0 (%11, %5)
    %13 = add i64 %5, %10
    %14 = const i64 3
    %15 = icmp slt i64 %5, %14
    condbr %15, bb1(%12, %13), bb2
bb2:
    %16 = extractfield i64 %4, 0
    %17 = extractfield i64 %4, 1
    %18 = const i64 1000
    %19 = mul i64 %16, %18
    %20 = add i64 %19, %17
    ret %20
}

fn @switch_exit_reads(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = make_aggregate struct.0 (%0, %1)
    %3 = const i64 0
    br bb1(%2, %3)
bb1(%4: struct.0, %5: i64):
    %6 = const i64 100
    %7 = mul i64 %5, %6
    %21 = make_aggregate struct.0 (%5, %6)
    %8 = make_aggregate struct.0 (%7, %7)
    %22 = extractfield i64 %21, 1
    %9 = extractfield i64 %8, 0
    %10 = const i64 1
    %11 = add i64 %9, %22
    %12 = make_aggregate struct.0 (%11, %5)
    %13 = add i64 %5, %10
    switch %5 [ 0: bb1(%12, %13) 1: bb1(%12, %13) 2: bb1(%12, %13) default: bb2 ]
bb2:
    %16 = extractfield i64 %4, 0
    %17 = extractfield i64 %4, 1
    %18 = const i64 1000
    %19 = mul i64 %16, %18
    %20 = add i64 %19, %17
    ret %20
}

fn @fuzz(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = const i64 70
    %3 = xor i64 %1, %2
    %4 = add i64 %0, %0
    %5 = sub i64 %1, %0
    %6 = mul i64 %5, %1
    %7 = make_aggregate struct.0 (%3, %4)
    %8 = make_aggregate struct.0 (%3, %1)
    %9 = const i64 0
    br bb1(%9, %6, %7, %8)
bb1(%10: i64, %11: i64, %12: struct.0, %13: struct.0):
    %14 = const i64 4
    %15 = icmp slt i64 %10, %14
    condbr %15, bb2, bb3
bb2:
    %16 = extractfield i64 %12, 0
    %17 = extractfield i64 %13, 1
    %18 = const i64 89
    %19 = sub i64 %16, %18
    %20 = mul i64 %11, %16
    %21 = or i64 %17, %16
    %22 = const i64 54
    %23 = mul i64 %19, %22
    %24 = const i64 1
    %25 = add i64 %10, %24
    %26 = const i64 3
    %27 = and i64 %10, %26
    %28 = make_aggregate struct.0 (%23, %11)
    %29 = make_aggregate struct.0 (%19, %17)
    %30 = make_aggregate struct.0 (%19, %17)
    %31 = extractfield i64 %28, 1
    %32 = extractfield i64 %29, 0
    %33 = extractfield i64 %30, 1
    switch %27 [ 0: bb4 1: bb5 2: bb6 default: bb7 ]
bb4:
    %34 = xor i64 %20, %21
    %35 = make_aggregate struct.0 (%31, %34)
    %36 = const i64 0
    %37 = icmp sgt i64 %25, %36
    condbr %37, bb3, bb1(%25, %10, %35, %28)
bb5:
    %38 = xor i64 %33, %33
    %39 = const i64 34
    %40 = mul i64 %33, %39
    %41 = make_aggregate struct.0 (%32, %32)
    br bb8(%23, %41, %12)
bb6:
    %42 = sub i64 %33, %20
    %43 = const i64 52
    %44 = add i64 %10, %43
    %45 = add i64 %42, %21
    %46 = make_aggregate struct.0 (%31, %10)
    br bb8(%16, %28, %46)
bb7:
    %47 = xor i64 %10, %31
    br bb8(%33, %30, %28)
bb8(%48: i64, %49: struct.0, %50: struct.0):
    %51 = extractfield i64 %49, 1
    %52 = extractfield i64 %50, 0
    %53 = add i64 %48, %48
    %54 = make_aggregate struct.0 (%53, %53)
    %55 = make_aggregate struct.0 (%53, %48)
    br bb1(%25, %53, %54, %55)
bb3:
    %56 = extractfield i64 %12, 1
    %57 = extractfield i64 %13, 1
    %58 = extractfield i64 %12, 0
    %59 = extractfield i64 %13, 0
    %60 = and i64 %59, %10
    %61 = const i64 17
    %62 = add i64 %60, %61
    %63 = const i64 26
    %64 = sub i64 %59, %63
    %65 = const i64 829
    %66 = mul i64 %11, %65
    %67 = xor i64 %66, %56
    %68 = const i64 834
    %69 = mul i64 %67, %68
    %70 = xor i64 %69, %57
    %71 = const i64 954
    %72 = mul i64 %70, %71
    %73 = xor i64 %72, %58
    %74 = const i64 551
    %75 = mul i64 %73, %74
    %76 = xor i64 %75, %59
    %77 = const i64 354
    %78 = mul i64 %76, %77
    %79 = xor i64 %78, %10
    %80 = const i64 90
    %81 = mul i64 %79, %80
    %82 = xor i64 %81, %60
    %83 = const i64 636
    %84 = mul i64 %82, %83
    %85 = xor i64 %84, %62
    %86 = const i64 526
    %87 = mul i64 %85, %86
    %88 = xor i64 %87, %64
    ret %88
}
"#;

#[test]
fn a_parameter_live_along_the_untaken_edge_keeps_its_bytes() {
    let module = parse(&format!("{HEADER}{UNTAKEN_EDGE}"));
    let names = ["d_walk", "exit_reads", "switch_exit_reads", "fuzz"];
    let checks = assert_agrees(&module, &names, &inputs());
    eprintln!("untaken edges: {checks} checks agree");
}

// ---- Frame and local sizes ----

/// `n` value-form `insertfield`s chained over an `n x i64` struct: each link
/// is a fresh SSA value, and only two are ever live at once.
fn insert_chain(n: usize) -> Module {
    let fields: Vec<String> = (0..n).map(|k| format!(": i64 @{}", 8 * k)).collect();
    let mut t = format!(
        "{HEADER}struct @S {{ {} }} size={} align=8 id=0\n\nfuncty.0 = (i64, i64) -> (i64)\n\n\
         fn @chain(functy.0) {{\nbb0(%0: i64, %1: i64):\n",
        fields.join(", "),
        8 * n
    );
    let ones: Vec<&str> = vec!["%1"; n];
    let _ = writeln!(t, "    %2 = make_aggregate struct.0 ({})", ones.join(", "));
    for k in 0..n {
        let _ = writeln!(
            t,
            "    %{} = insertfield struct.0 %{}, {k}, %0",
            k + 3,
            k + 2
        );
    }
    let _ = writeln!(t, "    %{} = extractfield i64 %{}, {}", n + 3, n + 2, n - 1);
    let _ = writeln!(t, "    ret %{}\n}}", n + 3);
    parser::parse_module(&t).expect("parse chain")
}

#[test]
fn homes_share_frame_bytes_by_liveness() {
    // 181 links over 1448 bytes: 263 KB of homes laid end to end.
    let module = insert_chain(181);
    let checks = assert_agrees(&module, &["chain"], &inputs());
    let closed = wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compile");
    let (_, frame) = function_shape(&closed, "chain");
    let frame = frame.expect("a framed function") as u32;
    assert!(
        frame <= 3 * 1448,
        "the chain's frame is {frame} bytes; two live 1448-byte values need 2896"
    );
    eprintln!("insert chain: frame {frame} bytes, {checks} checks agree");
}

/// A pointer is not an aggregate operand for value-producing insertfield.
/// Keep the old overloaded fixture as a strict refusal, not a frame proof.
#[test]
fn pointer_overloaded_insert_field_is_refused() {
    let mut t = format!(
        "{HEADER}type ty.0 = i64\n\nfuncty.0 = (i64, i64) -> (i64)\n\n\
         fn @wt(functy.0) {{\nbb0(%0: i64, %1: i64):\n    %2 = alloca [ty.0 x 32], align 8\n"
    );
    for k in 0..32 {
        let _ = writeln!(t, "    %{} = insertfield [ty.0 x 32] %2, {k}, %0", k + 3);
    }
    t.push_str(
        "    %42 = load i64, ptr %2\n    %44 = ptrtoint ptr %2 to i32\n    \
         %45 = sub i32 %44, %44\n    %46 = sext i32 %45 to i64\n    \
         %47 = add i64 %42, %46\n    %43 = add i64 %47, %1\n    ret %43\n}\n",
    );
    let module = parser::parse_module(&t).expect("parse");
    let error = wasm::compile_module_with_license(&module, &permit_unlicensed())
        .expect_err("pointer-overloaded insertfield must remain invalid IR");
    let message = error.to_string();
    assert!(
        message.contains("insert_field") && message.contains("aggregate operand"),
        "{message}"
    );
}

/// Explicit stores through an alloca need only that alloca's frame home.
/// Keep the same 32 writes, escaping-address shape and observed results.
#[test]
fn stores_through_an_alloca_own_no_additional_home() {
    let mut t = format!(
        "{HEADER}type ty.0 = i64\n\nfuncty.0 = (i64, i64) -> (i64)\n\n\
         fn @wt(functy.0) {{\nbb0(%0: i64, %1: i64):\n    %2 = alloca [ty.0 x 32], align 8\n"
    );
    for k in 0..32 {
        let index = k * 2 + 3;
        let address = index + 1;
        let _ = writeln!(t, "    %{index} = const usize {k}");
        let _ = writeln!(t, "    %{address} = gep i64, ptr %2, %{index}");
        let _ = writeln!(t, "    store i64 %0, ptr %{address}");
    }
    t.push_str(
        "    %100 = load i64, ptr %2\n    %101 = ptrtoint ptr %2 to i32\n    \
         %102 = sub i32 %101, %101\n    %103 = sext i32 %102 to i64\n    \
         %104 = add i64 %100, %103\n    %105 = add i64 %104, %1\n    ret %105\n}\n",
    );
    let module = parser::parse_module(&t).expect("parse");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "valid store fixture: {errors:?}");
    let closed = wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compile");
    validate(&closed);
    let (_, frame) = function_shape(&closed, "wt");
    assert_eq!(
        frame,
        Some(256),
        "only the 256-byte alloca occupies the frame"
    );
    if let Some(got) = run_wasm(&closed, "wt", &[(5, 1), (-9, 100)]) {
        assert_eq!(got, vec![Some(6), Some(91)]);
    }
}

/// A straight chain of `n` adds: one SSA value per link.
fn add_chain(n: usize) -> Module {
    let mut t = format!("{HEADER}functy.0 = (i64, i64) -> (i64)\n\nfn @chain(functy.0) {{\n");
    t.push_str("bb0(%0: i64, %1: i64):\n    %2 = add i64 %0, %1\n");
    for k in 0..n {
        let _ = writeln!(t, "    %{} = add i64 %{}, %1", k + 3, k + 2);
    }
    let _ = writeln!(t, "    ret %{}\n}}", n + 2);
    parser::parse_module(&t).expect("parse chain")
}

#[test]
fn locals_are_reused_by_liveness() {
    let module = add_chain(50_010);
    let closed = wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compile");
    validate(&closed);
    let (locals, _) = function_shape(&closed, "chain");
    assert!(
        locals < 16,
        "{locals} locals for a chain with two live values"
    );
    assert_eq!(interpret(&module, "chain", 5, 1), Some(5 + 50_011));
    if let Some(got) = run_wasm(&closed, "chain", &[(5, 1), (-7, 3)]) {
        assert_eq!(got, vec![Some(5 + 50_011), Some(-7 + 3 * 50_011)]);
    }
    let object = wasm::compile_object_with_license(&module, &permit_unlicensed()).expect("object");
    if let Some(linked) = link(&object)
        && let Some(got) = run_wasm(&linked, "chain", &[(5, 1)])
    {
        assert_eq!(got, vec![Some(5 + 50_011)]);
    }
}

/// Coalescing over loops and branches: a loop body with many short-lived
/// values, some live around the back edge, agrees with the interpreter.
#[test]
fn coalesced_locals_keep_loop_carried_values() {
    let mut t = format!(
        "{HEADER}functy.0 = (i64, i64) -> (i64)\n\nfn @spin(functy.0) {{\n\
         bbentry(%a: i64, %b: i64):\n    %zero = const i64 0\n    br bbloop(%zero, %a, %b)\n\
         bbloop(%i: i64, %x: i64, %y: i64):\n    %c9 = const i64 9\n\
         \x20   %more = icmp slt i64 %i, %c9\n    condbr %more, bbbody, bbout\nbbbody:\n"
    );
    let mut prev = "x".to_string();
    for k in 0..120 {
        let _ = writeln!(t, "    %k{k} = const i64 {}", k * 7 + 1);
        let op = ["add", "xor", "mul", "sub"][k % 4];
        let _ = writeln!(t, "    %t{k} = {op} i64 %{prev}, %k{k}");
        prev = format!("t{k}");
    }
    let _ = writeln!(t, "    %odd = and i64 %i, %y");
    t.push_str(
        "    %one = const i64 1\n    %bit = and i64 %odd, %one\n\
         \x20   %z = icmp eq i64 %bit, %zero\n",
    );
    let _ = writeln!(t, "    condbr %z, bbeven, bbodd\nbbeven:");
    let _ = writeln!(t, "    %e = add i64 %{prev}, %y");
    t.push_str("    br bbjoin(%e)\nbbodd:\n");
    let _ = writeln!(t, "    %o = xor i64 %{prev}, %x");
    t.push_str(
        "    br bbjoin(%o)\nbbjoin(%v: i64):\n    %j = add i64 %i, %one\n\
         \x20   br bbloop(%j, %v, %x)\nbbout:\n    %r = xor i64 %x, %y\n    ret %r\n}\n",
    );
    let module = parse(&t);
    let closed = wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compile");
    let (locals, _) = function_shape(&closed, "spin");
    assert!(locals < 64, "{locals} locals after coalescing");
    let checks = assert_agrees(&module, &["spin"], &inputs());
    eprintln!("coalesced loop: {locals} locals, {checks} checks agree");
}

#[test]
fn a_function_over_an_engine_limit_is_refused_by_name() {
    // 1001 parameters.
    let params: Vec<&str> = vec!["i32"; 1001];
    let mut t = format!(
        "{HEADER}functy.0 = ({}) -> (i32)\n\nfn @wide(functy.0) {{\nbb0(",
        params.join(", ")
    );
    let decl: Vec<String> = (0..1001).map(|k| format!("%{k}: i32")).collect();
    let _ = writeln!(t, "{}):\n    ret %0\n}}", decl.join(", "));
    let module = parser::parse_module(&t).expect("parse");
    match wasm::compile_module_with_license(&module, &permit_unlicensed()) {
        Err(wasm::lower::WasmLowerError::ImplementationLimit(m)) => {
            assert!(m.contains("1001 parameters"), "{m}")
        }
        other => panic!("expected an ImplementationLimit refusal, got {other:?}"),
    }
    // 50,001 values all live at once: no coalescing can bring it under the
    // limit.
    let n = 50_001;
    let mut t = format!("{HEADER}functy.0 = (i64, i64) -> (i64)\n\nfn @live(functy.0) {{\n");
    t.push_str("bb0(%0: i64, %1: i64):\n");
    for k in 0..n {
        let _ = writeln!(t, "    %{} = add i64 %0, %1", k + 2);
    }
    let _ = writeln!(t, "    %{} = add i64 %2, %3", n + 2);
    for k in 2..n {
        let _ = writeln!(t, "    %{} = add i64 %{}, %{}", n + 1 + k, n + k, k + 2);
    }
    let _ = writeln!(t, "    ret %{}\n}}", 2 * n);
    let module = parser::parse_module(&t).expect("parse");
    match wasm::compile_module_with_license(&module, &permit_unlicensed()) {
        Err(wasm::lower::WasmLowerError::ImplementationLimit(m)) => {
            assert!(m.contains("locals"), "{m}")
        }
        other => panic!(
            "expected an ImplementationLimit refusal, got {:?}",
            other.map(|b| b.len())
        ),
    }
}

// ---- A zero-byte bulk-memory op through an out-of-memory pointer ----

/// `zero_len` runs a zero-byte `memcopy` (both `overlap` settings) and a
/// zero-byte `memset` through `inttoptr (trunc a)`, which for most inputs is
/// far past the one-page memory, with the count computed from `b` so nothing
/// can fold it. `nonzero` copies and fills `b & 7` bytes inside a frame
/// buffer, so the guard must still let a nonzero count through.
const ZERO_LENGTH_BULK: &str = r#"
type ty.0 = u8

functy.0 = (i64, i64) -> (i64)

fn @zero_len(functy.0) {
bbentry(%a: i64, %b: i64):
    %ai = trunc i64 %a to i32
    %p = inttoptr i32 %ai to ptr
    %z64 = const i64 0
    %m = and i64 %b, %z64
    %n = trunc i64 %m to usize
    memcopy overlap ptr %p, ptr %p, %n
    memcopy ptr %p, ptr %p, %n
    %k = const u8 171
    memset ptr %p, %k, %n
    %c7 = const i64 7
    %r = add i64 %b, %c7
    ret %r
}

fn @nonzero(functy.0) {
bbentry(%a: i64, %b: i64):
    %src = alloca [ty.0 x 16]
    %dst = alloca [ty.0 x 16]
    %z = const u8 0
    %c16 = const usize 16
    memset ptr %dst, %z, %c16
    %k = const u8 90
    memset ptr %src, %k, %c16
    %c7 = const i64 7
    %m = and i64 %b, %c7
    %n = trunc i64 %m to usize
    memcopy overlap ptr %dst, ptr %src, %n
    %j = const u8 17
    memset ptr %src, %j, %n
    %c0 = const usize 0
    %pd = gep i64, ptr %dst, %c0
    %vd = load i64, ptr %pd
    %ps = gep i64, ptr %src, %c0
    %vs = load i64, ptr %ps
    %r = xor i64 %vd, %vs
    ret %r
}
"#;

/// A zero-byte `MemCopy` / `MemSet` returns through a pointer the memory does
/// not contain, exactly as the interpreter does, and the emitted guard does
/// not disturb a nonzero count.
#[test]
fn a_zero_byte_bulk_memory_op_through_an_out_of_memory_pointer_is_a_no_op() {
    let module = parse(&format!("{HEADER}{ZERO_LENGTH_BULK}"));
    // Addresses inside the page, at its end, past it, near and at 2^32 - 1.
    let addrs: [i64; 7] = [0, 1000, 65535, 65536, 4_000_000_000, 0xffff_fff8, -1];
    let counts: [i64; 5] = [0, 1, 7, 8, -1];
    let inputs: Vec<(i64, i64)> = addrs
        .iter()
        .flat_map(|&a| counts.iter().map(move |&b| (a, b)))
        .collect();
    for &(a, b) in &inputs {
        assert_eq!(
            interpret(&module, "zero_len", a, b),
            Some(b.wrapping_add(7)),
            "the interpreter defines zero_len({a}, {b})"
        );
    }
    let checks = assert_agrees(&module, &["zero_len", "nonzero"], &inputs);
    eprintln!("zero-byte bulk memory: {checks} checks agree");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
