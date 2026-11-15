// trust-cg-codegen/tests/wasm_r16_sections.rs - wasm32 lane: what an object's
// non-code sections and folded bodies carry at each level
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The round-16 object-composition changes of the wasm32 lane, read back
//! from the objects with `wasmparser` (not the lane's own encoder):
//!
//! * debug names: at O1 and above an object carries a `name` section that
//!   names each function whose symbol has the crate-private mark by its
//!   symbol without the mark (and without `.tcg.mv`), and names no other
//!   function; at O0 it carries none. The symbol table, the imports and so
//!   every name the linker, the internal-ABI gate and the bridge's link check
//!   read are those of the O0 object, plus only the O1+ internal entries;
//! * identical-body folding: at O1 and above the second of two identical
//!   exported bodies is exactly a forwarder to the first, a small identical
//!   pair and a weak copy are not folded, and at O0 nothing is; linked by
//!   `wasm-ld`, both stay distinct exported functions under their own names,
//!   the linked `name` section shows no crate-private mark, and node's
//!   results for every export equal the trust-ir reference interpreter's.
//! * a recursive group: of two identical bodies that both call one of them,
//!   the called one is kept and the other forwards to it, so no forwarder
//!   lies on the recursion, and node's results equal the interpreter's;
//! * an indirect recursion through another object: two identical global
//!   bodies that recurse through a function pointer this object never
//!   takes the address of are not folded (another object can hand either
//!   one's address to the other's indirect call), and linked with the
//!   object that does take the addresses, node's results equal the
//!   expected ones.
//!
//! `wasm-ld` (`WASM_LD` or PATH) and node are needed for the link and
//! execution legs; without them those legs are a loud SKIP.
//!
//! The entry this test drives (`compile_object_optimized`), the object's
//! debug names and the forwarder shape it reads are provisional surfaces
//! pending the owner's sign-off: this test follows them if they change, and
//! is not a contract for their shape.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm;
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};
use wasmparser::{KnownCustom, Linking, Name, Parser, Payload, SymbolInfo};

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const MIX: &str = "mix.tcg.crate.00000000000000b1";

/// `x` and `y` through `steps` multiply / xor / subtract rounds (no
/// constant the mid-end could fold), then `mix` of the result and `y`.
fn chain(name: &str, steps: usize, linkage: &str) -> String {
    let mut body = String::new();
    let mut prev = 0;
    for i in 0..steps {
        let op = ["mul", "xor", "sub"][i % 3];
        body.push_str(&format!("    %{} = {op} i32 %{prev}, %1\n", i + 2));
        prev = i + 2;
    }
    format!(
        "{linkage}fn @{name}(functy.0) {{\nbb0(%0: i32, %1: i32):\n{body}    \
         %{r} = call @func.0(%{prev}, %1)\n    ret %{r}\n}}\n\n",
        r = steps + 2
    )
}

fn module_text() -> String {
    let mut text = String::from(
        "module \"r16s\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = (i32, i32) -> (i32)\n\n",
    );
    text.push_str(&format!(
        "fn @{MIX}(functy.0) {{\n    ; #visibility: hidden\nbb0(%0: i32, %1: i32):\n    \
         %2 = add i32 %0, %1\n    %3 = mul i32 %2, %0\n    ret %3\n}}\n\n"
    ));
    text.push_str(&chain("big_a", 60, ""));
    text.push_str(&chain("big_b", 60, ""));
    text.push_str(&chain("small_a", 2, ""));
    text.push_str(&chain("small_b", 2, ""));
    text.push_str(&chain("weak_a", 61, "linkonce_odr "));
    text.push_str(&chain("weak_b", 61, "linkonce_odr "));
    text.push_str(&chain("weak_c", 60, "linkonce_odr "));
    text
}

const EXPORTS: [&str; 7] = [
    "big_a", "big_b", "small_a", "small_b", "weak_a", "weak_b", "weak_c",
];

fn parse(text: &str) -> Module {
    trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("module: {e}"))
}

fn compile(level: OptLevel) -> Vec<u8> {
    let bytes = wasm::compile_object_with_license_optimized(
        &parse(&module_text()),
        &permit_unlicensed(),
        level,
    )
    .unwrap_or_else(|e| panic!("{level:?}: {e}"));
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&bytes)
        .unwrap_or_else(|e| panic!("{level:?}: the object does not validate: {e}"));
    bytes
}

/// What the test reads from an object or a linked module.
#[derive(Default)]
struct View {
    func_imports: u32,
    /// Import `(module, name)` pairs.
    imports: Vec<(String, String)>,
    /// Function symbols: name -> (function index, flags).
    symbols: BTreeMap<String, (u32, u32)>,
    /// Every symbol of the table, rendered, in order.
    symtab: Vec<String>,
    /// Body bytes (local declarations through `end`), by defined ordinal.
    bodies: Vec<Vec<u8>>,
    /// `name` section function names, by function index.
    names: BTreeMap<u32, String>,
    has_name_section: bool,
    /// Function exports: name -> index.
    exports: BTreeMap<String, u32>,
}

fn view(bytes: &[u8]) -> View {
    let mut v = View::default();
    for payload in Parser::new(0).parse_all(bytes) {
        match payload.expect("parse") {
            Payload::ImportSection(r) => {
                for import in r {
                    let import = import.expect("import");
                    if matches!(import.ty, wasmparser::TypeRef::Func(_)) {
                        v.func_imports += 1;
                    }
                    v.imports
                        .push((import.module.to_string(), import.name.to_string()));
                }
            }
            Payload::ExportSection(r) => {
                for export in r {
                    let export = export.expect("export");
                    if export.kind == wasmparser::ExternalKind::Func {
                        v.exports.insert(export.name.to_string(), export.index);
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                v.bodies.push(bytes[body.range()].to_vec());
            }
            Payload::CustomSection(c) => match c.as_known() {
                KnownCustom::Linking(linking) => {
                    for sub in linking.subsections() {
                        let Linking::SymbolTable(map) = sub.expect("linking") else {
                            continue;
                        };
                        for info in map {
                            let info = info.expect("symbol");
                            v.symtab.push(format!("{info:?}"));
                            if let SymbolInfo::Func {
                                flags,
                                index,
                                name: Some(name),
                            } = info
                            {
                                v.symbols.insert(name.to_string(), (index, flags.bits()));
                            }
                        }
                    }
                }
                KnownCustom::Name(reader) => {
                    v.has_name_section = true;
                    for sub in reader {
                        if let Name::Function(map) = sub.expect("name subsection") {
                            for naming in map {
                                let naming = naming.expect("naming");
                                v.names.insert(naming.index, naming.name.to_string());
                            }
                        }
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }
    v
}

impl View {
    fn body_of(&self, symbol: &str) -> &[u8] {
        let (index, _) = self.symbols[symbol];
        &self.bodies[(index - self.func_imports) as usize]
    }
}

/// The forwarder of a `(i32, i32)` function to function `kept`.
fn forwarder(kept: u32) -> Vec<u8> {
    let mut body = vec![0, 0x20, 0, 0x20, 1, 0x10];
    let mut v = kept;
    for i in 0..5 {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        body.push(if i < 4 { b | 0x80 } else { b });
    }
    body.push(0x0b);
    body
}

#[test]
fn debug_names_drop_only_the_crate_mark_and_leave_every_symbol() {
    let base = view(&compile(OptLevel::O0));
    assert!(
        !base.has_name_section,
        "an O0 object carries no name section"
    );
    assert!(base.symbols.contains_key(MIX));
    for level in &LEVELS[1..] {
        let v = view(&compile(*level));
        assert!(v.has_name_section, "{level:?}: no name section");
        // The symbols and imports are those of the O0 object, plus only
        // internal entries.
        let names: BTreeSet<&String> = v
            .symbols
            .keys()
            .filter(|n| !n.ends_with(".tcg.mv"))
            .collect();
        assert_eq!(
            names,
            base.symbols.keys().collect::<BTreeSet<_>>(),
            "{level:?}: the function symbols changed"
        );
        assert_eq!(v.imports, base.imports, "{level:?}: the imports changed");
        // Exactly the marked symbols get a debug name, the symbol without
        // the mark and the internal-entry suffix.
        let mut want = BTreeMap::new();
        for (name, (index, _)) in &v.symbols {
            if let Some(at) = name.find(".tcg.crate.") {
                let tail = &name[at + ".tcg.crate.".len() + 16..];
                let plain = format!("{}{}", &name[..at], tail);
                let plain = plain.strip_suffix(".tcg.mv").unwrap_or(&plain).to_string();
                want.insert(*index, plain);
            }
        }
        assert!(!want.is_empty());
        assert_eq!(v.names, want, "{level:?}: the debug names");
        assert_eq!(v.names[&v.symbols[MIX].0], "mix");
    }
}

#[test]
fn identical_bodies_fold_into_forwarders_at_o1_and_above() {
    let base = view(&compile(OptLevel::O0));
    assert_eq!(
        base.body_of("big_a"),
        base.body_of("big_b"),
        "the pair must start identical"
    );
    assert_ne!(base.body_of("big_b"), forwarder(base.symbols["big_a"].0));
    for level in &LEVELS[1..] {
        let v = view(&compile(*level));
        let (a, flags) = v.symbols["big_a"];
        assert_eq!(flags & 0x1, 0, "big_a is strong");
        assert_eq!(
            v.body_of("big_b"),
            forwarder(a),
            "{level:?}: big_b must be a forwarder to big_a"
        );
        assert_ne!(v.body_of("big_a"), forwarder(a));
        // A weak copy folds onto a strong one, but two weak copies keep
        // their bodies (neither can be the kept one), and below the size
        // floor nothing folds.
        assert_eq!(v.body_of("weak_c"), forwarder(a), "{level:?}");
        assert_eq!(v.body_of("weak_a"), v.body_of("weak_b"), "{level:?}");
        assert_ne!(v.body_of("weak_a"), forwarder(v.symbols["weak_b"].0));
        assert_eq!(v.body_of("small_a"), v.body_of("small_b"), "{level:?}");
    }
}

fn wasm_ld() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("WASM_LD").filter(|p| !p.is_empty()) {
        return Some(PathBuf::from(p));
    }
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|d| d.join("wasm-ld"))
        .find(|p| p.is_file())
}

fn node() -> Option<PathBuf> {
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|d| d.join("node"))
        .find(|p| p.is_file())
}

fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_wasm_r16s_{tag}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn link(tag: &str, object: &[u8]) -> Option<Vec<u8>> {
    link_exporting(tag, object, &EXPORTS)
}

fn link_exporting(tag: &str, object: &[u8], exports: &[&str]) -> Option<Vec<u8>> {
    link_objects(tag, &[object], exports)
}

/// `wasm-ld` of `objects` into a module exporting `exports`.
fn link_objects(tag: &str, objects: &[&[u8]], exports: &[&str]) -> Option<Vec<u8>> {
    let ld = wasm_ld()?;
    let dir = scratch(tag);
    let mut cmd = Command::new(ld);
    cmd.args(["--no-entry", "--gc-sections"]);
    for e in exports {
        cmd.arg("--export").arg(e);
    }
    for (i, object) in objects.iter().enumerate() {
        let path = dir.join(format!("in{i}.o"));
        std::fs::write(&path, object).unwrap();
        cmd.arg(path);
    }
    let out = cmd
        .arg("-o")
        .arg(dir.join("out.wasm"))
        .output()
        .expect("run wasm-ld");
    assert!(
        out.status.success(),
        "wasm-ld: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(dir.join("out.wasm")).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    Some(bytes)
}

const INPUTS: [(i32, i32); 5] = [
    (0, 0),
    (1, 2),
    (-7, 13),
    (123_456, -987),
    (i32::MAX, i32::MIN),
];

fn run(tag: &str, bytes: &[u8]) -> Option<Vec<String>> {
    let calls: Vec<String> = EXPORTS
        .iter()
        .flat_map(|e| INPUTS.iter().map(move |(x, y)| format!("{e}({x}, {y})")))
        .collect();
    run_calls(tag, bytes, &calls)
}

/// Node's results of `calls` (JavaScript calls of the exports) on `bytes`.
fn run_calls(tag: &str, bytes: &[u8], calls: &[String]) -> Option<Vec<String>> {
    let node = node()?;
    let dir = scratch(tag);
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    std::fs::write(
        dir.join("run.js"),
        format!(
            "const fs = require('fs');\n\
             const E = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[2])), {{}}).exports;\n\
             process.stdout.write(JSON.stringify([{}].map(f => String(f()))));\n",
            calls
                .iter()
                .map(|c| format!("() => E.{c}"))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    )
    .unwrap();
    let out = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .output()
        .expect("run node");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.status.success(),
        "node: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    Some(serde_json::from_slice(&out.stdout).expect("node JSON"))
}

fn interpret(module: &Module, name: &str, x: i32, y: i32) -> String {
    let f = module.function_by_name(name).expect("function");
    let args = [x, y]
        .map(|v| InterpretValue::int(Ty::I32, i128::from(v)).expect("i32"))
        .to_vec();
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 1_000_000,
            max_call_depth: 64,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, args)
        .unwrap_or_else(|e| panic!("interpreter {name}: {e:?}"));
    match &out.returns[0].kind {
        InterpretValueKind::Int(v) => (v.as_signed() as i32).to_string(),
        other => panic!("interpreter {name}: {other:?}"),
    }
}

#[test]
fn folded_exports_link_as_distinct_functions_and_compute_their_results() {
    let module = parse(&module_text());
    let want: Vec<String> = EXPORTS
        .iter()
        .flat_map(|e| INPUTS.iter().map(|(x, y)| interpret(&module, e, *x, *y)))
        .collect();
    for level in LEVELS {
        let tag = format!("{level:?}");
        let Some(linked) = link(&tag, &compile(level)) else {
            eprintln!("SKIP folded_exports_link_as_distinct_functions: needs wasm-ld (WASM_LD)");
            return;
        };
        let v = view(&linked);
        let exported: BTreeSet<&str> = v.exports.keys().map(String::as_str).collect();
        assert_eq!(
            exported,
            EXPORTS.into_iter().collect(),
            "{tag}: the exports"
        );
        let indices: BTreeSet<u32> = v.exports.values().copied().collect();
        assert_eq!(
            indices.len(),
            EXPORTS.len(),
            "{tag}: two exports share a function"
        );
        // At O0 the linker names each function after its symbol; above,
        // after the object's debug names.
        let marked = v.names.values().any(|n| n.contains(".tcg.crate."));
        assert_eq!(
            marked,
            level == OptLevel::O0,
            "{tag}: the linked debug names {:?}",
            v.names
        );
        for e in EXPORTS {
            assert_eq!(
                v.names.get(&v.exports[e]).map(String::as_str),
                Some(e),
                "{tag}"
            );
        }
        let Some(got) = run(&tag, &linked) else {
            eprintln!("SKIP folded_exports_link_as_distinct_functions: needs node");
            return;
        };
        assert_eq!(got, want, "{tag}: node and the interpreter disagree");
    }
}

/// Two identical recursive bodies that both call `rec_z` (`func.1`): the
/// first `steps` mix rounds of `y`, then `n == 0 ? a : rec_z(n - 1, a) ^ a`.
fn recursive(name: &str, steps: usize) -> String {
    let mut body = String::new();
    let mut prev = 1;
    for i in 0..steps {
        let op = ["mul", "xor", "sub"][i % 3];
        body.push_str(&format!("    %{} = {op} i32 %{prev}, %0\n", i + 2));
        prev = i + 2;
    }
    let n = steps + 2;
    format!(
        "fn @{name}(functy.0) {{\nbb0(%0: i32, %1: i32):\n{body}    \
         %{z} = const i32 0\n    %{c} = icmp eq i32 %0, %{z}\n    condbr %{c}, bb1, bb2\n\
         bb1:\n    ret %{prev}\n\
         bb2:\n    %{one} = const i32 1\n    %{m} = sub i32 %0, %{one}\n    \
         %{r} = call @func.1(%{m}, %{prev})\n    %{x} = xor i32 %{r}, %{prev}\n    ret %{x}\n}}\n\n",
        z = n,
        c = n + 1,
        one = n + 2,
        m = n + 3,
        r = n + 4,
        x = n + 5,
    )
}

fn recursive_text() -> String {
    let mut text = String::from(
        "module \"r16r\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = (i32, i32) -> (i32)\n\n",
    );
    text.push_str(&recursive("rec_a", 60));
    text.push_str(&recursive("rec_z", 60));
    text
}

#[test]
fn a_recursive_group_keeps_the_member_its_bodies_call() {
    let module = parse(&recursive_text());
    let compile_rec = |level: OptLevel| {
        let bytes =
            wasm::compile_object_with_license_optimized(&module, &permit_unlicensed(), level)
                .unwrap_or_else(|e| panic!("{level:?}: {e}"));
        wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
            .validate_all(&bytes)
            .unwrap_or_else(|e| panic!("{level:?}: the object does not validate: {e}"));
        bytes
    };
    let base = view(&compile_rec(OptLevel::O0));
    assert_eq!(
        base.body_of("rec_a"),
        base.body_of("rec_z"),
        "the pair must start identical"
    );
    let inputs: [(i32, i32); 4] = [(0, 5), (1, -3), (9, 77), (40, 123_456)];
    let want: Vec<String> = ["rec_a", "rec_z"]
        .iter()
        .flat_map(|e| {
            let module = &module;
            inputs
                .iter()
                .map(move |(n, y)| interpret(module, e, *n, *y))
        })
        .collect();
    let calls: Vec<String> = ["rec_a", "rec_z"]
        .iter()
        .flat_map(|e| inputs.iter().map(move |(n, y)| format!("{e}({n}, {y})")))
        .collect();
    for level in LEVELS {
        let object = compile_rec(level);
        let v = view(&object);
        let z = v.symbols["rec_z"].0;
        if level == OptLevel::O0 {
            assert_ne!(v.body_of("rec_a"), forwarder(z));
        } else {
            // Folding rec_z onto rec_a would put rec_z's forwarder on every
            // recursion level; rec_a forwards to rec_z instead, and rec_z
            // keeps its body.
            assert_eq!(
                v.body_of("rec_a"),
                forwarder(z),
                "{level:?}: rec_a must forward to rec_z, the member the bodies call"
            );
            assert_ne!(v.body_of("rec_z"), forwarder(v.symbols["rec_a"].0));
        }
        let tag = format!("rec{level:?}");
        let Some(linked) = link_exporting(&tag, &object, &["rec_a", "rec_z"]) else {
            eprintln!("SKIP a_recursive_group_keeps_the_member_its_bodies_call: needs wasm-ld");
            return;
        };
        let Some(got) = run_calls(&tag, &linked, &calls) else {
            eprintln!("SKIP a_recursive_group_keeps_the_member_its_bodies_call: needs node");
            return;
        };
        assert_eq!(got, want, "{level:?}: node and the interpreter disagree");
    }
}

/// `walk(n, fp)` of [`walker`]: `steps` mix rounds of `n`, then
/// `n == 0 ? h : fp(n - 1, fp) ^ h`, computed here for the expected values.
fn walk_expected(n: i32, steps: usize) -> i32 {
    let mut h = n.wrapping_add(40_503);
    for i in 0..steps {
        h = match i % 3 {
            0 => h.wrapping_mul(n),
            1 => h ^ n,
            _ => h.wrapping_sub(n),
        };
    }
    if n == 0 {
        h
    } else {
        walk_expected(n - 1, steps) ^ h
    }
}

/// A global function `(n: i32, fp: ptr) -> i32` that recurses only through
/// the function pointer `fp` it is handed (see [`walk_expected`]).
fn walker(name: &str, steps: usize) -> String {
    let mut body = String::from("    %2 = const i32 40503\n    %3 = add i32 %0, %2\n");
    let mut prev = 3;
    for i in 0..steps {
        let op = ["mul", "xor", "sub"][i % 3];
        body.push_str(&format!("    %{} = {op} i32 %{prev}, %0\n", i + 4));
        prev = i + 4;
    }
    let n = steps + 4;
    format!(
        "fn @{name}(functy.0) {{\nbb0(%0: i32, %1: ptr):\n{body}    \
         %{z} = const i32 0\n    %{c} = icmp eq i32 %0, %{z}\n    condbr %{c}, bb1, bb2\n\
         bb1:\n    ret %{prev}\n\
         bb2:\n    %{one} = const i32 1\n    %{m} = sub i32 %0, %{one}\n    \
         %{r} = call_indirect %1(functy.0)(%{m}, %1)\n    %{x} = xor i32 %{r}, %{prev}\n    \
         ret %{x}\n}}\n\n",
        z = n,
        c = n + 1,
        one = n + 2,
        m = n + 3,
        r = n + 4,
        x = n + 5,
    )
}

const WALK_STEPS: usize = 60;

#[test]
fn an_indirect_recursion_another_object_can_close_keeps_both_bodies() {
    let walkers = parse(&format!(
        "module \"r16w\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = (i32, ptr) -> (i32)\n\n{}{}",
        walker("walk_a", WALK_STEPS),
        walker("walk_b", WALK_STEPS)
    ));
    // The driver takes each walker's address and hands it to that walker,
    // so `walk_b`'s indirect call lands on `walk_b` at every level: had
    // `walk_b` been folded onto `walk_a`, every level would run its
    // forwarder (an extra frame), though the cycle is all `walk_b`'s.
    let driver = parse(
        "module \"r16d\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = (i32, ptr) -> (i32)\nfuncty.1 = (i32) -> (i32)\n\n\
         external fn @walk_a(functy.0) {\n}\n\nexternal fn @walk_b(functy.0) {\n}\n\n\
         fn @run_a(functy.1) {\nbb0(%0: i32):\n    %1 = const ptr symaddr<walk_a>\n    \
         %2 = call @func.0(%0, %1)\n    ret %2\n}\n\n\
         fn @run_b(functy.1) {\nbb0(%0: i32):\n    %1 = const ptr symaddr<walk_b>\n    \
         %2 = call @func.1(%0, %1)\n    ret %2\n}\n",
    );
    let compile_at = |module: &Module, level: OptLevel| {
        let bytes =
            wasm::compile_object_with_license_optimized(module, &permit_unlicensed(), level)
                .unwrap_or_else(|e| panic!("{level:?}: {e}"));
        wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
            .validate_all(&bytes)
            .unwrap_or_else(|e| panic!("{level:?}: the object does not validate: {e}"));
        bytes
    };
    let ns = [0, 1, 7, 40];
    let calls: Vec<String> = ["run_a", "run_b"]
        .iter()
        .flat_map(|e| ns.iter().map(move |n| format!("{e}({n})")))
        .collect();
    let want: Vec<String> = ["run_a", "run_b"]
        .iter()
        .flat_map(|_| ns.iter().map(|&n| walk_expected(n, WALK_STEPS).to_string()))
        .collect();
    for level in LEVELS {
        let object = compile_at(&walkers, level);
        let v = view(&object);
        let (a, a_flags) = v.symbols["walk_a"];
        let (b, b_flags) = v.symbols["walk_b"];
        assert_eq!(
            (a_flags | b_flags) & 0x2,
            0,
            "{level:?}: both walkers are global"
        );
        assert_eq!(
            v.body_of("walk_a"),
            v.body_of("walk_b"),
            "{level:?}: the walkers must stay identical, neither a forwarder"
        );
        assert_ne!(v.body_of("walk_b"), forwarder(a), "{level:?}");
        assert_ne!(v.body_of("walk_a"), forwarder(b), "{level:?}");
        assert!(
            v.body_of("walk_a").len() > 128,
            "{level:?}: the walkers must be above the fold floor"
        );
        let tag = format!("walk{level:?}");
        let Some(linked) = link_objects(
            &tag,
            &[&object, &compile_at(&driver, level)],
            &["run_a", "run_b"],
        ) else {
            eprintln!("SKIP an_indirect_recursion_another_object_can_close: needs wasm-ld");
            return;
        };
        let Some(got) = run_calls(&tag, &linked, &calls) else {
            eprintln!("SKIP an_indirect_recursion_another_object_can_close: needs node");
            return;
        };
        assert_eq!(
            got, want,
            "{level:?}: node and the expected values disagree"
        );
    }
}

/// These hand-built backend fixtures carry no source proof. The explicit
/// legacy policy exercises lowering without changing production admission.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
