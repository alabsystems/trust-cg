// trust-cg-codegen/tests/wasm_p6_multivalue.rs - wasm32 lane: the internal
// multi-value ABI across objects
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The wasm object lane's internal ABI (P6 stage B): at O1 and above a
//! strong, hidden function under a crate-private name whose C form returns
//! through `sret` (several results, or a 128-bit one) is defined as an
//! internal entry `<name>.tcg.mv` returning wasm multi-value results, beside
//! a C-form entry under its own name that forwards to it; every direct call
//! in every object calls the internal entry, every function pointer names
//! the C-form entry.
//!
//! * Four objects of one "crate" — the callee object, an O2 caller, an O0
//!   caller (C-form calls only) and a static's object holding a function
//!   pointer — link with `wasm-ld` and agree, in node, with the whole program
//!   compiled as one closed module (BasicCABI everywhere) and with the
//!   trust-ir interpreter.
//! * Exported (default visibility), link-once, five-lane and O0 functions
//!   keep the C form; the address-taken function keeps its internal entry
//!   for direct calls and its C form for the pointer.
//! * The link binding of the ABI-boundary gate
//!   (`trust_cg_verify::wasm_internal_abi::check_link`) and `wasm-ld` both
//!   refuse a caller whose callee object defines no internal entry.
//! * A producer that withholds the `multivalue` feature
//!   (`WasmInlineHints::without_multivalue`) gets the C form everywhere, and
//!   its objects link and agree too.
//!
//! The objects come from the corpus shared with the gate's own target,
//! `trust-cg-verify/tests/wasm_internal_abi_gate.rs`, which holds the gate's
//! negative controls (mutated and hand-built objects) and checks every
//! object the lane emits for this corpus at O0 to O3.
//!
//! Node is required to execute the wasm and `wasm-ld` (`WASM_LD`) to link
//! the objects; the absence of either is a loud SKIP.
//!
//! The entries this test drives (`compile_object_optimized` through the shared
//! corpus, `compile_object_with_evidence`'s `local_emission.enabled` /
//! `fallbacks`, `compile_object_with_license_options_hints` with
//! `WasmOptOptions` and `WasmInlineHints::without_multivalue`) and the gate's
//! `trust_cg_verify::wasm_internal_abi::check_link` are provisional surfaces
//! pending the owner's sign-off: this test follows them if they change, and
//! is not a contract for their shape.

#[path = "../../trust-cg-verify/tests/support/wasm_internal_abi_corpus.rs"]
mod corpus;

use std::path::PathBuf;
use std::process::Command;

use corpus::*;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{self, WasmModulePolicy, WasmOptOptions};
use trust_cg_verify::wasm_internal_abi as gate;
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

const ENTRIES: [&str; 4] = ["a_entry", "b_entry", "b0_entry", "c_entry"];

/// [`compile`], validated with every wasm feature enabled.
fn object(module: &Module, level: OptLevel) -> Vec<u8> {
    let bytes = compile(module, level);
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&bytes)
        .unwrap_or_else(|e| panic!("`{}` does not validate: {e}", module.name));
    bytes
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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_p6mv_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Link `objects`; `Err` carries `wasm-ld`'s diagnostics. `None` when
/// `wasm-ld` is absent.
fn link(objects: &[&[u8]]) -> Option<Result<Vec<u8>, String>> {
    let Some(ld) = wasm_ld() else {
        eprintln!("SKIP: wasm-ld not found (set WASM_LD); the objects were not linked");
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
    for (k, o) in objects.iter().enumerate() {
        let p = dir.join(format!("o{k}.o"));
        std::fs::write(&p, o).unwrap();
        cmd.arg(p);
    }
    let out = cmd.output().expect("run wasm-ld");
    let result = if out.status.success() {
        Ok(std::fs::read(dir.join("m.wasm")).unwrap())
    } else {
        Err(String::from_utf8_lossy(&out.stderr).into_owned())
    };
    let _ = std::fs::remove_dir_all(&dir);
    Some(result)
}

fn inputs() -> Vec<(i64, i64)> {
    let edges: [i64; 8] = [0, 1, -1, 7, -300, i32::MAX as i64, i64::MAX, i64::MIN];
    let mut out = Vec::new();
    for &a in &edges {
        for &b in &edges {
            out.push((a, b));
        }
    }
    let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
    for _ in 0..40 {
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let a = s as i64;
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        out.push((a, (s as i64) >> 20));
    }
    out
}

/// Every named export on every input; `None` when node is absent.
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

fn interpret(module: &Module, name: &str, a: i64, b: i64) -> Option<i64> {
    let f = module.function_by_name(name)?;
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

/// Memory and global accesses in the body of the function `name` defines.
fn body_traffic(bytes: &[u8], name: &str) -> (usize, usize) {
    use wasmparser::Operator as O;
    let o = gate::decode_object(bytes).expect("decode");
    let f = o
        .symbols
        .iter()
        .find(|s| s.kind == 0 && s.flags & 0x10 == 0 && s.name.as_deref() == Some(name))
        .and_then(|s| s.index)
        .unwrap_or_else(|| panic!("no definition of `{name}`"));
    let body = &o.bodies[f as usize - o.func_imports.len()];
    let reader = wasmparser::BinaryReader::new(&o.code[body.code_start..body.end], 0);
    let ops = wasmparser::OperatorsReader::new(reader);
    let (mut memory, mut globals) = (0, 0);
    for op in ops {
        match op.expect("operator") {
            O::GlobalGet { .. } | O::GlobalSet { .. } => globals += 1,
            O::I32Load { .. }
            | O::I64Load { .. }
            | O::F64Load { .. }
            | O::I32Load8S { .. }
            | O::I32Load8U { .. }
            | O::I32Load16S { .. }
            | O::I32Load16U { .. }
            | O::I32Store { .. }
            | O::I64Store { .. }
            | O::F64Store { .. }
            | O::I32Store8 { .. }
            | O::I32Store16 { .. }
            | O::MemoryCopy { .. } => memory += 1,
            _ => {}
        }
    }
    (memory, globals)
}

#[test]
fn internal_entries_link_across_objects_and_agree() {
    let callee = callee_module();
    let a = object(&callee, OptLevel::O2);
    let b = object(&caller_module("b_entry"), OptLevel::O2);
    let b0 = object(&caller_module("b0_entry"), OptLevel::O0);
    let c = object(&table_module(), OptLevel::O2);

    // The callee object defines an internal entry and a C-form entry for
    // every strong crate-private function with a multi-value form, and
    // nothing else gets one.
    let sa = symbols(&a);
    for name in ["wide", "pair", "trio", "quad", "mixed", "taken"] {
        let n = cp(name);
        assert_eq!(sa.get(&mv(&n)), Some(&(0x4, true)), "`{n}` internal entry");
        assert_eq!(sa.get(&n), Some(&(0x4, true)), "`{n}` C-form entry");
    }
    for n in [cp("five"), cp("once"), "pub_wide".to_string()] {
        assert!(!sa.contains_key(&mv(&n)), "`{n}` keeps the C form only");
        assert!(sa.get(&n).is_some_and(|(_, d)| *d), "`{n}` is defined");
    }
    let ev = gate::check_object_against_module(&a, &callee).expect("the callee object's gate");
    assert_eq!(
        (ev.defined_entries, ev.forwarding_entries),
        (6, 6),
        "{ev:?}"
    );
    assert!(
        ev.direct_calls >= 6,
        "a_entry calls the internal entries: {ev:?}"
    );
    // The internal entries that compute only on scalars and pairs keep no
    // frame and touch no memory: their results leave as wasm values.
    for name in ["wide", "pair", "quad", "taken"] {
        assert_eq!(
            body_traffic(&a, &mv(&cp(name))),
            (0, 0),
            "`{name}`'s internal entry has no frame and no memory traffic"
        );
    }
    let o = gate::decode_object(&a).unwrap();
    assert!(
        o.features
            .iter()
            .any(|(p, n)| *p == b'+' && n == "multivalue"),
        "{:?}",
        o.features
    );

    // The O2 caller imports the internal entries it calls, and `taken`'s C
    // form too, for its function pointer; the O0 caller imports only C forms.
    let sb = symbols(&b);
    for name in ["wide", "pair", "trio", "quad", "mixed", "taken"] {
        assert_eq!(sb.get(&mv(&cp(name))), Some(&(0x14, false)), "{name}");
    }
    assert!(
        sb.contains_key(&cp("taken")),
        "taken's C form for the pointer"
    );
    assert!(
        !sb.contains_key(&cp("wide")),
        "no C-form import of a called-only callee"
    );
    let ev = gate::check_object(&b).expect("the O2 caller's gate");
    assert_eq!((ev.imported_entries, ev.defined_entries), (6, 0), "{ev:?}");
    let ev = gate::check_object(&b0).expect("the O0 caller's gate");
    assert_eq!(ev.imported_entries + ev.defined_entries, 0, "{ev:?}");
    assert!(symbols(&b0).keys().all(|n| !n.ends_with(".tcg.mv")));
    // The static's object names only C forms.
    assert!(symbols(&c).keys().all(|n| !n.ends_with(".tcg.mv")));

    let all: [&[u8]; 4] = [&a, &b, &b0, &c];
    let link_ev = gate::check_link(&all).expect("the four objects agree");
    assert_eq!((link_ev.entries, link_ev.imports), (6, 6), "{link_ev:?}");

    let whole = whole_module();
    let (reference, _) = wasm::compile_module_with_evidence_policy_and_license(
        &whole,
        &WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("compile the whole program as one closed module");
    let inputs = inputs();
    let Some(want) = run(&reference, &ENTRIES, &inputs) else {
        return;
    };
    // The reference agrees with the interpreter wherever it is defined.
    for (name, col) in ENTRIES.iter().zip(&want) {
        let mut defined = 0;
        for (&(x, y), have) in inputs.iter().zip(col) {
            if let Some(expect) = interpret(&whole, name, x, y) {
                defined += 1;
                assert_eq!(*have, Some(expect), "reference {name}({x}, {y})");
            }
        }
        // The interpreter runs every direct-call entry; `c_entry` calls only
        // through a static's pointers, which it may not model.
        assert!(
            *name == "c_entry" || defined * 2 >= inputs.len(),
            "the interpreter ran {name}"
        );
    }
    let Some(linked) = link(&all) else {
        return;
    };
    let linked = linked.expect("wasm-ld links the four objects");
    let got = run(&linked, &ENTRIES, &inputs).expect("node ran the reference");
    for ((name, w), g) in ENTRIES.iter().zip(&want).zip(&got) {
        for ((&(x, y), w), g) in inputs.iter().zip(w).zip(g) {
            assert_eq!(g, w, "linked {name}({x}, {y})");
        }
    }
}

#[test]
fn a_caller_needs_its_callees_internal_entries() {
    // Callee at O0 (C forms only), caller at O2 (internal entries): the
    // gate's link check and `wasm-ld` both refuse; nothing binds silently.
    let a0 = object(&callee_module(), OptLevel::O0);
    let b = object(&caller_module("b_entry"), OptLevel::O2);
    let err = gate::check_link(&[&a0, &b]).expect_err("no object defines the internal entries");
    assert!(err.contains(".tcg.mv"), "{err}");
    if let Some(linked) = link(&[&a0, &b]) {
        let err = linked.expect_err("wasm-ld refuses the undefined internal entries");
        assert!(err.contains(".tcg.mv"), "{err}");
    }
}

#[test]
fn the_emission_pass_validates_every_internal_entry_and_its_callers() {
    // The emission pass validates every body, the internal entries and their
    // callers included: nothing falls back.
    for module in [callee_module(), caller_module("b_entry")] {
        let (_, evidence) =
            wasm::compile_object_with_evidence_and_license(&module, &permit_unlicensed())
                .expect("compile");
        assert!(
            evidence.local_emission.enabled && evidence.local_emission.fallbacks.is_empty(),
            "{}: {:?}",
            module.name,
            evidence.local_emission.fallbacks
        );
    }
}

#[test]
fn a_session_without_multivalue_keeps_the_c_form() {
    // The producer withholds the `multivalue` feature (rustc's
    // `-C target-cpu=mvp`): no internal entry is defined or imported, no
    // `+multivalue` is declared, and the objects still link and agree.
    let hints = wasm::WasmInlineHints {
        without_multivalue: true,
        ..Default::default()
    };
    let compile_without = |module: &Module| {
        let bytes = wasm::compile_object_with_license_options_hints(
            module,
            &permit_unlicensed(),
            WasmOptOptions::at(OptLevel::O2),
            &hints,
        )
        .unwrap_or_else(|e| panic!("compile `{}`: {e}", module.name));
        wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
            .validate_all(&bytes)
            .unwrap_or_else(|e| panic!("`{}` does not validate: {e}", module.name));
        bytes
    };
    let callee = callee_module();
    let a = compile_without(&callee);
    let b = compile_without(&caller_module("b_entry"));
    let ev = gate::check_object_against_module(&a, &callee).expect("gate");
    assert_eq!(ev.defined_entries + ev.imported_entries, 0, "{ev:?}");
    let ev = gate::check_object(&b).expect("gate");
    assert_eq!(ev.defined_entries + ev.imported_entries, 0, "{ev:?}");
    for bytes in [&a, &b] {
        assert!(symbols(bytes).keys().all(|n| !n.ends_with(".tcg.mv")));
        let o = gate::decode_object(bytes).unwrap();
        assert!(
            !o.features.iter().any(|(_, n)| n == "multivalue"),
            "{:?}",
            o.features
        );
    }
    // The default hints admit the feature: the same callee at O2 defines
    // internal entries.
    let ev = gate::check_object(&object(&callee, OptLevel::O2)).expect("gate");
    assert!(ev.defined_entries > 0, "{ev:?}");

    let b0 = object(&caller_module("b0_entry"), OptLevel::O0);
    let c = object(&table_module(), OptLevel::O2);
    let all: [&[u8]; 4] = [&a, &b, &b0, &c];
    gate::check_link(&all).expect("the four objects agree");
    let whole = whole_module();
    let (reference, _) = wasm::compile_module_with_evidence_policy_and_license(
        &whole,
        &WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("compile the whole program as one closed module");
    let inputs = inputs();
    let Some(want) = run(&reference, &ENTRIES, &inputs) else {
        return;
    };
    let Some(linked) = link(&all) else {
        return;
    };
    let linked = linked.expect("wasm-ld links the four objects");
    let got = run(&linked, &ENTRIES, &inputs).expect("node ran the reference");
    for ((name, w), g) in ENTRIES.iter().zip(&want).zip(&got) {
        for ((&(x, y), w), g) in inputs.iter().zip(w).zip(g) {
            assert_eq!(g, w, "linked {name}({x}, {y})");
        }
    }
}

#[test]
fn reserved_internal_entry_names_are_refused() {
    let items = vec![define(&mv(&cp("wide")), Sym::Internal, 1, &callees()[0].3)];
    let module = assemble("reserved", "", &items);
    let err = wasm::compile_object_with_license(&module, &permit_unlicensed())
        .expect_err("a reserved name is refused");
    assert!(err.to_string().contains("[TCG-WASM-SYMBOL]"), "{err}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
