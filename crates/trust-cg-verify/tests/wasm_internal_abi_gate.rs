// trust-cg-verify/tests/wasm_internal_abi_gate.rs - the live gate for the
// wasm32 internal multi-value ABI
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Runs `trust_cg_verify::wasm_internal_abi` against the REAL wasm object
//! lane and against its negative controls.
//!
//! `src/wasm_internal_abi.rs` reads object bytes only (the dependency
//! direction is codegen -> verify), so its teeth live here, over objects the
//! live lane emits for the corpus in `support/wasm_internal_abi_corpus.rs`:
//!
//!  1. every object the lane emits for the corpus, at O0 to O3, passes the
//!     gate and the source binding against its trust-ir module; at O1 and
//!     above the callee object defines its six internal entries (so the
//!     checks ran over real internal entries, not an empty set), at O0 none;
//!  2. the link binding accepts the crate's four objects and refuses a
//!     caller whose callee object defines no internal entry, and a crate in
//!     which two objects define one internal entry;
//!  3. BYTE MUTATIONS of a real object are refused: the internal entry's
//!     symbol made default-visibility, exported or weak; a call relocation
//!     retyped as a table index; the `call` opcode turned into `ref.func`; a
//!     forwarding store moved off the BasicCABI layout (which only the
//!     source binding sees) or onto another result's bytes;
//!  4. HAND-BUILT objects crossing the boundary are refused: a table-entered,
//!     exported, element-segment, weak, default-visibility, non-crate-private
//!     or unsuffixed multi-value function; a local one only called directly
//!     is inside it.
//!
//! The checks are structural (module docs of `wasm_internal_abi`): they do
//! not prove that an internal entry computes its trust-ir function, which
//! `trust-cg-codegen/tests/wasm_p6_multivalue.rs` and the bridge's wasm32
//! differential exercise by execution. No external tool is needed here.
//!
//! The module under test (`trust_cg_verify::wasm_internal_abi`) and the
//! `compile_object_optimized` entry the corpus compiles through are
//! provisional surfaces pending the owner's sign-off: this target follows
//! them if they change, and is not a contract for their shape.
//!
//! `trust-cg-codegen` is a DEV-dependency of this crate for files like this
//! one (see `wasm_abi_proofs_gate.rs`).

#[path = "support/wasm_internal_abi_corpus.rs"]
mod corpus;

use corpus::*;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm;
use trust_cg_verify::wasm_internal_abi as gate;

#[test]
fn every_object_the_lane_emits_passes_the_gate() {
    let callee = callee_module();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        for module in [callee.clone(), caller_module("b_entry"), table_module()] {
            let bytes = compile(&module, level);
            let ev = gate::check_object_against_module(&bytes, &module)
                .unwrap_or_else(|e| panic!("{} at {level:?}: {e}", module.name));
            assert!(
                ev.checks.iter().all(|c| c.ok),
                "{} at {level:?}: {ev:?}",
                module.name
            );
            match (level, module.name.as_str()) {
                (OptLevel::O0, _) => assert_eq!(
                    ev.defined_entries + ev.imported_entries,
                    0,
                    "{} at O0 keeps the C form",
                    module.name
                ),
                (_, "callee") => {
                    assert_eq!(
                        (ev.defined_entries, ev.forwarding_entries),
                        (6, 6),
                        "the callee object at {level:?}: {ev:?}"
                    );
                    assert!(ev.direct_calls >= 6, "{level:?}: {ev:?}");
                }
                (_, "b_entry") => assert_eq!(
                    (ev.imported_entries, ev.defined_entries),
                    (6, 0),
                    "the caller object at {level:?}: {ev:?}"
                ),
                _ => assert_eq!(
                    ev.defined_entries + ev.imported_entries,
                    0,
                    "the static's object names only C forms: {ev:?}"
                ),
            }
        }
    }
}

#[test]
fn the_link_binding_accepts_the_crate_and_refuses_disagreement() {
    let a = compile(&callee_module(), OptLevel::O2);
    let b = compile(&caller_module("b_entry"), OptLevel::O2);
    let b0 = compile(&caller_module("b0_entry"), OptLevel::O0);
    let c = compile(&table_module(), OptLevel::O2);
    let ev = gate::check_link(&[&a, &b, &b0, &c]).expect("the four objects agree");
    assert_eq!((ev.entries, ev.imports), (6, 6), "{ev:?}");

    // Callee at O0 (C forms only), caller at O2 (internal entries).
    let a0 = compile(&callee_module(), OptLevel::O0);
    let err = gate::check_link(&[&a0, &b]).expect_err("no object defines the internal entries");
    assert!(err.contains(".tcg.mv"), "{err}");
    // Two objects defining one internal entry.
    let err = gate::check_link(&[&a, &a]).expect_err("an internal entry defined twice");
    assert!(err.contains("is defined by 2 objects"), "{err}");
}

#[test]
fn the_gate_refuses_mutated_objects() {
    let callee = callee_module();
    let a = compile(&callee, OptLevel::O2);
    let o = gate::decode_object(&a).unwrap();
    let wide = o
        .symbols
        .iter()
        .find(|s| s.name.as_deref() == Some(mv(&cp("wide")).as_str()))
        .expect("wide's internal entry");
    assert_eq!(a[wide.flags_at], 0x04, "a one-byte hidden flag");
    for (flags, what) in [
        (0x00, "default visibility"),
        (0x24, "exported"),
        (0x05, "weak"),
    ] {
        let err = gate::check_object(&patched(&a, wide.flags_at, flags))
            .expect_err(&format!("the gate refuses a {what} internal entry"));
        assert!(
            err.contains("local, or a strong hidden internal entry"),
            "{what}: {err}"
        );
    }
    // A direct call to an internal entry relocated as a table index, or
    // reached through `ref.func`.
    let wide_sym = o
        .symbols
        .iter()
        .position(|s| s.name.as_deref() == Some(mv(&cp("wide")).as_str()))
        .unwrap() as u32;
    let call = o
        .relocs
        .iter()
        .find(|r| r.ty == gate::R_FUNCTION_INDEX_LEB && r.index == wide_sym)
        .expect("a call to wide's internal entry");
    let err = gate::check_object(&patched(&a, call.ty_at, gate::R_TABLE_INDEX_SLEB))
        .expect_err("the gate refuses a table-index relocation of an internal entry");
    assert!(err.contains("is a direct call"), "{err}");
    let opcode_at = o.code_at + call.offset as usize - 1;
    assert_eq!(a[opcode_at], 0x10);
    let err = gate::check_object(&patched(&a, opcode_at, 0xd2))
        .expect_err("the gate refuses an internal entry reached by ref.func");
    assert!(err.contains("is a direct call"), "{err}");

    // `pair`'s C-form entry stores its `i8` result at offset 4. At 5 the
    // stores are still disjoint, so the object-only binding holds, but the
    // BasicCABI layout of `(i32, i8)` does not: the source binding refuses.
    let pair = o
        .symbols
        .iter()
        .find(|s| s.flags & 0x10 == 0 && s.name.as_deref() == Some(cp("pair").as_str()))
        .and_then(|s| s.index)
        .unwrap();
    let body = &o.bodies[pair as usize - o.func_imports.len()];
    let code = &o.code[body.code_start..body.end];
    // The last store: `i32.store8 align=0 offset=4`, then `end`.
    let n = code.len();
    assert_eq!(&code[n - 4..], &[0x3a, 0x00, 0x04, 0x0b], "{code:02x?}");
    let at = o.code_at + body.code_start + n - 2;
    let moved = patched(&a, at, 0x05);
    gate::check_object(&moved).expect("disjoint stores pass the object-only binding");
    let err = gate::check_object_against_module(&moved, &callee)
        .expect_err("the source binding refuses a store off the BasicCABI layout");
    assert!(err.contains("BasicCABI layout"), "{err}");
    // Overlapping the `i32` result instead fails the object-only binding.
    let err = gate::check_object(&patched(&a, at, 0x02)).expect_err("overlapping stores");
    assert!(err.contains("overlaps"), "{err}");
}

#[test]
fn the_gate_refuses_hand_built_boundary_crossings() {
    use wasm::encode::SymbolFlags;
    let hidden = SymbolFlags {
        hidden: true,
        ..Default::default()
    };
    let entry = mv(&cp("f"));
    let failed = |bytes: &[u8]| -> Vec<String> {
        gate::object_evidence(bytes)
            .expect("decode")
            .checks
            .into_iter()
            .filter(|c| !c.ok)
            .map(|c| c.name)
            .collect()
    };
    // The boundary itself holds for a hidden internal entry only called
    // directly; what fails is the missing C-form entry.
    let base = failed(&hand_object(&entry, hidden, false));
    assert!(
        base.iter().all(|n| n.contains("C-form entry")),
        "only the forwarding entry is missing: {base:?}"
    );
    let cases: [(&str, Vec<u8>, &str); 7] = [
        (
            "table-entered",
            hand_object(&entry, hidden, true),
            "is a direct call",
        ),
        ("exported", closed_exporting_module(), "is not exported"),
        (
            "in an element segment",
            closed_exporting_module(),
            "is in no element segment",
        ),
        (
            "weak",
            hand_object(
                &entry,
                SymbolFlags {
                    weak: true,
                    hidden: true,
                    ..Default::default()
                },
                false,
            ),
            "strong hidden internal entry",
        ),
        (
            "default visibility",
            hand_object(&entry, SymbolFlags::default(), false),
            "strong hidden internal entry",
        ),
        (
            "not crate-private",
            hand_object("plain.tcg.mv", hidden, false),
            "strong hidden internal entry",
        ),
        (
            "unsuffixed",
            hand_object(&cp("f"), hidden, false),
            "strong hidden internal entry",
        ),
    ];
    for (what, bytes, expect) in cases {
        let failures = failed(&bytes);
        assert!(
            failures.iter().any(|n| n.contains(expect)),
            "{what}: expected a failed `{expect}` check, got {failures:?}"
        );
        assert!(gate::check_object(&bytes).is_err(), "{what}");
    }
    // A local multi-value function only called directly is inside the
    // boundary.
    let local = failed(&hand_object(
        "anything",
        SymbolFlags {
            local: true,
            ..Default::default()
        },
        false,
    ));
    assert!(local.is_empty(), "{local:?}");
}
