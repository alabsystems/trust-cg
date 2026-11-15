// trust-cg-codegen/tests/tmbc_canonical.rs
// Canonical encoding determinism tests for the `.tmbc` binary format (#416).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Transport-format property 2:
//
//     Canonical encoding: forall m: Module, encode(m) produces a unique
//     byte sequence — no padding, no alignment-dependent output, no
//     hash-map iteration order dependency.
//
// These tests assert byte-for-byte equality of `encode_tmbc` output across:
//   (1) two modules built via the exact same builder sequence (baseline
//       determinism — same process, same run);
//   (2) two modules built via sequences that introduce extra intermediate
//       state churn (ordering-sensitivity probe);
//   (3) an encode -> decode -> encode round-trip (encoder is a fixed point
//       of the decode composition).
//
// Audit note (2026-04-19): upstream `trust_ir::binary` walks the module's
// Vec-backed collections in stored order. This test enforces that invariant
// as a regression guard so a future upstream change cannot silently
// reintroduce iteration-order dependency.

use trust_cg_codegen::pipeline::{decode_tmbc, encode_tmbc};
use trust_ir::{DialectTy, FatPtrKind, Global, Linkage, Module as TrustIrModule, Ty};
use trust_ir_build::ModuleBuilder;

/// Build `fn return_42() -> i64 { 42 }`.
fn make_const_module(name: &str) -> TrustIrModule {
    let mut mb = ModuleBuilder::new(name);
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("_return_42", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let r = fb.iconst(Ty::I64, 42);
    fb.ret(vec![r]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Build `fn add(a, b) -> i64 { a + b }` with two globals `G0`, `G1`
/// appended in positional order.
fn make_module_with_globals(name: &str) -> TrustIrModule {
    let mut mb = ModuleBuilder::new(name);
    let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("_add", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I64);
    let b = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let sum = fb.add(Ty::I64, a, b);
    fb.ret(vec![sum]);
    fb.build();
    mb.add_global(Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: "G0".into(),
        ty: Ty::I64,
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
    });
    mb.add_global(Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: "G1".into(),
        ty: Ty::I64,
        mutable: true,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
    });
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------------------------------------------------------------------
// (1) Baseline: same builder sequence, two constructions => identical bytes.
// ---------------------------------------------------------------------------

#[test]
fn encode_tmbc_is_deterministic_const_module() {
    let m1 = make_const_module("tmbc_canon_const");
    let m2 = make_const_module("tmbc_canon_const");
    let b1 = encode_tmbc(&m1).expect("encode m1");
    let b2 = encode_tmbc(&m2).expect("encode m2");
    assert_eq!(
        b1, b2,
        "encode_tmbc must be byte-deterministic for structurally-equal modules"
    );
}

#[test]
fn encode_tmbc_is_deterministic_module_with_globals() {
    let m1 = make_module_with_globals("tmbc_canon_globals");
    let m2 = make_module_with_globals("tmbc_canon_globals");
    let b1 = encode_tmbc(&m1).expect("encode m1");
    let b2 = encode_tmbc(&m2).expect("encode m2");
    assert_eq!(
        b1, b2,
        "encode_tmbc must be byte-deterministic for modules with globals"
    );
}

// ---------------------------------------------------------------------------
// (2) Churn probe: build one module, encode, drop, rebuild in a fresh
//     process-local allocator context, re-encode. Any HashMap-backed
//     container with a random seed (ASLR-randomized DefaultHasher) would
//     diverge across constructions inside the same process run; Vec-backed
//     collections should remain byte-stable.
// ---------------------------------------------------------------------------

#[test]
fn encode_tmbc_stable_across_many_reconstructions() {
    let reference =
        encode_tmbc(&make_module_with_globals("tmbc_canon_churn")).expect("encode reference");
    for i in 0..16 {
        // Allocate and drop noise to jitter allocator state between builds.
        let _scratch: Vec<String> = (0..i + 1).map(|k| format!("noise-{}-{}", i, k)).collect();
        let m = make_module_with_globals("tmbc_canon_churn");
        let b = encode_tmbc(&m).expect("encode iteration");
        assert_eq!(
            reference, b,
            "iteration {i}: encode_tmbc diverged from reference encoding"
        );
    }
}

// ---------------------------------------------------------------------------
// (3) Round-trip canonicality: encode -> decode -> encode is a fixed point.
//     If any field round-trips to a semantically-equal but
//     byte-non-equivalent state (e.g. reordering), this catches it.
// ---------------------------------------------------------------------------

#[test]
fn encode_decode_encode_is_fixed_point() {
    let m = make_module_with_globals("tmbc_canon_fixed_point");
    let b1 = encode_tmbc(&m).expect("encode #1");
    let round = decode_tmbc(&b1).expect("decode");
    let b2 = encode_tmbc(&round).expect("encode #2");
    assert_eq!(
        b1, b2,
        "encode . decode . encode must equal encode (canonical fixed point)"
    );
}

/// The outer tMBC envelope stays unchanged while the inner TrustIR payload
/// selects the minimum lossless version for each nominal type surface.
fn versioned_transport_modules() -> [(TrustIrModule, u32); 3] {
    let plain = make_const_module("exact_v38");
    let mut dialect = make_const_module("exact_v39");
    dialect
        .types
        .push(Ty::Dialect(Box::new(DialectTy::new("example", "token", 1))));
    let mut container = make_const_module("exact_v40");
    container
        .types
        .push(Ty::FatPtr(FatPtrKind::ContainerVtable));
    [(plain, 38), (dialect, 39), (container, 40)]
}

#[test]
fn tmbc_preserves_versioned_nominal_types_without_changing_outer_version() {
    for (module, inner_version) in versioned_transport_modules() {
        let encoded = encode_tmbc(&module).expect("encode versioned module");
        assert_eq!(&encoded[..4], b"tMBC");
        assert_eq!(&encoded[4..8], &1u32.to_le_bytes());
        assert_eq!(&encoded[8..16], b"TRUST_IR");
        assert_eq!(&encoded[16..20], &inner_version.to_le_bytes());
        let decoded = decode_tmbc(&encoded).expect("decode exact versioned module");
        assert_eq!(decoded, module, "inner version {inner_version}");
        assert_eq!(encode_tmbc(&decoded).unwrap(), encoded);
    }
}

#[test]
fn tmbc_rejects_trailers_and_concatenated_payloads_at_every_current_version() {
    for (module, inner_version) in versioned_transport_modules() {
        let encoded = encode_tmbc(&module).expect("encode versioned module");
        assert_eq!(decode_tmbc(&encoded).unwrap(), module);
        // Include both a second bare TrustIR payload and another complete tMBC
        // envelope: neither is framing the exact-input API may silently ignore.
        for suffix in [&[0u8][..], &[0xffu8][..], &encoded[8..], &encoded[..]] {
            let mut extended = encoded.clone();
            extended.extend_from_slice(suffix);
            let error = decode_tmbc(&extended).expect_err("unconsumed input must reject");
            let message = error.to_string();
            assert!(
                message.contains("failed to deserialize tMBC payload:")
                    && message.contains("trailing bytes"),
                "inner version {inner_version}: wrong refusal boundary: {message}"
            );
        }
    }
}

#[test]
fn tmbc_rejects_foreign_v39_parameter_modes_instead_of_erasing_them() {
    let module = make_module_with_globals("foreign_param_modes");
    let mut encoded = encode_tmbc(&module).expect("encode module");
    encoded[16..20].copy_from_slice(&39u32.to_le_bytes());
    assert_eq!(decode_tmbc(&encoded).unwrap(), module);
    // The divergent v39 lineage appends row count, FuncTyId, mode count and
    // modes (1=Lazy, 2=ByRef). Our transport must not silently drop that suffix.
    for mode in [1, 2] {
        let mut extended = encoded.clone();
        extended.extend_from_slice(&[1, 0, 2, mode, mode]);
        let error = decode_tmbc(&extended).expect_err("foreign modes must reject");
        assert!(error.to_string().contains("trailing bytes"));
    }
}
