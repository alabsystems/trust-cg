// trust-cg-verify/tests/wasm_value_domain_gate.rs — the P3 value-domain gate
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// THE BUILD GATE for the WebAssembly P3 ("value domain") opcode surface: the
// sub-word and FP linear-memory accesses (spec §5.4.4, bytes 0x28..=0x40), the
// sign-extension operators (§5.4.6, 0xc0..=0xc4), and the four named deferrals.
//
// The wasm lane's honesty rests on the coverage gate DECODING the opcode bytes
// the backend emits and reconstructing an obligation per instruction. P3 adds a
// large batch of opcodes at once; if the verify side does not grow with it, the
// gate's denominator quietly stops covering what the backend emits and an
// unobligated opcode reads as trusted rather than as debt. These tests pin the
// grown denominator, the credited set, and the RED set, so any drift in either
// direction fails the build.
//
// Every test states the invariant it locks in.

use trust_cg_verify::coverage_gate::{
    CoverageFinding, CoverageGate, GateArch, OpcodeClass, classify_wasm_value_domain,
};
use trust_cg_verify::lowering_proof::{VerificationConfig, verify_by_evaluation_with_config};
use trust_cg_verify::proof_database::{ProofCategory, ProofDatabase};
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::wasm_semantics as w;
use trust_cg_verify::wasm_value_domain as vd;

/// Run `f` on a 64 MiB stack so `ProofDatabase::new()` does not overflow the
/// default 8 MiB test-thread stack (proof_database.rs #205).
fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("wasm-value-domain-gate".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large-stack gate thread")
        .join()
        .expect("gate thread panicked")
}

// ===========================================================================
// 1. The inventory: the denominator grew with the opcode set
// ===========================================================================

/// PINS the P3 value-domain inventory: 32 rows = 28 credited opcode bytes +
/// 4 named deferrals, with 28 covered and 4 RED.
///
/// The 28 credited bytes are the 14 loads (0x28..=0x35), the 9 stores
/// (0x36..=0x3e) and the 5 sign-extension operators (0xc0..=0xc4). The 4 RED
/// rows are `br_table`, `memory.size`, `memory.grow` and data segments — each an
/// explicit `DeferredUnfaithfulModel` carrying its own reason, never an
/// allowlist exclusion and never a fake green.
#[test]
fn wasm_value_domain_inventory_pins_accepted_and_deferred_rows() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::WasmValueDomain));
    // Always print the audit so the deferrals stay visible in CI output.
    eprintln!("{}", report.audit_log());

    assert_eq!(
        report.total(),
        32,
        "P3 inventory row count changed — 28 credited opcode bytes + 4 named deferrals.\n{}",
        report.audit_log()
    );
    assert_eq!(
        report.emittable_count(),
        32,
        "every P3 row is EmittableNeedsProof: the credited bytes carry reconstructions and the \
         deferrals keep their debt IN the denominator. Nothing here may be allowlisted out.\n{}",
        report.audit_log()
    );
    assert_eq!(
        report.covered_count(),
        28,
        "P3 covered count changed — must be 28 (14 loads + 9 stores + 5 sign-extensions), ALL \
         credited via byte-decoded reconstruction. Do NOT inflate by crediting a deferral.\n{}",
        report.audit_log()
    );
    assert_eq!(
        report.allowlisted_count(),
        0,
        "no P3 row may be excluded from the denominator"
    );
    assert_eq!(
        report.failures().len(),
        4,
        "exactly the four named deferrals are RED:\n{}",
        report.failure_summary()
    );
}

/// LOCKS IN that every RED P3 row is a NAMED deferral, never a wiring gap.
///
/// A `NoProofMapping` row here would mean an opcode reached the inventory with
/// no obligation built for it at all — the #68-fneg class the gate exists to
/// catch. A `DeferredUnfaithfulModel` row is expected, auditable debt.
#[test]
fn wasm_value_domain_red_rows_are_named_deferrals() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::WasmValueDomain));
    let failures = report.failures();
    for row in &failures {
        assert!(
            matches!(
                row.finding,
                Some(CoverageFinding::DeferredUnfaithfulModel { .. })
            ),
            "P3 RED row {} is a WIRING GAP, not an honest deferral:\n{}",
            row.opcode_display,
            report.failure_summary()
        );
    }
    let names: std::collections::HashSet<&str> = failures
        .iter()
        .map(|row| row.opcode_display.as_str())
        .collect();
    assert_eq!(
        names,
        std::collections::HashSet::from([
            "wasm::br_table (0x0e)",
            "wasm::memory.size (0x3f)",
            "wasm::memory.grow (0x40)",
            "wasm::data segments (module section 11; memory.init 0xfc 8 / data.drop 0xfc 9)",
        ]),
        "the RED set changed — landing evidence removes a row, admitting debt adds one; both are \
         deliberate"
    );
}

/// LOCKS IN that every covered P3 row names RECONSTRUCTION as its credit path.
///
/// The mirror of `meta_c_every_credit_is_genuine_never_static_degenerate` for
/// this arch: the P3 headline must rest on `is_reconstructed() && Valid`, never
/// on a static `X == X` match.
#[test]
fn wasm_value_domain_credit_is_always_reconstruction() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::WasmValueDomain));
    for row in &report.rows {
        if row.class != OpcodeClass::EmittableNeedsProof || row.finding.is_some() {
            continue;
        }
        assert!(
            row.note.contains("[reconstruction]"),
            "covered P3 row {} does not name a reconstruction credit: {}",
            row.opcode_display,
            row.note
        );
    }
}

/// LOCKS IN that the enumerated surface and the classifier agree.
///
/// `classify_wasm_value_domain` returning `None` for an enumerated byte would
/// mean a row exists that the classifier does not recognize — the two halves
/// drifting apart is exactly how an opcode goes invisible.
#[test]
fn wasm_value_domain_surface_and_classifier_agree() {
    for byte in vd::all_wasm_value_domain_bytes() {
        assert_eq!(
            classify_wasm_value_domain(byte),
            Some(OpcodeClass::EmittableNeedsProof),
            "0x{byte:02x} is enumerated but not classified"
        );
    }
    for deferral in vd::WASM_VALUE_DOMAIN_DEFERRALS {
        if let Some(byte) = deferral.opcode_byte {
            assert_eq!(
                classify_wasm_value_domain(byte),
                Some(OpcodeClass::EmittableNeedsProof),
                "deferred 0x{byte:02x} must stay IN the denominator"
            );
        }
    }
    // A byte off the surface classifies as nothing at all (fail closed).
    for byte in [0x00u8, 0x6a, 0xc5, 0xff] {
        assert_eq!(classify_wasm_value_domain(byte), None, "0x{byte:02x}");
    }
}

// ===========================================================================
// 2. The obligations have teeth
// ===========================================================================

/// LOCKS IN that a ONE-BIT opcode slip inside the sub-word memory block is
/// REFUTED, per family.
///
/// `i32.load8_u` is 0x2d and `i32.load8_s` is 0x2c: they differ by the low bit
/// and by the extension they apply. That is exactly where a wrong opcode byte
/// hides, and an obligation that could not tell them apart would be decoration.
/// The store pair is included because a too-WIDE store is invisible to the value
/// obligation alone — only the width obligation sees it.
#[test]
fn wasm_value_domain_wrong_bytes_are_refuted() {
    let cfg = VerificationConfig::default();
    let guards = vd::all_value_domain_anti_tautologies();
    assert_eq!(guards.len(), 7, "the anti-tautology set changed");
    for ob in guards {
        let result = verify_by_evaluation_with_config(&ob, &cfg);
        assert!(
            !matches!(result, VerificationResult::Valid),
            "'{}' was NOT refuted (result {result:?}) — its obligation family is vacuous",
            ob.name
        );
    }
}

/// LOCKS IN the extension bit specifically: for EVERY sub-word load, swapping
/// `_u` for `_s` (or the reverse) at the same width REFUTES.
///
/// This quantifies over the whole sub-word block rather than sampling one pair,
/// so a future decoder edit that collapses two rows cannot pass by luck.
#[test]
fn every_subword_load_distinguishes_zero_from_sign_extension() {
    let cfg = VerificationConfig::default();
    // (signed byte, unsigned byte) at the same access width and value width.
    let pairs: [(u8, u8); 5] = [
        (0x2c, 0x2d), // i32.load8_s  / i32.load8_u
        (0x2e, 0x2f), // i32.load16_s / i32.load16_u
        (0x30, 0x31), // i64.load8_s  / i64.load8_u
        (0x32, 0x33), // i64.load16_s / i64.load16_u
        (0x34, 0x35), // i64.load32_s / i64.load32_u
    ];
    for (signed, unsigned) in pairs {
        for (intended, emitted) in [(signed, unsigned), (unsigned, signed)] {
            let ob = vd::mem_load_value_obligation(intended, emitted).unwrap_or_else(|| {
                panic!("0x{intended:02x}/0x{emitted:02x} must build an obligation")
            });
            assert!(
                !matches!(
                    verify_by_evaluation_with_config(&ob, &cfg),
                    VerificationResult::Valid
                ),
                "0x{intended:02x} lowered as 0x{emitted:02x} was NOT refuted — the extension bit \
                 is unchecked"
            );
        }
    }
}

/// LOCKS IN the store WIDTH specifically: for every narrowing store, emitting
/// the next WIDER store of the same value type REFUTES via the width obligation.
///
/// The value obligation cannot see this (the low bytes still match), so without
/// the width half a `store16`-for-`store8` slip would be credited green.
#[test]
fn every_narrowing_store_rejects_a_wider_store() {
    let cfg = VerificationConfig::default();
    // (intended narrowing store, a WIDER store of the same value type).
    let pairs: [(u8, u8); 5] = [
        (0x3a, 0x3b), // i32.store8  <- i32.store16
        (0x3a, 0x36), // i32.store8  <- i32.store
        (0x3b, 0x36), // i32.store16 <- i32.store
        (0x3c, 0x3d), // i64.store8  <- i64.store16
        (0x3d, 0x3e), // i64.store16 <- i64.store32
    ];
    for (intended, wider) in pairs {
        let ob = vd::mem_store_width_obligation(intended, wider)
            .unwrap_or_else(|| panic!("0x{intended:02x}/0x{wider:02x} must build an obligation"));
        assert!(
            !matches!(
                verify_by_evaluation_with_config(&ob, &cfg),
                VerificationResult::Valid
            ),
            "0x{intended:02x} lowered as the wider 0x{wider:02x} was NOT refuted — the store \
             width is unchecked"
        );
    }
}

/// LOCKS IN that the narrow-width family refutes the two renormalization bugs it
/// exists for: using the UNSIGNED mask on a signed narrow domain, and skipping
/// renormalization entirely.
#[test]
fn narrow_width_family_refutes_wrong_renormalization() {
    let cfg = VerificationConfig::default();
    for ob in [
        vd::proof_wrong_signed_narrow_uses_unsigned_mask(),
        vd::proof_wrong_narrow_skips_renormalization(),
    ] {
        assert!(
            !matches!(
                verify_by_evaluation_with_config(&ob, &cfg),
                VerificationResult::Valid
            ),
            "'{}' was NOT refuted",
            ob.name
        );
    }
}

// ===========================================================================
// 3. Registration: the narrow-width obligations are in the proof database
// ===========================================================================

/// PINS the WebAssembly Lowering category at 82 = the 54 pre-existing genuine
/// scalar witnesses + the 32 P3 narrow-width obligations, and asserts every one
/// is non-degenerate.
///
/// Registration is what makes the narrow-width obligations part of the audited
/// proof census rather than a test-local aside.
#[test]
fn narrow_width_proofs_are_registered_and_genuine() {
    let proofs = on_large_stack(|| {
        let db = ProofDatabase::new();
        db.by_category(ProofCategory::WasmLowering)
            .into_iter()
            .map(|p| {
                (
                    p.obligation.name.clone(),
                    p.obligation.is_genuinely_proven(),
                )
            })
            .collect::<Vec<_>>()
    });
    assert_eq!(
        proofs.len(),
        86,
        "WasmLowering registry changed — 54 genuine scalar witnesses + 32 P3 narrow-width \
         obligations"
    );
    for (name, genuine) in &proofs {
        assert!(
            genuine,
            "registered wasm proof '{name}' is degenerate (X==X)"
        );
    }
    let narrow = proofs
        .iter()
        .filter(|(name, _)| name.starts_with("narrow "))
        .count();
    assert_eq!(
        narrow, 32,
        "the 32 P3 narrow-width obligations are registered"
    );
}

// ===========================================================================
// 4. The spec table is the authority
// ===========================================================================

/// LOCKS IN the decoder against the WebAssembly Core Specification 2.0 opcode
/// table (§5.4.4 / §5.4.6), byte by byte.
///
/// The decoders are hand-mirrored from the spec, so this is the only thing
/// standing between a transposed digit and a silently wrong obligation. Each
/// row asserts mnemonic, access width, value width and extension together — a
/// single wrong field would otherwise hide behind two right ones.
#[test]
fn memory_opcode_bytes_match_the_spec_table() {
    use w::{WasmLoadExtend as E, WasmMemDirection as D};
    // (byte, mnemonic, direction, access_bits, value_bits, is_fp)
    let table: &[(u8, &str, D, u32, u32, bool)] = &[
        (0x28, "i32.load", D::Load(E::None), 32, 32, false),
        (0x29, "i64.load", D::Load(E::None), 64, 64, false),
        (0x2a, "f32.load", D::Load(E::None), 32, 32, true),
        (0x2b, "f64.load", D::Load(E::None), 64, 64, true),
        (0x2c, "i32.load8_s", D::Load(E::Sign), 8, 32, false),
        (0x2d, "i32.load8_u", D::Load(E::Zero), 8, 32, false),
        (0x2e, "i32.load16_s", D::Load(E::Sign), 16, 32, false),
        (0x2f, "i32.load16_u", D::Load(E::Zero), 16, 32, false),
        (0x30, "i64.load8_s", D::Load(E::Sign), 8, 64, false),
        (0x31, "i64.load8_u", D::Load(E::Zero), 8, 64, false),
        (0x32, "i64.load16_s", D::Load(E::Sign), 16, 64, false),
        (0x33, "i64.load16_u", D::Load(E::Zero), 16, 64, false),
        (0x34, "i64.load32_s", D::Load(E::Sign), 32, 64, false),
        (0x35, "i64.load32_u", D::Load(E::Zero), 32, 64, false),
        (0x36, "i32.store", D::Store, 32, 32, false),
        (0x37, "i64.store", D::Store, 64, 64, false),
        (0x38, "f32.store", D::Store, 32, 32, true),
        (0x39, "f64.store", D::Store, 64, 64, true),
        (0x3a, "i32.store8", D::Store, 8, 32, false),
        (0x3b, "i32.store16", D::Store, 16, 32, false),
        (0x3c, "i64.store8", D::Store, 8, 64, false),
        (0x3d, "i64.store16", D::Store, 16, 64, false),
        (0x3e, "i64.store32", D::Store, 32, 64, false),
    ];
    assert_eq!(table.len(), 23, "the spec memory block is 0x28..=0x3e");
    for &(byte, mnemonic, direction, access_bits, value_bits, is_fp) in table {
        let op = w::decode_mem_op(byte).unwrap_or_else(|| panic!("0x{byte:02x} must decode"));
        assert_eq!(op.mnemonic, mnemonic, "0x{byte:02x} mnemonic");
        assert_eq!(op.byte, byte, "0x{byte:02x} self-reported byte");
        assert_eq!(op.direction, direction, "0x{byte:02x} direction/extension");
        assert_eq!(op.access_bits, access_bits, "0x{byte:02x} access width");
        assert_eq!(op.value_bits, value_bits, "0x{byte:02x} value width");
        assert_eq!(op.is_fp, is_fp, "0x{byte:02x} FP flag");
    }
}

/// LOCKS IN the sign-extension operator table (spec §5.4.6, 0xc0..=0xc4).
#[test]
fn sign_extension_opcode_bytes_match_the_spec_table() {
    let table: &[(u8, &str, u32, u32)] = &[
        (0xc0, "i32.extend8_s", 8, 32),
        (0xc1, "i32.extend16_s", 16, 32),
        (0xc2, "i64.extend8_s", 8, 64),
        (0xc3, "i64.extend16_s", 16, 64),
        (0xc4, "i64.extend32_s", 32, 64),
    ];
    for &(byte, mnemonic, from_bits, value_bits) in table {
        let op = w::decode_sign_extend(byte).unwrap_or_else(|| panic!("0x{byte:02x} must decode"));
        assert_eq!(op.mnemonic, mnemonic);
        assert_eq!(op.byte, byte);
        assert_eq!(op.from_bits, from_bits, "0x{byte:02x} source width");
        assert_eq!(op.value_bits, value_bits, "0x{byte:02x} carrier width");
    }
    assert!(w::decode_sign_extend(0xbf).is_none());
    assert!(w::decode_sign_extend(0xc5).is_none());
}

/// LOCKS IN that `memory.size` (0x3f) and `memory.grow` (0x40) decode as
/// memory-META rather than as accesses.
///
/// They sit immediately after the store block, so treating either as an access
/// would silently manufacture an obligation about a byte that does not touch
/// memory contents at all.
#[test]
fn memory_meta_opcodes_are_not_accesses() {
    assert!(w::decode_mem_op(0x3f).is_none());
    assert!(w::decode_mem_op(0x40).is_none());
    assert_eq!(w::decode_memory_meta(0x3f), Some(w::WasmMemoryMetaOp::Size));
    assert_eq!(w::decode_memory_meta(0x40), Some(w::WasmMemoryMetaOp::Grow));
    assert!(w::decode_memory_meta(0x3e).is_none());
    assert!(w::decode_memory_meta(0x41).is_none());
}
