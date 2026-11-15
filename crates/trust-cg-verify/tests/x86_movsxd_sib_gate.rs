// trust-cg-verify/tests/x86_movsxd_sib_gate.rs - the scaled sign-extending load against the LIVE encoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The live half of the x86-64 `MOVSXD r64, [base + index*scale + disp]` family.
//!
//! `src/x86_movsxd_sib_proofs.rs` holds the independent SDM-derived decoder, the
//! register-write denotation of both sides, the typed obligation, the
//! negative-control batteries and the coverage-gate credit hook — all of which
//! take BYTES and none of which can call the encoder (`trust-cg-codegen` depends
//! on this crate, so it can only be a DEV-dependency here). This file supplies
//! the bytes by running the REAL x86-64 encoder.
//!
//! What happens here that cannot happen inside the library:
//!
//!   1. the captured corpus the credit hook stands on is RE-ENCODED through the
//!      live encoder and asserted byte-identical, so the gate row can never rest
//!      on a stale capture;
//!   2. the WHOLE destination x base x index x scale x displacement product goes
//!      through the live encoder and the obligation, so the credit's
//!      independence does not rest on the captured table being wide — including
//!      every register that makes a SIB field ambiguous (RSP as a base, R12 as
//!      an index, RBP and R13 as bases);
//!   3. the SDM register table the source side names registers through is
//!      anchored against `trust-cg-ir`'s `hw_enc`, the table the encoder really
//!      uses;
//!   4. the obligation is discharged as a real `ProofObligation` under the full
//!      `verify_by_evaluation` sampling sweep, and the two denotations are
//!      compared EXHAUSTIVELY over a contiguous 2^16 address window — neither of
//!      which the coverage-gate hook can afford to do;
//!   5. the credit hook is handed a SURVIVING control, a control that refutes
//!      for the WRONG REASON, a battery missing a required label, a decoder
//!      control that holds and a hold-vector that refutes, and must REFUSE each.
//!
//! A control that survives, or refutes for the wrong reason, means the
//! obligation is not faithful: fix the obligation, never the control.

use std::collections::BTreeSet;

use trust_cg_ir::X86Opcode;
use trust_cg_verify::lowering_proof::verify_by_evaluation;
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::x86_movsxd_sib_proofs as msx;

use msx::{
    ControlSide, EMITTED_X86_MOVSXD_SIB, EmittedScaledLoad, REQUIRED_CONTROL_LABELS,
    REQUIRED_DECODER_CONTROL_LABELS, REQUIRED_ENCODING_FACETS, REQUIRED_MODEL_CONTROL_LABELS,
    SDM_HAND_VECTORS_HOLD, ScaledLoadControl, ScaledLoadRefutationClass, ScaledSextLoadIntent,
    X86_MOVSXD_SIB_DEFERRALS,
};

#[path = "support/movsxd_sib_live_encode.rs"]
mod live;

use live::{assert_movsxd_sib_corpus_is_what_the_live_encoder_emits, live_encode, preg_named};

/// The sixteen 64-bit GPR names, in SDM number order.
const R64: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];

/// Every 64-bit GPR the x86-64 encoder accepts as a SIB INDEX. RSP is excluded
/// because `SIB.index = 100` with `REX.X = 0` is the SDM's no-index sentinel —
/// the very ambiguity the decoder models and `encoder_refuses_rsp_as_a_sib_index`
/// pins on the encoder side.
fn index_registers() -> Vec<&'static str> {
    R64.iter().copied().filter(|&r| r != "rsp").collect()
}

// ---------------------------------------------------------------------------
// 1. Freshness: the capture is what the live encoder emits today
// ---------------------------------------------------------------------------

/// FRESHNESS. The credit hook runs over a CAPTURE, because `coverage_gate.rs`
/// cannot run the encoder. Every captured entry is re-encoded through the live
/// encoder here and must be byte-identical, so an encoder change that alters
/// these bytes turns THIS test red instead of leaving a green row standing on a
/// fiction. `coverage_gate_tests` runs the same re-derivation, so the RATIO
/// cannot go green on a stale capture either.
#[test]
fn corpus_is_what_the_live_encoder_emits_today() {
    let checked = assert_movsxd_sib_corpus_is_what_the_live_encoder_emits();
    assert_eq!(checked, EMITTED_X86_MOVSXD_SIB.len());
}

/// The corpus must have no duplicate rows: a table that repeats one encoding
/// forty times would satisfy a bare length check while covering one shape.
#[test]
fn corpus_rows_are_distinct() {
    let mut seen = BTreeSet::new();
    for entry in EMITTED_X86_MOVSXD_SIB {
        assert!(
            seen.insert((entry.dst, entry.base, entry.index, entry.scale, entry.disp)),
            "duplicate corpus row: MOVSXD {},[{} + {}*{} {:+}]",
            entry.dst,
            entry.base,
            entry.index,
            entry.scale,
            entry.disp
        );
    }
}

// ---------------------------------------------------------------------------
// 2. The SDM register table is the encoder's table
// ---------------------------------------------------------------------------

/// The SOURCE side reaches a register NUMBER through the SDM table transcribed
/// in `x86_encoding_proofs`; the MACHINE side reaches one by DECODING. The only
/// thing joining the two ends is `trust-cg-ir`'s `hw_enc`, the table the encoder
/// really uses. Pin it: a transposed entry would otherwise make a wrong base or
/// index invisible to every register the corpus does not name.
#[test]
fn sdm_register_table_matches_trust_cg_ir_hw_enc() {
    for (number, name) in R64.iter().enumerate() {
        let preg = preg_named(name);
        assert_eq!(
            u32::from(preg.hw_enc()),
            number as u32,
            "SDM_R64 is position-indexed: `{name}` must be register NUMBER {number}, but \
             trust-cg-ir's hw_enc gives {}",
            preg.hw_enc()
        );
    }
}

/// The encoder must REFUSE RSP as a SIB index: `SIB.index = 100` with
/// `REX.X = 0` is the SDM's no-index sentinel, so an encoder that accepted it
/// would silently emit an instruction with NO index register. The decoder models
/// that form and the `D2` control refutes it; this pins the other end.
#[test]
fn encoder_refuses_rsp_as_a_sib_index() {
    use trust_cg_codegen::x86_64::{X86Encoder, X86InstOperands};
    let mut encoder = X86Encoder::new();
    let result = encoder.encode_instruction(
        X86Opcode::MovsxdRMSib,
        &X86InstOperands::rm_sib(
            preg_named("rax"),
            preg_named("rbx"),
            preg_named("rsp"),
            4,
            0,
        ),
    );
    assert!(
        result.is_err(),
        "the encoder accepted RSP as a SIB index; SIB.index=100 with REX.X=0 is the no-index \
         sentinel, so those bytes would denote [rbx] with no index at all"
    );
    // R12 shares the low three bits and IS legal, rescued by REX.X.
    let mut encoder = X86Encoder::new();
    encoder
        .encode_instruction(
            X86Opcode::MovsxdRMSib,
            &X86InstOperands::rm_sib(
                preg_named("rax"),
                preg_named("rbx"),
                preg_named("r12"),
                4,
                0,
            ),
        )
        .expect("R12 is a legal SIB index (REX.X=1 rescues SIB.index=100)");
    let bytes = encoder.finish();
    assert_eq!(
        bytes,
        vec![0x4A, 0x63, 0x04, 0xA3],
        "MOVSXD RAX,[RBX+R12*4] must set REX.X"
    );
}

// ---------------------------------------------------------------------------
// 3. The full operand sweep
// ---------------------------------------------------------------------------

/// THE SWEEP THE CAPTURE CANNOT BE. Every destination against every base against
/// every legal index at the jump-table scale, then every scale against every
/// displacement mode over a smaller register cross — all through the LIVE
/// encoder and the obligation. The captured corpus is a stratified selection;
/// this is the product.
#[test]
fn full_operand_sweep_holds() {
    let mut checked = 0usize;
    for dst in R64 {
        for base in R64 {
            for index in index_registers() {
                let intent = ScaledSextLoadIntent {
                    dst,
                    base,
                    index,
                    entry_bytes: 4,
                    disp: 0,
                };
                let bytes = live_encode(dst, base, index, 4, 0);
                msx::movsxd_sib_check(&intent, &bytes).unwrap_or_else(|r| {
                    panic!("{} = {bytes:02x?}: {r}", intent.label());
                });
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 16 * 16 * 15);

    let mut scale_disp = 0usize;
    for dst in ["rax", "r11"] {
        for base in R64 {
            for index in ["rcx", "r12"] {
                for scale in [1u32, 2, 4, 8] {
                    for disp in [0i64, 1, -1, 127, -128, 128, -129, 0x1234, -0x1234] {
                        let intent = ScaledSextLoadIntent {
                            dst,
                            base,
                            index,
                            entry_bytes: scale,
                            disp,
                        };
                        let bytes = live_encode(dst, base, index, scale, disp);
                        msx::movsxd_sib_check(&intent, &bytes).unwrap_or_else(|r| {
                            panic!("{} = {bytes:02x?}: {r}", intent.label());
                        });
                        scale_disp += 1;
                    }
                }
            }
        }
    }
    assert_eq!(scale_disp, 2 * 16 * 2 * 4 * 9);
}

/// Every REQUIRED encoding facet is reachable through the LIVE encoder, and the
/// captured corpus exhibits every one. Without this, a facet could be "required"
/// by the hook and quietly impossible, which would make the requirement a
/// no-op — or the corpus could drift narrow while the hook still passed on a
/// facet set it computed from the same narrow corpus.
#[test]
fn the_corpus_exhibits_every_required_facet() {
    let mut facets = BTreeSet::new();
    for entry in EMITTED_X86_MOVSXD_SIB {
        let intent = entry.intent();
        let holds = msx::movsxd_sib_check(&intent, entry.bytes)
            .unwrap_or_else(|r| panic!("{}: {r}", intent.label()));
        for facet in msx::facets_of(&holds.decoded, &intent) {
            facets.insert(facet);
        }
    }
    for required in REQUIRED_ENCODING_FACETS {
        assert!(
            facets.contains(required),
            "the captured corpus exhibits no {required:?} encoding"
        );
    }
}

// ---------------------------------------------------------------------------
// 4. The controls, over live bytes
// ---------------------------------------------------------------------------

/// Every control, over LIVE bytes rather than the capture, must refute FOR ITS
/// STATED REASON CLASS — and every required label must fire. The sweep runs the
/// battery on a strided subset of the operand product so the labels that need a
/// particular register or displacement shape (the R12 index, the RBP/R13 forced
/// disp8, the disp32 forms) are all reached.
#[test]
fn every_control_refutes_for_its_stated_reason_over_live_bytes() {
    let mut labels = BTreeSet::new();
    let mut model_labels = BTreeSet::new();
    let mut runs = 0usize;
    for dst in ["rax", "r10"] {
        for base in R64 {
            for index in ["rcx", "rbp", "r9", "r12", "r14"] {
                for scale in [1u32, 2, 4, 8] {
                    for disp in [0i64, 8, -8, 0x100, -0x1234] {
                        let intent = ScaledSextLoadIntent {
                            dst,
                            base,
                            index,
                            entry_bytes: scale,
                            disp,
                        };
                        let bytes = live_encode(dst, base, index, scale, disp);
                        let battery = msx::scaled_load_controls(&intent, &bytes);
                        assert!(
                            !battery.is_empty(),
                            "{} produced no controls",
                            intent.label()
                        );
                        for c in &battery {
                            msx::control_is_refuted_as_stated(c).unwrap_or_else(|e| panic!("{e}"));
                            labels.insert(c.label);
                        }
                        for m in msx::scaled_load_model_controls_for(&intent) {
                            msx::model_control_is_refuted_as_stated(&m, &intent, &bytes)
                                .unwrap_or_else(|e| panic!("{e}"));
                            model_labels.insert(m.label);
                        }
                        runs += 1;
                    }
                }
            }
        }
    }
    assert_eq!(runs, 2 * 16 * 5 * 4 * 5);
    for &required in REQUIRED_CONTROL_LABELS {
        assert!(
            labels.contains(required),
            "control `{required}` never fired over the live sweep"
        );
    }
    for &required in REQUIRED_MODEL_CONTROL_LABELS {
        assert!(
            model_labels.contains(required),
            "wrong-model control `{required}` never fired over the live sweep"
        );
    }
}

/// The hand-written SDM decoder controls all refute for their stated class, and
/// every required decoder label is present. These are the decisions the corpus
/// cannot reach, because the encoder never produces them.
#[test]
fn the_sdm_decoder_controls_all_refute() {
    let controls = msx::sdm_decoder_controls();
    let present: BTreeSet<&str> = controls.iter().map(|c| c.label).collect();
    for &required in REQUIRED_DECODER_CONTROL_LABELS {
        assert!(
            present.contains(required),
            "decoder control `{required}` is absent"
        );
    }
    for c in &controls {
        msx::control_is_refuted_as_stated(c).unwrap_or_else(|e| panic!("{e}"));
    }
}

/// REX.B DOES NOT CREATE A BASE REGISTER — the rule the corpus structurally
/// cannot reach, decided by hand.
///
/// SDM Vol 2A Table 2-3 says `SIB.base = 101b` with `ModR/M.mod = 00` means NO
/// base register and a disp32 follows, and Table 2-2 says `rm = 101b` with
/// `mod = 00` is RIP-relative — in both cases whatever REX.B says, because REX.B
/// EXTENDS a base that exists and here none does. The encoder never emits either
/// form (it forces an explicit disp8 for an RBP/R13 base), which is exactly why
/// D1/D4 alone could not decide the rule: both had REX.B CLEAR, so the extra
/// `&& !rex_b` a wrong decoder would carry was never evaluated, and under it the
/// bytes `49 63 04 8D` read as `[r13 + rcx*4 + disp32]`.
///
/// Three things are pinned here: that the LIVE encoder really never reaches the
/// form (so the hand vectors are necessary, not decoration); that the four
/// REX.B-set vectors refute for their stated classes; and — the sharp one —
/// that `49 63 04 8D` claimed as `[r13 + rcx*4]` is REFUTED, which is the pair
/// a REX.B-rescuing decoder would CREDIT.
#[test]
fn rex_b_does_not_create_a_base_register() {
    // (1) The live encoder never emits `mod = 00` with `SIB.base = 101`, over
    //     the whole base x index x scale x displacement product.
    let mut checked = 0usize;
    for base in R64 {
        for index in ["rcx", "r12"] {
            for scale in [1u32, 2, 4, 8] {
                for disp in [0i64, 8, -8, 0x100, -0x1234] {
                    let bytes = live_encode("rax", base, index, scale, disp);
                    let decoded = msx::sdm_decode_scaled_load(&bytes).expect("decode");
                    let sib = decoded.sib.expect("the SIB form always carries a SIB byte");
                    assert!(
                        !(decoded.modrm >> 6 == 0b00 && sib & 0b111 == 0b101),
                        "the encoder emitted mod=00 with SIB.base=101 for MOVSXD \
                         rax,[{base}+{index}*{scale}{disp:+}] = {bytes:02x?}; that is the SDM's \
                         NO-BASE form, so those bytes do not mean what the intent means"
                    );
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 16 * 2 * 4 * 5);

    // (2) The four REX.B-set decoder vectors are present and refute as stated.
    let controls = msx::sdm_decoder_controls();
    for required in [
        msx::D1B_NO_BASE_SIB_WITH_REX_B,
        msx::D1C_REX_B_DOES_NOT_MAKE_A_BASE,
        msx::D4B_RIP_RELATIVE_WITH_REX_B,
        msx::D4C_RIP_RELATIVE_NEEDS_DISP32,
    ] {
        let c = controls
            .iter()
            .find(|c| c.label == required)
            .unwrap_or_else(|| panic!("decoder control `{required}` is absent"));
        msx::control_is_refuted_as_stated(c).unwrap_or_else(|e| panic!("{e}"));
        assert!(
            c.bytes.first().is_some_and(|&b| b & 0b1 == 1),
            "`{required}` must carry REX.B SET or it decides nothing about the rule: {:02x?}",
            c.bytes
        );
    }

    // (3) THE SHARP ONE. `49 63 04 8D` is NOT `MOVSXD rax, [r13 + rcx*4]`: the
    //     SDM says a disp32 follows, so the string ends before a required
    //     field. A decoder in which REX.B rescued base=101 would decode exactly
    //     that instruction and CREDIT the pair.
    let r13_claim = ScaledSextLoadIntent {
        dst: "rax",
        base: "r13",
        index: "rcx",
        entry_bytes: 4,
        disp: 0,
    };
    let refutation = msx::movsxd_sib_check(&r13_claim, &[0x49, 0x63, 0x04, 0x8D])
        .expect_err("49 63 04 8D is NOT [r13 + rcx*4]");
    assert_eq!(
        refutation.class(),
        ScaledLoadRefutationClass::Framing,
        "the SDM no-base form takes a disp32, so the string is TRUNCATED: {refutation}"
    );
    // ... and what the encoder ACTUALLY emits for that intent is different
    // bytes entirely, which is the positive half of the same statement.
    let real = live_encode("rax", "r13", "rcx", 4, 0);
    assert_ne!(real.as_slice(), &[0x49, 0x63, 0x04, 0x8D]);
    msx::movsxd_sib_check(&r13_claim, &real).expect("the real encoding holds");
}

/// THE SDM DESTINATION WIDTH RULE (Vol 1 §3.4.1.1), decided over every
/// production — not only the 64-bit one the credited family reaches.
///
/// `movsxd_sib_check` refuses anything whose `dst_bits` is not 64 at the
/// Extension facet, BEFORE the Destination facet calls `dst_write_mask`, so the
/// 32-, 16- and 8-bit arms of that rule are unreachable for the credited family
/// and a mutation of them left every gate green. These vectors decode REAL byte
/// strings for all six productions this decoder's language contains and pin the
/// width AND the mask of each.
#[test]
fn the_write_mask_vectors_decide_the_sdm_destination_width_rule() {
    let present: BTreeSet<&str> = msx::DEST_WRITE_MASK_VECTORS
        .iter()
        .map(|v| v.label)
        .collect();
    for &required in msx::REQUIRED_WRITE_MASK_VECTOR_LABELS {
        assert!(
            present.contains(required),
            "write-mask vector `{required}` is absent"
        );
    }
    for v in msx::DEST_WRITE_MASK_VECTORS {
        msx::write_mask_vector_is_as_stated(v).unwrap_or_else(|e| panic!("{e}"));
    }

    // The 32-bit arm is the one that matters: a 32-bit operand writes a result
    // ZERO-EXTENDED to 64, so it changes the WHOLE root — the opposite of the
    // "it writes only the low 32" reading, and the mutation that survived.
    let thirty_two = msx::DEST_WRITE_MASK_VECTORS
        .iter()
        .find(|v| v.expect_dst_bits == 32)
        .expect("a 32-bit production is covered");
    assert_eq!(thirty_two.expect_mask, u64::MAX);
    let decoded = msx::sdm_decode_scaled_load(thirty_two.bytes).expect("decode");
    assert_eq!(decoded.dst_bits, 32);
    assert_eq!(decoded.dst_write_mask(), u64::MAX);

    // The runner has teeth: a vector stating the wrong mask must FAIL, and one
    // whose bytes do not decode is a battery DEFECT rather than a silent pass.
    let wrong = msx::DestWriteMaskVector {
        expect_mask: 0x0000_0000_FFFF_FFFF,
        ..*thirty_two
    };
    let err = msx::write_mask_vector_is_as_stated(&wrong)
        .expect_err("a vector stating the wrong mask must fail");
    assert!(err.contains("3.4.1.1"), "{err}");
    let undecodable = msx::DestWriteMaskVector {
        bytes: &[0x0F, 0x0B],
        ..*thirty_two
    };
    let err = msx::write_mask_vector_is_as_stated(&undecodable)
        .expect_err("a vector that does not decode compares nothing");
    assert!(err.contains("DID NOT DECODE"), "{err}");
}

/// THE ANTI-VACUITY GUARD, decided in both directions.
///
/// `compare_denotations` refuses a witness family that never exercises both
/// sign cases of the loaded doubleword, because a zero-extending machine model
/// would otherwise agree everywhere and the sign-extension facet would be
/// decided by nothing. Nothing in the corpus or in either control battery ever
/// hands it such a family, so DELETING the guard left all gate cases green.
/// These two controls give it teeth: an all-negative family and an
/// all-non-negative one, with the exact row counts demanded.
#[test]
fn the_vacuity_controls_give_the_anti_vacuity_guard_teeth() {
    let ran = msx::vacuity_controls_are_refused().expect("both vacuity controls must refute");
    assert_eq!(ran, msx::REQUIRED_VACUITY_CONTROL_LABELS.len());

    // The guard is not firing on everything: the REAL pair, whose family DOES
    // exercise both signs, passes the same comparison.
    let intent = ScaledSextLoadIntent {
        dst: "rax",
        base: "rbx",
        index: "rcx",
        entry_bytes: 4,
        disp: 0,
    };
    let bytes = live_encode("rax", "rbx", "rcx", 4, 0);
    let source = msx::intent_write(&intent).expect("source side");
    let machine = msx::sdm_decode_scaled_load(&bytes)
        .expect("decode")
        .machine_write()
        .expect("machine side");
    let outcome = msx::compare_denotations(&source.value, &machine.value, source.mask)
        .expect("the real pair must agree");
    assert!(
        outcome.negative_rows > 0 && outcome.negative_rows < outcome.rows,
        "the real witness family must exercise BOTH sign cases: {outcome:?}"
    );

    // And the hook fails closed when the guard is the only thing that could
    // refute: a family with one sign case is refused for VacuousWitnesses, not
    // for Value and not at all.
    let credit = msx::movsxd_sib_discharges_valid().expect("the credit hook must discharge");
    assert_eq!(
        credit.vacuity_controls_refuted,
        msx::REQUIRED_VACUITY_CONTROL_LABELS.len(),
        "the credit hook must RUN the vacuity controls, not merely allow them to exist"
    );
}

/// The SDM vectors the encoder never emits but which are legal spellings of the
/// same instruction must HOLD. If the decoder were an inversion of the encoder's
/// shortest-displacement ladder, these would refute.
#[test]
fn the_sdm_hand_vectors_that_must_hold_do_hold() {
    for &(why, intent, bytes) in SDM_HAND_VECTORS_HOLD {
        msx::movsxd_sib_check(&intent, bytes)
            .unwrap_or_else(|r| panic!("`{why}` ({}) = {bytes:02x?}: {r}", intent.label()));
    }
    // ... and none of them is a byte-for-byte copy of what the encoder emits,
    // which is the whole point of listing them.
    for &(why, intent, bytes) in SDM_HAND_VECTORS_HOLD {
        let live = live_encode(
            intent.dst,
            intent.base,
            intent.index,
            intent.entry_bytes,
            intent.disp,
        );
        assert_ne!(
            live.as_slice(),
            bytes,
            "`{why}` is exactly what the encoder emits, so it shows nothing about the decoder's \
             independence"
        );
    }
}

// ---------------------------------------------------------------------------
// 5. The credit hook refuses a defective battery
// ---------------------------------------------------------------------------

/// THE HOOK MUST REFUSE A BATTERY WITHOUT TEETH. Hand it a control that
/// SURVIVES, one that refutes for the WRONG REASON, and one missing a required
/// label; each must make the hook fail. Without this seam a hook whose control
/// check had been forced to `Ok` would still discharge on today's all-refuting
/// controls and no test would notice.
#[test]
fn credit_hook_refuses_surviving_or_misattributed_controls() {
    let real = |i: &ScaledSextLoadIntent, b: &[u8]| msx::scaled_load_controls(i, b);

    // (a) a SURVIVING control: the real bytes, the real intent, claimed wrong.
    let surviving = |i: &ScaledSextLoadIntent, b: &[u8]| {
        let mut v = msx::scaled_load_controls(i, b);
        v.push(ScaledLoadControl {
            label: REQUIRED_CONTROL_LABELS[0],
            side: ControlSide::Machine,
            intent: *i,
            bytes: b.to_vec(),
            expect: ScaledLoadRefutationClass::Destination,
        });
        v
    };
    let err = msx::movsxd_sib_credit_over_with(
        EMITTED_X86_MOVSXD_SIB,
        &surviving,
        &msx::sdm_decoder_controls(),
        SDM_HAND_VECTORS_HOLD,
    )
    .expect_err("a surviving control must withhold the credit");
    assert!(err.contains("SURVIVED"), "{err}");

    // (b) a control that refutes for the WRONG REASON.
    let misattributed = |i: &ScaledSextLoadIntent, b: &[u8]| {
        let mut v = msx::scaled_load_controls(i, b);
        let mut wrong = b.to_vec();
        wrong.push(0x90); // a trailing byte: a FRAMING defect
        v.push(ScaledLoadControl {
            label: REQUIRED_CONTROL_LABELS[0],
            side: ControlSide::Machine,
            intent: *i,
            bytes: wrong,
            expect: ScaledLoadRefutationClass::Scale, // ... claimed as a SCALE defect
        });
        v
    };
    let err = msx::movsxd_sib_credit_over_with(
        EMITTED_X86_MOVSXD_SIB,
        &misattributed,
        &msx::sdm_decoder_controls(),
        SDM_HAND_VECTORS_HOLD,
    )
    .expect_err("a misattributed control must withhold the credit");
    assert!(err.contains("WRONG REASON"), "{err}");

    // (c) a battery missing a required label.
    let dropped = REQUIRED_CONTROL_LABELS[0];
    let incomplete = |i: &ScaledSextLoadIntent, b: &[u8]| {
        msx::scaled_load_controls(i, b)
            .into_iter()
            .filter(|c| c.label != dropped)
            .collect::<Vec<_>>()
    };
    let err = msx::movsxd_sib_credit_over_with(
        EMITTED_X86_MOVSXD_SIB,
        &incomplete,
        &msx::sdm_decoder_controls(),
        SDM_HAND_VECTORS_HOLD,
    )
    .expect_err("a battery missing a required label must withhold the credit");
    assert!(err.contains(dropped), "{err}");

    // (d) an empty battery.
    let empty = |_: &ScaledSextLoadIntent, _: &[u8]| Vec::new();
    assert!(
        msx::movsxd_sib_credit_over_with(
            EMITTED_X86_MOVSXD_SIB,
            &empty,
            &msx::sdm_decoder_controls(),
            SDM_HAND_VECTORS_HOLD,
        )
        .is_err()
    );

    // The real battery discharges — otherwise (a)..(d) prove nothing.
    msx::movsxd_sib_credit_over_with(
        EMITTED_X86_MOVSXD_SIB,
        &real,
        &msx::sdm_decoder_controls(),
        SDM_HAND_VECTORS_HOLD,
    )
    .expect("the real battery must discharge");
}

/// The hook must also refuse a DECODER control that holds, an ABSENT decoder
/// control, and a HOLD vector that refutes.
#[test]
fn credit_hook_refuses_defective_decoder_controls_and_hold_vectors() {
    let real = |i: &ScaledSextLoadIntent, b: &[u8]| msx::scaled_load_controls(i, b);

    // A "decoder control" that is actually the real jump-table encoding, so it
    // holds instead of refuting.
    let mut holding = msx::sdm_decoder_controls();
    holding.push(ScaledLoadControl {
        label: REQUIRED_DECODER_CONTROL_LABELS[0],
        side: ControlSide::Machine,
        intent: ScaledSextLoadIntent {
            dst: "rax",
            base: "rbx",
            index: "rcx",
            entry_bytes: 4,
            disp: 0,
        },
        bytes: vec![0x48, 0x63, 0x04, 0x8B],
        expect: ScaledLoadRefutationClass::AddressShape,
    });
    let err = msx::movsxd_sib_credit_over_with(
        EMITTED_X86_MOVSXD_SIB,
        &real,
        &holding,
        SDM_HAND_VECTORS_HOLD,
    )
    .expect_err("a decoder control that HOLDS must withhold the credit");
    assert!(err.contains("SURVIVED"), "{err}");

    // An absent decoder control.
    let absent = REQUIRED_DECODER_CONTROL_LABELS[1];
    let thinned: Vec<_> = msx::sdm_decoder_controls()
        .into_iter()
        .filter(|c| c.label != absent)
        .collect();
    let err = msx::movsxd_sib_credit_over_with(
        EMITTED_X86_MOVSXD_SIB,
        &real,
        &thinned,
        SDM_HAND_VECTORS_HOLD,
    )
    .expect_err("an absent decoder control must withhold the credit");
    assert!(err.contains(absent), "{err}");

    // No decoder controls at all.
    assert!(
        msx::movsxd_sib_credit_over_with(EMITTED_X86_MOVSXD_SIB, &real, &[], SDM_HAND_VECTORS_HOLD)
            .is_err()
    );

    // A "must hold" vector that actually refutes (a 64-bit MOV, not a MOVSXD).
    let bad_hold: &[msx::SdmVector] = &[(
        "a MOV r64,m64 wrongly listed as a MOVSXD hold vector",
        ScaledSextLoadIntent {
            dst: "rax",
            base: "rbx",
            index: "rcx",
            entry_bytes: 4,
            disp: 0,
        },
        &[0x48, 0x8B, 0x04, 0x8B],
    )];
    let err = msx::movsxd_sib_credit_over_with(
        EMITTED_X86_MOVSXD_SIB,
        &real,
        &msx::sdm_decoder_controls(),
        bad_hold,
    )
    .expect_err("a hold vector that refutes must withhold the credit");
    assert!(err.contains("must HOLD"), "{err}");

    // No hold vectors at all.
    assert!(
        msx::movsxd_sib_credit_over_with(
            EMITTED_X86_MOVSXD_SIB,
            &real,
            &msx::sdm_decoder_controls(),
            &[]
        )
        .is_err()
    );
}

/// The hook must refuse a corpus carrying ONE wrong encoding, and one that is
/// empty or too narrow to exhibit the required facets.
#[test]
fn credit_hook_fails_closed_on_a_bad_corpus() {
    assert!(msx::movsxd_sib_credit_over(&[]).is_err());

    let narrow = [EMITTED_X86_MOVSXD_SIB[0]];
    let err = msx::movsxd_sib_credit_over(&narrow).expect_err("a one-row corpus cannot credit");
    assert!(err.contains("facet coverage"), "{err}");

    // The whole corpus, with one row's bytes replaced by a scale-8 encoding
    // while the row still claims a scale of 4.
    let mut rows: Vec<EmittedScaledLoad> = EMITTED_X86_MOVSXD_SIB.to_vec();
    let poisoned = rows
        .iter_mut()
        .find(|r| r.scale == 4)
        .expect("the corpus has a scale-4 row");
    poisoned.bytes = &[0x48, 0x63, 0x04, 0xC8]; // MOVSXD RAX,[RAX+RCX*8]
    let err =
        msx::movsxd_sib_credit_over(&rows).expect_err("a wrong captured encoding must be caught");
    assert!(err.contains("REFUTED"), "{err}");
}

// ---------------------------------------------------------------------------
// 6. The obligation, under the full sweep and exhaustively
// ---------------------------------------------------------------------------

/// The obligation is a real `ProofObligation`, it is NON-DEGENERATE by the
/// crate's own predicate, and it discharges `Valid` under the full
/// `verify_by_evaluation` sampling sweep — not only over the sixteen witness
/// rows the coverage-gate hook can afford.
#[test]
fn the_obligation_verifies_under_the_full_sampling_sweep() {
    let mut checked = 0usize;
    for entry in EMITTED_X86_MOVSXD_SIB {
        let intent = entry.intent();
        let obligation = msx::movsxd_sib_proof_obligation(&intent, entry.bytes)
            .unwrap_or_else(|| panic!("{}: the obligation must build", intent.label()));
        assert!(
            obligation.is_genuinely_proven(),
            "{}: the obligation is X == X",
            intent.label()
        );
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "{}: {result:?}",
            intent.label()
        );
        checked += 1;
    }
    assert_eq!(checked, EMITTED_X86_MOVSXD_SIB.len());
}

/// A WRONG SCALE must refute under the SAME full sweep, so the sweep above is
/// not passing because the evaluator agrees with everything.
#[test]
fn a_wrong_scale_refutes_under_the_full_sampling_sweep() {
    let intent = ScaledSextLoadIntent {
        dst: "rax",
        base: "rbx",
        index: "rcx",
        entry_bytes: 4,
        disp: 0,
    };
    // The bytes for a scale of EIGHT, claimed as an entry size of four.
    let bytes = live_encode("rax", "rbx", "rcx", 8, 0);
    let obligation =
        msx::movsxd_sib_proof_obligation(&intent, &bytes).expect("the obligation must build");
    let result = verify_by_evaluation(&obligation);
    assert!(
        matches!(result, VerificationResult::Invalid { .. }),
        "a scale-8 encoding claimed as a 4-byte entry size must REFUTE under the sweep, got \
         {result:?}"
    );
}

/// The two denotations agree EXHAUSTIVELY over a contiguous 2^16 address window.
///
/// The witness family in the credit hook is sixteen scattered points; this walks
/// every address in a block, which is the shape a real jump table occupies, and
/// counts how many of them carried a NEGATIVE doubleword — the sign-extension
/// facet is only exercised by those, so the count is asserted non-zero rather
/// than assumed.
#[test]
fn the_denotations_agree_exhaustively_over_a_contiguous_address_window() {
    use trust_cg_verify::smt::EvalEnv;

    let intent = ScaledSextLoadIntent {
        dst: "rax",
        base: "rbx",
        index: "rcx",
        entry_bytes: 4,
        disp: 0x40,
    };
    let bytes = live_encode("rax", "rbx", "rcx", 4, 0x40);
    let source = msx::intent_write(&intent).expect("source side");
    let decoded = msx::sdm_decode_scaled_load(&bytes).expect("decode");
    let machine = decoded.machine_write().expect("machine side");
    assert_ne!(source.value, machine.value, "the obligation is X == X");

    let mut negatives = 0usize;
    for index in 0u64..(1 << 16) {
        let mut env = EvalEnv::default();
        env.insert("reg_rbx".to_string(), 0x1_0000_0000);
        env.insert("reg_rcx".to_string(), index);
        let s = source.value.try_eval(&env).expect("source eval").as_u64();
        let m = machine.value.try_eval(&env).expect("machine eval").as_u64();
        assert_eq!(
            s, m,
            "the denotations disagree at selector {index}: source {s:#018x}, machine {m:#018x}"
        );
        if s & 0x8000_0000_0000_0000 != 0 {
            negatives += 1;
        }
    }
    assert!(
        negatives > 1000,
        "only {negatives} of 65536 window addresses carried a NEGATIVE doubleword; the \
         sign-extension facet would be barely exercised"
    );
}

/// A ZERO-EXTENDING model must DISAGREE over the same window, and at roughly
/// the rate the negative count predicts. Without this the window sweep would
/// prove only that the evaluator is a function.
#[test]
fn a_zero_extending_model_disagrees_over_the_same_window() {
    use trust_cg_verify::smt::EvalEnv;

    let intent = ScaledSextLoadIntent {
        dst: "rax",
        base: "rbx",
        index: "rcx",
        entry_bytes: 4,
        disp: 0x40,
    };
    let bytes = live_encode("rax", "rbx", "rcx", 4, 0x40);
    let source = msx::intent_write(&intent).expect("source side");
    let decoded = msx::sdm_decode_scaled_load(&bytes).expect("decode");
    let ea = decoded
        .machine_effective_address()
        .expect("the SIB form has an effective address");
    let zero_extending = SmtExpr::mem_load(ea, 32, false, 32).zero_ext(32);

    let mut disagreements = 0usize;
    for index in 0u64..(1 << 16) {
        let mut env = EvalEnv::default();
        env.insert("reg_rbx".to_string(), 0x1_0000_0000);
        env.insert("reg_rcx".to_string(), index);
        let s = source.value.try_eval(&env).expect("source eval").as_u64();
        let z = zero_extending.try_eval(&env).expect("model eval").as_u64();
        if s != z {
            disagreements += 1;
        }
    }
    assert!(
        disagreements > 1000,
        "a zero-extending model disagreed at only {disagreements} of 65536 addresses"
    );
}

// ---------------------------------------------------------------------------
// 7. The non-claims
// ---------------------------------------------------------------------------

/// The non-claims are carried as DATA and pinned here, so the row's honesty is
/// not a prose promise. The first of them is the one that matters: nothing emits
/// this opcode.
#[test]
fn the_non_claims_are_pinned() {
    let ids: BTreeSet<&str> = X86_MOVSXD_SIB_DEFERRALS.iter().map(|d| d.id).collect();
    for required in [
        "not-emitted",
        "not-selection",
        "not-memory-model",
        "not-table-entry",
        "value-over-witnesses",
        "not-isa-authority",
        "not-flags-or-placement",
        "not-a-decoder",
    ] {
        assert!(
            ids.contains(required),
            "the non-claim `{required}` was dropped"
        );
    }
    let not_emitted = X86_MOVSXD_SIB_DEFERRALS
        .iter()
        .find(|d| d.id == "not-emitted")
        .expect("present");
    assert!(
        not_emitted.what.contains("Nothing does"),
        "the `not-emitted` non-claim must say plainly that nothing emits this opcode"
    );
}

/// The credit hook discharges, and its counters are what the row's note reports.
#[test]
fn the_credit_hook_discharges_with_real_counters() {
    let credit = msx::movsxd_sib_discharges_valid().expect("the credit hook must discharge");
    assert_eq!(credit.entries, EMITTED_X86_MOVSXD_SIB.len());
    assert_eq!(credit.facets_seen, REQUIRED_ENCODING_FACETS.len());
    assert_eq!(
        credit.decoder_controls_refuted,
        REQUIRED_DECODER_CONTROL_LABELS.len()
    );
    assert_eq!(credit.hand_vectors_held, SDM_HAND_VECTORS_HOLD.len());
    assert!(credit.controls_refuted > 500, "{credit:?}");
    assert!(credit.model_controls_refuted > 100, "{credit:?}");
    assert_eq!(
        credit.witness_comparisons,
        EMITTED_X86_MOVSXD_SIB.len() * msx::WITNESS_ROWS
    );
    assert_eq!(
        credit.write_mask_vectors_checked,
        msx::DEST_WRITE_MASK_VECTORS.len()
    );
    assert_eq!(
        credit.vacuity_controls_refuted,
        msx::REQUIRED_VACUITY_CONTROL_LABELS.len()
    );
}
