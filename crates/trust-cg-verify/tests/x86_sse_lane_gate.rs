// trust-cg-verify/tests/x86_sse_lane_gate.rs - the SSE lane family against the LIVE encoder and real silicon
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The live half of the x86-64 SSE lane-routing family.
//!
//! `src/x86_sse_lane_proofs.rs` holds the independent SDM-derived decoder, the
//! bit-level routing denotation, the typed obligation, the negative-control
//! batteries and the coverage-gate credit hook — all of which take BYTES and an
//! INTENT, and none of which can call the encoder (`trust-cg-codegen` depends on
//! this crate, so it can only be a DEV-dependency here). This file supplies
//! both ends that the library cannot reach:
//!
//!   1. the captured corpus the credit stands on is RE-ENCODED through the live
//!      encoder and asserted byte-identical, so no gate row can rest on a stale
//!      capture;
//!   2. stratified sweeps — every register pair at both sides of the REX
//!      threshold, and every one of the 256 PSHUFD immediates — go through the
//!      live encoder and through the whole obligation;
//!   3. on an x86-64 host with SSE4.1, the SDM denotation is run against REAL
//!      SILICON: the same operand values are fed to the hardware instruction and
//!      to the model, and any disagreement fails. That is what defeats a shared
//!      misreading of the SDM, which no amount of internal consistency can.
//!
//! A control that survives, or refutes for the wrong reason, means the
//! obligation is not faithful: fix the obligation, never the control.

use std::collections::BTreeSet;

use trust_cg_verify::coverage_gate::{CoverageGate, GateArch, x86_deferred_value_op_reason};
use trust_cg_verify::x86_sse_lane_proofs as sse;

use sse::{
    EMITTED_X86_SSE_LANE_INSTANCES, EmittedSseLane, IntentOperand, SSE_LANE_ROWS, SseIntent,
    SseLaneOp, X86_SSE_LANE_DEFERRALS,
};

// ---------------------------------------------------------------------------
// Live-encoder plumbing
// ---------------------------------------------------------------------------

/// The live re-encode, shared with the target that PINS the ratio. It lives
/// in `support/` precisely so that `coverage_gate_tests` runs the SAME
/// freshness check this file does, rather than pinning the ratio over a
/// capture only this file ever re-derives.
#[path = "support/sse_lane_live_encode.rs"]
mod live;

use live::{assert_sse_lane_corpus_is_what_the_live_encoder_emits, live_encode, perm_to_imm};

fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("sse-lane-gate".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large-stack thread")
        .join()
        .expect("thread panicked")
}

// ---------------------------------------------------------------------------
// 1. Freshness: the capture is what the live encoder emits today
// ---------------------------------------------------------------------------

/// FRESHNESS. The credit hook runs over a CAPTURE, because `coverage_gate.rs`
/// cannot run the encoder. Every captured entry is re-encoded through the live
/// encoder here and must be byte-identical, so an encoder change that alters
/// these bytes turns THIS test red instead of leaving ten green rows standing
/// on a fiction.
#[test]
fn corpus_is_what_the_live_encoder_emits_today() {
    assert_sse_lane_corpus_is_what_the_live_encoder_emits();
    let seen: BTreeSet<SseLaneOp> = EMITTED_X86_SSE_LANE_INSTANCES
        .iter()
        .map(|e| e.op)
        .collect();
    assert_eq!(
        seen.len(),
        SSE_LANE_ROWS.len(),
        "every credited row needs a captured encoding"
    );
}

/// The credit hook, over the LIVE bytes rather than the capture.
#[test]
fn the_credit_discharges_over_live_bytes() {
    let live: Vec<EmittedSseLane> = EMITTED_X86_SSE_LANE_INSTANCES
        .iter()
        .map(|e| {
            let bytes = live_encode(&e.intent());
            assert_eq!(bytes.as_slice(), e.bytes, "{}", e.label());
            *e
        })
        .collect();
    let credit = sse::sse_lane_credit_over(&live).expect("the live corpus must discharge");
    assert_eq!(credit.rows_covered, 10);
    assert_eq!(credit.saturation_cases, 65536);
    assert!(credit.memory_forms > 0);
    assert!(credit.byte_mutants_refuted > 500);
    assert!(credit.model_controls_refuted > 200);
}

// ---------------------------------------------------------------------------
// 2. Sweeps through the live encoder
// ---------------------------------------------------------------------------

/// Every register pair, for every row, through the live encoder and the whole
/// obligation. The gate credit stands on a stratified corpus; this is the
/// exhaustive version of it, and it is why the corpus can stay small.
#[test]
fn every_register_pair_holds_for_every_row() {
    let mut checked = 0usize;
    for row in SSE_LANE_ROWS {
        for d in 0..16u8 {
            for s in 0..16u8 {
                let dst: &'static str = if row == SseLaneOp::Pmovmskb {
                    GPR32_NAMES[d as usize]
                } else {
                    XMM_NAMES[d as usize]
                };
                let intent = SseIntent {
                    op: row,
                    dst,
                    src: IntentOperand::Reg(XMM_NAMES[s as usize]),
                    perm: if row == SseLaneOp::Pshufd {
                        Some([1, 0, 3, 2])
                    } else {
                        None
                    },
                };
                let bytes = live_encode(&intent);
                sse::sse_lane_check(&intent, &bytes).unwrap_or_else(|r| {
                    panic!("{row:?} {dst},{} REFUTED: {r}", XMM_NAMES[s as usize])
                });
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 10 * 256);
}

/// All 256 PSHUFD immediates: the ORDER-field convention holds for every one of
/// them, not only for the immediates the instruction selector happens to spell.
#[test]
fn every_pshufd_immediate_holds() {
    for imm in 0..=255u8 {
        let perm = [imm & 3, (imm >> 2) & 3, (imm >> 4) & 3, (imm >> 6) & 3];
        let intent = SseIntent {
            op: SseLaneOp::Pshufd,
            dst: "xmm1",
            src: IntentOperand::Reg("xmm2"),
            perm: Some(perm),
        };
        let bytes = live_encode(&intent);
        assert_eq!(bytes.last(), Some(&imm), "imm8 placement");
        sse::sse_lane_check(&intent, &bytes)
            .unwrap_or_else(|r| panic!("PSHUFD imm {imm:#04x} REFUTED: {r}"));
        // And a permutation that is NOT the one the immediate spells must
        // refute — otherwise the row would be blind to the ORDER convention.
        let wrong = [perm[3], perm[2], perm[1], perm[0]];
        if wrong != perm {
            let bad = SseIntent {
                perm: Some(wrong),
                ..intent
            };
            assert!(
                sse::sse_lane_check(&bad, &bytes).is_err(),
                "PSHUFD imm {imm:#04x}: the reversed permutation {wrong:?} was ACCEPTED"
            );
        }
    }
}

/// THE ONE ISEL-SIDE PACKING THIS FAMILY CAN REACH.
///
/// The obligation compares the permutation the machine side unpacks from the
/// emitted imm8 against the permutation the corpus records as the intent — and
/// that corpus perm is hand transcribed from instruction selection's own
/// immediate literals, while `live_encode` hands the encoder an immediate it
/// packs by the SDM convention. So an isel that packed the ORDER fields in the
/// WRONG ORDER would move both sides together and the row would still hold.
/// The non-claims say so in as many words.
///
/// One isel path does not spell its immediate literally: the `v4i32` mask
/// shuffle COMPUTES one, selector by selector, from the lane values. That
/// packing IS reachable from here, and this test pins it against the SDM's
/// ORDER-field convention over all sixteen lane-value patterns — a reversal
/// there now fails a test instead of being invisible. The literal immediates
/// remain outside the family's reach, and are named in the non-claims.
#[test]
fn the_isel_mask_shuffle_immediate_packs_the_sdm_order_fields() {
    use trust_cg_lower::x86_64_isel::X86InstructionSelector;
    for bits in 0..16u8 {
        // The isel's own encoding of a v4i32 mask: lane `l` is all-ones (-1)
        // when `bits` has that lane set. Its seed register holds
        // `[-1, 0, 0, 0]`, so lane `l` must select source doubleword 0 for an
        // all-ones lane and doubleword 1 for a zero lane.
        let lane_values = [0, 1, 2, 3].map(|l: usize| if bits >> l & 1 == 1 { -1i64 } else { 0 });
        let perm = [0, 1, 2, 3].map(|l: usize| u8::from(lane_values[l] != -1));
        let imm = X86InstructionSelector::v4i32_mask_shuffle_imm(lane_values);
        let intent = SseIntent {
            op: SseLaneOp::Pshufd,
            dst: "xmm1",
            src: IntentOperand::Reg("xmm2"),
            perm: Some(perm),
        };
        assert_eq!(
            imm,
            i64::from(perm_to_imm(&intent)),
            "instruction selection packs the v4i32 mask shuffle for lanes {lane_values:?} as \
             {imm:#04x}, but the SDM's ORDER-field convention spells the permutation {perm:?} as \
             {:#04x}",
            perm_to_imm(&intent)
        );
        // And the whole obligation holds over the bytes the encoder emits for
        // that immediate, so the pin is on the same path the credit uses.
        let bytes = live_encode(&intent);
        assert_eq!(bytes.last().copied(), Some(imm as u8), "imm8 placement");
        sse::sse_lane_check(&intent, &bytes)
            .unwrap_or_else(|r| panic!("v4i32 mask shuffle imm {imm:#04x} REFUTED: {r}"));
    }
}

const XMM_NAMES: [&str; 16] = [
    "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10",
    "xmm11", "xmm12", "xmm13", "xmm14", "xmm15",
];
const GPR32_NAMES: [&str; 16] = [
    "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d",
    "r13d", "r14d", "r15d",
];

// ---------------------------------------------------------------------------
// 3. The gate rows
// ---------------------------------------------------------------------------

/// The ten rows are GREEN in the audit and are no longer named in the deferral
/// table — and, just as importantly, nothing else moved.
#[test]
fn the_ten_rows_are_credited_and_no_longer_deferred() {
    for row in SSE_LANE_ROWS {
        let opcode = sse::x86_opcode_of(row);
        assert_eq!(
            x86_deferred_value_op_reason(opcode),
            None,
            "{opcode:?} must have left the deferral table"
        );
    }
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::X86_64));
    for row in SSE_LANE_ROWS {
        let want = format!("x86_64::{:?}", sse::x86_opcode_of(row));
        let r = report
            .rows
            .iter()
            .find(|r| r.opcode_display == want)
            .unwrap_or_else(|| panic!("{want} is not in the audit"));
        assert!(
            r.finding.is_none(),
            "{want} is not green: {:?} — {}",
            r.finding,
            r.note
        );
        assert!(
            r.note.contains("SDM"),
            "{want}'s note must say what the credit is: {}",
            r.note
        );
    }
}

/// The non-claims are carried as DATA and pinned here, so the row cannot be
/// over-read and the list cannot quietly shrink.
#[test]
fn the_non_claims_are_pinned() {
    assert_eq!(
        X86_SSE_LANE_DEFERRALS.len(),
        11,
        "the non-claims list changed; update this pin deliberately"
    );
    for want in [
        "NOT that instruction selection chose the right instruction",
        // The PSHUFD entry states a NON-claim about this convention: an
        // isel-side packing bug moves the corpus perm and the emitted imm
        // together, so the row cannot see it. The entry used to claim the
        // opposite.
        "ORDER-field packing convention",
        "an isel-side packing bug moves both sides together",
        // MOVDQA-RR and PMOVMSKB: the two sides of the ROUTING comparison are
        // the SAME construction, and the row note may not pretend otherwise.
        "are structurally distinct",
        "TRUST BASE",
        "MNEMONIC-identity conjunct",
        "16-byte aligned",
        "post_ra_dataflow",
        "MXCSR",
    ] {
        assert!(
            X86_SSE_LANE_DEFERRALS.iter().any(|d| d.contains(want)),
            "the non-claims no longer mention `{want}`"
        );
    }
}

/// THE TEETH, at the gate target the meta-gate runs.
///
/// The credit hook is only worth its ten green rows if it REFUSES a battery
/// that has stopped being evidence. Each refusal below is a defect that was
/// once live in this family:
///
///   * a control that SURVIVES — the obligation does not read that facet;
///   * a control that cannot be BUILT, which used to be scored as "refuted by
///     construction" and made 35 of the published controls vacuous;
///   * a control that refutes for a reason OTHER than the one it names —
///     `operands SWAPPED` on PTEST used to "refute" purely because a
///     `Denotation::Flags` is never `==` a `Denotation::FlagIntent`;
///   * a ROW whose own controls all degenerate, credited on the strength of
///     labels that fired on some OTHER row.
#[test]
fn the_credit_hook_refuses_batteries_that_are_not_evidence() {
    use sse::{
        SseByteMutant, SseModelControl, SseRefutationClass, WrongMachineModel, sse_byte_mutants,
        sse_lane_credit_over, sse_lane_credit_over_with, sse_model_controls,
    };

    // (1) A control that survives: the CORRECT model, deliberately.
    let surviving = |e: &EmittedSseLane| {
        let mut v = sse_model_controls(e);
        v.push(SseModelControl {
            label: "deliberately CORRECT, so it must survive",
            model: WrongMachineModel::Mnemonic(sse::SseMnemonic::PunpcklbwX),
            expect: SseRefutationClass::Value,
        });
        v
    };
    let err = sse_lane_credit_over_with(
        EMITTED_X86_SSE_LANE_INSTANCES,
        &sse_byte_mutants,
        &surviving,
    )
    .expect_err("a surviving control must refuse the credit");
    assert!(err.contains("SURVIVED"), "{err}");

    // (2) A control that cannot be built. `operands SWAPPED` on a folded
    //     `xmm, m128` entry: there is no encoding whose ModRM.reg is memory.
    let unbuildable = |_: &EmittedSseLane| {
        vec![SseModelControl {
            label: "operands SWAPPED",
            model: WrongMachineModel::OperandsSwapped,
            expect: SseRefutationClass::Dest,
        }]
    };
    let err = sse_lane_credit_over_with(
        EMITTED_X86_SSE_LANE_INSTANCES,
        &sse_byte_mutants,
        &unbuildable,
    )
    .expect_err("an unbuildable control must refuse the credit");
    assert!(err.contains("could not be BUILT"), "{err}");

    // (3) A control refuting for the WRONG REASON, on each battery.
    let mislabelled_models = |e: &EmittedSseLane| {
        let mut v = sse_model_controls(e);
        for c in &mut v {
            c.expect = SseRefutationClass::Model;
        }
        v
    };
    let err = sse_lane_credit_over_with(
        EMITTED_X86_SSE_LANE_INSTANCES,
        &sse_byte_mutants,
        &mislabelled_models,
    )
    .expect_err("a misattributed wrong-model control must refuse the credit");
    assert!(err.contains("WRONG REASON"), "{err}");
    let mislabelled_bytes = |e: &EmittedSseLane| {
        let mut v: Vec<SseByteMutant> = sse_byte_mutants(e);
        for m in &mut v {
            m.expect = SseRefutationClass::Model;
        }
        v
    };
    let err = sse_lane_credit_over_with(
        EMITTED_X86_SSE_LANE_INSTANCES,
        &mislabelled_bytes,
        &sse_model_controls,
    )
    .expect_err("a misattributed byte mutant must refuse the credit");
    assert!(err.contains("WRONG REASON"), "{err}");

    // (4) A row reduced to entries on which its own controls all degenerate.
    //     PUNPCKLQDQ's `xmm1,xmm1` low-quadword broadcast is the real emitted
    //     shape that does it, and PUNPCKLQDQ is the row whose credit was once
    //     withdrawn for a vacuous obligation.
    let narrowed: Vec<EmittedSseLane> = EMITTED_X86_SSE_LANE_INSTANCES
        .iter()
        .copied()
        .filter(|e| {
            e.op != SseLaneOp::Punpcklqdq
                || (e.dst == "xmm1" && e.src == IntentOperand::Reg("xmm1"))
        })
        .collect();
    assert!(narrowed.iter().any(|e| e.op == SseLaneOp::Punpcklqdq));
    let err = sse_lane_credit_over(&narrowed)
        .expect_err("a row whose controls all degenerate must refuse the credit");
    assert!(
        err.contains("Punpcklqdq") && err.contains("never fired ON ROW"),
        "{err}"
    );
}

// ---------------------------------------------------------------------------
// 4. The native-silicon differential
// ---------------------------------------------------------------------------

/// THE SILICON DIFFERENTIAL.
///
/// Everything else in this family is internally consistent by construction: the
/// decoder, the SDM transcription and the parametric intent were all written by
/// the same hand from the same manual, so a MISREADING of the manual would be
/// invisible to them. This test is the only thing that is not: it feeds the same
/// operand values to the model and to the CPU, and requires the answers to
/// match.
///
/// It is not a proof. It is one CPU model, over a sampled grid of operand
/// values, and it says so in the non-claims. What it defeats is a shared
/// misreading, which is the failure mode an internal cross-check cannot see.
#[cfg(target_arch = "x86_64")]
mod silicon {
    use super::*;
    use core::arch::x86_64::*;
    use sse::{Denotation, Operand, machine_denotation, sdm_decode_sse};

    fn load(v: &[u8; 16]) -> __m128i {
        unsafe { _mm_loadu_si128(v.as_ptr().cast()) }
    }

    fn store(v: __m128i) -> [u8; 16] {
        let mut out = [0u8; 16];
        unsafe { _mm_storeu_si128(out.as_mut_ptr().cast(), v) };
        out
    }

    fn as_u128(v: [u8; 16]) -> u128 {
        u128::from_le_bytes(v)
    }

    /// A deterministic xorshift grid of register values, so a failure is
    /// reproducible. Includes the saturating-pack boundary bytes and the
    /// `0x7F` / `0x80` mask bytes a "non-zero" blend model gets wrong.
    fn reg_grid(round: u32) -> [[u8; 16]; 16] {
        let mut s = 0x2545_F491_4F6C_DD1Du64 ^ u64::from(round).wrapping_mul(0x9E37_79B9);
        let mut next = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut regs = [[0u8; 16]; 16];
        for (i, r) in regs.iter_mut().enumerate() {
            for b in r.iter_mut() {
                let x = next();
                *b = match (round + i as u32) % 4 {
                    // Sign-bit-only bytes: what separates "bit 7" from
                    // "non-zero" for PBLENDVB and PMOVMSKB.
                    0 => {
                        if x & 1 == 0 {
                            0x7F
                        } else {
                            0x80
                        }
                    }
                    // Pack boundary bytes.
                    1 => [0x00, 0x01, 0x7F, 0x80, 0xFF][(x % 5) as usize],
                    _ => x as u8,
                };
            }
        }
        regs
    }

    fn pshufd_on(a: __m128i, imm: u8) -> Option<__m128i> {
        // `_mm_shuffle_epi32` needs a CONST immediate, so the immediates the
        // corpus and the isel actually use are spelled out. Anything else
        // returns `None` and is skipped rather than silently passing.
        Some(unsafe {
            match imm {
                0x00 => _mm_shuffle_epi32::<0x00>(a),
                0x01 => _mm_shuffle_epi32::<0x01>(a),
                0x04 => _mm_shuffle_epi32::<0x04>(a),
                0x05 => _mm_shuffle_epi32::<0x05>(a),
                0x10 => _mm_shuffle_epi32::<0x10>(a),
                0x11 => _mm_shuffle_epi32::<0x11>(a),
                0x14 => _mm_shuffle_epi32::<0x14>(a),
                0x15 => _mm_shuffle_epi32::<0x15>(a),
                0x1B => _mm_shuffle_epi32::<0x1B>(a),
                0x40 => _mm_shuffle_epi32::<0x40>(a),
                0x41 => _mm_shuffle_epi32::<0x41>(a),
                0x44 => _mm_shuffle_epi32::<0x44>(a),
                0x45 => _mm_shuffle_epi32::<0x45>(a),
                0x4E => _mm_shuffle_epi32::<0x4E>(a),
                0x50 => _mm_shuffle_epi32::<0x50>(a),
                0x51 => _mm_shuffle_epi32::<0x51>(a),
                0x54 => _mm_shuffle_epi32::<0x54>(a),
                0x55 => _mm_shuffle_epi32::<0x55>(a),
                0x80 => _mm_shuffle_epi32::<0x80>(a),
                0xA0 => _mm_shuffle_epi32::<0xA0>(a),
                0xEE => _mm_shuffle_epi32::<0xEE>(a),
                0xF5 => _mm_shuffle_epi32::<0xF5>(a),
                0xFF => _mm_shuffle_epi32::<0xFF>(a),
                _ => return None,
            }
        })
    }

    /// What the HARDWARE produces for one corpus entry, given register values.
    fn silicon_value(entry: &EmittedSseLane, regs: &[[u8; 16]; 16]) -> Option<u128> {
        let d = sdm_decode_sse(entry.bytes).expect("the corpus decodes");
        let sse::SseRm::Reg(rm) = d.rm else {
            return None; // memory forms are not exercised on silicon here
        };
        let a = load(&regs[d.reg as usize]);
        let b = load(&regs[rm as usize]);
        let out = unsafe {
            match entry.op {
                SseLaneOp::Punpcklbw => _mm_unpacklo_epi8(a, b),
                SseLaneOp::Punpckhbw => _mm_unpackhi_epi8(a, b),
                SseLaneOp::Punpckldq => _mm_unpacklo_epi32(a, b),
                SseLaneOp::Punpcklqdq => _mm_unpacklo_epi64(a, b),
                SseLaneOp::Packuswb => _mm_packus_epi16(a, b),
                // A REAL `movdqa xmm,xmm`, not `b`. Returning the source value
                // here counted this row into the silicon tally without an
                // instruction ever executing, while the gate's prose said "the
                // same operand values go to the model and to the hardware
                // instruction" — and MOVDQA is one of the two rows whose two
                // model sides are the same construction, so silicon is the only
                // thing that can catch a shared misreading of it. There is no
                // intrinsic for a register-register MOVDQA (the compiler is
                // free to elide a copy), so it is spelled directly.
                SseLaneOp::MovdqaRR => {
                    let copied: __m128i;
                    core::arch::asm!(
                        "movdqa {d}, {s}",
                        d = out(xmm_reg) copied,
                        s = in(xmm_reg) b,
                        options(pure, nomem, nostack, preserves_flags),
                    );
                    copied
                }
                SseLaneOp::Pblendvb => _mm_blendv_epi8(a, b, load(&regs[0])),
                SseLaneOp::Pmovmskb => {
                    return Some(u128::from(_mm_movemask_epi8(b) as u32));
                }
                SseLaneOp::Pshufd => pshufd_on(b, d.imm8?)?,
                SseLaneOp::Ptest => return None, // flags, handled separately
            }
        };
        Some(as_u128(store(out)))
    }

    /// Every value row's SDM denotation, against the real instruction.
    #[test]
    fn the_sdm_denotation_agrees_with_this_cpu() {
        if !is_x86_feature_detected!("sse4.1") {
            eprintln!("SKIP: this host has no SSE4.1, so the silicon differential did not run");
            return;
        }
        let mut checked = 0usize;
        for round in 0..24u32 {
            let regs = reg_grid(round);
            let values = |op: Operand| match op {
                Operand::Xmm(n) => regs[n as usize],
                Operand::Mem { .. } => panic!("no memory operand is exercised on silicon"),
            };
            for entry in EMITTED_X86_SSE_LANE_INSTANCES {
                if !matches!(entry.src, IntentOperand::Reg(_)) {
                    continue;
                }
                let Some(expect) = silicon_value(entry, &regs) else {
                    continue;
                };
                let d = sdm_decode_sse(entry.bytes).expect("the corpus decodes");
                let Ok(Denotation::Value(v)) = machine_denotation(&d) else {
                    panic!("{}: no value denotation", entry.label());
                };
                let got = sse::eval_value_denot(&v, &values);
                assert_eq!(
                    got,
                    expect,
                    "{} round {round}: the SDM model says {got:#034x}, this CPU says \
                     {expect:#034x}",
                    entry.label()
                );
                checked += 1;
            }
        }
        assert!(checked > 1000, "only {checked} silicon comparisons ran");
    }

    /// PTEST's ZF and CF, against the real instruction.
    ///
    /// The four flags the SDM says are CLEARED are not read back here — the
    /// intrinsics expose only ZF and CF — and the non-claims say so. What this
    /// does settle is the pair of flags every interesting control corrupts.
    #[test]
    fn ptest_zf_and_cf_agree_with_this_cpu() {
        if !is_x86_feature_detected!("sse4.1") {
            eprintln!("SKIP: this host has no SSE4.1, so the silicon differential did not run");
            return;
        }
        let machine = sse::sdm_ptest_flags();
        let mut reached = [false; 4];
        let mut checked = 0usize;
        // The structured pairs the model's own witness family uses, so the two
        // are settled over the same domain, plus the random grid.
        let mut pairs: Vec<(u128, u128)> = Vec::new();
        for i in (0..128u32).step_by(7) {
            for j in (0..128u32).step_by(5) {
                pairs.push((1u128 << i, 1u128 << j));
                pairs.push((!(1u128 << i), 1u128 << j));
            }
        }
        pairs.push((0, 0));
        pairs.push((!0, !0));
        pairs.push((0, !0));
        pairs.push((!0, 0));
        for round in 0..8u32 {
            let regs = reg_grid(round);
            for i in 0..16 {
                for j in 0..16 {
                    pairs.push((as_u128(regs[i]), as_u128(regs[j])));
                }
            }
        }
        for (dest, src) in pairs {
            let dv = load(&dest.to_le_bytes());
            let sv = load(&src.to_le_bytes());
            let zf = unsafe { _mm_testz_si128(dv, sv) } == 1;
            let cf = unsafe { _mm_testc_si128(dv, sv) } == 1;
            let m = sse::eval_flag_denot(&machine, dest, src);
            assert_eq!(
                m[3], zf,
                "PTEST ZF: model {} vs silicon {zf} for DEST={dest:#034x} SRC={src:#034x}",
                m[3]
            );
            assert_eq!(
                m[0], cf,
                "PTEST CF: model {} vs silicon {cf} for DEST={dest:#034x} SRC={src:#034x}",
                m[0]
            );
            reached[usize::from(zf)] = true;
            reached[2 + usize::from(cf)] = true;
            checked += 1;
        }
        assert!(
            reached.iter().all(|&b| b),
            "the silicon sweep must reach both polarities of ZF and CF: {reached:?}"
        );
        assert!(checked > 2000, "only {checked} PTEST comparisons ran");
    }
}

/// The silicon differential, NAMED where it cannot run (L13-P14).
///
/// On a test binary that does not target x86-64 the module above is compiled
/// out, and until 2026-10-12 its two tests simply vanished: a direct run or a
/// full-matrix run on an arm64 host reported the target green with nothing
/// compared against a CPU and no line saying so. These stubs carry the same
/// test names, so every such run lists both as `ignored` with the reason
/// (`scripts/full_test_matrix_hosts.py` records them in `IGNORED_TESTS`, never
/// as passes), and forcing them with `--include-ignored` FAILS rather than
/// passing vacuously. No credit rests on them. Rosetta 2 is not a substitute:
/// it is translation, not silicon (OD-34), so an x86-64 binary run under it
/// would test the translator's SSE, not an x86-64 CPU. The soundness gate
/// runs this target only on a native x86-64 host (`SOUNDNESS_X86_HOST`).
#[cfg(not(target_arch = "x86_64"))]
mod silicon {
    /// Why the SDM-vs-silicon differential did not run in this binary.
    const NOT_RUN: &str = "x86-64 silicon differential NOT RUN: this test binary does not \
                           target x86_64, so the SDM denotation was compared against no CPU; \
                           Rosetta 2 translation is not silicon (OD-34); the soundness gate \
                           runs this target only on a native x86-64 host (SOUNDNESS_X86_HOST)";

    #[test]
    #[ignore = "x86-64 silicon differential NOT RUN: this binary does not target x86_64; Rosetta 2 translation is not silicon (OD-34); run on a native x86-64 host"]
    fn the_sdm_denotation_agrees_with_this_cpu() {
        panic!("{NOT_RUN} (target_arch = {})", std::env::consts::ARCH);
    }

    #[test]
    #[ignore = "x86-64 silicon differential NOT RUN: this binary does not target x86_64; Rosetta 2 translation is not silicon (OD-34); run on a native x86-64 host"]
    fn ptest_zf_and_cf_agree_with_this_cpu() {
        panic!("{NOT_RUN} (target_arch = {})", std::env::consts::ARCH);
    }
}

/// The environment variable the soundness gate's x86_64-native dispatch sets
/// (`scripts/soundness_check.sh`, TRUST_CG_X86_NATIVE_GATES) when it credits
/// this target as native-silicon evidence.
const REQUIRE_X86_SILICON: &str = "TRUST_CG_REQUIRE_X86_SILICON";

/// When the gate requires the silicon differential, a build without it fails.
///
/// The `silicon` module above compiles only for `target_arch = "x86_64"`, so on
/// any other host this target passes having compared nothing against a CPU. The
/// gate therefore runs the target only on a native x86-64 host and sets
/// `TRUST_CG_REQUIRE_X86_SILICON=1` there; this test turns that requirement into
/// a failure wherever the silicon half is absent. On an x86-64 host without
/// SSE4.1 the silicon tests print `SKIP:`, which the gate's result parser
/// counts, so that host fails the gate too. Without the variable (ordinary
/// `cargo test` on any host) it asserts nothing.
#[test]
fn the_required_silicon_differential_is_compiled_in() {
    // Spelled as ONE unconditional assertion over a `cfg!` boolean rather than a
    // `#[cfg]`-gated body, because the lint gate rejects both alternatives: an
    // early `return` is the function's last statement on x86-64
    // (`needless_return`), and compiling the check out entirely leaves
    // `REQUIRE_X86_SILICON` unused there. This form reads the constant and
    // evaluates the condition on every target, and says the same thing: on
    // x86-64 the differential is compiled in by construction, so the assertion
    // holds vacuously; anywhere else, requiring it is a request to credit
    // native-silicon evidence that was never gathered.
    let compiled_in = cfg!(target_arch = "x86_64");
    let required =
        std::env::var_os(REQUIRE_X86_SILICON).as_deref() == Some(std::ffi::OsStr::new("1"));
    assert!(
        compiled_in || !required,
        "{REQUIRE_X86_SILICON}=1 but this test binary targets {}: the SDM-vs-silicon \
         differential is not compiled in, so this run would credit native-silicon evidence \
         that was never gathered",
        std::env::consts::ARCH
    );
}

/// Print what the credit actually established. The meta-gate runs these targets
/// with `--show-output`, so the numbers behind the ten green rows are visible in
/// the gate log rather than only inside an assertion message.
#[test]
fn credit_summary_is_reported() {
    let c = sse::sse_lane_discharges_valid().expect("the credit must discharge");
    println!(
        "x86 SSE lane credit: {} captured encodings ({} reg-reg, {} folded xmm,m128) over {} \
         rows; {} result bits compared exactly; {} byte mutants and {} wrong-model controls \
         REFUTE; PACKUSWB narrow exhaustive over {} inputs; PTEST flags agree on {} witnesses",
        c.entries,
        c.register_forms,
        c.memory_forms,
        c.rows_covered,
        c.bits_compared,
        c.byte_mutants_refuted,
        c.model_controls_refuted,
        c.saturation_cases,
        c.ptest_witnesses,
    );
    assert_eq!(c.rows_covered, 10);
}
