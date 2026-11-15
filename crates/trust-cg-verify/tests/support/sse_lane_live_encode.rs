// trust-cg-verify/tests/support/sse_lane_live_encode.rs - the SSE lane corpus, re-derived from the live encoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! FRESHNESS for the x86-64 SSE lane-routing credit, in one place.
//!
//! The ten SSE lane coverage rows are credited over
//! [`EMITTED_X86_SSE_LANE_INSTANCES`], a CAPTURE of bytes the real encoder
//! produced, because `trust-cg-verify` cannot call `trust-cg-codegen` (that
//! crate depends on this one, so it can only be a DEV-dependency, and only in
//! tests). A capture can rot. The re-derivation below encodes every captured
//! entry through the LIVE encoder and requires byte identity.
//!
//! WHY IT LIVES HERE RATHER THAN IN ONE TEST FILE. It used to live only in
//! `x86_sse_lane_gate.rs`, while `coverage_gate_tests.rs` — the target that
//! PINS the published x86-64 ratio — re-derived nothing. An encoder change
//! that made these bytes wrong (say `Punpcklbw` emitting the PUNPCKHBW opcode
//! byte) would have left the credit hook happily decoding the FROZEN bytes,
//! all ten rows green and the ratio-pinning target passing. `MovRI` had
//! already closed exactly this by putting its re-derivation inside the
//! ratio-pinning target; this module is the same fix, shared by both targets
//! via `#[path]` so there is one definition of "what the encoder emits today"
//! and not two.

#![allow(dead_code)]

use trust_cg_codegen::x86_64::{X86Encoder, X86InstOperands};
use trust_cg_ir::X86PReg;
use trust_cg_verify::x86_sse_lane_proofs as sse;

use sse::{EMITTED_X86_SSE_LANE_INSTANCES, IntentOperand, SseIntent, SseLaneOp};

/// The `trust-cg-ir` physical register whose DISPLAY NAME is `name`. The scan
/// is over `trust-cg-ir`'s own name table — never over `hw_enc`, which is the
/// table under test.
pub fn preg_named(name: &str) -> X86PReg {
    (0u16..80)
        .map(X86PReg::new)
        .find(|r| r.to_string() == name)
        .unwrap_or_else(|| panic!("trust-cg-ir has no register named `{name}`"))
}

/// The imm8 that spells a `Pshufd` intent's permutation, by the SDM's ORDER
/// field packing (`imm[2j+1:2j]` selects the source doubleword of result
/// doubleword `j`).
///
/// THE TEST may compute it this way; the OBLIGATION may not, and does not — the
/// machine side derives the permutation from the emitted byte and the source
/// side states it independently. Note what this means for the claim: because
/// the sweep HANDS the encoder an immediate packed by this convention, the
/// family establishes that the encoder places the imm8 unmutated, NOT that
/// instruction selection packs those fields the same way. The non-claims list
/// says so, and `x86_sse_lane_gate` pins the one isel packer that COMPUTES an
/// immediate against this same convention.
pub fn perm_to_imm(intent: &SseIntent) -> u8 {
    let p = intent.perm.expect("a Pshufd intent needs a permutation");
    p[0] | (p[1] << 2) | (p[2] << 4) | (p[3] << 6)
}

/// The bytes the REAL encoder emits for one intent.
pub fn live_encode(intent: &SseIntent) -> Vec<u8> {
    let opcode = sse::x86_opcode_of(intent.op);
    let dst = preg_named(intent.dst);
    let ops = match intent.src {
        IntentOperand::Reg(s) => {
            let src = preg_named(s);
            match intent.op {
                SseLaneOp::Pshufd => X86InstOperands::rri(dst, src, perm_to_imm(intent) as i64),
                _ => X86InstOperands::rr(dst, src),
            }
        }
        IntentOperand::Mem { base, disp } => {
            let b = preg_named(base);
            let m = X86InstOperands::rm(dst, b, i64::from(disp));
            match intent.op {
                SseLaneOp::Pshufd => X86InstOperands {
                    imm: perm_to_imm(intent) as i64,
                    ..m
                },
                _ => m,
            }
        }
    };
    let mut encoder = X86Encoder::new();
    encoder
        .encode_instruction(opcode, &ops)
        .unwrap_or_else(|e| panic!("live encoder refused {opcode:?} {}: {e:?}", intent.dst));
    encoder.finish()
}

/// The SDM register-number tables the SOURCE side reaches a register number
/// through, pinned against their literal spelling.
///
/// `SDM_XMM` and `SDM_R32` are position-indexed: the number IS the index. They
/// are the single path from an operand NAME in the machine-IR intent to a
/// number the machine side can be compared against, and the gate-time corpus is
/// register-SPARSE — it never names `xmm10` or `xmm11` — so transposing two
/// entries there was invisible to every ratio-pinning target and caught only by
/// the 16x16 sweep in `x86_sse_lane_gate`. This pins the tables themselves, in
/// the targets that publish the ratio.
pub fn assert_sdm_register_tables_are_in_number_order() {
    for (number, name) in sse::SDM_XMM.iter().enumerate() {
        assert_eq!(
            *name,
            format!("xmm{number}"),
            "SDM_XMM is position-indexed: entry {number} must be the register of NUMBER {number}"
        );
        assert_eq!(sse::sdm_xmm(name), Some(number as u8), "sdm_xmm({name})");
    }
    for (number, name) in [
        "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d",
        "r12d", "r13d", "r14d", "r15d",
    ]
    .iter()
    .enumerate()
    {
        assert_eq!(
            sse::sdm_gpr32(name),
            Some(number as u8),
            "SDM_R32 must give {name} the number {number} — PMOVMSKB's destination is named \
             through this table"
        );
    }
}

/// Re-derive every captured SSE lane encoding from the live encoder and require
/// byte identity, and pin the register tables the source side names registers
/// through. Returns the number of entries checked.
///
/// A target that PINS the x86-64 coverage ratio calls this, so the pin cannot
/// stand on bytes the backend no longer emits.
pub fn assert_sse_lane_corpus_is_what_the_live_encoder_emits() -> usize {
    let mut checked = 0usize;
    for entry in EMITTED_X86_SSE_LANE_INSTANCES {
        let live = live_encode(&entry.intent());
        assert_eq!(
            live.as_slice(),
            entry.bytes,
            "STALE SSE LANE CORPUS: {} is emitted as {live:02x?} by the live encoder but captured \
             as {:02x?}. The ten x86-64 SSE lane credits would rest on bytes the backend no longer \
             emits; re-capture and re-run tests/x86_sse_lane_gate.rs",
            entry.label(),
            entry.bytes
        );
        checked += 1;
    }
    assert!(
        checked >= 100,
        "the SSE lane corpus shrank to {checked} entries"
    );
    assert_sdm_register_tables_are_in_number_order();
    checked
}
