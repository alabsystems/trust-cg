// trust-cg-codegen - pin: the verify crate's post-index word MIRRORS match the
// real byte-exact encoders.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
//! `trust-cg-verify` has NO dependency on `trust-cg-codegen` (the dependency
//! runs the other way), so the machine side of the NEON post-index writeback
//! obligations cannot call the real encoders. It carries hand-written MIRRORS of
//! the instruction word layout instead
//! (`neon_semantics::neon_{ldp,stp}_q_post_word`).
//!
//! A mirror is only worth something if something pins it to the original. This
//! test lives HERE — the only crate that can see both — and fails the moment the
//! two drift. Without it, a change to `encoding_neon.rs` would silently leave the
//! writeback obligations proving a fact about an instruction the backend no
//! longer emits.

use trust_cg_codegen::aarch64::encoding_neon;
use trust_cg_verify::neon_semantics::{neon_ldp_q_post_word, neon_stp_q_post_word};

/// The Q-pair post-index offsets the backend actually emits, plus the boundary
/// values of the signed 7-bit scaled immediate field.
const OFFSETS: &[i64] = &[32, 16, -32, -16, 0, 1008, -1024];

#[test]
fn ldp_q_post_word_mirror_matches_codegen() {
    for &offset in OFFSETS {
        let real = encoding_neon::encode_ldp_q_post_imm(offset, 1, 2, 0)
            .unwrap_or_else(|e| panic!("codegen rejected LDP offset {offset}: {e:?}"));
        let mirror = neon_ldp_q_post_word(offset, 1, 2, 0);
        assert_eq!(
            mirror, real,
            "verify's LDP-Q-post word mirror drifted from the real encoder at offset \
             {offset}: mirror {mirror:#010x} vs codegen {real:#010x}. The NEON post-index \
             writeback obligations decode imm7 out of THIS word, so a drift means they \
             prove a fact about an instruction the backend does not emit."
        );
    }
}

#[test]
fn stp_q_post_word_mirror_matches_codegen() {
    for &offset in OFFSETS {
        let real = encoding_neon::encode_stp_q_post_imm(offset, 1, 2, 0)
            .unwrap_or_else(|e| panic!("codegen rejected STP offset {offset}: {e:?}"));
        let mirror = neon_stp_q_post_word(offset, 1, 2, 0);
        assert_eq!(
            mirror, real,
            "verify's STP-Q-post word mirror drifted from the real encoder at offset \
             {offset}: mirror {mirror:#010x} vs codegen {real:#010x}"
        );
    }
}

/// The two forms must differ in exactly the L bit (22) — LDP loads, STP stores.
/// If a refactor ever made them equal, both writeback obligations would still
/// discharge while describing the same instruction.
#[test]
fn ldp_and_stp_words_differ_only_in_the_l_bit() {
    let ldp = neon_ldp_q_post_word(32, 1, 2, 0);
    let stp = neon_stp_q_post_word(32, 1, 2, 0);
    assert_ne!(ldp, stp, "LDP and STP post-index words must not coincide");
    assert_eq!(
        ldp ^ stp,
        1 << 22,
        "LDP and STP must differ in exactly the L bit (22); got {:#010x}",
        ldp ^ stp
    );
}
