// trust-cg-verify/tests/support/a64_value_live_encode.rs - the AArch64 decoded-value corpus, re-derived from the live encoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! FRESHNESS for the AArch64 decoded-word value credits (register copies,
//! SMULL, BFM, RBIT, `ADD #imm12, LSL #12`, MRS), in one place.
//!
//! The rows are credited over [`CAPTURED_A64_VALUE_WORDS`], a CAPTURE of words
//! the real encoder produced, because `trust-cg-verify` cannot call
//! `trust-cg-codegen` (that crate depends on this one, so it is only a
//! dev-dependency). A capture can rot, so every target that pins the ratio
//! these rows move re-encodes every captured entry through the LIVE encoder and
//! requires word identity, through this one shared definition.

#![allow(dead_code)]

use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_verify::aarch64_value_decode_proofs::CAPTURED_A64_VALUE_WORDS;

/// Re-encode every captured entry with the live encoder; panic on any stale
/// word. Returns the number of entries checked.
pub fn assert_a64_value_corpus_is_what_the_live_encoder_emits() -> usize {
    let mut checked = 0usize;
    for entry in CAPTURED_A64_VALUE_WORDS {
        let inst = entry.inst();
        let live = encode_instruction(&inst)
            .unwrap_or_else(|error| panic!("live encoder refused captured {inst:?}: {error:?}"));
        assert_eq!(
            live, entry.word,
            "captured {inst:?} ({:?}) is stale: the live encoder emits {live:#010x}, the \
             corpus records {:#010x}",
            entry.form, entry.word
        );
        checked += 1;
    }
    assert!(checked > 0, "the decoded-value corpus is empty");
    checked
}
