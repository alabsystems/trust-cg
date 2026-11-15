// trust-cg-verify/tests/support/movsxd_sib_live_encode.rs - the MOVSXD-SIB corpus, re-derived from the live encoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! FRESHNESS for the x86-64 scaled-sign-extending-load credit, in one place.
//!
//! The `MovsxdRMSib` coverage row is credited over
//! [`EMITTED_X86_MOVSXD_SIB`], a CAPTURE of bytes the real encoder produced,
//! because `trust-cg-verify` cannot call `trust-cg-codegen` (that crate depends
//! on this one, so it can only be a DEV-dependency, and only in tests). A
//! capture can rot. The re-derivation below encodes every captured entry through
//! the LIVE encoder and requires byte identity.
//!
//! WHY IT LIVES HERE RATHER THAN IN ONE TEST FILE. `MovRI` and the SSE lane
//! family each learned this the hard way: while the re-derivation lived only in
//! the family's own gate, the targets that PIN the published x86-64 ratio
//! re-derived nothing, and an encoder change that made the bytes wrong would
//! have left the credit hook happily decoding FROZEN bytes with every
//! ratio-pinning target green. This module is that fix for the third family,
//! shared by `x86_movsxd_sib_gate` and `coverage_gate_tests` via `#[path]` so
//! there is one definition of "what the encoder emits today" and not two.

#![allow(dead_code)]

use trust_cg_codegen::x86_64::{X86Encoder, X86InstOperands};
use trust_cg_ir::{X86Opcode, X86PReg};
use trust_cg_verify::x86_movsxd_sib_proofs as msx;

use msx::EMITTED_X86_MOVSXD_SIB;

/// The `trust-cg-ir` physical register whose DISPLAY NAME is `name`. The scan is
/// over `trust-cg-ir`'s own name table — never over `hw_enc`, which is the table
/// under test.
pub fn preg_named(name: &str) -> X86PReg {
    (0u16..80)
        .map(X86PReg::new)
        .find(|r| r.to_string() == name)
        .unwrap_or_else(|| panic!("trust-cg-ir has no register named `{name}`"))
}

/// The bytes the REAL encoder emits for `MovsxdRMSib dst, [base + index*scale + disp]`.
pub fn live_encode(dst: &str, base: &str, index: &str, scale: u32, disp: i64) -> Vec<u8> {
    let mut encoder = X86Encoder::new();
    encoder
        .encode_instruction(
            X86Opcode::MovsxdRMSib,
            &X86InstOperands::rm_sib(
                preg_named(dst),
                preg_named(base),
                preg_named(index),
                scale as u8,
                disp,
            ),
        )
        .unwrap_or_else(|e| {
            panic!("live encoder refused MOVSXD {dst},[{base}+{index}*{scale}{disp:+}]: {e:?}")
        });
    encoder.finish()
}

/// Re-derive every captured MOVSXD-SIB encoding from the live encoder and
/// require byte identity. Returns the number of entries checked.
///
/// A target that PINS the x86-64 coverage ratio calls this, so the pin cannot
/// stand on bytes the backend no longer emits.
pub fn assert_movsxd_sib_corpus_is_what_the_live_encoder_emits() -> usize {
    let mut checked = 0usize;
    for entry in EMITTED_X86_MOVSXD_SIB {
        let live = live_encode(entry.dst, entry.base, entry.index, entry.scale, entry.disp);
        assert_eq!(
            live.as_slice(),
            entry.bytes,
            "STALE MOVSXD-SIB CORPUS: MOVSXD {},[{} + {}*{} {:+#x}] is emitted as {live:02x?} by \
             the live encoder but captured as {:02x?}. The x86-64 MovsxdRMSib credit would rest \
             on bytes the backend no longer emits; re-capture and re-run \
             tests/x86_movsxd_sib_gate.rs",
            entry.dst,
            entry.base,
            entry.index,
            entry.scale,
            entry.disp,
            entry.bytes
        );
        checked += 1;
    }
    assert!(
        checked >= 40,
        "the MOVSXD-SIB corpus shrank to {checked} entries"
    );
    checked
}
