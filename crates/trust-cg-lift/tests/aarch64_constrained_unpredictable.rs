// trust-cg-lift/tests/aarch64_constrained_unpredictable
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Operand-alias combinations whose encodings are allocated but whose effects
//! AArch64 leaves CONSTRAINED UNPREDICTABLE must never enter the lifting lane.

use trust_cg_lift::disasm::aarch64::{DecodeError, Instruction, decode};

#[track_caller]
fn constrained(word: u32) {
    assert!(
        matches!(decode(word), Err(DecodeError::ConstrainedUnpredictable { word: got, .. }) if got == word),
        "0x{word:08x} must fail closed as constrained-unpredictable; got {:?}",
        decode(word),
    );
}

#[track_caller]
fn decodes(word: u32) {
    assert!(
        matches!(
            decode(word),
            Ok(Instruction::LoadStoreIndexed(_)
                | Instruction::LoadStoreUnscaled(_)
                | Instruction::LoadStorePair(_)
                | Instruction::LoadStoreExclusiveAcquireRelease(_))
        ),
        "legal boundary word 0x{word:08x} must keep decoding; got {:?}",
        decode(word),
    );
}

#[test]
fn indexed_scalar_transfer_must_not_alias_writeback_base() {
    for word in [0xf81e_b7de, 0x7843_dd8c, 0xb890_1e10, 0x3800_3cc6] {
        constrained(word);
    }

    // One-register controls, SP/ZR exemption, and no-writeback boundary.
    for word in [
        0xf81e_b7dd,
        0x7843_dd8b,
        0xb890_1e11,
        0x3800_3cc5,
        0xf840_87ff,
        0xf840_8000,
    ] {
        decodes(word);
    }

    // q0 and x0 are different architectural registers despite sharing index 0.
    decodes(0x3cc1_0400); // ldr q0,[x0],#16
}

#[test]
fn load_pair_must_not_name_one_destination_twice() {
    for word in [
        0xa97b_8040,
        0x2940_0040,
        0x69c5_0541,
        0xa941_7c5f,
        0xa8c1_0ca3,
        0x28c0_7fff,
        0xad40_0040, // ldp q0,q0,[x2]
    ] {
        constrained(word);
    }

    for word in [
        0xa97b_8440,
        0x2940_0440,
        0x69c5_0941,
        0xa941_045f,
        0xa8c1_10a3,
        0x28c0_07ff,
        0xa901_0040,
        0xad40_0440,
    ] {
        decodes(word);
    }
}

#[test]
fn indexed_integer_pair_must_not_alias_writeback_base() {
    for word in [0xa989_0442, 0xa8a5_6301, 0xa9c7_9eb5, 0x28c1_0c61] {
        constrained(word);
    }

    for word in [
        0xa989_0443,
        0xa8a5_5f01,
        0xa9c7_9eb1,
        0x28c1_0861,
        0xa9c1_07e0,
        0xa940_0800,
    ] {
        decodes(word);
    }

    // SIMD/FP transfer registers do not alias the GPR base register.
    decodes(0xacc1_0c42); // ldp q2,q3,[x2],#32
    decodes(0xac81_0c42); // stp q2,q3,[x2],#32
}

#[test]
fn store_exclusive_status_must_not_alias_data_or_address() {
    // This decoder models the acquire/release exclusive sub-family (STLXR);
    // plain STXR remains fail-closed as unsupported.
    constrained(0x8803_fca3); // stlxr w3,w3,[x5]
    constrained(0x8805_fca4); // stlxr w5,w4,[x5]

    decodes(0x8803_fca4); // stlxr w3,w4,[x5]
    decodes(0x881f_fc01); // stlxr wzr,w1,[x0]
    decodes(0x8800_ffe1); // stlxr w0,w1,[sp]
    decodes(0x885f_fc00); // ldaxr w0,[x0]
}
