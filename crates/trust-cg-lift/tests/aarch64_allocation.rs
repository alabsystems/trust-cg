// trust-cg-lift - AArch64 decode-or-reject ALLOCATION tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Allocation-fidelity regression pins for the AArch64 leaf decoder.
//!
//! # Why this file exists separately from `aarch64_roundtrip.rs`
//!
//! `aarch64_roundtrip.rs` asserts `decode(encode(fields)) == fields`. A
//! round-trip is STRUCTURALLY BLIND to a decoder that accepts MORE than the
//! encoder produces: every word it examines is, by construction, inside the
//! encoder's image. Every hole pinned below lives outside that image, which is
//! why 121 passing round-trip tests coexisted with 123,430 words this decoder
//! named that objdump calls undefined and 72,107 words it renamed onto a
//! different allocated instruction.
//!
//! # What each test asserts
//!
//! Two classes, both from the differential sweep against Apple/LLVM 21 objdump:
//!
//!   * GHOST — objdump answers `<unknown>`; the architecture allocates nothing
//!     here, and the decoder named it anyway.
//!   * MISMATCH — objdump names a DIFFERENT ALLOCATED INSTRUCTION; the decoder
//!     resolved one real instruction onto a neighbouring real instruction. This
//!     is the worse class: the word assembles, executes, and does something
//!     other than what the decoder said.
//!
//! # Provenance of every word in this file
//!
//! Each word below was produced by the differential sweep, then INDEPENDENTLY
//! confirmed by assembling it verbatim (`.incbin`, so the assembler never
//! re-encodes) and reading it back with `objdump`. The comment on each word
//! records objdump's exact answer. No word here was hand-encoded.

use trust_cg_lift::disasm::aarch64::{DecodeError, decode};

/// Assert the decoder REFUSES `word`, naming what objdump calls it.
///
/// Any of the three refusal variants satisfies this. The assertion is about the
/// VERDICT — the word must not reach a consumer as a decoded instruction — not
/// about which rejection reason the decoder reaches first. `Unallocated` and
/// `ConstrainedUnpredictable` in particular are decided on independent axes
/// (does the architecture allocate this encoding, versus does this operand
/// choice have a single architectural meaning), and a word can be refused by
/// either; pinning one reason would make the test fail on a strictly-better
/// decoder that happened to check the other axis first.
#[track_caller]
fn refuses(word: u32, objdump_says: &str) {
    match decode(word) {
        Err(
            DecodeError::Unallocated { .. }
            | DecodeError::Unsupported { .. }
            | DecodeError::ConstrainedUnpredictable { .. },
        ) => {}
        Ok(insn) => panic!(
            "0x{word:08x} is `{objdump_says}` per objdump, but the decoder ACCEPTED it as {insn:?}"
        ),
    }
}

/// Assert the decoder still ACCEPTS `word` — the fixes must not over-refuse.
#[track_caller]
fn accepts(word: u32, objdump_says: &str) {
    if let Err(e) = decode(word) {
        panic!("0x{word:08x} is `{objdump_says}` per objdump, but the decoder REFUSED it: {e}");
    }
}

// ---------------------------------------------------------------------------
// F3 — an ALLOCATED instruction resolved onto a DIFFERENT ALLOCATED instruction.
// ---------------------------------------------------------------------------

/// `opc=0b01, V=0, L=0` in the pair space is STGP (FEAT_MTE), not STP.
///
/// This is the sharpest case in the file. The interpreter that consumes this
/// decoder maps `opc=0b01, V=0` to LDPSW — scale 4, sign-extending. STGP scales
/// `imm7` by 16 and stores 64-bit registers plus an allocation tag. An STGP word
/// was therefore executed at the WRONG ADDRESS with the WRONG ACCESS WIDTH,
/// silently.
#[test]
fn refuses_stgp_masquerading_as_stp() {
    // clang: `stgp x0, x1, [x2, #16]`  -> objdump: stgp x0, x1, [x2, #16]
    refuses(0x6900_8440, "stgp x0, x1, [x2, #16]");
    // clang: `stgp x0, x1, [x2, #16]!` -> objdump: stgp x0, x1, [x2, #16]!
    refuses(0x6980_8440, "stgp x0, x1, [x2, #16]!");
    // clang: `stgp x0, x1, [x2], #16`  -> objdump: stgp x0, x1, [x2], #16
    refuses(0x6880_8440, "stgp x0, x1, [x2], #16");
}

/// `opc=0b11` in the pair space is STTP/LDTP (FEAT_THE), not STP/LDP.
#[test]
fn refuses_sttp_ldtp_masquerading_as_stp_ldp() {
    refuses(0xe900_8441, "sttp x1, x1, [x2, #8]");
    refuses(0xe940_8441, "ldtp x1, x1, [x2, #8]");
    refuses(0xe880_8441, "sttp x1, x1, [x2], #8");
    refuses(0xe8c0_8441, "ldtp x1, x1, [x2], #8");
}

/// The pair rows that ARE StP/LDP/LDPSW must still decode.
///
/// The load row uses DISTINCT transfer registers on purpose. `ldp w1, w1, ...`
/// would exercise the same `(opc, V, L)` row, but `Rt == Rt2` on a load is
/// independently CONSTRAINED UNPREDICTABLE, so such a word is not a witness
/// that the row is allocated — it is refused for a reason that has nothing to
/// do with allocation. Keeping it here would make this test assert that the
/// decoder ACCEPTS a word the architecture leaves undefined.
#[test]
fn still_accepts_the_real_pair_rows() {
    // clang: `ldp w1, w3, [x2, #4]` -> objdump: ldp w1, w3, [x2, #0x4]
    accepts(0x2940_8c41, "ldp w1, w3, [x2, #4]"); // opc=01 V=0 L=1
    accepts(0xa900_8441, "stp x1, x1, [x2, #8]"); // opc=10 V=0 L=0
    accepts(0x2900_8441, "stp w1, w1, [x2, #4]"); // opc=00 V=0 L=0
    accepts(0x6d00_8441, "stp d1, d1, [x2, #8]"); // opc=01 V=1 L=0
    accepts(0xad00_8441, "stp q1, q1, [x2, #16]"); // opc=10 V=1 L=0
}

// ---------------------------------------------------------------------------
// CONSTRAINED UNPREDICTABLE — an ALLOCATED encoding whose OPERAND choice has no
// single architectural meaning. A third class, independent of GHOST/MISMATCH:
// the row is real, the registers are what make the word unliftable.
// ---------------------------------------------------------------------------

/// `LDP` with `Rt == Rt2` has no defined result — the architecture does not say
/// which load lands in the shared destination.
///
/// This word is the sharpest illustration of the header's point that a
/// round-trip is structurally blind. The two independent oracles disagree by
/// design:
///
///   * Apple clang 21 REFUSES to assemble it — `error: unpredictable LDP
///     instruction, Rt2==Rt`. So no encoder, including ours, can produce it,
///     and no round-trip test can ever present it to the decoder.
///   * objdump NAMES it anyway, `ldp w1, w1, [x2, #0x4]`, because a
///     disassembler prints what the fields spell.
///
/// A differential that only compares MNEMONICS therefore scores this word as
/// agreement. It is a decode-or-reject question, which is why it is pinned here
/// and not there.
#[test]
fn refuses_load_pair_with_aliased_transfer_registers() {
    // raw word from the sweep (clang will not emit it); objdump: ldp w1, w1, [x2, #0x4]
    refuses(0x2940_8441, "ldp w1, w1, [x2, #4]");
}

/// Bit 10 is the "Advanced SIMD three SAME" class bit. With bit10=0 the same
/// `[15:11]` pattern is three-DIFFERENT (widening multiply-accumulate, widening
/// subtract) or two-register-misc — different operand meanings entirely.
#[test]
fn refuses_neon_three_different_masquerading_as_three_same() {
    // clang: `smlal  v0.8h, v1.8b, v2.8b`  -> objdump: smlal.8h  v0, v1, v2
    refuses(0x0e22_8020, "smlal.8h v0, v1, v2");
    // clang: `smlal2 v0.4s, v1.8h, v2.8h`  -> objdump: smlal2.4s v0, v1, v2
    refuses(0x4e62_8020, "smlal2.4s v0, v1, v2");
    // clang: `umlal  v3.4s, v4.4h, v5.4h`  -> objdump: umlal.4s  v3, v4, v5
    refuses(0x2e65_8083, "umlal.4s v3, v4, v5");
    // clang: `ssubw  v6.8h, v7.8h, v8.8b`  -> objdump: ssubw.8h  v6, v7, v8
    refuses(0x0e28_30e6, "ssubw.8h v6, v7, v8");
    // clang: `rev16  v9.16b, v10.16b`      -> objdump: rev16.16b v9, v10
    refuses(0x4e20_1949, "rev16.16b v9, v10");
}

/// Every `L=1` system word was decoded as MRS. `op0` (bits [20:19]) picks the
/// class: `0b01` is SYSL, a system INSTRUCTION result read, not a system
/// REGISTER read.
#[test]
fn refuses_sysl_masquerading_as_mrs() {
    // clang: `sysl x0, #3, c7, c3, #7` -> objdump: sysl x0, #3, c7, c3, #7
    refuses(0xd52b_73e0, "sysl x0, #3, c7, c3, #7");
    // objdump: sysl x21, #0, c0, c0, #0
    refuses(0xd528_0015, "sysl x21, #0, c0, c0, #0");
    // objdump: tstart xzr   (op0=0b00, L=1 — also not MRS)
    refuses(0xd523_307f, "tstart xzr");
}

/// A real MRS must still decode.
#[test]
fn still_accepts_real_mrs() {
    accepts(0xd53b_d060, "mrs x0, TPIDRRO_EL0"); // op0=0b11
}

/// The ONE place these fixes deliberately refuse a word the REFERENCE decodes.
///
/// LLVM's disassembler prints a generic `mrs x0, S<op0>_<op1>_C<n>_C<m>_<op2>`
/// for the whole `L=1` space, including `op0=0b00`. The architecture does not:
/// MRS is defined for `op0=0b1x`, and `op0=0b00, L=1` is unallocated apart from
/// the FEAT_TME `TSTART`/`TTEST` carve-outs. Here the reference is the PERMISSIVE
/// party, so agreeing with it would mean naming words that UNDEF on hardware.
///
/// This narrowing gave up 1,222 previously-"agreeing" words in the 5,078,879-word
/// sweep. It is recorded here rather than left as an unexplained delta, because
/// an unrecorded acceptance change is exactly the kind of claim this program has
/// had to retract. It costs nothing in practice: trustc emits only `op0=0b11`
/// system-register reads, and the 5,293-word emitted corpus is unaffected.
#[test]
fn refuses_generic_op0_zero_system_read_that_objdump_calls_mrs() {
    refuses(
        0xd520_0000,
        "mrs x0, S0_0_C0_C0_0 (LLVM generic naming; UNDEF on hardware)",
    );
    refuses(
        0xd520_00cb,
        "mrs x11, S0_0_C0_C0_6 (LLVM generic naming; UNDEF on hardware)",
    );
}

/// In the register-offset prefetch space the `Rt` field is the prefetch
/// operation, and `type=0b11` is not a prefetch type — that quarter is RPRFM
/// (FEAT_RPRFM), a range prefetch with different operands.
#[test]
fn refuses_rprfm_masquerading_as_prfm() {
    // objdump: rprfm #3, x0, [x13]
    refuses(0xf8a0_49bb, "rprfm #3, x0, [x13]");
    // objdump: rprfm #23, x3, [x4]
    refuses(0xf8a3_689f, "rprfm #23, x3, [x4]");
}

/// Plain PRFM (prfop type 0b00/0b01/0b10) must still decode, in every form.
#[test]
fn still_accepts_real_prfm() {
    accepts(0xf8a3_6885, "prfm pldl3strm, [x4, x3]"); // register offset, Rt=5
    accepts(0xf983_2085, "prfm pldl3strm, [x4, #1600]"); // unsigned imm
}

// ---------------------------------------------------------------------------
// F2 — reserved / sf-dependent FIELDS never validated.
// ---------------------------------------------------------------------------

/// `sf=0` makes the operand 32 bits, so a 6-bit shift amount of 32..63 is
/// UNDEFINED, not a wide shift.
#[test]
fn refuses_32bit_shifted_register_amount_above_31() {
    // objdump: <unknown>   (orr w1, w2, w3, lsl #32)
    refuses(0x2a03_8041, "<unknown>");
    // objdump: <unknown>   (and w1, w2, w3, lsr #48)
    refuses(0x0a43_c041, "<unknown>");
    // objdump: <unknown>   (add w1, w2, w3, lsl #32)
    refuses(0x0b03_8041, "<unknown>");
    // objdump: <unknown>   (subs w1, w2, w3, asr #63)
    refuses(0x6b83_fc41, "<unknown>");
}

/// The same amounts at `sf=1` are real 64-bit shifts and must still decode.
#[test]
fn still_accepts_64bit_shifted_register_amount_above_31() {
    accepts(0xaa03_8041, "orr x1, x2, x3, lsl #32");
    accepts(0x8b03_8041, "add x1, x2, x3, lsl #32");
}

/// `hw` selects a 16-bit lane; a 32-bit destination has only lanes 0 and 1.
#[test]
fn refuses_32bit_move_wide_high_halfword_lane() {
    // objdump: <unknown>   (movz w0, #1, lsl #32)
    refuses(0x52c0_0020, "<unknown>");
    // objdump: <unknown>   (movk w0, #1, lsl #48)
    refuses(0x72e0_0020, "<unknown>");
}

/// 64-bit MOVZ/MOVK at the same lanes must still decode.
#[test]
fn still_accepts_64bit_move_wide_high_halfword_lane() {
    accepts(0xd2c0_0020, "mov x0, #4294967296");
    accepts(0xf2e0_0020, "movk x0, #1, lsl #48");
}

/// Half of the scalar load/store `(size, V, opc)` space is unallocated. The
/// table was measured for all five addressing forms; these are its rows.
#[test]
fn refuses_unallocated_scalar_load_store_size_v_opc() {
    // (size, V, opc) unallocated in EVERY form:
    //   V=1: (01,1,10) (01,1,11) (10,1,10) (10,1,11) (11,1,10) (11,1,11)
    //   V=0: (10,0,11) (11,0,11)
    // unsigned-offset form, base x4 / Rt x1 / imm12=8
    refuses(0x7d80_2081, "<unknown>");
    refuses(0xbd80_2081, "<unknown>");
    refuses(0xb9c0_2081, "<unknown>");
    refuses(0xf9c0_2081, "<unknown>");
    // unscaled (LDUR-family) form
    refuses(0x7c80_8081, "<unknown>");
    refuses(0xb8c0_8081, "<unknown>");
    // register-offset form
    refuses(0xb8e0_6881, "<unknown>");
}

/// PRFM has no base-writeback form, so `size=0b11, V=0, opc=0b10` is allocated
/// in the offset/unscaled/register forms and UNALLOCATED in pre/post-index.
#[test]
fn refuses_prefetch_with_base_writeback() {
    // objdump: <unknown>   (post-index, size=11 V=0 opc=10)
    refuses(0xf880_8481, "<unknown>");
    // objdump: <unknown>   (pre-index, size=11 V=0 opc=10)
    refuses(0xf880_8c81, "<unknown>");
}

/// The same triple without writeback is PRFM/PRFUM and must still decode.
#[test]
fn still_accepts_prefetch_without_writeback() {
    accepts(0xf980_2081, "prfm pldl1strm, [x4, #64]");
    accepts(0xf880_8081, "prfum pldl1strm, [x4, #8]");
}

/// LD1/ST1 (one register, post-indexed) DOES allocate the 64-bit lane.
///
/// `q=0, size=0b11` has no arrangement in the AdvSIMD three-same class, and a
/// shared validator was applying that class's rule here — refusing allocated
/// instructions with a reason that asserted the opposite of the architecture.
/// The two classes have DIFFERENT allocation tables, which is exactly why
/// `validate_scalar_load_store` takes a form discriminator instead of being
/// shared blind.
#[test]
fn still_accepts_ld1_st1_one_register_64bit_lane() {
    // raw words from the sweep; objdump: ld1.1d / st1.1d { v0 }, [x0], #8
    accepts(0x0cdf_7c00, "ld1.1d { v0 }, [x0], #8");
    accepts(0x0c9f_7c00, "st1.1d { v0 }, [x0], #8");
}

/// NEON MUL has no 64-bit-lane arrangement, unlike ADD/SUB/CMxx.
#[test]
fn refuses_neon_mul_with_64bit_elements() {
    // objdump: <unknown>   (mul with size=0b11)
    refuses(0x4ee2_9c61, "<unknown>");
}

/// ADD/SUB at `size=0b11, q=1` are real (`.2d`) and must still decode.
#[test]
fn still_accepts_neon_add_sub_with_64bit_elements() {
    accepts(0x4ee2_8461, "add.2d v1, v3, v2");
    accepts(0x6ee2_8461, "sub.2d v1, v3, v2");
}

/// FMOV between a general register and an FP register is a BIT COPY: the widths
/// must match. `sf=1` with ftype=S, or `sf=0` with ftype=D, is unallocated.
#[test]
fn refuses_fmov_with_mismatched_register_widths() {
    // objdump: <unknown>   (sf=1, ftype=00 -> X <-> S)
    refuses(0x9e26_0061, "<unknown>");
    refuses(0x9e27_0061, "<unknown>");
    // objdump: <unknown>   (sf=0, ftype=01 -> W <-> D)
    refuses(0x1e66_0061, "<unknown>");
    refuses(0x1e67_0061, "<unknown>");
}

/// The width-matched FMOVs must still decode.
#[test]
fn still_accepts_fmov_with_matched_register_widths() {
    accepts(0x1e26_0061, "fmov w1, s3");
    accepts(0x9e66_0061, "fmov x1, d3");
    accepts(0x9e67_0061, "fmov d1, x3");
}

/// FCVT converts BETWEEN precisions; same-type encodings are unallocated.
#[test]
fn refuses_fcvt_between_identical_precisions() {
    // objdump: <unknown>   (ftype=00 -> 00)
    refuses(0x1e22_4061, "<unknown> (fcvt s <- s)");
    // objdump: <unknown>   (ftype=01 -> 01)
    refuses(0x1e62_c061, "<unknown> (fcvt d <- d)");
    // objdump: <unknown>   (ftype=11 -> 11)
    refuses(0x1ee3_c061, "<unknown> (fcvt h <- h)");
}

/// Real precision conversions must still decode.
#[test]
fn still_accepts_fcvt_between_differing_precisions() {
    accepts(0x1e22_c061, "fcvt d1, s3");
    accepts(0x1e62_4061, "fcvt s1, d3");
}
