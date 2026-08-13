// trust-cg-ir - Overflow carrier op-kind + width packing
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The op-kind + width tag packed into the third operand of a
//! [`crate::inst::AArch64Opcode::TrapOverflowExact`] carrier.
//!
//! # Why a packed tag is load-bearing for SOUNDNESS
//!
//! The Certified-Elimination Kernel fingerprints a carrier's whole operand
//! identity (`[lhs, rhs, Imm(tag)]` via [`crate::guard::fingerprint_operands`]).
//! Unlike the bounds/null/div/shift carriers, an overflow carrier over the SAME
//! `[lhs, rhs]` registers can mean six DIFFERENT checks — signed add, signed
//! sub, unsigned add, unsigned sub, signed mul, unsigned mul — over the carrier
//! widths (add/sub: 32/64; mul: 64 only). If the carrier's operand identity did
//! not encode the op-kind and width, a proof discharging a *signed-add* overflow
//! (or a *signed-mul* one, or a *32-bit* one) could discharge the fingerprint of
//! an *unsigned-sub* (or *64-bit*) carrier over the same registers, because the
//! `[lhs, rhs]` prefix would collide. By folding `(op_kind, width)` into a single
//! immediate that participates in the fingerprint, a wrong-op or wrong-width
//! overflow proof fingerprints differently and CANNOT discharge the carrier — in
//! particular a mul proof can never discharge an add/sub carrier and vice versa.
//!
//! The width also selects the correct flag-recompute register in the KEPT
//! expansion (`XZR` for 64-bit, `WZR` for 32-bit), and the op-kind selects the
//! flag-setter (`ADDS` vs `SUBS`) plus the matching skip condition.

/// The arithmetic kind whose overflow a [`crate::inst::AArch64Opcode::TrapOverflowExact`]
/// carrier checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverflowOp {
    /// Signed `a + b` — overflow on `V` (signed overflow), skip on `VC`.
    SignedAdd,
    /// Signed `a - b` — overflow on `V` (signed overflow), skip on `VC`.
    SignedSub,
    /// Unsigned `a + b` — overflow (carry out) on `C`/`HS`, skip on `LO`.
    UnsignedAdd,
    /// Unsigned `a - b` — overflow (borrow) on `!C`/`LO`, skip on `HS`.
    UnsignedSub,
    /// Signed `a * b` — overflow iff the high 64 bits of the signed 128-bit
    /// product differ from the sign-extension of the low 64 bits. The KEPT
    /// expansion is `MUL lo; SMULH hi; ASR sign, lo, #63; CMP hi, sign; B.EQ
    /// skip; BRK` (skip on equality = NO overflow). 64-bit only (SMULH has no
    /// 32-bit variant).
    SignedMul,
    /// Unsigned `a * b` — overflow iff the high 64 bits of the unsigned 128-bit
    /// product are nonzero. The KEPT expansion is `UMULH hi; CMP hi, #0; B.EQ
    /// skip; BRK` (skip on `hi == 0` = NO overflow). 64-bit only (UMULH has no
    /// 32-bit variant).
    UnsignedMul,
}

impl OverflowOp {
    /// The stable small-integer code for this op-kind. Stable so the packed tag
    /// is reproducible across the producer (ISel) and consumer (expansion/kernel).
    pub const fn code(self) -> u8 {
        match self {
            OverflowOp::SignedAdd => 0,
            OverflowOp::SignedSub => 1,
            OverflowOp::UnsignedAdd => 2,
            OverflowOp::UnsignedSub => 3,
            OverflowOp::SignedMul => 4,
            OverflowOp::UnsignedMul => 5,
        }
    }

    /// Inverse of [`Self::code`].
    pub const fn from_code(code: u8) -> Option<Self> {
        match code {
            0 => Some(OverflowOp::SignedAdd),
            1 => Some(OverflowOp::SignedSub),
            2 => Some(OverflowOp::UnsignedAdd),
            3 => Some(OverflowOp::UnsignedSub),
            4 => Some(OverflowOp::SignedMul),
            5 => Some(OverflowOp::UnsignedMul),
            _ => None,
        }
    }

    /// True iff this op is a subtraction (`SUBS` flag-setter) rather than an add.
    ///
    /// Multiplications are NEITHER add nor sub: their KEPT expansion uses the
    /// `MUL`/`SMULH`/`UMULH` mul-high idiom (selected via [`Self::is_mul`]), not
    /// the `ADDS`/`SUBS` flag-recompute, so `is_sub` stays `false` for both mul
    /// variants. A mul op must NEVER fall into the add/sub expansion branch.
    pub const fn is_sub(self) -> bool {
        matches!(self, OverflowOp::SignedSub | OverflowOp::UnsignedSub)
    }

    /// True iff this op is a multiplication (`MUL`/`SMULH`/`UMULH` mul-high
    /// detection idiom) rather than an add/sub. The KEPT expansion branches on
    /// this BEFORE the add/sub flag-recompute, because a mul has no `ADDS/SUBS`
    /// flag-setter form.
    pub const fn is_mul(self) -> bool {
        matches!(self, OverflowOp::SignedMul | OverflowOp::UnsignedMul)
    }
}

/// Pack an `(op_kind, width)` pair into the single immediate carried as operand 2
/// of a `TrapOverflowExact` carrier.
///
/// Layout: `op_code * 256 + width`. `width` is always 32 or 64 (the only widths
/// the ISel produces), so `width < 256` and the two fields never collide. Every
/// distinct `(op, width)` maps to a distinct tag, which is exactly the property
/// the operand fingerprint relies on.
pub const fn pack_overflow_tag(op: OverflowOp, width: u16) -> i64 {
    (op.code() as i64) * 256 + (width as i64)
}

/// Unpack a `TrapOverflowExact` op-tag back into `(op_kind, width)`.
///
/// Returns `None` for a malformed tag (unknown op code, or a width outside the
/// supported `{32, 64}` set) so the expansion can FAIL CLOSED to a bare trap
/// rather than emit a wrong-width flag-recompute.
pub fn unpack_overflow_tag(tag: i64) -> Option<(OverflowOp, u16)> {
    if tag < 0 {
        return None;
    }
    let width = (tag % 256) as u16;
    let code = (tag / 256) as u64;
    if code > u64::from(u8::MAX) {
        return None;
    }
    let op = OverflowOp::from_code(code as u8)?;
    if width != 32 && width != 64 {
        return None;
    }
    Some((op, width))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_every_op_and_width() {
        for op in [
            OverflowOp::SignedAdd,
            OverflowOp::SignedSub,
            OverflowOp::UnsignedAdd,
            OverflowOp::UnsignedSub,
            OverflowOp::SignedMul,
            OverflowOp::UnsignedMul,
        ] {
            for width in [32u16, 64u16] {
                let tag = pack_overflow_tag(op, width);
                assert_eq!(unpack_overflow_tag(tag), Some((op, width)));
            }
        }
    }

    /// The mul variants are NEITHER add nor sub: `is_sub` must stay `false` (so a
    /// mul tag never falls into the `ADDS/SUBS` flag-recompute expansion) and
    /// `is_mul` must be `true` (so the expansion routes to the `MUL/SMULH/UMULH`
    /// mul-high idiom). Getting this wrong would silently expand a mul-overflow
    /// carrier as a bogus add/sub check (FAIL-OPEN miscompile).
    #[test]
    fn mul_is_neither_add_nor_sub_and_is_mul() {
        for op in [OverflowOp::SignedMul, OverflowOp::UnsignedMul] {
            assert!(!op.is_sub(), "{op:?}.is_sub() must be false");
            assert!(op.is_mul(), "{op:?}.is_mul() must be true");
        }
        for op in [
            OverflowOp::SignedAdd,
            OverflowOp::SignedSub,
            OverflowOp::UnsignedAdd,
            OverflowOp::UnsignedSub,
        ] {
            assert!(!op.is_mul(), "{op:?}.is_mul() must be false");
        }
    }

    /// SOUNDNESS: distinct (op, width) pairs MUST produce distinct tags, so a
    /// wrong-op or wrong-width overflow proof cannot collide on the fingerprint.
    #[test]
    fn distinct_pairs_have_distinct_tags() {
        let mut seen = std::collections::HashSet::new();
        for op in [
            OverflowOp::SignedAdd,
            OverflowOp::SignedSub,
            OverflowOp::UnsignedAdd,
            OverflowOp::UnsignedSub,
            OverflowOp::SignedMul,
            OverflowOp::UnsignedMul,
        ] {
            for width in [32u16, 64u16] {
                assert!(
                    seen.insert(pack_overflow_tag(op, width)),
                    "tag collision for {op:?}/{width}"
                );
            }
        }
        // add@64 and sub@64 must differ; add@32 and add@64 must differ.
        assert_ne!(
            pack_overflow_tag(OverflowOp::SignedAdd, 64),
            pack_overflow_tag(OverflowOp::SignedSub, 64)
        );
        assert_ne!(
            pack_overflow_tag(OverflowOp::SignedAdd, 32),
            pack_overflow_tag(OverflowOp::SignedAdd, 64)
        );
        assert_ne!(
            pack_overflow_tag(OverflowOp::UnsignedAdd, 64),
            pack_overflow_tag(OverflowOp::SignedAdd, 64)
        );
        // SOUNDNESS: a mul tag must differ from EVERY add/sub tag (a mul proof can
        // never discharge an add/sub carrier over the same registers and vice
        // versa) and signed-mul@64 must differ from unsigned-mul@64.
        assert_ne!(
            pack_overflow_tag(OverflowOp::SignedMul, 64),
            pack_overflow_tag(OverflowOp::SignedAdd, 64)
        );
        assert_ne!(
            pack_overflow_tag(OverflowOp::SignedMul, 64),
            pack_overflow_tag(OverflowOp::UnsignedMul, 64)
        );
        assert_ne!(
            pack_overflow_tag(OverflowOp::UnsignedMul, 64),
            pack_overflow_tag(OverflowOp::UnsignedSub, 64)
        );
    }

    #[test]
    fn rejects_malformed_tags() {
        assert_eq!(unpack_overflow_tag(-1), None);
        // width 16 unsupported
        assert_eq!(unpack_overflow_tag(16), None);
        // op code 6 unknown (6 * 256 + 64) — codes 0..=5 are SignedAdd..UnsignedMul.
        assert_eq!(unpack_overflow_tag(6 * 256 + 64), None);
        // op code 4 (SignedMul) IS valid now; it must round-trip, not reject.
        assert_eq!(
            unpack_overflow_tag(4 * 256 + 64),
            Some((OverflowOp::SignedMul, 64))
        );
    }
}
