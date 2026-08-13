// trust-cg-codegen/global_stub.rs - The 0xFADE global-address stub codec
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Single source of truth for the `0xFADE`-tagged **global-address stub**
//! encoding: an opaque `trust_ir::Constant::Int` bit pattern a frontend packs
//! into a function body to mean "the run-time ADDRESS of
//! `module.globals[index] + offset`".
//!
//! # Bit layout (64 bits, carried as a non-negative `i128`)
//!
//! ```text
//! bits[63:48] = 0xFADE   (the tag)
//! bits[47:32] = global index into `module.globals` (16 bits, <= 0xFFFF)
//! bits[31:0]  = byte offset into that global      (32 bits)
//! ```
//!
//! The value is the `u64` packing reinterpreted as a NON-NEGATIVE `i128`
//! (`as u64 as i128`), never sign-extended.
//!
//! # The decode contract (what "is a stub" means)
//!
//! The AUTHORITATIVE consumer is the lower adapter's
//! `decode_imported_global_addr` (`trust-cg-lower/src/adapter.rs`). It first
//! restricts decoding to a **top-level** `Inst::Const` whose declared type is a
//! supported thin pointer/reference carrier (`Ptr`, `Ref`, `RefMut`,
//! `PtrConst`, or `PtrMut`) or the legacy `Ty::I64` address carrier, then
//! treats its `Constant::Int(v)` payload as a stub iff:
//!
//! 1. `0 <= v <= u64::MAX` (the value fits an unsigned 64-bit pattern; a
//!    sign-extended NEGATIVE `i128` — how signed integer constants are
//!    carried — can therefore never collide), and
//! 2. `(v as u64) >> 48 == 0xFADE`.
//!
//! [`decode_global_addr_stub`] mirrors the payload predicate exactly — bit for
//! bit. A caller that operates on typed IR must additionally apply the
//! same typed carrier gate, as [`crate::module_merge`] does. Nested constants
//! (aggregate/array elements, switch case values) and top-level constants of
//! other declared types are NEVER decoded by the adapter; a tag-shaped integer
//! there is plain data.
//!
//! # Ambiguity
//!
//! The tag interval
//! `[0xFADE_0000_0000_0000, 0xFADF_0000_0000_0000)` is reserved at a decoded
//! supported thin pointer/reference or legacy `Ty::I64` carrier position. It is
//! not reserved for `Ty::U64`, `Ty::U128`, `Ty::Usize`, or other declared
//! types; those values remain numeric. `Rc` is deliberately excluded because
//! trust-cg has no ownership-preserving Rc ABI, and `Func` because these stubs
//! name data globals rather than code pointers. Producers (the rustc bridge,
//! the LLVM importer) emit stubs only at top-level `Inst::Const` positions, and
//! passes that cannot establish both the position and carrier must FAIL CLOSED
//! on tag-shaped integers they are not certain about (see `module_merge`'s
//! paranoia rejections) rather than guess.
//!
//! Known encoder/decoder sites this codec is the source of truth for:
//! * encode: rustc bridge `global_addr_stub{,_with_offset}` (now delegating
//!   here), `trust-cg-llvm-import/src/parser.rs`.
//! * decode: `trust-cg-lower/src/adapter.rs::decode_imported_global_addr`
//!   (kept literal there — `trust-cg-lower` cannot depend on this crate; the
//!   golden tests below pin this codec to that exact behavior).

/// The 16-bit tag in bits\[63:48\] marking a `Constant::Int` as a
/// global-address stub.
pub const GLOBAL_ADDR_STUB_TAG: u64 = 0xFADE;

/// Largest global index representable in a stub (bits\[47:32\]).
pub const GLOBAL_ADDR_STUB_MAX_INDEX: u64 = 0xFFFF;

/// Largest byte offset representable in a stub (bits\[31:0\]).
pub const GLOBAL_ADDR_STUB_MAX_OFFSET: u64 = 0xFFFF_FFFF;

/// Encode `&module.globals[global_index] + offset` as a stub `Constant::Int`
/// payload. CHECKED: an index or offset outside its field width is an error
/// (fail-closed) — silent masking would alias a different global or address.
pub fn encode_global_addr_stub(global_index: u64, offset: u64) -> Result<i128, String> {
    if global_index > GLOBAL_ADDR_STUB_MAX_INDEX {
        return Err(format!(
            "global-address stub index {global_index} exceeds the 16-bit stub range \
             (max {GLOBAL_ADDR_STUB_MAX_INDEX})"
        ));
    }
    if offset > GLOBAL_ADDR_STUB_MAX_OFFSET {
        return Err(format!(
            "global-address stub offset {offset} exceeds the 32-bit stub range \
             (max {GLOBAL_ADDR_STUB_MAX_OFFSET})"
        ));
    }
    Ok(((GLOBAL_ADDR_STUB_TAG << 48) | (global_index << 32) | offset) as i128)
}

/// Decode a `Constant::Int` payload as a global-address stub, returning
/// `Some((global_index, offset))` iff the value matches the stub predicate.
///
/// EXACT mirror of the lower adapter's `decode_imported_global_addr`
/// discrimination (`trust-cg-lower/src/adapter.rs`): out-of-`u64`-range and
/// negative values are never stubs; the tag must occupy bits\[63:48\].
pub fn decode_global_addr_stub(value: i128) -> Option<(u64, u32)> {
    if !(0..=(u64::MAX as i128)).contains(&value) {
        return None;
    }
    let bits = value as u64;
    if bits >> 48 != GLOBAL_ADDR_STUB_TAG {
        return None;
    }
    let index = (bits >> 32) & 0xFFFF;
    let offset = (bits & 0xFFFF_FFFF) as u32;
    Some((index, offset))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Golden values pinning the EXACT bit layout the lower adapter decodes
    /// (`decode_imported_global_addr`) and the bridge/LLVM-importer encode.
    /// If this test ever needs changing, every encoder/decoder site listed in
    /// the module docs must change in lockstep.
    #[test]
    fn golden_bit_layout() {
        assert_eq!(
            encode_global_addr_stub(0, 0).unwrap(),
            0xFADE_0000_0000_0000_u64 as i128
        );
        assert_eq!(
            encode_global_addr_stub(1, 0).unwrap(),
            0xFADE_0001_0000_0000_u64 as i128
        );
        assert_eq!(
            encode_global_addr_stub(0xFFFF, 0xFFFF_FFFF).unwrap(),
            0xFADE_FFFF_FFFF_FFFF_u64 as i128
        );
        assert_eq!(
            encode_global_addr_stub(0x0042, 0x1234_5678).unwrap(),
            0xFADE_0042_1234_5678_u64 as i128
        );
    }

    #[test]
    fn round_trips_exhaustive_fields() {
        for index in [0u64, 1, 2, 0x7F, 0xFF, 0x100, 0xFFFE, 0xFFFF] {
            for offset in [0u64, 1, 8, 0xFFFF, 0x1_0000, 0xFFFF_FFFF] {
                let enc = encode_global_addr_stub(index, offset).unwrap();
                assert_eq!(
                    decode_global_addr_stub(enc),
                    Some((index, offset as u32)),
                    "round-trip failed for index={index} offset={offset}"
                );
                // Re-encoding the decode is the identity (used by the merge
                // self-check to prove a remapped stub is well-formed).
                let (i2, o2) = decode_global_addr_stub(enc).unwrap();
                assert_eq!(encode_global_addr_stub(i2, u64::from(o2)).unwrap(), enc);
            }
        }
    }

    /// The decode predicate must match the adapter EXACTLY: negative values
    /// (sign-extended signed constants), values above u64::MAX, and untagged
    /// values are never stubs.
    #[test]
    fn decode_rejects_non_stub_values() {
        // Negative i128 (e.g. a signed i64 constant whose bit pattern's high
        // 16 bits happen to be 0xFADE — carried SIGN-EXTENDED, so negative).
        assert_eq!(decode_global_addr_stub(-1), None);
        assert_eq!(
            decode_global_addr_stub(0xFADE_0000_0000_0000_u64 as i64 as i128),
            None,
            "a sign-extended i64 with the tag pattern is negative as i128 — not a stub"
        );
        // Above the u64 range.
        assert_eq!(decode_global_addr_stub((u64::MAX as i128) + 1), None);
        assert_eq!(
            decode_global_addr_stub(0xFFFF_FADE_0000_0000_0000_i128),
            None
        );
        // In range but untagged.
        assert_eq!(decode_global_addr_stub(0), None);
        assert_eq!(decode_global_addr_stub(42), None);
        assert_eq!(decode_global_addr_stub(u64::MAX as i128), None);
        assert_eq!(
            decode_global_addr_stub(0xFADD_0000_0000_0000_u64 as i128),
            None
        );
        assert_eq!(
            decode_global_addr_stub(0xFADF_0000_0000_0000_u64 as i128),
            None
        );
        // The tag band itself IS decoded (the inherent in-band ambiguity the
        // module docs describe — callers own the fail-closed paranoia).
        assert_eq!(
            decode_global_addr_stub(0xFADE_0007_0000_002A_u64 as i128),
            Some((7, 42))
        );
    }

    #[test]
    fn encode_fails_closed_on_field_overflow() {
        assert!(encode_global_addr_stub(0x1_0000, 0).is_err());
        assert!(encode_global_addr_stub(u64::MAX, 0).is_err());
        assert!(encode_global_addr_stub(0, 0x1_0000_0000).is_err());
        assert!(encode_global_addr_stub(0, u64::MAX).is_err());
    }
}
