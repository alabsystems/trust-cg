// Trust-toolchain slice — the production trust-ir `PointerLayoutShape::total_bits`
// (trust-ir/crates/trust-ir/src/shape.rs:300) lowered VERBATIM over the real
// `PointerLayoutShape` struct.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (2nd batch, fn #3).
//
// `total_bits` computes the total in-register width of a pointer value (thin or
// fat) from its layout shape: a thin pointer is `data_bits`; a fat pointer is
// `data_bits + metadata_bits`, CHECKED for u32 overflow (`checked_add`). The
// trust-ir layout/codegen machinery uses `PointerLayoutShape` to model how a
// `Ptr`/`FatPtr`/`Ref` is passed and stored; `total_bits` is the size query a
// caller uses to reason about that value's footprint.
//
// It is PURE, deterministic, closure-free, self-contained:
//   * a match over `metadata_bits: Option<u32>` (the Some/None discriminant),
//   * real `checked_add` u32 arithmetic that returns `Option<u32>` (overflow ->
//     None) — and the `Option<u32>` discriminant uses a SMALL niche tag (u32 has
//     a spare value), unlike `Option<u128>` (16-byte tag, the frontend boundary),
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O, NO rustc internals.
//
// TRANSCRIBED VERBATIM:
//   * `PointerLayoutShape` struct (shape.rs:267-273) — fields in order; the
//     `PointerMetadataShape` enum (shape.rs:224-230) it references, so rustc lays
//     the struct out identically to production.
//   * `total_bits` (shape.rs:300-305) — THE EMIT ROOT, byte-for-byte.

#![allow(dead_code)]

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TyId(pub u32);

// ── PointerMetadataShape (shape.rs:224-230) — VERBATIM (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PointerMetadataShape {
    SliceLen { elem: TyId },
    StrLen,
    VTable { trait_id: u32 },
}

// ── PointerLayoutShape (shape.rs:267-273) — VERBATIM (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PointerLayoutShape {
    pub data_bits: u32,
    pub metadata_bits: Option<u32>,
    pub metadata: Option<PointerMetadataShape>,
}

impl PointerLayoutShape {
    // ── total_bits (shape.rs:300-305) — THE EMIT ROOT, VERBATIM. ──
    pub fn total_bits(self) -> Option<u32> {
        match self.metadata_bits {
            Some(metadata_bits) => self.data_bits.checked_add(metadata_bits),
            None => Some(self.data_bits),
        }
    }
}

// ── C-ABI entrypoint. The verified body is `total_bits`; this wrapper only
//    constructs a `PointerLayoutShape` from scalar fields (presence flags +
//    values for the two Options — `metadata` is set to a fixed VTable shape when
//    present, since `total_bits` never reads `metadata`, only `metadata_bits`),
//    calls the REAL fn, then flattens the `Option<u32>` result: returns the value
//    + 1 when Some (so 0 unambiguously means None — total_bits is always < u32::MAX
//    in the Some case here, the +1 cannot overflow our test inputs). The
//    construction + flatten are OUTSIDE the verified body. ──
#[no_mangle]
pub extern "C" fn total_bits_entry(
    data_bits: u32,
    meta_present: u32,
    meta_bits: u32,
) -> u64 {
    let metadata_bits: Option<u32> = if meta_present != 0 {
        Some(meta_bits)
    } else {
        None
    };
    let metadata: Option<PointerMetadataShape> = if meta_present != 0 {
        Some(PointerMetadataShape::VTable { trait_id: 0 })
    } else {
        None
    };
    let shape = PointerLayoutShape {
        data_bits,
        metadata_bits,
        metadata,
    };
    // Encode Option<u32>: None -> 0 ; Some(v) -> (v as u64) | (1 << 32) presence bit.
    match shape.total_bits() {
        Some(v) => (v as u64) | (1u64 << 32),
        None => 0,
    }
}

fn main() {
    // Smoke: thin(64) -> Some(64) ; fat(64,64) -> Some(128) ; overflow -> None.
    println!("{:#x}", total_bits_entry(64, 0, 0)); // Some(64)
    println!("{:#x}", total_bits_entry(64, 1, 64)); // Some(128)
    println!("{:#x}", total_bits_entry(u32::MAX, 1, 1)); // checked_add overflow -> None (0)
}
