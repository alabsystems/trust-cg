// Trust-toolchain slice — the production trust-ir `FatPtrKind::metadata_shape`
// (trust-ir/crates/trust-ir/src/shape.rs:243) lowered VERBATIM over the real
// `FatPtrKind` / `PointerMetadataShape` enums.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (batch 3).
//
// `metadata_shape(self)` maps a fat-pointer KIND to the SHAPE of its metadata
// word: a slice carries its element-type id as a length descriptor; a `str`
// carries a length; a trait object carries a vtable descriptor keyed by trait
// id. The trust-ir layout machinery (`shape.rs:206`, `698`, `703`) calls it to
// decide how the metadata lane of a fat `PointerLayoutShape` is laid out, so it
// is a genuine layout query of the compiler's own IR.
//
// It is PURE, deterministic, closure-free, self-contained:
//   * an enum -> enum map over `FatPtrKind` (3 arms), like `swap_cmp`, but
//     CARRYING PAYLOADS: `Slice(elem)` -> `SliceLen { elem }` (a `TyId(u32)`
//     copied through), `TraitObject { trait_id }` -> `VTable { trait_id }` (a
//     `u32` copied through), and `Str` -> `StrLen` (fieldless). This exercises
//     reading a payload off the input enum and writing it into the output enum,
//     a different lowering surface from the fieldless `swap_cmp`.
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O, NO rustc internals.
//
// TRANSCRIBED VERBATIM:
//   * `FatPtrKind` (ty.rs:39-43) — variant set & order.
//   * `PointerMetadataShape` (shape.rs:226-230) — variant set & order.
//   * `TyId` newtype (value.rs `typed_id!`: `pub struct $name(pub u32)`).
//   * `metadata_shape` (shape.rs:243-249) — THE EMIT ROOT, byte-for-byte.

#![allow(dead_code)]

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TyId(pub u32);

// ── FatPtrKind (ty.rs:39-43) — VERBATIM (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FatPtrKind {
    Slice(TyId),
    Str,
    TraitObject { trait_id: u32 },
}

// ── PointerMetadataShape (shape.rs:226-230) — VERBATIM (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PointerMetadataShape {
    SliceLen { elem: TyId },
    StrLen,
    VTable { trait_id: u32 },
}

impl FatPtrKind {
    // ── metadata_shape (shape.rs:243-249) — THE EMIT ROOT, VERBATIM. ──
    pub fn metadata_shape(&self) -> PointerMetadataShape {
        match *self {
            FatPtrKind::Slice(elem) => PointerMetadataShape::SliceLen { elem },
            FatPtrKind::Str => PointerMetadataShape::StrLen,
            FatPtrKind::TraitObject { trait_id } => PointerMetadataShape::VTable { trait_id },
        }
    }
}

// ── Mono root for standalone re-emit (`--mir-emit-closure metadata_shape_root`). ──
#[no_mangle]
pub fn metadata_shape_root(k: &FatPtrKind) -> PointerMetadataShape {
    k.metadata_shape()
}

fn main() {
    let a = FatPtrKind::Slice(TyId(7)).metadata_shape();
    let b = FatPtrKind::Str.metadata_shape();
    let c = FatPtrKind::TraitObject { trait_id: 9 }.metadata_shape();
    println!("{:?} {:?} {:?}", a, b, c);
}
