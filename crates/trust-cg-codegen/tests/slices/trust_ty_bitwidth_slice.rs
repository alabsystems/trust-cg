// Trust-toolchain FOOTHOLD slice — the production trust-ir `Ty::bit_width` /
// `Ty::bit_width_with` (trust-ir/crates/trust-ir/src/ty.rs:153 + :185) lowered
// over the REAL `Ty` enum.
//
// This is SELF-APPLICATION of the verify-native==JIT method to TRUST ITSELF:
// `Ty::bit_width_with` is a PURE, deterministic, target-parametric type-size
// computation — the same family as the clean-kernel `Expr` folds, but it is a
// function of the COMPILER's own IR (`trust-ir`), not of clean's kernel. It has:
//   * a wide branch over the `Ty` enum (every scalar/pointer/aggregate arm),
//   * RECURSION through `Box<Ty>` (Vector's element type, in both fns),
//   * `Option` / `checked_mul` saturating arithmetic (overflow -> None),
//   * a real soundness invariant: pointer-like types return `None` from the
//     pointer-AGNOSTIC `bit_width` (NOT a baked-in 64 — that would be a latent
//     miscompile on wasm32), and only `bit_width_with(pointer_bits)` resolves
//     them to the target's pointer width. (See the `// Trust:` note at ty.rs:151.)
//
// TRANSCRIBED VERBATIM (faithful, from ty.rs / value.rs):
//   * `Ty` enum (ty.rs:55-131) — every variant, in order.
//   * `FatPtrKind` (ty.rs:37-43), `SetRepr` (ty.rs:12-22) — the inline enums.
//   * the id newtypes `TyId/StructId/EnumId/FuncTyId/RecordId/ClosureTyId`
//     (value.rs `typed_id!`: `pub struct $name(pub u32)`).
//   * `pub const DEFAULT_POINTER_BITS: u32 = 64` (ty.rs:142).
//   * `Ty::bit_width` (ty.rs:153-175) VERBATIM.
//   * `Ty::bit_width_with` (ty.rs:185-196) VERBATIM — the EMIT ROOT.
//
// NOTHING is modeled or shimmed: this function touches no env / HashMap / Arc /
// RefCell / I/O / rustc internals. It is a closed computation over `Ty`. The only
// adaptation is dropping the `#[cfg_attr(feature="serde", ...)]` derives (no serde
// in the slice) and the `Display`/builder impls (unused by bit_width) — the enum
// SHAPE and the two transcribed fns are byte-for-byte the production source.

#![allow(dead_code)]

// ── id newtypes (value.rs `typed_id!` expansion; only the field shape matters
//    for `Ty`'s layout — these are `pub struct $name(pub u32)`). ──
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TyId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncTyId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EnumId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RecordId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClosureTyId(pub u32);

impl TyId {
    pub const fn new(index: u32) -> Self {
        Self(index)
    }
}

// ── SetRepr (ty.rs:12-22) — VERBATIM (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum SetRepr {
    /// Flat bitset lowering (small bounded scalar elements).
    Bitset,
    /// Boxed runtime container (hash set / sorted vec). Default conservative
    /// choice; frontends may refine to `Bitset` when they can prove the
    /// universe is small and dense.
    #[default]
    Boxed,
}

// ── FatPtrKind (ty.rs:37-43) — VERBATIM (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FatPtrKind {
    Slice(TyId),
    Str,
    TraitObject { trait_id: u32 },
}

// ── Ty (ty.rs:55-131) — VERBATIM variant set & order (serde cfg_attr dropped;
//    doc comments preserved where they carry the lowering-relevant shape). ──
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    // Signed integers
    I8,
    I16,
    I32,
    I64,
    I128,
    // Unsigned integers
    U8,
    U16,
    U32,
    U64,
    U128,
    // Floating point
    F16,
    F32,
    F64,
    // Special types
    Bool,
    /// Fixed-width SIMD vector. Element type is inline (`Box<Ty>`), lane count `u32`.
    Vector(Box<Ty>, u32),
    Ptr,
    FatPtr(FatPtrKind),
    Unit,
    Never,
    // Composite types
    Struct(StructId),
    Array(TyId, u64),
    Tuple(Vec<Ty>),
    Enum(EnumId),
    Func(FuncTyId),
    // Reference types (Rust borrowing)
    Ref(Box<Ty>),
    RefMut(Box<Ty>),
    // Raw pointer types (C semantics)
    PtrConst(Box<Ty>),
    PtrMut(Box<Ty>),
    // Reference counted (Swift ARC)
    Rc(Box<Ty>),
    // Aggregate types (issue #30, item 1).
    Set(TyId, SetRepr),
    Sequence(TyId),
    Record(RecordId),
    Closure(ClosureTyId),
}

/// The default thin-pointer width, in bits, for the 64-bit targets TrustIr
/// currently supports. (ty.rs:142, VERBATIM.)
pub const DEFAULT_POINTER_BITS: u32 = 64;

impl Ty {
    /// Bit width of a type whose size is **target-independent**. (ty.rs:153-175,
    /// VERBATIM.)
    ///
    /// Returns `None` for every pointer-like type (`Ptr`, `*const`/`*mut`,
    /// `&`/`&mut`, `Rc`, fat pointers): their width is the target's pointer
    /// size, which is only known with a target. Resolve them with
    /// [`Ty::bit_width_with`] (e.g. 32 on wasm32, 64 on aarch64/x86-64).
    // Trust: pointers must not report a context-free 64-bit width — that is a
    // latent miscompile/missproof on 32-bit targets such as wasm32.
    pub fn bit_width(&self) -> Option<u32> {
        match self {
            Ty::Bool => Some(1),
            Ty::I8 | Ty::U8 => Some(8),
            Ty::I16 | Ty::U16 => Some(16),
            Ty::I32 | Ty::U32 => Some(32),
            Ty::I64 | Ty::U64 => Some(64),
            Ty::I128 | Ty::U128 => Some(128),
            Ty::F16 => Some(16),
            Ty::F32 => Some(32),
            Ty::F64 => Some(64),
            Ty::Vector(elem, lanes) => elem.bit_width().and_then(|bits| bits.checked_mul(*lanes)),
            // Pointer-like types are target-dependent — see `bit_width_with`.
            Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_)
            | Ty::FatPtr(_) => None,
            _ => None,
        }
    }

    /// Bit width of a type given the target's thin-pointer width in bits
    /// (`pointer_bits` — e.g. 32 on wasm32, 64 on aarch64/x86-64). (ty.rs:185-196,
    /// VERBATIM — this is the EMIT ROOT.)
    pub fn bit_width_with(&self, pointer_bits: u32) -> Option<u32> {
        match self {
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
                Some(pointer_bits)
            }
            Ty::FatPtr(_) => pointer_bits.checked_mul(2),
            Ty::Vector(elem, lanes) => elem
                .bit_width_with(pointer_bits)
                .and_then(|bits| bits.checked_mul(*lanes)),
            _ => self.bit_width(),
        }
    }
}

// ── A C-ABI entrypoint so the native oracle and the JIT can both be called over
//    the SAME inputs. `bit_width_with` returns `Option<u32>`; we flatten it to an
//    i64 sentinel (-1 = None, else the bit count) so the harness compares a single
//    scalar bit-identically. The flatten is OUTSIDE the verified body (it only
//    discriminates the Option the real fn returns).
//
//    NOTE: this wrapper is NOT the emit root; `bit_width_with` is. It exists only
//    to give the test a stable C signature; the verified logic is the transcribed
//    fn above.
#[no_mangle]
pub extern "C" fn bit_width_with_entry(ty_tag: u32, pointer_bits: u32) -> i64 {
    // Build one of a fixed menu of `Ty` values selected by `ty_tag`, then call
    // the REAL `bit_width_with`. (The menu construction is test scaffolding; the
    // computation under test is `bit_width_with`.)
    let ty = ty_for_tag(ty_tag);
    match ty.bit_width_with(pointer_bits) {
        Some(b) => b as i64,
        None => -1,
    }
}

/// Test menu: map a small tag to a representative `Ty`, covering every arm of
/// `bit_width_with` (scalar delegate, thin-pointer, fat-pointer x2, vector
/// recursion incl. vector-of-pointer, overflow, aggregate -> None).
fn ty_for_tag(tag: u32) -> Ty {
    match tag {
        0 => Ty::Bool,
        1 => Ty::I8,
        2 => Ty::I16,
        3 => Ty::I32,
        4 => Ty::I64,
        5 => Ty::I128,
        6 => Ty::U8,
        7 => Ty::U32,
        8 => Ty::F16,
        9 => Ty::F32,
        10 => Ty::F64,
        11 => Ty::Ptr,
        12 => Ty::PtrConst(Box::new(Ty::I32)),
        13 => Ty::PtrMut(Box::new(Ty::I8)),
        14 => Ty::Ref(Box::new(Ty::I64)),
        15 => Ty::RefMut(Box::new(Ty::U64)),
        16 => Ty::Rc(Box::new(Ty::I32)),
        17 => Ty::FatPtr(FatPtrKind::Str),
        18 => Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
        19 => Ty::Vector(Box::new(Ty::I32), 4),  // 128
        20 => Ty::Vector(Box::new(Ty::Bool), 8), // 8
        21 => Ty::Vector(Box::new(Ty::F64), 2),  // 128
        22 => Ty::Vector(Box::new(Ty::Ptr), 2),  // 2*pointer_bits (recurse via _with)
        23 => Ty::Unit,
        24 => Ty::Never,
        25 => Ty::Struct(StructId(0)),
        26 => Ty::Array(TyId::new(0), 10),
        27 => Ty::Tuple(vec![Ty::I32, Ty::Bool]),
        28 => Ty::Enum(EnumId(0)),
        29 => Ty::Func(FuncTyId(0)),
        30 => Ty::Set(TyId::new(0), SetRepr::Boxed),
        31 => Ty::Sequence(TyId::new(0)),
        32 => Ty::Record(RecordId(0)),
        33 => Ty::Closure(ClosureTyId(0)),
        // Overflow case: a huge vector lane count so `bits.checked_mul(lanes)`
        // overflows u32 -> None.
        34 => Ty::Vector(Box::new(Ty::I128), u32::MAX),
        _ => Ty::Unit,
    }
}

fn main() {
    // Smoke: print a couple so a native run is observable when compiled as a bin.
    println!("{}", bit_width_with_entry(19, 64)); // <4 x i32> = 128
    println!("{}", bit_width_with_entry(11, 32)); // Ptr @ wasm32 = 32
    println!("{}", bit_width_with_entry(17, 64)); // fatptr = 128
}
