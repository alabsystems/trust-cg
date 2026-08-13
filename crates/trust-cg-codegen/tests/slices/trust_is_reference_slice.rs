// Trust-toolchain slice — the production trust-ir `Ty::is_reference`
// (trust-ir/crates/trust-ir/src/ty.rs:338) lowered VERBATIM over the real `Ty`.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (batch 3).
//
// `is_reference(self)` classifies a `Ty` as a reference-like type: `&T`, `&mut
// T`, `*const T`, `*mut T`, `Rc<T>`, or a fat pointer. The trust-ir type system
// uses this classification to decide whether a value is pointer-passed / needs
// borrow handling, so it is a genuine soundness-relevant query of the IR's own
// type enum (misclassifying a reference is a calling-convention/codegen bug).
//
// It is PURE, deterministic, closure-free, self-contained:
//   * a `matches!` (a single `match`) over the WIDE `Ty` enum (32 variants),
//     reading only the discriminant — true for exactly 6 of the reference-like
//     arms, false for every other arm via the `_` fall-through inside `matches!`.
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O, NO rustc internals.
//
// TRANSCRIBED VERBATIM:
//   * `Ty` enum (ty.rs:55-131) — every variant, in order (only the discriminant
//     is read; payloads matter only for layout).
//   * `FatPtrKind` (ty.rs:39-43), `SetRepr` (ty.rs:12-22), and the id newtypes
//     (`pub struct $name(pub u32)`) needed to spell `Ty`.
//   * `is_reference` (ty.rs:338-348) — THE EMIT ROOT, byte-for-byte.

#![allow(dead_code)]

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum SetRepr {
    Bitset,
    #[default]
    Boxed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FatPtrKind {
    Slice(TyId),
    Str,
    TraitObject { trait_id: u32 },
}

// ── Ty (ty.rs:55-131) — VERBATIM variant set & order (serde cfg_attr dropped). ──
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    F16,
    F32,
    F64,
    Bool,
    Vector(Box<Ty>, u32),
    Ptr,
    FatPtr(FatPtrKind),
    Unit,
    Never,
    Struct(StructId),
    Array(TyId, u64),
    Tuple(Vec<Ty>),
    Enum(EnumId),
    Func(FuncTyId),
    Ref(Box<Ty>),
    RefMut(Box<Ty>),
    PtrConst(Box<Ty>),
    PtrMut(Box<Ty>),
    Rc(Box<Ty>),
    Set(TyId, SetRepr),
    Sequence(TyId),
    Record(RecordId),
    Closure(ClosureTyId),
}

impl Ty {
    // ── is_reference (ty.rs:338-348) — THE EMIT ROOT, VERBATIM. ──
    pub fn is_reference(&self) -> bool {
        matches!(
            self,
            Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Rc(_)
                | Ty::FatPtr(_)
        )
    }
}

// ── Mono root for standalone re-emit (`--mir-emit-closure is_reference_root`). ──
#[no_mangle]
pub fn is_reference_root(t: &Ty) -> bool {
    t.is_reference()
}

fn main() {
    println!("{}", Ty::Ref(Box::new(Ty::I32)).is_reference()); // true
    println!("{}", Ty::FatPtr(FatPtrKind::Str).is_reference()); // true
    println!("{}", Ty::I32.is_reference()); // false
    println!("{}", Ty::Ptr.is_reference()); // false (thin Ptr is NOT reference here)
}
