// Trust-toolchain slice — the production trust-ir `Ty::is_aggregate`
// (trust-ir/crates/trust-ir/src/ty.rs:356) lowered VERBATIM over the real `Ty`.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (batch 3).
//
// `is_aggregate(self)` classifies a `Ty` as an aggregate / collection type:
// Set, Sequence, Record, Tuple, Array, Struct, or Enum. The trust-ir type
// system uses this to decide which types have no fixed bit width and require
// auxiliary definitions or element-type lookups, so it is a genuine query of
// the IR's own type enum that gates layout/lowering decisions.
//
// It is PURE, deterministic, closure-free, self-contained:
//   * a `matches!` (a single `match`) over the WIDE `Ty` enum (32 variants),
//     reading only the discriminant — true for exactly 7 of the aggregate arms,
//     false for every other arm via the `_` fall-through inside `matches!`. A
//     DIFFERENT true-set from `is_reference`, so the JIT must decode a different
//     subset of the discriminant space.
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O, NO rustc internals.
//
// TRANSCRIBED VERBATIM:
//   * `Ty` enum (ty.rs:55-131) — every variant, in order.
//   * `FatPtrKind` (ty.rs:39-43), `SetRepr` (ty.rs:12-22), and the id newtypes.
//   * `is_aggregate` (ty.rs:356-367) — THE EMIT ROOT, byte-for-byte.

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
    // ── is_aggregate (ty.rs:356-367) — THE EMIT ROOT, VERBATIM. ──
    pub fn is_aggregate(&self) -> bool {
        matches!(
            self,
            Ty::Set(_, _)
                | Ty::Sequence(_)
                | Ty::Record(_)
                | Ty::Tuple(_)
                | Ty::Array(_, _)
                | Ty::Struct(_)
                | Ty::Enum(_)
        )
    }
}

// ── Mono root for standalone re-emit (`--mir-emit-closure is_aggregate_root`). ──
#[no_mangle]
pub fn is_aggregate_root(t: &Ty) -> bool {
    t.is_aggregate()
}

fn main() {
    println!("{}", Ty::Struct(StructId(0)).is_aggregate()); // true
    println!("{}", Ty::Tuple(vec![]).is_aggregate()); // true
    println!("{}", Ty::Enum(EnumId(0)).is_aggregate()); // true
    println!("{}", Ty::I32.is_aggregate()); // false
    println!("{}", Ty::Ref(Box::new(Ty::I32)).is_aggregate()); // false
}
