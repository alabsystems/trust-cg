// Trust-toolchain slice — the production trust-ir
// `Ty::is_integer_vector_mask_for_select_ty` (trust-ir/crates/trust-ir/src/ty.rs:328)
// lowered VERBATIM over the real `Ty` enum.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (batch 4 — the FIRST
// MEATIER, two-operand structural VALIDATOR; the prior 8 are single-enum scalar
// predicates/folds).
//
// `is_integer_vector_mask_for_select_ty(self, select_ty)` is a SOUNDNESS-CRITICAL
// helper of the IR's select-condition validator (`Inst::validate_select_condition_ty`,
// inst.rs:906): it answers "is `self` a *physical* integer mask (e.g. `<4 x i32>`
// of all-ones) being mis-used as a `select` condition for a result type
// `select_ty`?". A TrustIr `select` over `<N x T>` REQUIRES a logical `<N x bool>`
// condition; a same-lane integer vector is a PHYSICAL mask that must first be
// compared-to-zero. Mis-classifying it is a vector-select codegen bug (the wrong
// lanes get selected). This is exactly the structural check the validator consults
// to emit `PhysicalIntegerMaskRequiresCompareToZero`.
//
// Why it is MEATIER than the prior 8 (and still PURE / closure-free / iterator-
// free / self-contained):
//   * it is a TWO-OPERAND query — it reads BOTH `self` and `select_ty`,
//   * each operand is decoded through `Ty::vector_shape`, which returns
//     `Option<(&Ty, u32)>` — an `Option` of a TUPLE carrying a BORROW (`&Ty`) and
//     a `u32` lane count (Box-deref of the `Vector` element via `elem.as_ref()`),
//   * the body then pattern-matches a NESTED 2-TUPLE of those two `Option`s
//     `(Some((..)), Some((..)))`, compares the two lane counts (`==` on u32), AND
//     RECURSES one structural level into the condition element type via
//     `cond_elem.is_integer()` (a Box-reachable discriminant read).
//   * NO closures, NO `.iter()/.map()/.all()/.and_then()`, NO HashMap/Arc/RefCell,
//     NO env/I/O, NO rustc internals.
//
// TRANSCRIBED VERBATIM (faithful, from ty.rs):
//   * `Ty` enum (ty.rs:55-131) — every variant, in order (serde cfg_attr dropped).
//   * `FatPtrKind` (ty.rs:37-43), `SetRepr` (ty.rs:12-22), and the id newtypes
//     (`pub struct $name(pub u32)`) needed to spell `Ty` so rustc lays it out
//     byte-identically to production.
//   * `is_integer`/`is_signed`/`is_unsigned` (ty.rs:199-211) — the recursion leaf.
//   * `vector_shape` (ty.rs:227-232) — the Option<(&Ty,u32)> decoder.
//   * `is_integer_vector_mask_for_select_ty` (ty.rs:328-335) — THE EMIT ROOT.

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
    // ── is_integer / is_signed / is_unsigned (ty.rs:199-211) — VERBATIM. ──
    pub fn is_integer(&self) -> bool {
        self.is_signed() || self.is_unsigned()
    }

    pub fn is_signed(&self) -> bool {
        matches!(self, Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128)
    }

    pub fn is_unsigned(&self) -> bool {
        matches!(self, Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128)
    }

    // ── vector_shape (ty.rs:227-232) — VERBATIM. Returns Option<(&Ty, u32)>. ──
    pub fn vector_shape(&self) -> Option<(&Ty, u32)> {
        match self {
            Ty::Vector(elem, lanes) => Some((elem.as_ref(), *lanes)),
            _ => None,
        }
    }

    // ── is_integer_vector_mask_for_select_ty (ty.rs:328-335) — THE EMIT ROOT,
    //    VERBATIM. ──
    pub fn is_integer_vector_mask_for_select_ty(&self, select_ty: &Ty) -> bool {
        match (self.vector_shape(), select_ty.vector_shape()) {
            (Some((cond_elem, cond_lanes)), Some((_select_elem, select_lanes))) => {
                cond_lanes == select_lanes && cond_elem.is_integer()
            }
            _ => false,
        }
    }
}

// ── Mono root for standalone re-emit (`--mir-emit-closure mask_root`). The
//    verified body is `is_integer_vector_mask_for_select_ty`; this just forwards
//    the two `&Ty` operands so the function instantiates and re-emits. ──
#[no_mangle]
pub fn mask_root(cond_ty: &Ty, select_ty: &Ty) -> bool {
    cond_ty.is_integer_vector_mask_for_select_ty(select_ty)
}

fn main() {
    // Smoke: <4 x i32> is a physical integer mask for a <4 x f32> select. -> true
    let c = Ty::Vector(Box::new(Ty::I32), 4);
    let s = Ty::Vector(Box::new(Ty::F32), 4);
    println!("{}", c.is_integer_vector_mask_for_select_ty(&s)); // true
    // Same lanes but FLOAT condition element -> NOT an integer mask. -> false
    let cf = Ty::Vector(Box::new(Ty::F32), 4);
    println!("{}", cf.is_integer_vector_mask_for_select_ty(&s)); // false
    // Lane mismatch -> false even with integer element.
    let c2 = Ty::Vector(Box::new(Ty::I32), 2);
    println!("{}", c2.is_integer_vector_mask_for_select_ty(&s)); // false (2 != 4)
    // Non-vector condition -> false.
    println!("{}", Ty::I32.is_integer_vector_mask_for_select_ty(&s)); // false
}
