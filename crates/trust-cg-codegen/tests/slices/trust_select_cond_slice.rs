// SELF-CONTAINED trust-ir `Inst::validate_select_condition_ty` slice — the REAL
// per-instruction TYPE-COMPATIBILITY VALIDATOR copied VERBATIM from
// trust-ir/crates/trust-ir/src/inst.rs:906 (validate_select_condition_ty),
// :892 (required_select_condition_ty), and the `Ty` predicates it calls in
// trust-ir/crates/trust-ir/src/ty.rs:318 (select_condition_ty), :328
// (is_integer_vector_mask_for_select_ty), :227 (vector_shape), :199/204/209
// (is_integer/is_signed/is_unsigned), plus the production `Ty` enum (ty.rs:55).
//
// WHY SOUNDNESS-CRITICAL: this validator is the SOURCE of the `mask_select` bug —
// it decides whether a `select`'s condition type is a legal logical TrustIr mask
// (scalar `bool` / `<N x bool>`) or an ILLEGAL physical integer-vector mask that a
// backend would silently mis-treat. Accepting a physical mask as a logical one is
// a direct miscompile. The decision has three outcomes (Ok / PhysicalMask /
// TypeMismatch); the root below maps them to a u8 so the JIT path never heap-clones
// a `Ty` (the real `SelectConditionTypeError` payload would `.clone()` Boxed Tys),
// while the DECISION LOGIC stays VERBATIM.
//
// Faithfulness: the `Ty` enum is the production variant SET + ORDER (so rustc
// niche-encodes the discriminant identically and `<N x bool>` `Box<Ty>` compares
// byte-for-byte). The `==` on `Ty` is the derived `PartialEq` over the 33-variant
// niche-encoded enum incl. the nested `Box<Ty>` recursion — exactly the production
// comparison. A bail here is a REAL frontend gap on REAL Trust validator code.

#![allow(dead_code)]
#![allow(clippy::all)]

// ---- id newtypes (the production `typed_id!` shape: `pub struct N(pub u32)`) ----
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TyId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FuncTyId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnumId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecordId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClosureTyId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SetRepr {
    Bitset,
    #[default]
    Boxed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FatPtrKind {
    Slice(TyId),
    Str,
    TraitObject { trait_id: u32 },
}

// ---- the production `Ty` enum, VERBATIM variant SET + ORDER (ty.rs:55-131) ----
#[derive(Debug, Clone, PartialEq, Eq)]
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
    // VERBATIM ty.rs:153-175 — the SOUNDNESS-CRITICAL physical bit width every
    // load/store/extend in codegen sizes off. Recurses into vector lanes and uses
    // `checked_mul` so an overflowing `<N x i128>` returns None instead of wrapping.
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

    // VERBATIM ty.rs:199-215 — the predicates the mask check consults.
    pub fn is_integer(&self) -> bool {
        self.is_signed() || self.is_unsigned()
    }
    pub fn is_signed(&self) -> bool {
        matches!(self, Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128)
    }
    pub fn is_unsigned(&self) -> bool {
        matches!(self, Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128)
    }

    // VERBATIM ty.rs:227-232.
    pub fn vector_shape(&self) -> Option<(&Ty, u32)> {
        match self {
            Ty::Vector(elem, lanes) => Some((elem.as_ref(), *lanes)),
            _ => None,
        }
    }

    // VERBATIM ty.rs:318-323. Scalar -> Bool; vector -> <N x bool> mask.
    pub fn select_condition_ty(&self) -> Ty {
        match self {
            Ty::Vector(_, lanes) => Ty::Vector(Box::new(Ty::Bool), *lanes),
            _ => Ty::Bool,
        }
    }

    // VERBATIM ty.rs:328-335. A same-lane-count integer vector is a PHYSICAL mask,
    // never a legal logical select condition.
    pub fn is_integer_vector_mask_for_select_ty(&self, select_ty: &Ty) -> bool {
        match (self.vector_shape(), select_ty.vector_shape()) {
            (Some((cond_elem, cond_lanes)), Some((_select_elem, select_lanes))) => {
                cond_lanes == select_lanes && cond_elem.is_integer()
            }
            _ => false,
        }
    }
}

// VERBATIM inst.rs:892-894.
pub fn required_select_condition_ty(value_ty: &Ty) -> Ty {
    value_ty.select_condition_ty()
}

/// The DECISION of the real `Inst::validate_select_condition_ty` (inst.rs:906-930),
/// transcribed VERBATIM but returning the three outcomes as a u8 instead of the
/// heavy `Result<(), SelectConditionTypeError>` (the error payload `.clone()`s Tys
/// — a heap concern orthogonal to the decision). 0 = Ok (cond == required),
/// 1 = PhysicalIntegerMaskRequiresCompareToZero, 2 = TypeMismatch.
pub fn validate_select_condition_ty_code(select_ty: &Ty, cond_ty: &Ty) -> u8 {
    let expected_cond_ty = required_select_condition_ty(select_ty);
    if cond_ty == &expected_cond_ty {
        return 0;
    }
    if cond_ty.is_integer_vector_mask_for_select_ty(select_ty) {
        return 1;
    }
    2
}

// A `#[no_mangle]` mono ROOT that forces validate_select_condition_ty_code (and its
// whole call graph: required_select_condition_ty, select_condition_ty, the derived
// `Ty == Ty`, is_integer_vector_mask_for_select_ty, vector_shape, is_integer/
// is_signed/is_unsigned) to be collected by the stage1 monomorphization collector.
#[no_mangle]
pub extern "C" fn validate_select_condition_ty_root(select_ty: &Ty, cond_ty: &Ty) -> u8 {
    validate_select_condition_ty_code(select_ty, cond_ty)
}

// A `#[no_mangle]` mono ROOT for `Ty::bit_width` (and its recursion). The
// `Option<u32>` is sentinel-encoded to i64 (-1 = None) so the FFI return is trivial
// while `bit_width` itself stays VERBATIM.
#[no_mangle]
pub extern "C" fn bit_width_root(ty: &Ty) -> i64 {
    match ty.bit_width() {
        Some(w) => w as i64,
        None => -1,
    }
}

fn main() {}
