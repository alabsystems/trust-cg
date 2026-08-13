// SELF-CONTAINED trust-ir `Constant::value_matches_ty` slice — the REAL
// constant validator method copied VERBATIM from
// trust-ir/crates/trust-ir/src/shape.rs (value_matches_ty :993, shape_matches_ty
// :958, int_value_fits_ty :1005) + the `Constant` (constant.rs:7) and `Ty`
// (ty.rs:55) enums, made standalone so the stage1 MIR `--mir-emit-closure` path
// can lower the WHOLE call graph rooted at value_matches_ty.
//
// Faithfulness notes (what changed vs the real modules, and why it preserves the
// layout + the lowered call graph):
//   * The id newtypes (`StructId`, `TyId`, ...) -> the SAME `pub struct N(pub u32)`
//     shape the production `typed_id!` macro emits. The `FuncId` payload of
//     `Constant::Closure`/`FnDef` is the same single-`u32` newtype.
//   * `Constant::Float(f64)` keeps the bare `f64` payload (the production serde
//     `with = "float_bits"` attribute is a SERIALIZATION concern that does not
//     change the in-memory layout). All other variants are byte-identical.
//   * The `Ty` enum is the VERBATIM production variant SET and ORDER, so rustc
//     niche-encodes its discriminant identically (the same layout the already-
//     verified int_value_fits_ty round-trip depends on).
//
// Everything else — value_matches_ty's `.iter().all(|elem| ..)` recursion over
// the Vector lanes, the int_value_fits_ty per-width range check, and the
// shape_matches_ty fallback match — is the REAL trust-ir logic, so a bail here is
// a REAL frontend gap on REAL Trust compiler code.

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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FuncId(pub u32);

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
    // VERBATIM ty.rs:199-215 (the predicates value_matches_ty's guard calls).
    pub fn is_integer(&self) -> bool {
        self.is_signed() || self.is_unsigned()
    }
    pub fn is_signed(&self) -> bool {
        matches!(self, Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128)
    }
    pub fn is_unsigned(&self) -> bool {
        matches!(self, Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128)
    }
    pub fn is_float(&self) -> bool {
        matches!(self, Ty::F16 | Ty::F32 | Ty::F64)
    }
}

// ---- the production `Constant` enum, VERBATIM (constant.rs:7-102) -------------
#[derive(Debug, Clone)]
pub enum Constant {
    Int(i128),
    Float(f64),
    Bool(bool),
    Aggregate(Vec<Constant>),
    Array(Vec<Constant>),
    Vector(Vec<Constant>),
    Sequence(Vec<Constant>),
    Set(Vec<Constant>),
    Record(Vec<(String, Constant)>),
    Closure {
        func: FuncId,
        captures: Vec<Constant>,
    },
    FnDef(FuncId),
    SymbolAddr {
        symbol: String,
        addend: i64,
    },
    PhantomData,
}

impl Constant {
    // VERBATIM shape.rs:958-984. The structural shape check value_matches_ty
    // falls through to for every non-Int / non-Vector constant.
    pub fn shape_matches_ty(&self, ty: &Ty) -> bool {
        match (self, ty) {
            (Constant::Int(_), t) if t.is_integer() => true,
            (Constant::Int(_), Ty::Ptr) => true,
            (Constant::Float(_), t) if t.is_float() => true,
            (Constant::Bool(_), Ty::Bool) => true,
            (Constant::Aggregate(_), Ty::Tuple(_))
            | (Constant::Aggregate(_), Ty::Array(_, _))
            | (Constant::Aggregate(_), Ty::Struct(_))
            | (Constant::Aggregate(_), Ty::Record(_)) => true,
            (Constant::Array(_), Ty::Array(_, _)) => true,
            (Constant::Vector(_), Ty::Vector(_, _)) => true,
            (Constant::Sequence(_), Ty::Sequence(_)) => true,
            (Constant::Set(_), Ty::Set(_, _)) => true,
            (Constant::Record(_), Ty::Record(_)) => true,
            (Constant::Closure { .. }, Ty::Closure(_)) => true,
            (Constant::FnDef(_), Ty::Func(_)) => true,
            (Constant::SymbolAddr { .. }, Ty::Ptr) => true,
            (Constant::SymbolAddr { .. }, Ty::Func(_)) => true,
            (Constant::PhantomData, Ty::Unit) => true,
            _ => false,
        }
    }

    // VERBATIM shape.rs:993-1002 — THE TARGET. `.iter().all(|elem| ..)` over the
    // Vector lanes, the recursion into value_matches_ty, the int_value_fits_ty
    // scalar leaf, and the shape_matches_ty fallback.
    pub fn value_matches_ty(&self, ty: &Ty) -> bool {
        match (self, ty) {
            (Constant::Int(value), ty) if ty.is_integer() => int_value_fits_ty(*value, ty),
            (Constant::Vector(elems), Ty::Vector(elem_ty, lanes)) => {
                elems.len() == *lanes as usize
                    && elems.iter().all(|elem| elem.value_matches_ty(elem_ty))
            }
            _ => self.shape_matches_ty(ty),
        }
    }
}

// VERBATIM shape.rs:1005-1019 — the already-verified per-scalar range check.
fn int_value_fits_ty(value: i128, ty: &Ty) -> bool {
    match ty {
        Ty::I8 => value >= i8::MIN as i128 && value <= i8::MAX as i128,
        Ty::I16 => value >= i16::MIN as i128 && value <= i16::MAX as i128,
        Ty::I32 => value >= i32::MIN as i128 && value <= i32::MAX as i128,
        Ty::I64 => value >= i64::MIN as i128 && value <= i64::MAX as i128,
        Ty::I128 => true,
        Ty::U8 => value >= 0 && value <= u8::MAX as i128,
        Ty::U16 => value >= 0 && value <= u16::MAX as i128,
        Ty::U32 => value >= 0 && value <= u32::MAX as i128,
        Ty::U64 => value >= 0 && value <= u64::MAX as i128,
        Ty::U128 => value >= 0,
        _ => false,
    }
}

// A `#[no_mangle]` mono ROOT that forces value_matches_ty (and its whole call
// graph: int_value_fits_ty, shape_matches_ty, the `.iter().all` closure) to be
// collected by the stage1 monomorphization collector.
#[no_mangle]
pub extern "C" fn value_matches_ty_root(c: &Constant, ty: &Ty) -> bool {
    c.value_matches_ty(ty)
}

fn main() {}
