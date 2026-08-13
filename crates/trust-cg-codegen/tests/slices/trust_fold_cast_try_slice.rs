// Trust-toolchain slice — the production trust-ir `fold_cast`
// (trust-ir/crates/trust-ir/src/alloc_bound.rs:270) lowered VERBATIM over the
// real `CastOp` enum and the real `Ty` enum + `Ty::bit_width{,_with}`.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (3rd batch, fn #2).
//
// `fold_cast(op, src_ty, dst_ty, val) -> Option<i128>` is the CAST arm of the
// trust-ir ALLOCATION-BOUNDS const-folder (`alloc_bound.rs`; the const-prop walk
// uses it alongside `fold_binop` to track a count value through casts). It is a
// genuine SOUNDNESS predicate: a WRONG fold of a narrowing `Trunc` would
// under/over-estimate an allocation count and yield an out-of-bounds access — a
// direct memory-safety miscompile. Every arm is conservative: an unknown value
// (`val == None`) or an unmodelled cast returns `None` (no static bound).
//
// It is PURE, deterministic, closure-free, self-contained:
//   * an early-return on `val == None` (the `?`),
//   * a match over `CastOp`: SExt/Bitcast pass through, ZExt guards non-negative,
//     Trunc computes `dst_ty.bit_width_with(64)`, range-checks `bits` (the
//     `0 < bits <= 127` guard — `bits==0` and `bits>127` return None, both real
//     soundness edges), then masks with `(1i128 << bits) - 1` (REAL shift+mask
//     arithmetic over i128), `_ => None`,
//   * the Trunc arm CALLS the (already independently verified) `bit_width_with`
//     combinator, so this slice exercises it composed inside `fold_cast`,
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O, NO rustc internals.
//
// TRANSCRIBED VERBATIM:
//   * `CastOp` enum (inst.rs:105-123) — every variant in order.
//   * `Ty` enum (ty.rs:55-131) + `bit_width`/`bit_width_with` (ty.rs:153/185) —
//     reused from the verified `trust_ty_bitwidth_slice.rs` transcription
//     (needed because `fold_cast`'s Trunc arm calls `dst_ty.bit_width_with`).
//   * `fold_cast` (alloc_bound.rs:270-290) — THE EMIT ROOT, byte-for-byte.
// The only adaptation is dropping the serde cfg_attr derives and the unused
// `_src_ty` is kept (it is part of the verbatim signature; the body ignores it).

#![allow(dead_code)]

// ── id newtypes (value.rs `typed_id!` expansion: `pub struct $name(pub u32)`). ──
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
    Bitset,
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

pub const DEFAULT_POINTER_BITS: u32 = 64;

impl Ty {
    /// (ty.rs:153-175, VERBATIM.)
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

    /// (ty.rs:185-196, VERBATIM.)
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

// ── CastOp (inst.rs:105-123) — VERBATIM variant set & order (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CastOp {
    Trunc,
    ZExt,
    SExt,
    FPTrunc,
    FPExt,
    FPToUI,
    FPToSI,
    UIToFP,
    SIToFP,
    PtrToInt,
    IntToPtr,
    PtrToPtr,
    Bitcast,
    Transmute,
    ReifyFnPointer,
}

// ── fold_cast (alloc_bound.rs:276-290) — THE EMIT ROOT.
//
// The SYMPTOM-2 PROBE FORM (2026-06-29 finding B.2): transcribed 100%
// BYTE-FOR-BYTE from production — the `val?` / `(v >= 0).then_some(v)` /
// `dst_ty.bit_width_with(64)?` sugar is KEPT (the desugared sibling slice,
// `trust_fold_cast_slice.rs`, replaces it). The `?` desugar lowers to calls
// through the `<Option<_> as Try>::branch` / `FromResidual` shims — the exact
// surface on which the 2026-06-29 JIT hung after calling the branch shim once.
fn fold_cast(
    op: CastOp,
    _src_ty: &Ty,
    dst_ty: &Ty,
    val: Option<i128>,
) -> Option<i128> {
    let v = val?;
    match op {
        CastOp::SExt | CastOp::Bitcast => Some(v),
        CastOp::ZExt => (v >= 0).then_some(v),
        CastOp::Trunc => {
            let bits = dst_ty.bit_width_with(64)?;
            if bits == 0 || bits > 127 {
                return None;
            }
            let mask = (1i128 << bits) - 1;
            Some(v & mask)
        }
        _ => None,
    }
}

/// Map a small tag to a `CastOp` (covers every arm of `fold_cast`).
fn cast_op_for_tag(tag: u32) -> CastOp {
    match tag {
        0 => CastOp::Trunc,
        1 => CastOp::ZExt,
        2 => CastOp::SExt,
        3 => CastOp::FPTrunc,
        4 => CastOp::FPExt,
        5 => CastOp::FPToUI,
        6 => CastOp::FPToSI,
        7 => CastOp::UIToFP,
        8 => CastOp::SIToFP,
        9 => CastOp::PtrToInt,
        10 => CastOp::IntToPtr,
        11 => CastOp::PtrToPtr,
        12 => CastOp::Bitcast,
        13 => CastOp::Transmute,
        _ => CastOp::ReifyFnPointer,
    }
}

/// Map a small tag to a representative `dst_ty` for the Trunc arm: the scalar
/// integer widths (so `bit_width_with` yields 8/16/32/64/128 -> the 128 case
/// hits the `bits > 127` guard), a pointer (64), Bool (1), and an aggregate
/// (`bit_width_with` -> None -> the `?` short-circuits Trunc to None).
fn dst_ty_for_tag(tag: u32) -> Ty {
    match tag {
        0 => Ty::I8,
        1 => Ty::I16,
        2 => Ty::I32,
        3 => Ty::I64,
        4 => Ty::I128,
        5 => Ty::U8,
        6 => Ty::U16,
        7 => Ty::U32,
        8 => Ty::U64,
        9 => Ty::U128,
        10 => Ty::Bool,
        11 => Ty::Ptr,
        12 => Ty::Unit,
        // An aggregate whose `bit_width_with` is None — a Struct (not a Tuple, to
        // avoid the `vec![..]` heap alloc that would pull in `__rust_alloc`; the
        // `bit_width`/`bit_width_with` answer is the same `None`).
        _ => Ty::Struct(StructId(0)),
    }
}

/// Plain-old-data view of `Option<i128>` (no niche): `present` flag + the i128
/// value. The entry reads/writes the i128 through this struct so NO i128 is built
/// from two 64-bit halves inside the wrapper (the half-reconstruction `shl`+`or`
/// and the result `>> 64` extraction tripped a trust-cg AArch64 i128 ISel
/// high-half binding bug — see the run notes). The verified `fold_cast` body is
/// unchanged; only the scaffolding ABI moved to pass-i128-by-reference.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct OptI128POD {
    pub present: u64,
    pub value: i128,
}

// ── C-ABI entrypoint. The verified body is `fold_cast`; this wrapper only reads
//    `Option<i128> val` from an `OptI128POD` IN param, selects a `CastOp` from
//    `op_tag` and a `dst_ty` from `dst_tag`, calls the REAL fn, then writes the
//    `Option<i128>` result back into an `OptI128POD` OUT param. The pack/unpack
//    are OUTSIDE the verified body and use NO i128 half-arithmetic.
#[no_mangle]
pub extern "C" fn fold_cast_entry_try(
    op_tag: u32,
    dst_tag: u32,
    val_in: &OptI128POD,
    out: &mut OptI128POD,
) {
    let val: Option<i128> = if val_in.present != 0 {
        Some(val_in.value)
    } else {
        None
    };
    let op = cast_op_for_tag(op_tag);
    let dst = dst_ty_for_tag(dst_tag);
    // `src_ty` is ignored by the verbatim body; a fixed placeholder is fine.
    let src = Ty::I64;
    let r = fold_cast(op, &src, &dst, val);
    match r {
        Some(x) => {
            out.present = 1;
            out.value = x;
        }
        None => {
            out.present = 0;
            out.value = 0;
        }
    }
}

fn main() {
    // Smoke: Trunc to i8 of 0x1FF -> 0xFF.
    let v = OptI128POD { present: 1, value: 0x1FF };
    let mut o = OptI128POD { present: 9, value: 0 };
    fold_cast_entry_try(0, 0, &v, &mut o);
    println!("{} {}", o.present, o.value); // 1 255
}
