// trust-cg-codegen/wasm/lower/abi.rs - trust-ir signatures as wasm function types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! How a trust-ir signature becomes a wasm function type.
//!
//! Every parameter and result is classified into a LANE by its
//! [`Carrier`]:
//!
//! * a scalar is one wasm parameter / result;
//! * a zero-sized value is nothing at all;
//! * a memory-carried value is passed as the `i32` ADDRESS of its bytes and
//!   returned through a hidden leading `sret` pointer the caller supplies.
//!
//! Two calling conventions share that scheme and differ only where the C ABI
//! says so. `CallingConv::C` follows the WebAssembly Basic C ABI
//! (tool-conventions `BasicCABI.md`, what clang and rustc's `extern "C"` emit
//! on wasm32 — checked against an LLVM-compiled reference object):
//!
//! * a struct whose only non-empty member is one scalar (a "singleton") AS
//!   LARGE AS THE STRUCT is passed and returned AS that scalar (clang's
//!   `isSingleElementStruct` requires the sizes to match; rustc gives such a
//!   newtype a `Scalar` representation and passes it `Direct` under both
//!   conventions). A padded singleton — `#[repr(align(8))] struct A(u32)`,
//!   size 8 — is an ordinary aggregate: rustc and clang pass it by address
//!   and return it through `sret`;
//! * a 128-bit integer is passed as two `i64` halves (low, high) and returned
//!   through `sret`;
//! * every other aggregate is passed by address and returned through `sret`.
//!
//! `CallingConv::Rust` is the lane's own convention for bodies it defines:
//! aggregates by address, `sret` returns, 128-bit integers split exactly as for
//! C (rustc's LLVM lowering does the same for `i128`). It is only an ABI between functions this lane compiles; a
//! Rust-convention AGGREGATE crossing a link boundary is refused by the object
//! lowering, because rustc's own Rust ABI for aggregates is not modeled here.
//!
//! Several results — rustc's `PassMode::Pair`, lowered to two return values —
//! are returned the way LLVM's wasm32 ABI returns a multi-value aggregate:
//! through the hidden `sret` buffer, each value at its C-layout offset (the
//! first at 0, each next one at the running size rounded up to its own
//! alignment — rustc's `ScalarPair` rule). A memory-carried result (a 128-bit
//! integer, an aggregate) takes its bytes' place in that buffer by the same
//! rule. Zero-sized results occupy nothing and do not count: a signature with
//! ONE valued result is a single-value return whatever `()`s surround it.
//! Wasm multi-value results are not used: they are not the C ABI, and an
//! LLVM-compiled caller or callee would disagree.
//!
//! **The internal ABI** ([`lower_internal_sig`]) is the one exception, and
//! only for functions an object proves internal to its crate (`lower.rs`,
//! `internal_abi_plan`): a signature whose C form returns through `sret`
//! because it has several valued results or one 128-bit result, every one of
//! them a scalar or a 128-bit integer and at most
//! [`INTERNAL_ABI_MAX_RESULTS`] wasm values in all, returns them as wasm
//! multi-value results instead (a 128-bit integer as its low and high `i64`
//! halves, in that order), with no `sret` parameter. Its parameters are the C
//! form's. Every other signature has no internal form.

use trust_ir::{CallingConv, FuncTy, Module, Ty};

use super::super::encode::{FuncType, ValType};
use super::super::layout::{self, Carrier};
use super::WasmLowerError;

/// How one trust-ir parameter crosses a wasm call.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ParamLane {
    /// One wasm parameter carrying the value.
    Scalar(ValType),
    /// Nothing: a zero-sized value.
    Void,
    /// One `i32` parameter: the address of the value's bytes.
    ByAddr { size: u32 },
    /// C ABI singleton: the struct's one scalar member, at `offset`, passed
    /// directly.
    Singleton { vt: ValType, offset: u32, ty: Ty },
    /// Two `i64` parameters: the low and high halves of a 128-bit integer
    /// that sits at `offset` of the value (0 for a bare `i128`).
    Split128 { offset: u32 },
}

/// How one trust-ir result crosses a wasm return.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum RetLane {
    Scalar(ValType),
    Void,
    /// Written through the hidden leading `sret` pointer.
    Sret {
        size: u32,
    },
    /// C ABI singleton: returned as its one scalar member at `offset`.
    Singleton {
        vt: ValType,
        offset: u32,
        ty: Ty,
    },
    /// Internal ABI only ([`lower_internal_sig`]): a 128-bit integer returned
    /// as two `i64` results, the low half first.
    Wide,
    /// One value of a MULTI-value return, written into the `sret` buffer at
    /// `offset`: a scalar is stored there, a memory-carried value's bytes are
    /// copied there.
    Field {
        offset: u32,
        ty: Ty,
    },
}

/// A lowered signature.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct WasmSig {
    pub params: Vec<ParamLane>,
    pub rets: Vec<RetLane>,
    /// A hidden leading `i32` parameter carries the result address.
    pub sret: bool,
    /// Size and alignment of the `sret` buffer, when there is one.
    pub sret_layout: Option<(u32, u32)>,
    pub wasm: FuncType,
}

impl WasmSig {
    /// The index of the one result written through `sret` straight into the
    /// call result's home slot: the signature's only valued result, when it is
    /// memory-carried (a multi-value return's buffer is a scratch buffer).
    pub fn direct_sret_index(&self) -> Option<usize> {
        let mut valued = self
            .rets
            .iter()
            .enumerate()
            .filter(|(_, r)| !matches!(r, RetLane::Void));
        match (valued.next(), valued.next()) {
            (Some((i, RetLane::Sret { .. })), None) => Some(i),
            _ => None,
        }
    }

    /// True when the signature needs the multi-value extension: only an
    /// internal-ABI signature ([`lower_internal_sig`]) has more than one wasm
    /// result.
    pub fn multivalue(&self) -> bool {
        self.wasm.results.len() > 1
    }
}

/// The one scalar a C-ABI singleton struct reduces to, with its offset.
///
/// A struct/tuple (or one-element array) whose members are all zero-sized
/// except exactly one, recursively, reduces to that member when the member is
/// exactly as large as the whole value (so it sits at offset 0 and there is no
/// padding); a scalar reduces to itself. Anything else (two non-empty
/// members, a padded or over-aligned wrapper, an enum, a fat pointer) is not a
/// singleton.
fn singleton_scalar(module: &Module, ty: &Ty) -> Result<Option<(Ty, u32)>, WasmLowerError> {
    let Some((inner, offset)) = singleton_member(module, ty)? else {
        return Ok(None);
    };
    let (outer_size, _) = layout::size_align(module, ty)?;
    let (inner_size, _) = layout::size_align(module, &inner)?;
    Ok((offset == 0 && inner_size == outer_size).then_some((inner, offset)))
}

/// The one non-empty scalar member of `ty`, with its offset, ignoring size.
fn singleton_member(module: &Module, ty: &Ty) -> Result<Option<(Ty, u32)>, WasmLowerError> {
    if layout::scalar_valtype(ty).is_some() {
        return Ok(Some((ty.clone(), 0)));
    }
    match ty {
        Ty::I128 | Ty::U128 => Ok(Some((ty.clone(), 0))),
        Ty::Struct(_) | Ty::Tuple(_) => {
            let mut found: Option<(Ty, u32)> = None;
            for part in layout::record_fields(module, ty)? {
                if layout::carrier_of(module, &part.ty)? == Carrier::Void {
                    continue;
                }
                if found.is_some() {
                    return Ok(None);
                }
                match singleton_member(module, &part.ty)? {
                    Some((inner, off)) => found = Some((inner, part.offset + off)),
                    None => return Ok(None),
                }
            }
            Ok(found)
        }
        Ty::Array(_, 1) => {
            let (elem, _, _) = layout::array_elem(module, ty)?;
            singleton_member(module, &elem)
        }
        _ => Ok(None),
    }
}

/// A type's carrier is never a pair (`layout::carrier_of`); the ABI is
/// decided by type.
fn no_type_pair(ty: &Ty) -> WasmLowerError {
    WasmLowerError::UnsupportedType(format!("{ty:?} has no type-level pair carrier"))
}

fn param_lane(module: &Module, ty: &Ty, _cc: CallingConv) -> Result<ParamLane, WasmLowerError> {
    match layout::carrier_of(module, ty)? {
        Carrier::Scalar(vt) => Ok(ParamLane::Scalar(vt)),
        Carrier::Void => Ok(ParamLane::Void),
        Carrier::Pair => Err(no_type_pair(ty)),
        Carrier::Mem { size, .. } => {
            if matches!(ty, Ty::I128 | Ty::U128) {
                return Ok(ParamLane::Split128 { offset: 0 });
            }
            if let Some((inner, offset)) = singleton_scalar(module, ty)? {
                if matches!(inner, Ty::I128 | Ty::U128) {
                    return Ok(ParamLane::Split128 { offset });
                }
                let vt = layout::scalar_valtype(&inner).ok_or_else(|| {
                    WasmLowerError::UnsupportedType(format!("singleton member {inner:?}"))
                })?;
                return Ok(ParamLane::Singleton {
                    vt,
                    offset,
                    ty: inner,
                });
            }
            Ok(ParamLane::ByAddr { size })
        }
    }
}

fn ret_lane(module: &Module, ty: &Ty, _cc: CallingConv) -> Result<RetLane, WasmLowerError> {
    match layout::carrier_of(module, ty)? {
        Carrier::Scalar(vt) => Ok(RetLane::Scalar(vt)),
        Carrier::Void => Ok(RetLane::Void),
        Carrier::Pair => Err(no_type_pair(ty)),
        Carrier::Mem { size, .. } => {
            if !matches!(ty, Ty::I128 | Ty::U128)
                && let Some((inner, offset)) = singleton_scalar(module, ty)?
                && let Some(vt) = layout::scalar_valtype(&inner)
            {
                return Ok(RetLane::Singleton {
                    vt,
                    offset,
                    ty: inner,
                });
            }
            Ok(RetLane::Sret { size })
        }
    }
}

/// Whether `ty` reduces to a singleton scalar through STRUCT and TUPLE
/// members only, with no padding: the member is exactly as large as `ty`.
/// rustc gives such a newtype a `Scalar` (or, around a 128-bit integer, an
/// `i128`) representation and passes it directly under its own Rust ABI
/// exactly as the C ABI does. A one-element ARRAY on the path is an `Array`
/// representation that rustc casts to an integer register instead, and a
/// padded or over-aligned wrapper is a `Memory` representation rustc passes
/// by address or casts to an integer depending on its size — neither is what
/// this lane's convention does, so neither counts.
fn is_record_singleton(module: &Module, ty: &Ty) -> Result<bool, WasmLowerError> {
    if !record_singleton_member(module, ty)? {
        return Ok(false);
    }
    Ok(singleton_scalar(module, ty)?.is_some())
}

/// [`is_record_singleton`] without the size check: the path to the one
/// non-empty member runs through structs and tuples only.
fn record_singleton_member(module: &Module, ty: &Ty) -> Result<bool, WasmLowerError> {
    if layout::scalar_valtype(ty).is_some() || matches!(ty, Ty::I128 | Ty::U128) {
        return Ok(true);
    }
    match ty {
        Ty::Struct(_) | Ty::Tuple(_) => {
            let mut found = false;
            for part in layout::record_fields(module, ty)? {
                if layout::carrier_of(module, &part.ty)? == Carrier::Void {
                    continue;
                }
                if found || !record_singleton_member(module, &part.ty)? {
                    return Ok(false);
                }
                found = true;
            }
            Ok(found)
        }
        _ => Ok(false),
    }
}

/// Why a `CallingConv::Rust` signature may not cross a LINK boundary (a
/// declaration, a symbol other objects may call, a function pointer that may
/// escape, an indirect call to a target that may be foreign), or `None` when
/// it may.
///
/// This lane's Rust convention passes every other aggregate by address and
/// returns it through `sret`; rustc's own Rust ABI on wasm32 instead casts a
/// small aggregate to an integer, splits a scalar pair into two parameters,
/// and returns a small aggregate in a register. Only the lanes both agree on
/// cross: scalars, zero-sized values, 128-bit integers (two `i64` halves
/// in, `sret` out) and struct/tuple singletons ([`is_record_singleton`]).
pub(crate) fn rust_link_boundary_refusal(
    module: &Module,
    ft: &FuncTy,
) -> Result<Option<String>, WasmLowerError> {
    for (i, ty) in ft.params.iter().enumerate() {
        if layout::carrier_of(module, ty)?.is_mem() && !is_record_singleton(module, ty)? {
            return Ok(Some(format!("parameter {i} of aggregate type {ty:?}")));
        }
    }
    let valued: Vec<&Ty> = ft
        .returns
        .iter()
        .filter(|t| !matches!(layout::carrier_of(module, t), Ok(Carrier::Void)))
        .collect();
    if valued.len() > 1 {
        return Ok(Some(format!("{} valued results", valued.len())));
    }
    for ty in valued {
        if layout::carrier_of(module, ty)?.is_mem() && !is_record_singleton(module, ty)? {
            return Ok(Some(format!("a result of aggregate type {ty:?}")));
        }
    }
    Ok(None)
}

/// Lower a trust-ir signature under calling convention `cc`.
pub(crate) fn lower_sig(
    module: &Module,
    ft: &FuncTy,
    cc: CallingConv,
) -> Result<WasmSig, WasmLowerError> {
    if !matches!(cc, CallingConv::C | CallingConv::Rust) {
        return Err(WasmLowerError::UnsupportedCallingConv(format!(
            "{cc:?}; the WASM backend lowers CallingConv::C and CallingConv::Rust"
        )));
    }
    if ft.is_vararg {
        // A C variadic call passes its anonymous arguments through a memory
        // buffer (BasicCABI), which is not lowered. A Rust-convention `(...)`
        // is the THIR producer's placeholder for an upstream function it did
        // not lower: its parameters — and therefore its ABI — are unknown.
        return Err(WasmLowerError::UnsupportedAbi(match cc {
            CallingConv::Rust => format!(
                "a Rust-convention signature with unknown parameters `(...)` (a producer \
                 placeholder for a body it did not lower) has no ABI to call it by; {} fixed \
                 parameter(s)",
                ft.params.len()
            ),
            _ => format!(
                "a C variadic signature ({} fixed parameter(s)): anonymous arguments are passed \
                 through a memory buffer that this lane does not lower",
                ft.params.len()
            ),
        }));
    }
    let params = ft
        .params
        .iter()
        .map(|t| param_lane(module, t, cc))
        .collect::<Result<Vec<_>, _>>()?;
    let mut rets = ft
        .returns
        .iter()
        .map(|t| ret_lane(module, t, cc))
        .collect::<Result<Vec<_>, _>>()?;
    let mut sret_layout = None;
    let valued = rets.iter().filter(|r| !matches!(r, RetLane::Void)).count();
    if valued > 1 {
        // Several values: one sret buffer, each value (scalar or bytes) at its
        // C-layout offset.
        let overflow = || WasmLowerError::FrameLayoutOverflow("sret buffer".to_string());
        let mut cursor = 0u32;
        let mut max_align = 1u32;
        for (lane, ty) in rets.iter_mut().zip(&ft.returns) {
            if matches!(lane, RetLane::Void) {
                continue;
            }
            let (size, align) = layout::size_align(module, ty)?;
            cursor = cursor
                .checked_next_multiple_of(align)
                .ok_or_else(overflow)?;
            *lane = RetLane::Field {
                offset: cursor,
                ty: ty.clone(),
            };
            cursor = cursor.checked_add(size).ok_or_else(overflow)?;
            max_align = max_align.max(align);
        }
        let size = cursor
            .checked_next_multiple_of(max_align)
            .ok_or_else(|| WasmLowerError::FrameLayoutOverflow("sret buffer".to_string()))?;
        sret_layout = Some((size, max_align));
    }
    for (lane, ty) in rets.iter().zip(&ft.returns) {
        if let RetLane::Sret { size } = lane {
            let (_, align) = layout::size_align(module, ty)?;
            sret_layout = Some((*size, align));
        }
    }
    let sret = sret_layout.is_some();
    let mut wasm = FuncType::default();
    if sret {
        wasm.params.push(ValType::I32);
    }
    for lane in &params {
        match lane {
            ParamLane::Scalar(vt) | ParamLane::Singleton { vt, .. } => wasm.params.push(*vt),
            ParamLane::Void => {}
            ParamLane::ByAddr { .. } => wasm.params.push(ValType::I32),
            ParamLane::Split128 { .. } => {
                wasm.params.push(ValType::I64);
                wasm.params.push(ValType::I64);
            }
        }
    }
    for lane in &rets {
        match lane {
            RetLane::Scalar(vt) | RetLane::Singleton { vt, .. } => wasm.results.push(*vt),
            // Only the internal form has a `Wide` lane.
            RetLane::Wide => wasm.results.extend([ValType::I64, ValType::I64]),
            RetLane::Void | RetLane::Sret { .. } | RetLane::Field { .. } => {}
        }
    }
    Ok(WasmSig {
        params,
        rets,
        sret,
        sret_layout,
        wasm,
    })
}

/// The most wasm results an internal-ABI signature returns. Four lanes
/// carry a 128-bit integer beside two scalars, or two 128-bit integers.
pub(crate) const INTERNAL_ABI_MAX_RESULTS: usize = 4;

/// The internal-ABI form of `ft` under `cc`, when it has one: the C form
/// ([`lower_sig`]) returns through `sret` and every valued result is a scalar
/// or a 128-bit integer, at most [`INTERNAL_ABI_MAX_RESULTS`] wasm values in
/// all. The parameters are the C form's lanes without the leading `sret`
/// pointer; the results are [`RetLane::Scalar`] (the scalar's own wasm type)
/// and [`RetLane::Wide`] (two `i64`s, low half first) in result order, with
/// zero-sized results still [`RetLane::Void`]. `None` keeps the C form: it is
/// already free of `sret`, or a result is an aggregate.
pub(crate) fn lower_internal_sig(
    module: &Module,
    ft: &FuncTy,
    cc: CallingConv,
) -> Result<Option<WasmSig>, WasmLowerError> {
    let c = lower_sig(module, ft, cc)?;
    if !c.sret {
        return Ok(None);
    }
    let mut rets = Vec::with_capacity(ft.returns.len());
    let mut results = Vec::new();
    for ty in &ft.returns {
        match layout::carrier_of(module, ty)? {
            Carrier::Void => rets.push(RetLane::Void),
            Carrier::Scalar(vt) => {
                rets.push(RetLane::Scalar(vt));
                results.push(vt);
            }
            Carrier::Mem { .. } if matches!(ty, Ty::I128 | Ty::U128) => {
                rets.push(RetLane::Wide);
                results.extend([ValType::I64, ValType::I64]);
            }
            Carrier::Mem { .. } | Carrier::Pair => return Ok(None),
        }
    }
    if results.len() > INTERNAL_ABI_MAX_RESULTS {
        return Ok(None);
    }
    let mut wasm = c.wasm;
    // The C form's leading `i32` is the `sret` pointer (`lower_sig`).
    wasm.params.remove(0);
    wasm.results = results;
    Ok(Some(WasmSig {
        params: c.params,
        rets,
        sret: false,
        sret_layout: None,
        wasm,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sig(returns: Vec<Ty>) -> WasmSig {
        let m = trust_ir::parser::parse_module(
            "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
             struct @P { : i64 @0, : i64 @8 } size=16 align=8 id=0\n\
             struct @W { : i32 @0 } size=4 align=4 id=1\n",
        )
        .expect("parse");
        let ft = FuncTy {
            params: Vec::new(),
            returns,
            abi: None,
            is_vararg: false,
        };
        lower_sig(&m, &ft, CallingConv::Rust).expect("lower_sig")
    }

    /// A multi-value return lays every value, memory-carried ones included,
    /// into one sret buffer at its C-layout offset.
    #[test]
    fn a_multi_value_return_carries_a_memory_value_in_the_sret_buffer() {
        let s = sig(vec![Ty::I128, Ty::Bool]);
        assert_eq!(
            s.rets,
            [
                RetLane::Field {
                    offset: 0,
                    ty: Ty::I128
                },
                RetLane::Field {
                    offset: 16,
                    ty: Ty::Bool
                }
            ]
        );
        assert_eq!(s.sret_layout, Some((32, 16)));
        assert!(s.wasm.results.is_empty());
        assert_eq!(s.direct_sret_index(), None);

        let s = sig(vec![Ty::Struct(trust_ir::StructId::new(1)), Ty::I32]);
        assert_eq!(s.sret_layout, Some((8, 4)));
        assert!(matches!(s.rets[1], RetLane::Field { offset: 4, .. }));
    }

    /// A singleton is passed and returned as its member only when the member
    /// fills the struct; a padded or over-aligned wrapper is an ordinary
    /// aggregate (by address in, `sret` out), as clang and rustc lower it,
    /// and under the Rust convention it may not cross a link boundary.
    #[test]
    fn a_padded_singleton_is_an_ordinary_aggregate() {
        let m = trust_ir::parser::parse_module(
            "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
             struct @W { : u32 @0 } size=4 align=4 id=0\n\
             struct @A8 { : u32 @0 } size=8 align=8 id=1\n\
             struct @H { : u16 @0 } size=4 align=4 id=2\n",
        )
        .expect("parse");
        let lanes = |id: u32| {
            let ty = Ty::Struct(trust_ir::StructId::new(id));
            let ft = FuncTy {
                params: vec![ty.clone()],
                returns: vec![ty],
                abi: None,
                is_vararg: false,
            };
            let s = lower_sig(&m, &ft, CallingConv::C).expect("lower_sig");
            let rust = rust_link_boundary_refusal(&m, &ft).expect("refusal");
            (s.params[0].clone(), s.rets[0].clone(), rust.is_none())
        };
        let (p, r, crosses) = lanes(0);
        assert!(matches!(p, ParamLane::Singleton { offset: 0, .. }), "{p:?}");
        assert!(matches!(r, RetLane::Singleton { offset: 0, .. }), "{r:?}");
        assert!(crosses);
        for id in [1, 2] {
            let (p, r, crosses) = lanes(id);
            assert!(matches!(p, ParamLane::ByAddr { .. }), "{id}: {p:?}");
            assert!(matches!(r, RetLane::Sret { .. }), "{id}: {r:?}");
            assert!(
                !crosses,
                "{id}: a padded Rust singleton crossed the boundary"
            );
        }
    }

    /// The internal form returns scalars and 128-bit halves as wasm results
    /// with no `sret` parameter; a signature with no `sret` in its C form, an
    /// aggregate result, or more than four wasm values has none.
    #[test]
    fn the_internal_form_returns_scalars_and_halves_as_results() {
        let m = trust_ir::parser::parse_module(
            "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
             struct @P { : i64 @0, : i64 @8 } size=16 align=8 id=0\n",
        )
        .expect("parse");
        let internal = |params: Vec<Ty>, returns: Vec<Ty>| {
            let ft = FuncTy {
                params,
                returns,
                abi: None,
                is_vararg: false,
            };
            lower_internal_sig(&m, &ft, CallingConv::C).expect("lower_internal_sig")
        };
        let s = internal(vec![Ty::I128, Ty::I32], vec![Ty::U128]).expect("internal");
        assert_eq!(s.rets, [RetLane::Wide]);
        assert!(!s.sret);
        assert_eq!(
            s.wasm.params,
            [ValType::I64, ValType::I64, ValType::I32],
            "the parameters are the C form's, without the sret pointer"
        );
        assert_eq!(s.wasm.results, [ValType::I64, ValType::I64]);
        assert!(s.multivalue());

        let s = internal(vec![], vec![Ty::I32, Ty::Unit, Ty::I8]).expect("internal");
        assert_eq!(
            s.rets,
            [
                RetLane::Scalar(ValType::I32),
                RetLane::Void,
                RetLane::Scalar(ValType::I32)
            ]
        );
        assert_eq!(s.wasm.results, [ValType::I32, ValType::I32]);

        let s = internal(vec![], vec![Ty::I128, Ty::I128, Ty::I32]);
        assert!(s.is_none(), "five wasm values exceed the budget: {s:?}");
        let s = internal(vec![], vec![Ty::I128, Ty::F64, Ty::Bool]).expect("four values fit");
        assert_eq!(
            s.wasm.results,
            [ValType::I64, ValType::I64, ValType::F64, ValType::I32]
        );
        let s = internal(vec![], vec![Ty::I128, Ty::I128]).expect("internal");
        assert_eq!(s.wasm.results.len(), 4);
        for returns in [
            vec![Ty::I32],
            vec![Ty::Unit, Ty::I64],
            vec![Ty::Struct(trust_ir::StructId::new(0))],
            vec![Ty::Struct(trust_ir::StructId::new(0)), Ty::I32],
        ] {
            let s = internal(vec![], returns.clone());
            assert!(s.is_none(), "{returns:?} has no internal form: {s:?}");
        }
    }

    /// Zero-sized results do not make a return multi-valued: the one
    /// memory-carried result is written straight into the caller's slot.
    #[test]
    fn one_memory_result_beside_zero_sized_ones_is_a_direct_sret() {
        let p = Ty::Struct(trust_ir::StructId::new(0));
        let s = sig(vec![Ty::Unit, p.clone()]);
        assert_eq!(s.direct_sret_index(), Some(1));
        assert_eq!(s.sret_layout, Some((16, 8)));
        let s = sig(vec![p, Ty::Unit]);
        assert_eq!(s.direct_sret_index(), Some(0));
        let s = sig(vec![Ty::Unit, Ty::I128]);
        assert_eq!(s.direct_sret_index(), Some(1));
        let s = sig(vec![Ty::Unit, Ty::I32]);
        assert_eq!(s.direct_sret_index(), None);
        assert_eq!(s.wasm.results, [ValType::I32]);
    }
}
