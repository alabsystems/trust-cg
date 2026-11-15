// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Tests for the x86-64 source-bound body owner.
//!
//! Fixtures are real: LIR comes from the trust-ir adapter and the machine
//! stream from the real x86-64 instruction selector, driven exactly as the
//! AOT compiler drives it. Negative controls mutate that stream (or select it
//! under another calling convention) and must end as a typed mismatch, a
//! failed row, or an uncredited row, never as Formal credit.
//!
//! Tool-gated tests replay through the identity-admitted AY and an explicit
//! Clean/Carcara checker, and fail, naming what is missing and how to provide
//! it, when either is absent ([`replay_environment`]): a lane that cannot
//! judge never passes.

use super::*;
use crate::ay_bridge::{AYConfig, AYResult, generate_smt2_query_raw};
use crate::function_verifier::{
    FunctionVerificationPreconditionFailure, InstructionVerificationResult, OpcodeInventoryStatus,
};
use crate::lowering_proof::VerificationConfig;
use crate::provenance_xcheck::ProvenanceXCheckMode;
use crate::verify::VerificationStrength;
use crate::{FunctionVerificationRequest, X86FunctionVerifier};
use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest};
use trust_cg_ir::regs::VReg;
use trust_cg_ir::x86_64_regs::X86PReg;
use trust_cg_lower::instructions::{Instruction, IntCC};
use trust_cg_lower::x86_64_isel::{X86CallAbi, X86InstructionSelector};
use trust_ir::{BinOp, CastOp, FieldDef, StructDef, StructId, StructRepr, Ty};
use trust_ir_build::ModuleBuilder;

const SYSV: Option<X86SourceBoundAbi> = Some(X86SourceBoundAbi::SystemV);

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape {
    // ---- slice 1: I64 constants, copies, add, sub over a jump chain
    /// `add(a: u64, b: u64) -> u64` (wrapping).
    Add,
    /// `sub(a: u64, b: u64) -> u64` (wrapping).
    Sub,
    /// `ident(x: u64) -> u64`.
    Ident,
    /// `size_of`-like constant return.
    Const,
    /// `core::hint::black_box::<u64>`: `Copy; Jump; Return`.
    BlackBox,
    // ---- slice 2 (A): pointer carriers
    /// `ptr::cast`: `*mut S -> *mut u8` (`PtrToPtr`; aggregate pointee
    /// metadata on the parameter).
    PtrCast,
    /// `p as usize`: `*const u8 -> usize` (`PtrToInt`).
    PtrToAddr,
    /// `a as *mut u8`: `usize -> *mut u8` (`IntToPtr`).
    AddrToPtr,
    // ---- slice 2 (B): narrow carriers
    U8Ident,
    I16Ident,
    U32Ident,
    BoolIdent,
    /// `is_val_statically_known`-like `-> bool { false }`.
    BoolFalse,
    BoolTrue,
    /// `u8 as u64`.
    ZextU8,
    /// `i8 as i64`.
    SextI8,
    /// `u16 as u32`.
    ZextU16,
    /// `i16 as i64`.
    SextI16,
    /// `u32 as u64`.
    ZextU32,
    /// `i32 as i64`.
    SextI32,
    /// `bool as u64`.
    ZextBool,
    /// `u64 as u8`.
    TruncU8,
    /// `u64 as u32`.
    TruncU32,
    /// `u32 as u16`.
    TruncU16,
    /// `x & 1 != 0`-free truncation to bool (trust-ir `Trunc` to `Bool`).
    TruncBool,
    /// `i8::cast_unsigned`: a same-carrier `Bitcast`.
    I8AsU8,
    /// `a.wrapping_add(b)` on `u8`.
    AddU8,
    /// `a.wrapping_add(b)` on `i32`.
    AddI32,
    /// `a.wrapping_sub(b)` on `i16`.
    SubI16,
    /// `a.wrapping_mul(b)` on `u32`.
    MulU32,
    /// `a & b` on `bool`.
    BoolAnd,
    /// `a ^ b` on `bool`.
    BoolXor,
    // ---- slice 2 (C): arithmetic beyond congruence
    /// `x.wrapping_add(5)`.
    AddImm,
    /// `x.wrapping_sub(5)`.
    SubImm,
    And,
    Or,
    Xor,
    /// `a.wrapping_mul(b)`.
    Mul,
    /// `x << 3`.
    ShlImm,
    /// `x >> 3` (unsigned).
    LshrImm,
    /// `(x as u8) << 3` on the 32-bit carrier.
    ShlU8Imm,
    /// `(x as u8) >> 3` (the selector re-zero-extends the carrier first).
    LshrU8Imm,
    /// `x >> 3` on `i64` (arithmetic).
    AshrImm,
    /// `x >> 3` on `i8` (the selector re-sign-extends the carrier first).
    AshrI8Imm,
    /// `a.wrapping_mul(b)` on `i16`.
    MulI16,
    /// `a.wrapping_add(b << 2)` on `u64` (a scaled LEA computes it too).
    AddShl2,
    // ---- slice 3: direct calls (callees are declared in the same module)
    /// `g1(x)`: a call wrapper.
    CallWrap,
    /// `g2(b, a)`: the arguments in the other order.
    CallSwap,
    /// `g1(x) + x`: a parameter lives across the call in a virtual register.
    CallAfter,
    /// `g1(g1(x))`: the second call consumes the first's result.
    CallChain,
    /// `g1(a) - g1(b)`: the same callee twice, in a fixed order.
    CallSeq,
    /// `hv(x); g1(x)`: a void call, then a returning one.
    CallThenCall,
    /// `fn(x: u64) { hv(x) }`: a void body whose observable is the call.
    CallVoid,
    /// `fn(loc: *const u8) -> ! { sink(loc) }`: a diverging call and a trap.
    CallDiverge,
    /// `fn() -> ! { d2(5, 7) }`: constant arguments to a diverging call.
    CallDivergeConst,
    /// `n(x: u32) -> u8`: a narrow argument and a narrow (AL) result.
    CallNarrow,
    /// `pb(x) -> bool`: a bool result (EAX = 0/1).
    CallBoolResult,
    /// `bg(true) -> u64`: a bool argument (a clean 32-bit bool).
    CallBoolArg,
    /// `h16(a: i16) -> i32`: the adapter widens the i16 argument to i32.
    CallI16,
    /// `g0() -> u64`: a call without arguments.
    CallNoArgs,
    /// `g1(x); x`: the call's result is dead.
    CallDeadResult,
    /// `g6(f, e, d, c, b, a)`: all six System V argument registers.
    CallSix,
    /// `w32(x) as u64`: a u32 result (EAX) widened to the u64 return.
    CallWiden,
    /// `k16(x) as u64`: a u16 result (AX) zero-extended to the u64 return.
    CallU16Widen,
    /// `g1(a) + c`: a parameter received in RDX lives across the call.
    CallAfterThird,
}

pub(crate) const SLICE_ONE: [Shape; 5] = [
    Shape::Add,
    Shape::Sub,
    Shape::Ident,
    Shape::Const,
    Shape::BlackBox,
];

pub(crate) const POINTERS: [Shape; 3] = [Shape::PtrCast, Shape::PtrToAddr, Shape::AddrToPtr];

pub(crate) const NARROW: [Shape; 24] = [
    Shape::U8Ident,
    Shape::I16Ident,
    Shape::U32Ident,
    Shape::BoolIdent,
    Shape::BoolFalse,
    Shape::BoolTrue,
    Shape::ZextU8,
    Shape::SextI8,
    Shape::ZextU16,
    Shape::SextI16,
    Shape::ZextU32,
    Shape::SextI32,
    Shape::ZextBool,
    Shape::TruncU8,
    Shape::TruncU32,
    Shape::TruncU16,
    Shape::TruncBool,
    Shape::I8AsU8,
    Shape::AddU8,
    Shape::AddI32,
    Shape::SubI16,
    Shape::BoolAnd,
    Shape::BoolXor,
    Shape::ShlU8Imm,
];

pub(crate) const ARITHMETIC: [Shape; 13] = [
    Shape::AddImm,
    Shape::SubImm,
    Shape::And,
    Shape::Or,
    Shape::Xor,
    Shape::Mul,
    Shape::ShlImm,
    Shape::LshrImm,
    Shape::LshrU8Imm,
    Shape::AshrImm,
    Shape::AshrI8Imm,
    Shape::MulU32,
    Shape::MulI16,
];

/// Shapes whose lowering the qualification replays in more than one machine
/// form (see [`machine_variants`]).
pub(crate) const VARIANT_SOURCES: [Shape; 1] = [Shape::AddShl2];

pub(crate) const CALLS: [Shape; 19] = [
    Shape::CallWrap,
    Shape::CallSwap,
    Shape::CallAfter,
    Shape::CallChain,
    Shape::CallSeq,
    Shape::CallThenCall,
    Shape::CallVoid,
    Shape::CallDiverge,
    Shape::CallDivergeConst,
    Shape::CallNarrow,
    Shape::CallBoolResult,
    Shape::CallBoolArg,
    Shape::CallI16,
    Shape::CallNoArgs,
    Shape::CallDeadResult,
    Shape::CallSix,
    Shape::CallWiden,
    Shape::CallU16Widen,
    Shape::CallAfterThird,
];

/// Every shape whose real selection the owner admits.
pub(crate) fn all_shapes() -> Vec<Shape> {
    SLICE_ONE
        .iter()
        .chain(&POINTERS)
        .chain(&NARROW)
        .chain(&ARITHMETIC)
        .chain(&VARIANT_SOURCES)
        .chain(&CALLS)
        .copied()
        .collect()
}

impl Shape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::new();
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }

    /// Parameter types and the result type.
    fn signature(self, pointee: &Ty) -> (Vec<Ty>, Ty) {
        use Shape::*;
        let u8p = Ty::PtrMut(Box::new(Ty::U8));
        match self {
            Add | Sub | And | Or | Xor | Mul | AddShl2 => (vec![Ty::U64, Ty::U64], Ty::U64),
            Ident | BlackBox | AddImm | SubImm | ShlImm | LshrImm => (vec![Ty::U64], Ty::U64),
            AshrImm => (vec![Ty::I64], Ty::I64),
            AshrI8Imm => (vec![Ty::I8], Ty::I8),
            MulI16 => (vec![Ty::I16, Ty::I16], Ty::I16),
            Const => (vec![], Ty::U64),
            PtrCast => (vec![Ty::PtrMut(Box::new(pointee.clone()))], u8p),
            PtrToAddr => (vec![Ty::PtrConst(Box::new(Ty::U8))], Ty::Usize),
            AddrToPtr => (vec![Ty::Usize], u8p),
            U8Ident => (vec![Ty::U8], Ty::U8),
            I16Ident => (vec![Ty::I16], Ty::I16),
            U32Ident => (vec![Ty::U32], Ty::U32),
            BoolIdent => (vec![Ty::Bool], Ty::Bool),
            BoolFalse | BoolTrue => (vec![], Ty::Bool),
            ZextU8 => (vec![Ty::U8], Ty::U64),
            SextI8 => (vec![Ty::I8], Ty::I64),
            ZextU16 => (vec![Ty::U16], Ty::U32),
            SextI16 => (vec![Ty::I16], Ty::I64),
            ZextU32 => (vec![Ty::U32], Ty::U64),
            SextI32 => (vec![Ty::I32], Ty::I64),
            ZextBool => (vec![Ty::Bool], Ty::U64),
            TruncU8 => (vec![Ty::U64], Ty::U8),
            TruncU32 => (vec![Ty::U64], Ty::U32),
            TruncU16 => (vec![Ty::U32], Ty::U16),
            TruncBool => (vec![Ty::U64], Ty::Bool),
            I8AsU8 => (vec![Ty::I8], Ty::U8),
            AddU8 => (vec![Ty::U8, Ty::U8], Ty::U8),
            AddI32 => (vec![Ty::I32, Ty::I32], Ty::I32),
            SubI16 => (vec![Ty::I16, Ty::I16], Ty::I16),
            MulU32 => (vec![Ty::U32, Ty::U32], Ty::U32),
            BoolAnd | BoolXor => (vec![Ty::Bool, Ty::Bool], Ty::Bool),
            ShlU8Imm | LshrU8Imm => (vec![Ty::U8], Ty::U8),
            CallWrap | CallSwap | CallAfter | CallChain | CallSeq | CallThenCall | CallVoid
            | CallDiverge | CallDivergeConst | CallNarrow | CallBoolResult | CallBoolArg
            | CallI16 | CallNoArgs | CallDeadResult | CallSix | CallWiden | CallU16Widen
            | CallAfterThird => {
                unreachable!("{self:?} is built by `call_lir`")
            }
        }
    }

    fn is_call(self) -> bool {
        CALLS.contains(&self)
    }
}

/// The LIR the trust-ir adapter produces for a slice-3 shape: the function
/// under test plus declarations of every callee it may name.
fn call_lir(shape: Shape) -> Function {
    use Shape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body");
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let u64s = |n: usize| vec![Ty::U64; n];
    let loc = Ty::PtrConst(Box::new(Ty::U8));
    let g0 = declare("g0", vec![], u64s(1));
    let g1 = declare("g1", u64s(1), u64s(1));
    let g2 = declare("g2", u64s(2), u64s(1));
    let g6 = declare("g6", u64s(6), u64s(1));
    let hv = declare("hv", u64s(1), vec![]);
    let sink = declare("sink", vec![loc.clone()], vec![]);
    let d2 = declare("d2", u64s(2), vec![]);
    let n = declare("n", vec![Ty::U32], vec![Ty::U8]);
    let pb = declare("pb", u64s(1), vec![Ty::Bool]);
    let bg = declare("bg", vec![Ty::Bool], u64s(1));
    let h16 = declare("h16", vec![Ty::I16], vec![Ty::I32]);
    let w32 = declare("w32", vec![Ty::U32], vec![Ty::U32]);
    let k16 = declare("k16", u64s(1), vec![Ty::U16]);
    let (params, result): (Vec<Ty>, Option<Ty>) = match shape {
        CallWrap | CallAfter | CallChain | CallThenCall | CallDeadResult | CallBoolResult => (
            u64s(1),
            Some(if shape == CallBoolResult {
                Ty::Bool
            } else {
                Ty::U64
            }),
        ),
        CallSwap | CallSeq => (u64s(2), Some(Ty::U64)),
        CallVoid => (u64s(1), None),
        CallDiverge => (vec![loc.clone()], None),
        CallDivergeConst => (vec![], None),
        CallNarrow => (vec![Ty::U32], Some(Ty::U8)),
        CallBoolArg | CallNoArgs => (vec![], Some(Ty::U64)),
        CallI16 => (vec![Ty::I16], Some(Ty::I32)),
        CallSix => (u64s(6), Some(Ty::U64)),
        CallWiden => (vec![Ty::U32], Some(Ty::U64)),
        CallU16Widen => (u64s(1), Some(Ty::U64)),
        CallAfterThird => (u64s(3), Some(Ty::U64)),
        other => unreachable!("{other:?} has no calls"),
    };
    let signature = builder.add_func_type(params.clone(), result.iter().cloned().collect());
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    let value = match shape {
        CallWrap => Some(f.call(g1, vec![args[0]])),
        CallSwap => Some(f.call(g2, vec![args[1], args[0]])),
        CallAfter => {
            let y = f.call(g1, vec![args[0]]);
            Some(f.add(Ty::U64, y, args[0]))
        }
        CallChain => {
            let y = f.call(g1, vec![args[0]]);
            Some(f.call(g1, vec![y]))
        }
        CallSeq => {
            let x = f.call(g1, vec![args[0]]);
            let y = f.call(g1, vec![args[1]]);
            Some(f.sub(Ty::U64, x, y))
        }
        CallThenCall => {
            f.call_void(hv, vec![args[0]]);
            Some(f.call(g1, vec![args[0]]))
        }
        CallVoid => {
            f.call_void(hv, vec![args[0]]);
            None
        }
        CallDiverge => {
            f.call_void(sink, vec![args[0]]);
            f.unreachable();
            f.build();
            return translated(builder, shape);
        }
        CallDivergeConst => {
            let five = f.iconst(Ty::U64, 5);
            let seven = f.iconst(Ty::U64, 7);
            f.call_void(d2, vec![five, seven]);
            f.unreachable();
            f.build();
            return translated(builder, shape);
        }
        CallNarrow => Some(f.call(n, vec![args[0]])),
        CallBoolResult => Some(f.call(pb, vec![args[0]])),
        CallBoolArg => {
            let yes = f.bool_const(true);
            Some(f.call(bg, vec![yes]))
        }
        CallI16 => Some(f.call(h16, vec![args[0]])),
        CallNoArgs => Some(f.call(g0, vec![])),
        CallDeadResult => {
            let _ = f.call(g1, vec![args[0]]);
            Some(args[0])
        }
        CallSix => Some(f.call(
            g6,
            vec![args[5], args[4], args[3], args[2], args[1], args[0]],
        )),
        CallWiden => {
            let narrow = f.call(w32, vec![args[0]]);
            Some(f.zext(Ty::U32, Ty::U64, narrow))
        }
        CallU16Widen => {
            let narrow = f.call(k16, vec![args[0]]);
            Some(f.zext(Ty::U16, Ty::U64, narrow))
        }
        CallAfterThird => {
            let y = f.call(g1, vec![args[0]]);
            Some(f.add(Ty::U64, y, args[2]))
        }
        other => unreachable!("{other:?} has no calls"),
    };
    f.ret(value.into_iter().collect());
    f.build();
    translated(builder, shape)
}

/// The LIR of `shape`'s function in the translated module.
fn translated(builder: ModuleBuilder, shape: Shape) -> Function {
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == shape.name())
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

/// The LIR the trust-ir adapter produces for `shape`.
pub(crate) fn lir(shape: Shape) -> Function {
    use Shape::*;
    if shape.is_call() {
        return call_lir(shape);
    }
    let mut builder = ModuleBuilder::new("x86_source_bound_body");
    let pointee = Ty::Struct(builder.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "first".into(),
                ty: Ty::U64,
                offset: None,
            },
            FieldDef {
                name: "second".into(),
                ty: Ty::U64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    }));
    let (params, result) = shape.signature(&pointee);
    let signature = builder.add_func_type(params.clone(), vec![result.clone()]);
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    let binary = |f: &mut trust_ir_build::FunctionBuilder<'_>, op: BinOp, ty: Ty| {
        f.binop(op, ty, args[0], args[1])
    };
    let value = match shape {
        Add => f.add(Ty::U64, args[0], args[1]),
        Sub => f.sub(Ty::U64, args[0], args[1]),
        Ident | U8Ident | I16Ident | U32Ident | BoolIdent => args[0],
        Const => f.iconst(Ty::U64, 4),
        BlackBox => {
            let tail = f.create_block();
            let copied = f.copy(Ty::U64, args[0]);
            f.br(tail, vec![]);
            f.switch_to_block(tail);
            copied
        }
        PtrCast => f.cast(CastOp::PtrToPtr, params[0].clone(), result.clone(), args[0]),
        PtrToAddr => f.cast(CastOp::PtrToInt, params[0].clone(), Ty::Usize, args[0]),
        AddrToPtr => f.cast(CastOp::IntToPtr, Ty::Usize, result.clone(), args[0]),
        BoolFalse => f.bool_const(false),
        BoolTrue => f.bool_const(true),
        ZextU8 | ZextU16 | ZextU32 | ZextBool => f.zext(params[0].clone(), result.clone(), args[0]),
        SextI8 | SextI16 | SextI32 => f.sext(params[0].clone(), result.clone(), args[0]),
        TruncU8 | TruncU32 | TruncU16 | TruncBool => {
            f.trunc(params[0].clone(), result.clone(), args[0])
        }
        I8AsU8 => f.cast(CastOp::Bitcast, Ty::I8, Ty::U8, args[0]),
        AddU8 => binary(&mut f, BinOp::Add, Ty::U8),
        AddI32 => binary(&mut f, BinOp::Add, Ty::I32),
        SubI16 => binary(&mut f, BinOp::Sub, Ty::I16),
        MulU32 => binary(&mut f, BinOp::Mul, Ty::U32),
        MulI16 => binary(&mut f, BinOp::Mul, Ty::I16),
        BoolAnd => binary(&mut f, BinOp::And, Ty::Bool),
        BoolXor => binary(&mut f, BinOp::Xor, Ty::Bool),
        AddImm | SubImm => {
            let five = f.iconst(Ty::U64, 5);
            let op = if shape == AddImm {
                BinOp::Add
            } else {
                BinOp::Sub
            };
            f.binop(op, Ty::U64, args[0], five)
        }
        And => binary(&mut f, BinOp::And, Ty::U64),
        Or => binary(&mut f, BinOp::Or, Ty::U64),
        Xor => binary(&mut f, BinOp::Xor, Ty::U64),
        Mul => binary(&mut f, BinOp::Mul, Ty::U64),
        ShlImm | LshrImm => {
            let three = f.iconst(Ty::U64, 3);
            let op = if shape == ShlImm {
                BinOp::Shl
            } else {
                BinOp::LShr
            };
            f.binop(op, Ty::U64, args[0], three)
        }
        ShlU8Imm | LshrU8Imm => {
            let three = f.iconst(Ty::U8, 3);
            let op = if shape == ShlU8Imm {
                BinOp::Shl
            } else {
                BinOp::LShr
            };
            f.binop(op, Ty::U8, args[0], three)
        }
        AshrImm => {
            let three = f.iconst(Ty::I64, 3);
            f.binop(BinOp::AShr, Ty::I64, args[0], three)
        }
        AshrI8Imm => {
            let three = f.iconst(Ty::I8, 3);
            f.binop(BinOp::AShr, Ty::I8, args[0], three)
        }
        AddShl2 => {
            let two = f.iconst(Ty::U64, 2);
            let scaled = f.binop(BinOp::Shl, Ty::U64, args[1], two);
            f.add(Ty::U64, args[0], scaled)
        }
        other => unreachable!("{other:?} is built by `call_lir`"),
    };
    f.ret(vec![value]);
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let mut lir = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"));
    assert_eq!(lir.len(), 1);
    lir.remove(0).0
}

thread_local! {
    /// Whether [`select`] keeps the constant-amount `I128` shift fold on (the
    /// default, as the compiler selects): [`with_i128_const_shift_fold`].
    static I128_CONST_SHIFT_FOLD: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
}

/// `f` with [`select`]'s constant-amount `I128` shift fold (ruling OD-215)
/// `enabled`. Off is the selector before the fold, every constant amount on
/// the general CL/CMOV path: the historical custody of the goldens the fold
/// moved renders them so. Tests only.
pub(crate) fn with_i128_const_shift_fold<T>(enabled: bool, f: impl FnOnce() -> T) -> T {
    let before = I128_CONST_SHIFT_FOLD.with(|cell| cell.replace(enabled));
    let result = f();
    I128_CONST_SHIFT_FOLD.with(|cell| cell.set(before));
    result
}

/// Pre-RA x86-64 ISel for `source`, selected exactly as the AOT compiler
/// selects it (`Compiler::compile_x86_64`), under `abi` (the constant-amount
/// `I128` shift fold off only inside [`with_i128_const_shift_fold`]).
pub(crate) fn select(source: &Function, abi: X86CallAbi) -> X86ISelFunction {
    let signature = trust_cg_lower::function::Signature {
        params: source.signature.params.clone(),
        returns: source.signature.returns.clone(),
    };
    let mut isel = X86InstructionSelector::with_abi(source.name.clone(), signature.clone(), abi);
    if !I128_CONST_SHIFT_FOLD.with(std::cell::Cell::get) {
        isel.set_i128_const_shift_fold(false);
    }
    isel.set_stack_slots(source.stack_slots.clone());
    isel.seed_value_types(&source.value_types);
    isel.seed_function_value_use_counts(source);
    isel.seed_pure_callees(&source.pure_callees);
    isel.seed_sret_param(source.abi_sret_param)
        .expect("sret parameter");
    isel.seed_sret_arg_callees(&source.sret_arg_callees);
    isel.seed_sret_arg_indirect_callees(&source.sret_arg_indirect_callees);
    let order = source.layout_order();
    isel.seed_iconst_origins(
        order
            .iter()
            .map(|block| source.blocks[block].instructions.as_slice()),
    );
    for block in &order {
        isel.ensure_block(*block);
    }
    isel.lower_formal_arguments(&signature, source.entry_block)
        .expect("formal arguments");
    for block in &order {
        let body = &source.blocks[block];
        if *block != source.entry_block && !body.params.is_empty() {
            isel.define_block_params(&body.params);
        }
        isel.select_block(*block, &body.instructions)
            .expect("selection");
    }
    isel.finalize_with_eh_info(&source.eh_info)
        .expect("finalize")
}

pub(crate) fn pair(shape: Shape) -> (Function, X86ISelFunction) {
    let source = lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// Walk-ordered rows: `(ordinal, block, index)`.
fn rows(machine: &X86ISelFunction) -> Vec<(usize, Block, usize)> {
    let mut rows = Vec::new();
    for block in &machine.block_order {
        for index in 0..machine.blocks[block].insts.len() {
            rows.push((rows.len(), *block, index));
        }
    }
    rows
}

fn inst_mut(machine: &mut X86ISelFunction, ordinal: usize) -> &mut X86ISelInst {
    let (_, block, index) = rows(machine)[ordinal];
    &mut machine.blocks.get_mut(&block).unwrap().insts[index]
}

fn inst(machine: &X86ISelFunction, ordinal: usize) -> &X86ISelInst {
    let (_, block, index) = rows(machine)[ordinal];
    &machine.blocks[&block].insts[index]
}

fn find(machine: &X86ISelFunction, opcode: X86Opcode) -> Vec<usize> {
    rows(machine)
        .into_iter()
        .filter(|(_, block, index)| machine.blocks[block].insts[*index].opcode == opcode)
        .map(|(ordinal, _, _)| ordinal)
        .collect()
}

fn opcodes(machine: &X86ISelFunction) -> Vec<X86Opcode> {
    rows(machine)
        .iter()
        .map(|(_, block, index)| machine.blocks[block].insts[*index].opcode)
        .collect()
}

fn preg(encoding: u16) -> O {
    O::PReg(X86PReg::new(encoding))
}

fn vreg(id: u32) -> O {
    O::VReg(VReg::new(id, RegClass::Gpr64))
}

fn replay_config() -> AYConfig {
    AYConfig {
        solver: None,
        timeout_ms: 30_000,
        produce_models: true,
    }
}

/// Evaluate the theorem at one concrete entry assignment by computing every
/// definition in order (the premises are definitional, so this is the unique
/// satisfying assignment), then compare the two observables. Test-only
/// semantics check; it is never credit.
fn sides_agree_at(obligation: &ProofObligation, seed: u64) -> bool {
    sides_agree_with(obligation, seed, &[])
}

/// [`sides_agree_at`] with each free input named in `fixed` set to its given
/// value instead of the sample's.
fn sides_agree_with(obligation: &ProofObligation, seed: u64, fixed: &[(&str, u64)]) -> bool {
    use crate::smt::{EvalEnv, EvalResult};
    let mut env = EvalEnv::default();
    let mut state = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    for (name, width) in free_inputs_of(obligation) {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        // Alternate dense random words with sparse ones so narrow values
        // meet both clean and dirty upper bits.
        let sampled = if seed.is_multiple_of(3) {
            state & 0xff
        } else {
            state
        };
        let value = fixed
            .iter()
            .find(|(fixed, _)| *fixed == name)
            .map_or(sampled, |(_, value)| *value);
        env.insert(name, crate::smt::mask(value, width));
    }
    for premise in obligation.preconditions.iter().rev() {
        let E::Eq { lhs, rhs } = premise else {
            panic!("premise {premise} is not an equation")
        };
        let E::Var { name, .. } = lhs.as_ref() else {
            panic!("premise {premise} defines no name")
        };
        let EvalResult::Bv(value) = rhs.eval(&env) else {
            panic!("definition of {name} is not a bitvector")
        };
        env.insert(name.clone(), value);
    }
    // Compare item by item (the evaluator holds at most 64 bits, and a
    // several-item observable is a conjunction of per-item equations).
    observable_items(obligation)
        .iter()
        .all(|(source, machine)| source.eval(&env) == machine.eval(&env))
}

/// The observed items as `(source, machine)` pairs: the one equation of a
/// single-item theorem, or each equation of the conjunction a several-item
/// theorem states against `true`.
fn observable_items(obligation: &ProofObligation) -> Vec<(E, E)> {
    if obligation.trust_ir_expr != E::bool_const(true) {
        return vec![(
            obligation.trust_ir_expr.clone(),
            obligation.aarch64_expr.clone(),
        )];
    }
    let mut items = Vec::new();
    let mut conjunction = &obligation.aarch64_expr;
    loop {
        let (equation, rest) = match conjunction {
            E::And { lhs, rhs } => (lhs.as_ref(), Some(rhs.as_ref())),
            last => (last, None),
        };
        let E::Eq { lhs, rhs } = equation else {
            panic!("observed item {equation} is not an equation")
        };
        items.push((lhs.as_ref().clone(), rhs.as_ref().clone()));
        match rest {
            Some(rest) => conjunction = rest,
            None => return items,
        }
    }
}

fn holds_on_samples(obligation: &ProofObligation) -> bool {
    (0..96).all(|seed| sides_agree_at(obligation, seed))
}

fn refuted_on_samples(obligation: &ProofObligation) -> bool {
    (0..96).any(|seed| !sides_agree_at(obligation, seed))
}

fn takes_and_returns_bool(source: &Function) -> bool {
    source.signature.returns == [Type::B1] && source.signature.params.contains(&Type::B1)
}

/// Whether `name` is a call's free input: `r{k}` or `g{k}` (RAX), `q{k}` or
/// `h{k}` (RDX, slice 5).
fn is_call_input(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some('r' | 'g' | 'q' | 'h'))
        && !chars.as_str().is_empty()
        && chars.all(|c| c.is_ascii_digit())
}

/// Whether `name` is a symbol's address: the slice-5 free input `sym{j}`.
fn is_symbol_input(name: &str) -> bool {
    name.strip_prefix("sym")
        .is_some_and(|j| !j.is_empty() && j.chars().all(|c| c.is_ascii_digit()))
}

/// Whether `name` is a slice-4 free input: a paired load's value `l{j}` or
/// an undefined machine value `u{k}` / `w{k}`; or a private stack byte's
/// initial value `f{k}` (slice 6).
fn is_memory_input(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some('l' | 'u' | 'w' | 'f'))
        && !chars.as_str().is_empty()
        && chars.all(|c| c.is_ascii_digit())
}

/// Every free input the obligation declares (entry registers, each call's
/// result and undefined result bits, each paired load's value, each symbol's
/// address, each undefined machine value, slice 7, each call-defined byte of
/// an escaped slot and, slice 13, each slot address stored as data and each
/// incoming stack eightbyte, an `e_` entry, and, slice 15, each byte a store
/// through a derived address left, and, slice 21, each FP leaf), with its
/// width. A name a premise defines is none (OD-233: a defined cut input is
/// set by its definition).
fn free_inputs_of(obligation: &ProofObligation) -> Vec<(String, u32)> {
    let defined: HashSet<&str> = obligation
        .preconditions
        .iter()
        .filter_map(|premise| match premise {
            E::Eq { lhs, .. } => match lhs.as_ref() {
                E::Var { name, .. } => Some(name.as_str()),
                _ => None,
            },
            _ => None,
        })
        .collect();
    obligation
        .inputs
        .iter()
        .filter(|(name, _)| !defined.contains(name.as_str()))
        .filter(|(name, _)| {
            name.starts_with("e_")
                || is_float_leaf_name(name)
                // Slice 23 (OD-206): an arithmetic leaf of a generalization,
                // or (sampled as two 64-bit words) one of a 128-bit leaf's
                // halves.
                || normal::is_arith_leaf_name(name)
                || name
                    .strip_suffix("_hi")
                    .or_else(|| name.strip_suffix("_lo"))
                    .is_some_and(normal::is_arith_leaf_name)
                || is_call_input(name)
                || is_memory_input(name)
                || is_symbol_input(name)
                || parse_call_byte_name(name).is_some()
                || is_header_input(name)
                || parse_access_byte_name(name).is_some()
                || parse_slot_address_name(name).is_some()
        })
        .cloned()
        .collect()
}

/// The theorem of a pair in the plain spelling (no value numbering: the
/// claims as built), for the controls that inspect how the claims and the
/// definitions are constructed; slice 18's canonical spelling only re-spells
/// them, exactly (`slice18::canonical_spelling_preserves_every_fixture_theorem`).
pub(crate) fn plain_theorem(source: &Function, machine: &X86ISelFunction) -> ProofObligation {
    theorem_with_path_encoding(
        source,
        machine,
        SYSV,
        PathEncoding {
            value_number: ValueNumbering::Off,
            ..PathEncoding::CANONICAL
        },
    )
    .unwrap_or_else(|refusal| panic!("the plain spelling: {refusal}"))
}

/// The plain spelling ([`plain_theorem`]) of a pair the owner binds (it
/// panics, naming `what`, when the owner refuses the pair).
pub(crate) fn owned_plain_theorem(
    source: &Function,
    machine: &X86ISelFunction,
    what: &str,
) -> ProofObligation {
    source_bound_x86_body(source, machine, SYSV)
        .unwrap_or_else(|refusal| panic!("{what}: {refusal}"));
    plain_theorem(source, machine)
}

/// The structural check the owner applied to the theorem it states for a
/// single-query pair, re-run: a value-numbered theorem (slice 18) is checked
/// as a part is, one claim sufficing ([`check_definitional_part`]); every
/// other with two claims at least ([`check_definitional`]).
pub(crate) fn owner_check(
    source: &Function,
    machine: &X86ISelFunction,
    obligation: &ProofObligation,
    entries: &[(String, u32)],
) -> Result<(), String> {
    match single_theorem_with_encoding(source, machine, SYSV, PathEncoding::CANONICAL, false) {
        Some(Ok((_, _, spelling))) if spelling != Spelling::Plain => {
            check_definitional_part(obligation, entries)
        }
        _ => check_definitional(obligation, entries),
    }
}

/// Whether `name` is a loop header's free input (slice 12): a parameter's
/// value `x{H}v{i}`, the free bits of its register `x{H}t{i}` (psABI walk)
/// or `x{H}c{i}` (clean-bool walk), or a header byte `x{H}b{slot}o{offset}`.
pub(crate) fn is_header_input(name: &str) -> bool {
    name.strip_prefix('x').is_some_and(|rest| {
        let digits = rest.chars().take_while(char::is_ascii_digit).count();
        digits > 0 && matches!(rest[digits..].chars().next(), Some('v' | 't' | 'c' | 'b'))
    })
}

#[track_caller]
fn expect_mismatch(
    source: &Function,
    machine: &X86ISelFunction,
    what: &str,
    predicate: impl Fn(&X86BodyMismatch) -> bool,
) {
    match source_bound_x86_body(source, machine, SYSV) {
        Err(X86BodyRefusal::Mismatch(mismatch)) => {
            assert!(
                predicate(&mismatch),
                "{what}: unexpected mismatch {mismatch}"
            )
        }
        Err(other) => panic!("{what}: expected a typed mismatch, got {other}"),
        Ok(_) => panic!("{what}: a wrong lowering built a body theorem"),
    }
}

#[track_caller]
fn expect_unsupported(source: &Function, machine: &X86ISelFunction, what: &str) {
    match source_bound_x86_body(source, machine, SYSV) {
        Err(X86BodyRefusal::Unsupported(_)) => {}
        Err(other) => panic!("{what}: expected Unsupported, got {other}"),
        Ok(_) => panic!("{what}: an out-of-domain pair built a body theorem"),
    }
}

/// A wrong lowering that the owner still binds (the Rust affine check cannot
/// judge it): the replayed query itself must be refutable.
#[track_caller]
fn assert_theorem_refutes(source: &Function, machine: &X86ISelFunction, what: &str) {
    let owner = source_bound_x86_body(source, machine, SYSV)
        .unwrap_or_else(|refusal| panic!("{what}: {refusal}"));
    assert!(
        refuted_on_samples(owner.obligation()),
        "{what}: the replayed query must refute the wrong lowering"
    );
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

#[test]
fn verify_owned_register_table_agrees_with_the_ir_register_encodings() {
    use trust_cg_ir::x86_64_regs as regs;
    let named = [
        (RAX, regs::RAX, regs::EAX),
        (RCX, regs::RCX, regs::ECX),
        (RDX, regs::RDX, regs::EDX),
        (RBX, regs::RBX, regs::EBX),
        (RSP, regs::RSP, regs::ESP),
        (RBP, regs::RBP, regs::EBP),
        (RSI, regs::RSI, regs::ESI),
        (RDI, regs::RDI, regs::EDI),
        (R8, regs::R8, regs::R8D),
        (R9, regs::R9, regs::R9D),
        (R12, regs::R12, regs::R12D),
        (R13, regs::R13, regs::R13D),
        (R14, regs::R14, regs::R14D),
        (R15, regs::R15, regs::R15D),
    ];
    for (root, reg, alias) in named {
        assert_eq!(root, reg.encoding(), "{}", ROOT_NAMES[root as usize]);
        assert!(reg.is_gpr64());
        // The 32-bit alias names the same root.
        assert!(alias.is_gpr32());
        assert_eq!(alias.encoding() - GPR32_ALIAS_BASE, root);
        assert_eq!(
            gpr(&O::PReg(alias)),
            Some(Reg {
                root: Root::Physical(root),
                bits: 32
            })
        );
        assert_eq!(
            regs::x86_gpr64_to_gpr32(reg),
            Some(alias),
            "{}",
            ROOT_NAMES[root as usize]
        );
    }
    // 8- and 16-bit aliases merge into their register: never admitted.
    assert_eq!(gpr(&O::PReg(regs::AL)), None);
    assert_eq!(gpr(&O::PReg(regs::AX)), None);
    // Same System V order as the selector's table, owned separately here.
    assert_eq!(
        SYSV_ARGUMENT_ROOTS.map(X86PReg::new),
        trust_cg_ir::x86_64_regs::X86_ARG_GPRS
    );
}

#[test]
fn fixtures_have_the_expected_lir_and_pre_ra_shapes() {
    use X86Opcode::*;
    let (source, machine) = pair(Shape::BlackBox);
    let order = source.layout_order();
    assert_eq!(order.len(), 2, "black_box is a two-block chain");
    let lir_opcodes: Vec<_> = order
        .iter()
        .flat_map(|block| source.blocks[block].instructions.iter())
        .map(|inst| std::mem::discriminant(&inst.opcode))
        .collect();
    assert_eq!(
        lir_opcodes,
        vec![
            std::mem::discriminant(&L::Copy),
            std::mem::discriminant(&L::Jump { dest: Block(0) }),
            std::mem::discriminant(&L::Return),
        ]
    );
    assert_eq!(opcodes(&machine), vec![MovRR, MovRR, Jmp, MovRR, Ret]);
    assert_eq!(
        opcodes(&pair(Shape::Add).1),
        vec![MovRR, MovRR, AddRR, MovRR, Ret]
    );

    // (A) A pointer cast is a LIR `Copy` of the I64 carrier; the aggregate
    // pointee rides as sidecar metadata; the selector emits three 64-bit moves.
    let (cast, cast_machine) = pair(Shape::PtrCast);
    assert_eq!(cast.signature.params, vec![Type::I64]);
    assert_eq!(cast.signature.returns, vec![Type::I64]);
    assert_eq!(cast.param_pointee_types.len(), 1);
    assert!(
        cast.blocks[&cast.entry_block]
            .instructions
            .iter()
            .any(|inst| inst.opcode == L::Copy)
    );
    assert_eq!(opcodes(&cast_machine), vec![MovRR, MovRR, MovRR, Ret]);

    // (B) Narrow values ride 32-bit carriers: formal and return moves are
    // MovRR32 through the 32-bit aliases.
    // The adapter returns a u8 through an I32 carrier (`Uextend`), which the
    // selector re-zero-extends from the low byte.
    let (u8_source, u8_ident) = pair(Shape::U8Ident);
    assert!(
        u8_source.blocks[&u8_source.entry_block]
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, L::Uextend { .. }))
    );
    assert_eq!(opcodes(&u8_ident), vec![MovRR32, Movzx, MovRR32, Ret]);
    assert_eq!(
        inst(&u8_ident, 0).operands[1],
        O::PReg(trust_cg_ir::x86_64_regs::EDI)
    );
    assert_eq!(
        inst(&u8_ident, 2).operands[0],
        O::PReg(trust_cg_ir::x86_64_regs::EAX)
    );
    assert_eq!(
        opcodes(&pair(Shape::ZextU8).1),
        vec![MovRR32, Movzx, MovRR, Ret]
    );
    assert_eq!(
        opcodes(&pair(Shape::SextI8).1),
        vec![MovRR32, MovsxB, MovRR, Ret]
    );
    assert_eq!(
        opcodes(&pair(Shape::ZextU32).1),
        vec![MovRR32, MovRR32, MovRR, Ret]
    );
    assert_eq!(
        opcodes(&pair(Shape::SextI32).1),
        vec![MovRR32, Movsx, MovRR, Ret]
    );
    // Slice 15: a `bool` parameter is the `movzx` of its register's low byte,
    // after which the zero extension of `b as u64` is a 32-bit copy.
    assert_eq!(
        opcodes(&pair(Shape::ZextBool).1),
        vec![Movzx, MovRR32, MovRR, Ret]
    );
    assert_eq!(
        opcodes(&pair(Shape::TruncBool).1),
        vec![MovRR, Movzx, AndRI, MovRR32, Ret]
    );
    assert_eq!(
        opcodes(&pair(Shape::BoolFalse).1),
        vec![MovRI, MovRR32, Ret]
    );
    // `i8 as u8` is a same-carrier LIR `Bitcast`: the identity on the bits.
    let (as_unsigned, _) = pair(Shape::I8AsU8);
    assert!(
        as_unsigned.blocks[&as_unsigned.entry_block]
            .instructions
            .iter()
            .any(|inst| inst.opcode == L::Bitcast { to_ty: Type::I8 })
    );
    assert_eq!(
        opcodes(&pair(Shape::LshrU8Imm).1),
        vec![MovRR32, MovRI, Movzx, ShrRI, Movzx, MovRR32, Ret]
    );
}

#[test]
fn owner_builds_for_every_admitted_shape_and_covers_every_value_row() {
    for shape in all_shapes() {
        let (source, machine) = pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}\n{machine:#?}"));
        let expected: Vec<usize> = rows(&machine)
            .into_iter()
            .filter(|(_, block, index)| {
                let opcode = machine.blocks[block].insts[*index].opcode;
                !opcode.is_pseudo()
                    && !matches!(
                        opcode,
                        X86Opcode::Jmp | X86Opcode::Ret | X86Opcode::Call | X86Opcode::Ud2
                    )
            })
            .map(|(ordinal, _, _)| ordinal)
            .collect();
        assert_eq!(owner.bound_rows(), expected, "{shape:?}");
        // Every call is paired, in order, with the machine CALL row of the
        // same callee.
        let calls = find(&machine, X86Opcode::Call);
        assert_eq!(
            owner
                .call_sites()
                .iter()
                .map(|(_, _, row)| *row)
                .collect::<Vec<_>>(),
            calls,
            "{shape:?}"
        );
        assert_eq!(shape.is_call(), !calls.is_empty(), "{shape:?}");
        // A function that takes and returns a bool is walked under both
        // caller conventions; each walk names every covered write once.
        let walks = if takes_and_returns_bool(&source) {
            2
        } else {
            1
        };
        assert_eq!(
            owner.machine_definitions().len(),
            walks * expected.len(),
            "{shape:?}"
        );
        assert_eq!(owner.abi(), X86SourceBoundAbi::SystemV);
        assert_eq!(owner.obligation().name, X86_BODY_OBLIGATION_NAME);
        assert!(owner.obligation().name.contains("whole-body theorem"));
        assert!(source_admits_x86_body_owner(&source, SYSV), "{shape:?}");
        // Jmp, Ret and Call are never covered; they stay CoveredElsewhere.
        // Ud2 keeps its trap disposition.
        for ordinal in find(&machine, X86Opcode::Jmp)
            .into_iter()
            .chain(find(&machine, X86Opcode::Ret))
            .chain(find(&machine, X86Opcode::Call))
            .chain(find(&machine, X86Opcode::Ud2))
        {
            assert!(!owner.covers(ordinal));
        }
    }
}

#[test]
fn every_premise_is_a_fresh_definition_and_the_sides_are_distinct() {
    for shape in all_shapes() {
        let (source, machine) = pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        let obligation = owner.obligation();
        let entries = free_inputs_of(obligation);
        assert_eq!(
            owner_check(&source, &machine, obligation, &entries),
            Ok(()),
            "{shape:?}"
        );
        assert!(obligation.is_genuinely_proven(), "{shape:?}");
        assert_ne!(obligation.trust_ir_expr, obligation.aarch64_expr);
        assert_eq!(
            obligation.machine_side_provenance,
            MachineSideProvenance::StaticDb
        );
        for premise in &obligation.preconditions {
            let E::Eq { lhs, .. } = premise else {
                panic!("{shape:?}: premise {premise} is not an equation")
            };
            let E::Var { name, .. } = lhs.as_ref() else {
                panic!("{shape:?}: premise {premise} defines no name")
            };
            assert!(!name.starts_with("e_"), "{shape:?}: {premise}");
        }
        // Every entry is a 64-bit register; nothing else is free.
        for (name, width) in &obligation.inputs {
            if name.starts_with("e_") {
                assert_eq!(*width, 64, "{shape:?}: {name}");
            }
        }
    }
}

#[test]
fn non_definitional_premises_are_a_construction_refusal() {
    for shape in [Shape::Add, Shape::BoolIdent, Shape::AddU8] {
        let (source, machine) = pair(shape);
        // The plain spelling: its definitions are the ones to tamper with
        // (slice 18 value-numbers `BoolIdent`'s two caller views away).
        let base = plain_theorem(&source, &machine);
        let entries = free_inputs_of(&base);
        // Refused under both rules: a plain theorem's (two claims) and a
        // spelled theorem's or a part's (one claim suffices, slice 18).
        let refused = |obligation: &ProofObligation| {
            check_definitional(obligation, &entries).is_err()
                && check_definitional_part(obligation, &entries).is_err()
        };
        // Constraining an entry variable would make the premises unsatisfiable
        // for some inputs.
        let mut constrained = base.clone();
        constrained
            .preconditions
            .push(E::var("e_rdi", 64).eq_expr(E::bv_const(0, 64)));
        assert!(refused(&constrained));
        // A contradictory pair defines the same name twice.
        let mut twice = base.clone();
        twice
            .preconditions
            .insert(0, E::var("m0", 64).eq_expr(E::bv_const(1, 64)));
        assert!(refused(&twice));
        // A cycle: the first definition uses a later name.
        let mut cycle = base.clone();
        let last = cycle.preconditions.len() - 1; // outermost = first definition
        let E::Eq { lhs, .. } = &cycle.preconditions[last] else {
            unreachable!()
        };
        let first = lhs.as_ref().clone();
        let width = first.bv_width();
        cycle.preconditions[last] = first.eq_expr(E::var("m0", 64).extract(width - 1, 0));
        assert!(refused(&cycle), "{shape:?}");
        // A bare constraint that defines nothing.
        let mut bare = base.clone();
        bare.preconditions.push(E::bool_const(false));
        assert!(refused(&bare));
        // An undeclared name, a declaration at the wrong width, and a
        // degenerate theorem.
        let mut undeclared = base.clone();
        undeclared.inputs.pop();
        assert!(refused(&undeclared));
        let mut rewidened = base.clone();
        let narrowest = rewidened
            .inputs
            .iter()
            .position(|(name, _)| name == "p0")
            .unwrap();
        rewidened.inputs[narrowest].1 = 7;
        assert!(refused(&rewidened));
        let mut degenerate = base.clone();
        degenerate.aarch64_expr = degenerate.trust_ir_expr.clone();
        assert!(refused(&degenerate));
        let mut unequal = base.clone();
        unequal.aarch64_expr = E::var("e_rdi", 64).concat(E::var("e_rdi", 64));
        assert!(refused(&unequal));
    }
}

/// SHA-256 of the golden file below. The golden bytes can change only
/// together with this reviewed constant: a regenerated file alone fails.
const SNAPSHOT_SHA256: &str = "538604c08e4909cf64944b4da0a236f5a3b2ed045fa2c84be754f73a505af47a";

/// Split a rendered snapshot file into `(shape label, query)` sections.
fn snapshot_sections(text: &str) -> Vec<(String, String)> {
    text.split(";;;; ")
        .filter(|section| !section.is_empty())
        .map(|section| {
            let (label, query) = section.split_once('\n').unwrap_or((section, ""));
            (label.to_owned(), query.to_owned())
        })
        .collect()
}

/// The exact replayed SMT2 of every admitted shape, pinned in one golden
/// file whose digest is pinned here. The encoding is canonical: it is never
/// tuned per function, and names carry no function name or block number.
/// After a deliberate, reviewed encoding change, `TCG_X86_BODY_SNAPSHOT_WRITE=1`
/// rewrites the file and FAILS, printing the new digest; the change lands
/// only when [`SNAPSHOT_SHA256`] is updated by hand to match.
#[test]
fn replayed_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str = include_str!("../tests/fixtures/x86_source_bound_body/snapshots.smt2");
    let mut rendered = String::new();
    for shape in all_shapes() {
        let (source, machine) = pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
        rendered.push_str(&format!(";;;; {shape:?}\n{smt2}\n"));
        // No function name reaches the query: renaming changes nothing.
        let (mut source, mut machine) = (source.clone(), machine.clone());
        source.name = "renamed_function".into();
        machine.name = "renamed_function".into();
        let renamed = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert_eq!(
            generate_smt2_query_raw(renamed.obligation(), &replay_config()),
            smt2
        );
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SNAPSHOT_SHA256 to {:x} and re-run without \
             TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    if rendered != GOLDEN {
        let now = snapshot_sections(&rendered);
        let pinned: std::collections::BTreeMap<String, String> =
            snapshot_sections(GOLDEN).into_iter().collect();
        let mut drifted = Vec::new();
        for (label, query) in &now {
            match pinned.get(label) {
                Some(old) if old == query => {}
                Some(old) => drifted.push(format!(
                    "---- {label} pinned\n{old}\n---- {label} now\n{query}"
                )),
                None => drifted.push(format!("---- {label} is new\n{query}")),
            }
        }
        let current: std::collections::BTreeSet<&str> =
            now.iter().map(|(label, _)| label.as_str()).collect();
        for label in pinned.keys() {
            if !current.contains(label.as_str()) {
                drifted.push(format!("---- {label} is no longer rendered"));
            }
        }
        panic!(
            "snapshots drifted ({} shapes):\n{}",
            drifted.len(),
            drifted.join("\n")
        );
    }
}

/// The slice-1 theorems keep their bytes apart from the dropped preserved
/// tail: pinned inline so the encoding change is reviewable on its own.
#[test]
fn slice_one_add_theorem_is_the_returned_rax_equation() {
    let (source, machine) = pair(Shape::Add);
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    let legacy = "(set-option :timeout 30000)\n\
(set-option :produce-models true)\n\
(set-logic QF_BV)\n\
(declare-const e_rdi (_ BitVec 64))\n\
(declare-const e_rsi (_ BitVec 64))\n\
(declare-const p0 (_ BitVec 64))\n\
(declare-const p1 (_ BitVec 64))\n\
(declare-const s0 (_ BitVec 64))\n\
(declare-const m0 (_ BitVec 64))\n\
(declare-const m1 (_ BitVec 64))\n\
(declare-const m2 (_ BitVec 64))\n\
(declare-const m3 (_ BitVec 64))\n\
(assert (and (= p0 e_rdi) (and (= p1 e_rsi) (and (= s0 (bvadd p0 p1)) (and (= m0 e_rdi) (and (= m1 e_rsi) (and (= m2 (bvadd m0 m1)) (and (= m3 m2) (not (= s0 m3))))))))))\n\
(check-sat)\n\
(exit)";
    assert_eq!(
        crate::ay_bridge::legacy_right_spine_query_for_test(owner.obligation(), &replay_config()),
        legacy
    );
    let canonical = legacy.replace(
        "(assert (and (= p0 e_rdi) (and (= p1 e_rsi) (and (= s0 (bvadd p0 p1)) (and (= m0 e_rdi) (and (= m1 e_rsi) (and (= m2 (bvadd m0 m1)) (and (= m3 m2) (not (= s0 m3))))))))))",
        "(assert (and (and (and (= p0 e_rdi) (= p1 e_rsi)) (and (= s0 (bvadd p0 p1)) (= m0 e_rdi))) (and (and (= m1 e_rsi) (= m2 (bvadd m0 m1))) (and (= m3 m2) (not (= s0 m3))))))",
    );
    assert_ne!(canonical, legacy);
    assert_eq!(
        generate_smt2_query_raw(owner.obligation(), &replay_config()),
        canonical
    );
}

/// The theorem holds on sampled entry values for every correct shape (test
/// evidence only) and is refuted by evaluation for a wrong value that the
/// exact affine check cannot judge (a preserved root's entry value copied
/// into RAX).
#[test]
fn theorem_evaluates_valid_and_refutes_an_opaque_wrong_value() {
    for shape in all_shapes() {
        let (source, machine) = pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert!(holds_on_samples(owner.obligation()), "{shape:?}");
    }
    let (source, mut machine) = pair(Shape::Ident);
    let ret_copy = find(&machine, X86Opcode::MovRR)[1];
    inst_mut(&mut machine, ret_copy).operands[1] = preg(RBX);
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .expect("an RBX-dependent value cannot be judged exactly; the theorem decides");
    assert!(refuted_on_samples(owner.obligation()));
}

/// The observable is exactly the return bits the callers of the result type
/// read: the ABI width, and for a bool the backend's clean 32-bit EAX (plus
/// AL under the psABI views when a bool parameter makes the two caller
/// conventions differ). The preserved roots are never part of it, because the
/// walk (not the solver) judges their preservation.
#[test]
fn the_observable_is_exactly_the_abi_return_bits_and_preservation_is_the_walks() {
    for (shape, bits) in [
        (Shape::Add, vec![64]),
        (Shape::PtrCast, vec![64]),
        (Shape::U32Ident, vec![32]),
        (Shape::I16Ident, vec![16]),
        (Shape::U8Ident, vec![8]),
        (Shape::ZextBool, vec![64]),
        (Shape::BoolFalse, vec![32]),
        (Shape::TruncBool, vec![32]),
        (Shape::BoolIdent, vec![32, 8]),
        (Shape::BoolXor, vec![32, 8]),
        // Slice 3: the result, then every call argument at the bits the
        // callee reads.
        (Shape::CallWrap, vec![64, 64]),
        (Shape::CallSwap, vec![64, 64, 64]),
        (Shape::CallVoid, vec![64]),
        (Shape::CallDiverge, vec![64]),
        (Shape::CallNarrow, vec![8, 32]),
        (Shape::CallBoolResult, vec![32, 64]),
        (Shape::CallBoolArg, vec![64, 32]),
        (Shape::CallI16, vec![32, 32]),
        (Shape::CallNoArgs, vec![64]),
        (Shape::CallSix, vec![64; 7]),
    ]
    .into_iter()
    .map(|(shape, bits)| (shape, bits.into_iter().collect::<Vec<u32>>()))
    {
        let (source, machine) = pair(shape);
        source_bound_x86_body(&source, &machine, SYSV).unwrap();
        // The items as built: the plain spelling (slice 18's canonical one
        // value-numbers them, dropping those true by the definitions).
        let plain = plain_theorem(&source, &machine);
        let obligation = &plain;
        let items = observable_items(obligation);
        let widths: Vec<u32> = items.iter().map(|(source, _)| source.bv_width()).collect();
        assert_eq!(widths, bits, "{shape:?}");
        // One item is the plain equation; several are a conjunction.
        assert_eq!(
            obligation.trust_ir_expr == E::bool_const(true),
            bits.len() > 1,
            "{shape:?}"
        );
        for (source_item, machine_item) in &items {
            assert_eq!(source_item.bv_width(), machine_item.bv_width(), "{shape:?}");
            for used in source_item
                .free_vars()
                .into_iter()
                .chain(machine_item.free_vars())
            {
                assert!(!used.starts_with("e_"), "{shape:?}: {used}");
            }
        }
    }
    // A write to any preserved root is refused before a theorem exists.
    for (register, name) in [(RBX, "rbx"), (RSP, "rsp"), (R12, "r12"), (RBP, "rbp")] {
        for (shape, alias) in [(Shape::Add, register), (Shape::U8Ident, register + 16)] {
            let (source, mut machine) = pair(shape);
            let entry = machine.block_order[0];
            machine.blocks.get_mut(&entry).unwrap().insts.insert(
                0,
                X86ISelInst::new(X86Opcode::MovRI, vec![preg(alias), O::Imm(0)]),
            );
            expect_mismatch(
                &source,
                &machine,
                "preserved write",
                |m| matches!(m, X86BodyMismatch::PreservedWrite { register, .. } if *register == name),
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Negative controls: a wrong lowering is refused (no solver)
// ---------------------------------------------------------------------------

/// Each mutant is refused by the owner AND, where the owner's walk would still
/// build the query, the query itself is refuted by evaluation: the Rust check
/// is a refusal shortcut, not the only thing standing between a wrong lowering
/// and credit.
#[track_caller]
fn assert_value_mutant_refused(source: &Function, machine: &X86ISelFunction, what: &str) {
    expect_mismatch(source, machine, what, |m| {
        matches!(m, X86BodyMismatch::ReturnValue { lane: 0 })
    });
    let theorem = theorem_without_affine_refusal(source, machine, SYSV)
        .unwrap_or_else(|refusal| panic!("{what}: {refusal}"));
    assert!(
        refuted_on_samples(&theorem),
        "{what}: the replayed query must itself be refutable"
    );
}

#[test]
fn wrong_arithmetic_is_refused() {
    let (source, mut machine) = pair(Shape::Add);
    let add = find(&machine, X86Opcode::AddRR)[0];
    inst_mut(&mut machine, add).opcode = X86Opcode::SubRR;
    assert_value_mutant_refused(&source, &machine, "SubRR in place of AddRR");

    let (source, mut machine) = pair(Shape::Sub);
    let sub = find(&machine, X86Opcode::SubRR)[0];
    inst_mut(&mut machine, sub).operands.swap(1, 2);
    assert_value_mutant_refused(&source, &machine, "swapped SubRR operands");

    // Opcodes the affine check cannot judge: only the theorem refutes them.
    for (shape, from, to) in [
        (Shape::Add, X86Opcode::AddRR, X86Opcode::ImulRR),
        (Shape::And, X86Opcode::AndRR, X86Opcode::OrRR),
        (Shape::Xor, X86Opcode::XorRR, X86Opcode::AndRR),
        (Shape::Mul, X86Opcode::ImulRR, X86Opcode::AddRR),
        (Shape::AddU8, X86Opcode::AddRR, X86Opcode::SubRR),
        (Shape::ShlImm, X86Opcode::ShlRI, X86Opcode::ShrRI),
        (Shape::LshrImm, X86Opcode::ShrRI, X86Opcode::ShlRI),
        (Shape::ShlImm, X86Opcode::ShlRI, X86Opcode::SarRI),
        // Shapes whose theorems the qualified AY does not certify are still
        // judged: a wrong lowering of them is refuted, never merely
        // unverified.
        (Shape::AshrImm, X86Opcode::SarRI, X86Opcode::ShrRI),
        // (A logical shift of the sign-extended i8 carrier would be right:
        // bits 0..7 of the result come from bits 3..10 of the carrier.)
        (Shape::AshrI8Imm, X86Opcode::MovsxB, X86Opcode::Movzx),
        (Shape::MulU32, X86Opcode::ImulRR, X86Opcode::AddRR),
        (Shape::MulI16, X86Opcode::ImulRR, X86Opcode::SubRR),
    ] {
        let (source, mut machine) = pair(shape);
        let row = find(&machine, from)[0];
        inst_mut(&mut machine, row).opcode = to;
        assert_theorem_refutes(
            &source,
            &machine,
            &format!("{shape:?}: {to:?} for {from:?}"),
        );
    }
    // A wrong shift count and a wrong immediate.
    let (source, mut machine) = pair(Shape::ShlImm);
    let shl = find(&machine, X86Opcode::ShlRI)[0];
    inst_mut(&mut machine, shl).operands[2] = O::Imm(4);
    assert_theorem_refutes(&source, &machine, "shift count 4 for 3");
    let (source, mut machine) = pair(Shape::AddImm);
    let add = find(&machine, X86Opcode::AddRR)[0];
    let lhs = inst(&machine, add).operands[1].clone();
    inst_mut(&mut machine, add).opcode = X86Opcode::AddRI;
    inst_mut(&mut machine, add).operands =
        vec![inst(&machine, add).operands[0].clone(), lhs, O::Imm(6)];
    assert_value_mutant_refused(&source, &machine, "AddRI with immediate 6 for 5");
    // A scaled LEA with the wrong scale.
    let (_, source, mut machine) = machine_variants()
        .into_iter()
        .find(|(label, _, _)| label == "AddShl2/LeaSib")
        .unwrap();
    let lea = find(&machine, X86Opcode::LeaSib)[0];
    let O::SibMemAddr { scale, .. } = &mut inst_mut(&mut machine, lea).operands[1] else {
        unreachable!()
    };
    assert_eq!(*scale, 4);
    *scale = 2;
    assert_theorem_refutes(&source, &machine, "LeaSib scale 2 for a shift by 2");
}

#[test]
fn wrong_or_missing_return_copy_is_refused() {
    let (source, mut machine) = pair(Shape::Add);
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    let formal = find(&machine, X86Opcode::MovRR)[0];
    let formal_vreg = inst_mut(&mut machine, formal).operands[0].clone();
    inst_mut(&mut machine, ret_copy).operands[1] = formal_vreg;
    assert_value_mutant_refused(&source, &machine, "return reads the wrong vreg");

    let (source, mut machine) = pair(Shape::Add);
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    let (_, block, index) = rows(&machine)[ret_copy];
    machine.blocks.get_mut(&block).unwrap().insts.remove(index);
    expect_mismatch(&source, &machine, "return copy dropped", |m| {
        matches!(m, X86BodyMismatch::UndefinedReturn { register: "rax" })
    });
}

#[test]
fn wrong_argument_registers_are_refused() {
    let (source, mut machine) = pair(Shape::Add);
    let formal = find(&machine, X86Opcode::MovRR)[0];
    assert_eq!(inst_mut(&mut machine, formal).operands[1], preg(RDI));
    inst_mut(&mut machine, formal).operands[1] = preg(RSI);
    assert_value_mutant_refused(&source, &machine, "param 0 read from RSI");

    // A narrow parameter read from the wrong 32-bit alias.
    let (source, mut machine) = pair(Shape::AddU8);
    let formal = find(&machine, X86Opcode::MovRR32)[0];
    assert_eq!(
        inst(&machine, formal).operands[1],
        O::PReg(trust_cg_ir::x86_64_regs::EDI)
    );
    inst_mut(&mut machine, formal).operands[1] = O::PReg(trust_cg_ir::x86_64_regs::ESI);
    assert_theorem_refutes(&source, &machine, "u8 param 0 read from ESI");
    let (source, mut machine) = pair(Shape::U8Ident);
    inst_mut(&mut machine, 0).operands[1] = O::PReg(trust_cg_ir::x86_64_regs::ESI);
    expect_mismatch(
        &source,
        &machine,
        "u8 param read from an argument register it does not have",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rsi"),
    );

    // The Windows x64 lowering (RCX, RDX) verified under System V.
    let source = lir(Shape::Add);
    let win64 = select(&source, X86CallAbi::WindowsX64);
    expect_mismatch(
        &source,
        &win64,
        "Win64 lowering under SysV",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rcx"),
    );
    // And the Win64 convention itself is outside the lane.
    assert!(matches!(
        source_bound_x86_body(&source, &win64, Some(X86SourceBoundAbi::WindowsX64)),
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::Abi(
            X86SourceBoundAbi::WindowsX64
        )))
    ));
}

#[test]
fn wrong_immediate_is_refused() {
    let (source, mut machine) = pair(Shape::Const);
    let movri = find(&machine, X86Opcode::MovRI)[0];
    inst_mut(&mut machine, movri).operands[1] = O::Imm(5);
    assert_value_mutant_refused(&source, &machine, "wrong MovRI immediate");

    let (source, mut machine) = pair(Shape::BoolTrue);
    let movri = find(&machine, X86Opcode::MovRI)[0];
    inst_mut(&mut machine, movri).operands[1] = O::Imm(0);
    assert_theorem_refutes(&source, &machine, "bool true materialized as 0");
}

/// Width errors: a 64-bit value returned through a 32-bit move, a 32-bit
/// value widened by a sign extension that belongs to a zero extension, and
/// the reverse.
#[test]
fn wrong_width_or_extension_is_refused() {
    let (source, mut machine) = pair(Shape::Ident);
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    inst_mut(&mut machine, ret_copy).opcode = X86Opcode::MovRR32;
    assert_theorem_refutes(&source, &machine, "u64 returned through MovRR32");
    let (source, mut machine) = pair(Shape::PtrCast);
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    inst_mut(&mut machine, ret_copy).opcode = X86Opcode::MovRR32;
    assert_theorem_refutes(&source, &machine, "pointer returned through MovRR32");

    // (shape, the extension row: opcode and occurrence, the wrong opcode)
    for (shape, from, occurrence, to) in [
        (Shape::ZextU8, X86Opcode::Movzx, 0, X86Opcode::MovsxB),
        (Shape::SextI8, X86Opcode::MovsxB, 0, X86Opcode::Movzx),
        (Shape::SextI16, X86Opcode::MovsxW, 0, X86Opcode::MovzxW),
        (Shape::SextI32, X86Opcode::Movsx, 0, X86Opcode::MovRR32),
        (Shape::ZextU32, X86Opcode::MovRR32, 1, X86Opcode::Movsx),
        (Shape::ZextU8, X86Opcode::Movzx, 0, X86Opcode::MovzxW),
        (Shape::TruncU16, X86Opcode::MovzxW, 0, X86Opcode::Movzx),
    ] {
        let (source, mut machine) = pair(shape);
        let row = find(&machine, from)[occurrence];
        inst_mut(&mut machine, row).opcode = to;
        assert_theorem_refutes(
            &source,
            &machine,
            &format!("{shape:?}: {to:?} for {from:?}"),
        );
    }
    // Mixed register widths define only the low 32 bits (slice 15: the
    // encoder picks one width, and the bits above are what the allocated
    // registers held): a 64-bit sum returned through them is refuted.
    let (source, mut machine) = pair(Shape::Add);
    let add = find(&machine, X86Opcode::AddRR)[0];
    let narrow = O::VReg(VReg::new(40, RegClass::Gpr32));
    let sum = std::mem::replace(&mut inst_mut(&mut machine, add).operands[0], narrow.clone());
    for (ordinal, _, _) in rows(&machine) {
        let row = inst_mut(&mut machine, ordinal);
        if row.opcode == X86Opcode::MovRR && row.operands[1] == sum {
            row.operands[1] = narrow.clone();
        }
    }
    assert_theorem_refutes(&source, &machine, "mixed-width AddRR");
}

/// The callers pin which return bits are read, and no more.
#[test]
fn narrow_returns_observe_exactly_the_abi_defined_bits() {
    // A bool result whose bits 1..7 are dirty: bit 0 is right, but an
    // LLVM-compiled caller (`movzbl %al, %eax`, no mask) reads the whole byte.
    let (source, mut machine) = pair(Shape::BoolFalse);
    let movri = find(&machine, X86Opcode::MovRI)[0];
    inst_mut(&mut machine, movri).operands[1] = O::Imm(0xfe);
    assert_theorem_refutes(&source, &machine, "bool false with bits 1..7 set");
    let (source, mut machine) = pair(Shape::BoolTrue);
    let movri = find(&machine, X86Opcode::MovRI)[0];
    inst_mut(&mut machine, movri).operands[1] = O::Imm(-1);
    assert_theorem_refutes(&source, &machine, "bool true as all ones");
    // A truncation to bool that forgets to clear bits 1..7.
    let (source, mut machine) = pair(Shape::TruncBool);
    let and = find(&machine, X86Opcode::AndRI)[0];
    inst_mut(&mut machine, and).operands[2] = O::Imm(0xff);
    assert_theorem_refutes(&source, &machine, "trunc to bool without the mask");

    // Positive control: bits above an integer result's ABI width are never
    // constrained. A u8 result whose carrier holds 0x7bcd00xx is correct: the
    // backend's own callers copy AL with MOVZX and LLVM callers re-extend.
    let (source, mut machine) = pair(Shape::U8Ident);
    let entry = machine.block_order[0];
    let carrier = inst(&machine, 0).operands[0].clone();
    let dirty = O::VReg(VReg::new(machine.next_vreg + 10, RegClass::Gpr32));
    let body = &mut machine.blocks.get_mut(&entry).unwrap().insts;
    body.insert(
        1,
        X86ISelInst::new(
            X86Opcode::OrRI,
            vec![dirty.clone(), carrier, O::Imm(0x7bcd_0000)],
        ),
    );
    body[2].operands[1] = dirty;
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert!(holds_on_samples(owner.obligation()));
}

/// A bool result is the backend's clean 32-bit boolean: its own callers copy
/// EAX with `MovRR32` and may forward it to a callee that relies on the
/// 32-bit zero extension (`b as u32` compiles to `movl %edi, %eax` under
/// LLVM). So EAX bits 8..31 are observed, not only the psABI byte.
#[test]
fn a_bool_result_is_the_backends_clean_32_bit_carrier() {
    // `-> bool { false }` materialized as 0x100 and `-> bool { true }` as
    // 0x101: AL is right, EAX is not. Both used to earn credit.
    for (shape, imm) in [(Shape::BoolFalse, 0x100), (Shape::BoolTrue, 0x101)] {
        let (source, mut machine) = pair(shape);
        let movri = find(&machine, X86Opcode::MovRI)[0];
        inst_mut(&mut machine, movri).operands[1] = O::Imm(imm);
        assert_theorem_refutes(&source, &machine, &format!("{shape:?} as {imm:#x}"));
    }
    // The selector's own bool identity (`movzx v, dil; mov eax, v`; until
    // slice 15 the 32-bit copy of EDI) is correct for both caller
    // conventions: a caller that passes a clean 32-bit bool reads a clean EAX
    // back, and a psABI caller (bits 8..31 of EDI unspecified) reads AL.
    for shape in [Shape::BoolIdent, Shape::BoolAnd, Shape::BoolXor] {
        let (source, machine) = pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert!(holds_on_samples(owner.obligation()), "{shape:?}");
        // Both caller views are stated (the plain spelling's names; slice
        // 18's spelling substitutes their bit moves).
        let plain = plain_theorem(&source, &machine);
        let names: Vec<&str> = plain.inputs.iter().map(|(name, _)| name.as_str()).collect();
        assert!(names.contains(&"a0") && names.contains(&"z0"), "{names:?}");
    }
    // Only the clean-bool walk catches a bool identity that sets EAX bit 8:
    // AL is still right for a psABI caller.
    let (source, mut machine) = pair(Shape::BoolIdent);
    let formal = inst(&machine, 0).operands[0].clone();
    let marked = O::VReg(VReg::new(machine.next_vreg + 10, RegClass::Gpr32));
    let entry = machine.block_order[0];
    let body = &mut machine.blocks.get_mut(&entry).unwrap().insts;
    body.insert(
        1,
        X86ISelInst::new(X86Opcode::OrRI, vec![marked.clone(), formal, O::Imm(0x100)]),
    );
    body[2].operands[1] = marked;
    assert_theorem_refutes(&source, &machine, "bool identity that sets EAX bit 8");
    // Only the psABI walk catches a bool identity that folds EDI bits 8..15
    // into AL: a clean 32-bit caller passes zeros there. (Since slice 15 the
    // selector's parameter is the `movzx` of EDI's low byte, so the mutant
    // reads the bits above it from EDI itself.)
    let (source, mut machine) = pair(Shape::BoolIdent);
    let formal = inst(&machine, 0).operands[0].clone();
    let high = O::VReg(VReg::new(machine.next_vreg + 10, RegClass::Gpr32));
    let folded = O::VReg(VReg::new(machine.next_vreg + 11, RegClass::Gpr32));
    let entry = machine.block_order[0];
    let body = &mut machine.blocks.get_mut(&entry).unwrap().insts;
    body.insert(
        1,
        X86ISelInst::new(
            X86Opcode::ShrRI,
            vec![
                high.clone(),
                O::PReg(trust_cg_ir::x86_64_regs::EDI),
                O::Imm(8),
            ],
        ),
    );
    body.insert(
        2,
        X86ISelInst::new(X86Opcode::OrRR, vec![folded.clone(), formal, high]),
    );
    body[3].operands[1] = folded;
    assert_theorem_refutes(&source, &machine, "bool identity that folds EDI bits 8..15");
}

/// Admission never depends on what the replayer can certify. An arithmetic
/// shift right, a multiply on a 32-bit carrier and a scaled LEA are inside
/// the domain with exact semantics (their theorems hold); the qualification
/// host's replayer does not certify them, so their rows stay Unverified
/// there, and a wrong lowering of them is refuted like any other
/// (`wrong_arithmetic_is_refused`).
#[test]
fn shapes_the_replayer_cannot_certify_are_admitted_with_exact_semantics() {
    for (shape, opcode, bits) in [
        (Shape::AshrImm, X86Opcode::SarRI, 64),
        (Shape::AshrI8Imm, X86Opcode::SarRI, 32),
        (Shape::MulU32, X86Opcode::ImulRR, 32),
        (Shape::MulI16, X86Opcode::ImulRR, 32),
    ] {
        let (source, machine) = pair(shape);
        assert!(source_admits_x86_body_owner(&source, SYSV), "{shape:?}");
        let row = *find(&machine, opcode)
            .first()
            .unwrap_or_else(|| panic!("{shape:?}: the selection has no {opcode:?}"));
        assert_eq!(gpr(&inst(&machine, row).operands[0]).unwrap().bits, bits);
        let owner = source_bound_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
        assert!(owner.covers(row), "{shape:?}");
        assert!(holds_on_samples(owner.obligation()), "{shape:?}");
    }
    let (_, source, machine) = machine_variants()
        .into_iter()
        .find(|(label, _, _)| label == "AddShl2/LeaSib")
        .unwrap();
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert!(owner.covers(find(&machine, X86Opcode::LeaSib)[0]));
    assert!(holds_on_samples(owner.obligation()));
}

/// A bool parameter defines only its low byte (psABI: bit 0 the value, bits
/// 1..7 zero). A lowering that relies on LLVM's stronger 32-bit zero
/// extension is refuted, and one that relies on bits 1..7 is not.
#[test]
fn a_bool_parameter_defines_only_its_low_byte() {
    let (source, mut machine) = pair(Shape::ZextBool);
    let movzx = find(&machine, X86Opcode::Movzx)[0];
    inst_mut(&mut machine, movzx).opcode = X86Opcode::MovRR32;
    assert_theorem_refutes(&source, &machine, "bool widened by a 32-bit move");
    // Movzx of the low byte relies only on bits 1..7, which the psABI zeroes.
    let (source, machine) = pair(Shape::ZextBool);
    assert!(holds_on_samples(
        source_bound_x86_body(&source, &machine, SYSV)
            .unwrap()
            .obligation()
    ));
    // Narrow integer parameters define only their own width.
    let (source, mut machine) = pair(Shape::ZextU8);
    let movzx = find(&machine, X86Opcode::Movzx)[0];
    inst_mut(&mut machine, movzx).opcode = X86Opcode::MovzxW;
    assert_theorem_refutes(&source, &machine, "u8 widened from 16 bits");
}

#[test]
fn dead_rows_must_not_clobber_or_read_undefined_state() {
    for (register, name) in [(RBX, "rbx"), (RSP, "rsp"), (R12, "r12"), (RBP, "rbp")] {
        let (source, mut machine) = pair(Shape::Add);
        let entry = machine.block_order[0];
        machine.blocks.get_mut(&entry).unwrap().insts.insert(
            0,
            X86ISelInst::new(X86Opcode::MovRI, vec![preg(register), O::Imm(0)]),
        );
        expect_mismatch(
            &source,
            &machine,
            "dead preserved write",
            |m| matches!(m, X86BodyMismatch::PreservedWrite { register, .. } if *register == name),
        );
    }
    let (source, mut machine) = pair(Shape::Add);
    let entry = machine.block_order[0];
    let fresh = machine.next_vreg + 7;
    machine.blocks.get_mut(&entry).unwrap().insts.insert(
        0,
        X86ISelInst::new(X86Opcode::MovRR, vec![vreg(fresh + 1), vreg(fresh)]),
    );
    expect_mismatch(&source, &machine, "dead undefined read", |m| {
        matches!(m, X86BodyMismatch::UndefinedRead { .. })
    });
    // A caller-saved scratch write that is never observed is harmless and
    // covered.
    let (source, mut machine) = pair(Shape::Add);
    let entry = machine.block_order[0];
    machine.blocks.get_mut(&entry).unwrap().insts.insert(
        0,
        X86ISelInst::new(X86Opcode::MovRI, vec![preg(11), O::Imm(9)]),
    );
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert!(owner.covers(0));
}

#[test]
fn control_skeleton_defects_are_refused() {
    let (source, base) = pair(Shape::BlackBox);
    let jmp = find(&base, X86Opcode::Jmp)[0];
    let entry = base.block_order[0];
    let tail = base.block_order[1];

    // Jmp to a different block (itself): cyclic and disagreeing.
    let mut machine = base.clone();
    inst_mut(&mut machine, jmp).operands[0] = O::Block(entry);
    expect_mismatch(&source, &machine, "jmp to another block", |m| {
        matches!(m, X86BodyMismatch::Control { .. })
    });

    // A successor list that disagrees with the Jmp.
    let mut machine = base.clone();
    machine.blocks.get_mut(&entry).unwrap().successors = vec![entry];
    expect_mismatch(&source, &machine, "successor disagrees", |m| {
        matches!(m, X86BodyMismatch::Control { .. })
    });

    // An unreachable extra block, laid out or not.
    for laid_out in [true, false] {
        let mut machine = base.clone();
        let extra = Block(99);
        machine.ensure_block(extra);
        machine
            .blocks
            .get_mut(&extra)
            .unwrap()
            .insts
            .push(X86ISelInst::new(X86Opcode::Ret, vec![]));
        if !laid_out {
            machine.block_order.retain(|block| *block != extra);
        }
        expect_mismatch(
            &source,
            &machine,
            "unreachable extra block",
            |m| matches!(m, X86BodyMismatch::UnreachableBlock { block } if *block == extra),
        );
    }

    // A second Ret: a return before the end of a block.
    let mut machine = base.clone();
    machine
        .blocks
        .get_mut(&tail)
        .unwrap()
        .insts
        .insert(0, X86ISelInst::new(X86Opcode::Ret, vec![]));
    expect_mismatch(&source, &machine, "second Ret", |m| {
        matches!(m, X86BodyMismatch::Control { .. })
    });
    let mut machine = base.clone();
    machine
        .blocks
        .get_mut(&entry)
        .unwrap()
        .insts
        .insert(jmp, X86ISelInst::new(X86Opcode::Ret, vec![]));
    expect_mismatch(&source, &machine, "Ret before the Jmp", |m| {
        matches!(m, X86BodyMismatch::Control { .. })
    });
}

/// Pointer casts: the owner's subject is the LIR, where the adapter's no-op
/// casts are `Copy`. Anything that changes bits is another opcode, and a
/// `Copy` retyped by a hint is a cast with semantics: never admitted.
#[test]
fn pointer_casts_with_semantics_are_not_admitted() {
    // A pointer carrier retyped to I32 through a sidecar hint.
    let mut retyped = lir(Shape::PtrCast);
    let copy = retyped.blocks[&retyped.entry_block]
        .instructions
        .iter()
        .find(|inst| inst.opcode == L::Copy)
        .unwrap()
        .results[0];
    retyped.value_types.insert(copy, Type::I32);
    assert!(!source_admits_x86_body_owner(&retyped, SYSV));
    // A bit-reinterpreting cast of a pointer carrier.
    let mut bitcast = lir(Shape::PtrCast);
    let entry = bitcast.entry_block;
    for inst in &mut bitcast.blocks.get_mut(&entry).unwrap().instructions {
        if inst.opcode == L::Copy {
            inst.opcode = L::Bitcast { to_ty: Type::F64 };
        }
    }
    assert!(!source_admits_x86_body_owner(&bitcast, SYSV));
    // Pointee metadata must name a distinct pointer-carrier parameter.
    let mut misplaced = lir(Shape::PtrCast);
    misplaced.param_pointee_types[0].param_index = 3;
    assert!(!source_admits_x86_body_owner(&misplaced, SYSV));
    let mut doubled = lir(Shape::PtrCast);
    let first = doubled.param_pointee_types[0].clone();
    doubled.param_pointee_types.push(first);
    assert!(!source_admits_x86_body_owner(&doubled, SYSV));
    // A pointer truncated to 32 bits is a `Trunc`, not a `Copy`: lowering it
    // as a 64-bit copy is refuted.
    // Slice 15: a copy of mixed widths defines its low 32 bits, which is
    // all a 32-bit result needs: the theorem holds.
    let (source, mut machine) = pair(Shape::TruncU32);
    let movrr32 = find(&machine, X86Opcode::MovRR32)[0];
    inst_mut(&mut machine, movrr32).opcode = X86Opcode::MovRR;
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert!(
        holds_on_samples(owner.obligation()),
        "mixed-width truncating MovRR"
    );
    let (source, mut machine) = pair(Shape::TruncU32);
    let movrr32 = find(&machine, X86Opcode::MovRR32)[0];
    let dst = inst(&machine, movrr32).operands[0].clone();
    let O::VReg(dst) = dst else { unreachable!() };
    inst_mut(&mut machine, movrr32).operands[0] = O::VReg(VReg::new(dst.id, RegClass::Gpr64));
    inst_mut(&mut machine, movrr32).opcode = X86Opcode::MovRR;
    // (the return move still reads it as 32 bits: a class conflict)
    expect_unsupported(&source, &machine, "one vreg under two classes");
}

/// `bool as u8`, the LIR `Uextend { from_ty: B1, to_ty: I8 }` the selector
/// once refused (`u8::carrying_add`'s `carry as u8`, Darwin x86-64 `core`
/// census), is inside the domain as it stands: the owner states trust-ir's
/// zero extension of the 0/1 value to eight bits, and the selector's rows for
/// it are the `movzx` of the bool's low byte, or a 32-bit copy of a
/// parameter whose entry `movzx` already cleared every bit from 8 up. The
/// theorem holds for a parameter, a compare's result and `carrying_add`
/// itself, and refutes a `true` extended to all ones (the sign extension,
/// `sext_bool`'s meaning) and an extension of the bool's bit 1.
#[test]
fn zero_extension_of_a_bool_into_a_byte_is_inside_the_domain() {
    /// `name(params) -> results`, the LIR the adapter makes of it, and its
    /// System V selection.
    fn selected(
        name: &str,
        params: Vec<Ty>,
        results: Vec<Ty>,
        body: impl FnOnce(
            &mut trust_ir_build::FunctionBuilder<'_>,
            &[trust_ir::ValueId],
        ) -> Vec<trust_ir::ValueId>,
    ) -> (Function, X86ISelFunction) {
        let mut builder = ModuleBuilder::new("x86_source_bound_body");
        let signature = builder.add_func_type(params.clone(), results);
        let mut f = builder.function(name, signature);
        let entry = f.create_block();
        let args: Vec<_> = params
            .into_iter()
            .map(|ty| f.add_block_param(entry, ty))
            .collect();
        f.switch_to_block(entry);
        let values = body(&mut f, &args);
        f.ret(values);
        f.build();
        let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &builder.build().expect("ModuleBuilder::build: test fixture"),
            trust_cg_lower::GuardCarrierArch::X86_64,
            trust_cg_lower::TlsDialect::default(),
            &permit_unlicensed(),
        )
        .unwrap()
        .remove(0)
        .0;
        let extensions = source
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .filter(|inst| {
                inst.opcode
                    == L::Uextend {
                        from_ty: Type::B1,
                        to_ty: Type::I8,
                    }
            })
            .count();
        assert_eq!(extensions, 1, "{name}: one bool-to-byte extension");
        let machine = select(&source, X86CallAbi::SystemV);
        (source, machine)
    }
    let bool_as_u8 = || {
        selected("bool_as_u8", vec![Ty::Bool], vec![Ty::U8], |f, a| {
            vec![f.zext(Ty::Bool, Ty::U8, a[0])]
        })
    };
    let lt_as_u8 = || {
        selected("lt_as_u8", vec![Ty::U64, Ty::U64], vec![Ty::U8], |f, a| {
            let less = f.icmp(trust_ir::ICmpOp::Ult, Ty::U64, a[0], a[1]);
            vec![f.zext(Ty::Bool, Ty::U8, less)]
        })
    };
    let carrying_add = || {
        selected(
            "carrying_add_u8",
            vec![Ty::U8, Ty::U8, Ty::Bool],
            vec![Ty::U8, Ty::Bool],
            |f, a| {
                let s = f.add(Ty::U8, a[0], a[1]);
                let c1 = f.icmp(trust_ir::ICmpOp::Ult, Ty::U8, s, a[0]);
                let carry_in = f.zext(Ty::Bool, Ty::U8, a[2]);
                let t = f.add(Ty::U8, s, carry_in);
                let c2 = f.icmp(trust_ir::ICmpOp::Ult, Ty::U8, t, s);
                vec![t, f.binop(BinOp::Or, Ty::Bool, c1, c2)]
            },
        )
    };

    /// The row extending the bool `bool_reg` defines: the first row after its
    /// definition that reads it as a `movzx` or 32-bit copy source.
    fn extension_of(machine: &X86ISelFunction, definition: usize) -> usize {
        let bool_reg = inst(machine, definition).operands[0].clone();
        rows(machine)
            .into_iter()
            .map(|(ordinal, _, _)| ordinal)
            .find(|row| {
                *row > definition
                    && matches!(
                        inst(machine, *row).opcode,
                        X86Opcode::Movzx | X86Opcode::MovRR32
                    )
                    && inst(machine, *row).operands[1] == bool_reg
            })
            .expect("the bool's extension")
    }
    /// The entry `movzx` of the bool parameter (from its argument byte).
    fn bool_parameter(machine: &X86ISelFunction) -> usize {
        find(machine, X86Opcode::Movzx)
            .into_iter()
            .find(|row| matches!(inst(machine, *row).operands[1], O::PReg(_)))
            .expect("the bool parameter's entry movzx")
    }
    /// The compare's `movzx` of its `setcc` byte.
    fn compare_bool(machine: &X86ISelFunction) -> usize {
        let setcc = find(machine, X86Opcode::Setcc)[0];
        let byte = inst(machine, setcc).operands[0].clone();
        find(machine, X86Opcode::Movzx)
            .into_iter()
            .find(|row| *row > setcc && inst(machine, *row).operands[1] == byte)
            .expect("the compare's movzx")
    }

    // The selections: a parameter's extension is the 32-bit copy of its entry
    // `movzx`, a compare result's the `movzx` of its byte.
    let (source, machine) = bool_as_u8();
    let extension = extension_of(&machine, bool_parameter(&machine));
    assert_eq!(inst(&machine, extension).opcode, X86Opcode::MovRR32);
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert!(owner.covers(extension), "bool_as_u8");
    assert!(holds_on_samples(owner.obligation()), "bool_as_u8");
    let (source, machine) = lt_as_u8();
    let extension = extension_of(&machine, compare_bool(&machine));
    assert_eq!(inst(&machine, extension).opcode, X86Opcode::Movzx);
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert!(owner.covers(extension), "lt_as_u8");
    assert!(holds_on_samples(owner.obligation()), "lt_as_u8");
    let (source, machine) = carrying_add();
    let extension = extension_of(&machine, bool_parameter(&machine));
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap_or_else(|refusal| panic!("carrying_add_u8: {refusal}"));
    assert!(owner.covers(extension), "carrying_add_u8");
    assert!(holds_on_samples(owner.obligation()), "carrying_add_u8");

    // `true` extended to all ones: the extension's row becomes `neg`, which
    // computes `0 - b` (0xFF for `true`), LIR's sign extension (the
    // `sext_bool` fixtures' lowering).
    for (label, (source, mut machine), from_compare) in [
        ("bool_as_u8", bool_as_u8(), false),
        ("lt_as_u8", lt_as_u8(), true),
        ("carrying_add_u8", carrying_add(), false),
    ] {
        let definition = if from_compare {
            compare_bool(&machine)
        } else {
            bool_parameter(&machine)
        };
        let row = extension_of(&machine, definition);
        inst_mut(&mut machine, row).opcode = X86Opcode::Neg;
        assert_theorem_refutes(&source, &machine, &format!("{label}: true as all ones"));
    }
    // The extension of bit 1 of the bool (always 0) instead of bit 0.
    let (source, mut machine) = lt_as_u8();
    let extension = extension_of(&machine, compare_bool(&machine));
    let bool_reg = inst(&machine, extension).operands[1].clone();
    let shifted = O::VReg(VReg::new(machine.next_vreg + 10, RegClass::Gpr32));
    let (_, block, index) = rows(&machine)[extension];
    let body = &mut machine.blocks.get_mut(&block).unwrap().insts;
    body.insert(
        index,
        X86ISelInst::new(X86Opcode::ShrRI, vec![shifted.clone(), bool_reg, O::Imm(1)]),
    );
    body[index + 1].operands[1] = shifted;
    assert_theorem_refutes(&source, &machine, "lt_as_u8: bit 1 extended");
}

#[test]
fn out_of_domain_sources_and_abis_are_unsupported() {
    let (add, machine) = pair(Shape::Add);
    assert!(matches!(
        source_bound_x86_body(&add, &machine, None),
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::NoAbi))
    ));
    assert!(!source_admits_x86_body_owner(&add, None));

    let mut cases: Vec<(&str, Function)> = Vec::new();
    let mut wide = add.clone();
    wide.signature.params = vec![Type::I128, Type::I128];
    wide.signature.returns = vec![Type::I128];
    cases.push(("I128", wide));
    let mut float = add.clone();
    float.signature.params = vec![Type::F64, Type::F64];
    cases.push(("F64", float));
    let mut seven = add.clone();
    seven.signature.params = vec![Type::I64; 7];
    cases.push(("seven params", seven));
    let mut void = add.clone();
    void.signature.returns.clear();
    cases.push(("void", void));
    // Private stack slots are admitted (slice 4) only fixed and bounded.
    let mut slot = add.clone();
    let mut runtime = trust_cg_lower::StackSlotInfo::new(8, 8);
    runtime.allocation = StackSlotAllocationKind::RuntimeSized {
        size_source: trust_cg_ir::function::StackSlotSizeSource::Unknown,
    };
    slot.stack_slots.push(runtime);
    cases.push(("runtime-sized stack slot", slot));
    let mut huge = add.clone();
    huge.stack_slots
        .push(trust_cg_lower::StackSlotInfo::new(MAX_SLOT_BYTES + 1, 8));
    cases.push(("oversized stack slot", huge));
    let mut sret = add.clone();
    sret.abi_sret_param = Some(trust_cg_lower::function::AbiSretParam { param_index: 0 });
    cases.push(("sret", sret));
    let replace = |opcode: L, results: Vec<Value>| {
        let mut changed = add.clone();
        let entry = changed.entry_block;
        let block = changed.blocks.get_mut(&entry).unwrap();
        let args = block.instructions[0].args.clone();
        block.instructions[0] = Instruction {
            opcode,
            args,
            results,
        };
        changed
    };
    cases.push((
        "icmp",
        replace(L::Icmp { cond: IntCC::Equal }, vec![Value(2)]),
    ));
    // (A shift by a non-constant amount of the value's own carrier is slice
    // 10's, see `slice10::`; a division is slice 14's, see `slice14::`.)
    cases.push((
        "load",
        replace(
            L::Load {
                ty: Type::I64,
                align: None,
            },
            vec![Value(2)],
        ),
    ));
    cases.push((
        "call",
        replace(
            L::Call {
                name: "callee".into(),
                binding: Default::default(),
            },
            vec![Value(2)],
        ),
    ));
    // A bool constant that is not 0 or 1.
    let mut odd_bool = lir(Shape::BoolFalse);
    let entry = odd_bool.entry_block;
    odd_bool.blocks.get_mut(&entry).unwrap().instructions[0].opcode = L::Iconst {
        ty: Type::B1,
        imm: 2,
    };
    cases.push(("B1 constant 2", odd_bool));
    // An out-of-range constant shift amount.
    let mut far = lir(Shape::ShlImm);
    let entry = far.entry_block;
    for inst in &mut far.blocks.get_mut(&entry).unwrap().instructions {
        if let L::Iconst { imm, .. } = &mut inst.opcode {
            *imm = 64;
        }
    }
    cases.push(("shl by 64", far));
    // A bitcast that changes the carrier is not a signedness reinterpretation.
    let mut widening = lir(Shape::I8AsU8);
    let entry = widening.entry_block;
    for inst in &mut widening.blocks.get_mut(&entry).unwrap().instructions {
        if let L::Bitcast { to_ty } = &mut inst.opcode {
            *to_ty = Type::I16;
        }
    }
    cases.push(("carrier-changing bitcast", widening));
    for (what, source) in &cases {
        assert!(!source_admits_x86_body_owner(source, SYSV), "{what}");
        expect_unsupported(source, &machine, what);
    }

    // A stack-slot TABLE is in the domain: this theorem runs on PRE-frame-
    // lowering ISel output, so the prologue a slot forces is not in scope. A
    // row may reference a slot only as the base of a modelled `[slot + disp]`
    // operand (slice 4, `row_mentions_unmodelled_stack_slot`); anywhere else it
    // makes no claim.
    {
        let mut slot = add.clone();
        slot.stack_slots
            .push(trust_cg_lower::StackSlotInfo::new(8, 8));
        assert!(
            source_admits_x86_body_owner(&slot, SYSV),
            "a slot TABLE that no instruction references must be admitted"
        );
        let (_, mut machine) = pair(Shape::Add);
        machine.stack_slots = vec![trust_cg_lower::StackSlotInfo::new(8, 8)];
        assert!(
            source_bound_x86_body(&slot, &machine, SYSV).is_ok(),
            "a slot table on BOTH sides, referenced by no row, must build a theorem"
        );

        let (mut source, mut machine) = pair(Shape::Add);
        source.stack_slots = vec![trust_cg_lower::StackSlotInfo::new(8, 8)];
        machine.stack_slots = source.stack_slots.clone();
        let add_row = find(&machine, X86Opcode::AddRR)[0];
        inst_mut(&mut machine, add_row).operands[1] = O::StackSlot(0);
        expect_unsupported(&source, &machine, "ALU row referencing a stack slot");
        let mut sib = machine.clone();
        let row = inst_mut(&mut sib, add_row);
        row.opcode = X86Opcode::LeaSib;
        row.operands = vec![
            row.operands[0].clone(),
            O::SibMemAddr {
                base: Box::new(O::PReg(trust_cg_ir::x86_64_regs::RDI)),
                index: Box::new(O::StackSlot(0)),
                scale: 1,
                disp: 0,
            },
        ];
        expect_unsupported(&source, &sib, "stack slot as a SIB index");
    }

    // Out-of-domain machine rows make no claim either: memory, flags, calls,
    // a SIB scale the encoder refuses.
    let (source, mut machine) = pair(Shape::Add);
    let add_row = find(&machine, X86Opcode::AddRR)[0];
    inst_mut(&mut machine, add_row).opcode = X86Opcode::CmpRR;
    expect_unsupported(&source, &machine, "CmpRR row");
    let (source, mut machine) = pair(Shape::Add);
    let add_row = find(&machine, X86Opcode::AddRR)[0];
    let operands = inst(&machine, add_row).operands.clone();
    *inst_mut(&mut machine, add_row) = X86ISelInst::new(
        X86Opcode::LeaSib,
        vec![
            operands[0].clone(),
            O::SibMemAddr {
                base: Box::new(operands[1].clone()),
                index: Box::new(operands[2].clone()),
                scale: 3,
                disp: 0,
            },
        ],
    );
    expect_unsupported(&source, &machine, "LeaSib scale 3");
    let (source, mut machine) = pair(Shape::Add);
    let add_row = find(&machine, X86Opcode::AddRR)[0];
    inst_mut(&mut machine, add_row).flags = InstFlags::HAS_SIDE_EFFECTS;
    expect_unsupported(&source, &machine, "side-effect flag");
    let (source, mut machine) = pair(Shape::U8Ident);
    inst_mut(&mut machine, 0).operands[1] = O::PReg(trust_cg_ir::x86_64_regs::DIL);
    expect_unsupported(&source, &machine, "8-bit physical alias");
}

/// Slice 25.0: the stack-slot scan's refusal names one row, the same on every
/// run, and counts the rows that reference a slot outside a modelled operand.
/// The row named is the first such row of the blocks `block_order` names (at
/// its walk ordinal), then of the blocks it omits by ascending id (at its
/// index), whatever the `HashMap` order of `machine.blocks`. The first case
/// edits one row of a real selection; the others add synthetic blocks to one,
/// which the scan judges before any layout or control check.
#[test]
fn the_stack_slot_scan_names_its_first_row_in_layout_order() {
    use trust_cg_lower::x86_64_isel::X86ISelBlock;
    const SCAN: &str = "unsupported source-bound x86-64 body: machine function is outside the \
                        body domain: a row that references a stack slot outside a modelled \
                        `[slot + disp]` operand or scaled-index base: ";
    #[track_caller]
    fn scan_refusal(source: &Function, machine: &X86ISelFunction) -> String {
        match source_bound_x86_body(source, machine, SYSV) {
            Err(refusal @ X86BodyRefusal::Unsupported(X86BodyUnsupported::MachineFunction(_))) => {
                format!("{refusal}")
            }
            Err(other) => panic!("expected the stack-slot scan's refusal, got {other}"),
            Ok(_) => panic!("a row naming a stack slot built a body theorem"),
        }
    }
    let slots = vec![trust_cg_lower::StackSlotInfo::new(8, 8)];

    // A real selection that references no slot passes the scan.
    let (_, machine) = pair(Shape::Add);
    assert_eq!(unmodelled_stack_slot_rows(&machine), None);

    // A real selection, one ALU row edited to read the slot.
    let (mut source, mut machine) = pair(Shape::Add);
    source.stack_slots = slots.clone();
    machine.stack_slots = slots.clone();
    let add_row = find(&machine, X86Opcode::AddRR)[0];
    let (_, add_block, _) = rows(&machine)[add_row];
    inst_mut(&mut machine, add_row).operands[1] = O::StackSlot(0);
    let operands = inst(&machine, add_row).operands.clone();
    assert_eq!(
        scan_refusal(&source, &machine),
        format!(
            "{SCAN}block {add_block:?} row {add_row}, AddRR with operands {operands:?} (1 such \
             row)"
        )
    );

    // Synthetic blocks: two laid out after the real ones, in an order that is
    // not their ids', and two that `block_order` omits. Five rows offend: a
    // slot as a SIB index and four bare slots; the copies do not.
    let (mut source, mut machine) = pair(Shape::Add);
    source.stack_slots = slots.clone();
    machine.stack_slots = slots;
    let real_rows = rows(&machine).len();
    let bare = |id| X86ISelInst::new(X86Opcode::AddRR, vec![vreg(id), O::StackSlot(0)]);
    let slot_index = |id| {
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![
                vreg(id),
                O::SibMemAddr {
                    base: Box::new(vreg(1)),
                    index: Box::new(O::StackSlot(0)),
                    scale: 1,
                    disp: 0,
                },
            ],
        )
    };
    let copy = |id| X86ISelInst::new(X86Opcode::MovRR, vec![vreg(id), vreg(1)]);
    let block = |insts| X86ISelBlock {
        insts,
        successors: Vec::new(),
    };
    machine.blocks.insert(
        Block(905),
        block(vec![copy(900), slot_index(901), bare(902)]),
    );
    machine.blocks.insert(Block(901), block(vec![bare(903)]));
    machine.blocks.insert(Block(950), block(vec![bare(904)]));
    machine
        .blocks
        .insert(Block(920), block(vec![copy(905), copy(906), bare(907)]));
    machine.block_order.extend([Block(905), Block(901)]);
    let first = format!(
        "{SCAN}block Block(905) row {}, LeaSib with operands {:?} (5 such rows)",
        real_rows + 1,
        slot_index(901).operands
    );
    assert_eq!(scan_refusal(&source, &machine), first);

    // The same function with its blocks inserted in other orders: the map
    // iterates differently (a scan in the map's order would name different
    // rows), the refusal does not.
    let mut entries: Vec<(Block, X86ISelBlock)> = machine.blocks.clone().into_iter().collect();
    entries.sort_by_key(|(block, _)| *block);
    let mut map_order_first = HashSet::new();
    for turn in 0..64 {
        let mut order = entries.clone();
        order.rotate_left(turn % entries.len());
        if turn % 2 == 1 {
            order.reverse();
        }
        let mut rebuilt = machine.clone();
        rebuilt.blocks = order.into_iter().collect();
        map_order_first.insert(
            rebuilt
                .blocks
                .iter()
                .find(|(_, body)| body.insts.iter().any(row_mentions_unmodelled_stack_slot))
                .map(|(block, _)| *block),
        );
        assert_eq!(
            scan_refusal(&source, &rebuilt),
            first,
            "insertion order {turn}"
        );
    }
    assert!(
        map_order_first.len() > 1,
        "the rebuilt maps must iterate in more than one order: {map_order_first:?}"
    );

    // Layout order, not id order: with the two laid-out blocks swapped, the
    // first offending row is the other block's.
    let mut swapped = machine.clone();
    let tail = swapped.block_order.len();
    swapped.block_order.swap(tail - 2, tail - 1);
    assert_eq!(
        scan_refusal(&source, &swapped),
        format!(
            "{SCAN}block Block(901) row {real_rows}, AddRR with operands {:?} (5 such rows)",
            bare(903).operands
        )
    );

    // A repeated name and a name with no body add no row and move no ordinal.
    let mut repeated = machine.clone();
    repeated
        .block_order
        .extend([Block(905), Block(999), Block(901)]);
    assert_eq!(scan_refusal(&source, &repeated), first);

    // Only blocks `block_order` omits: the lowest id first, at its index.
    let mut omitted = machine.clone();
    omitted.block_order.truncate(tail - 2);
    omitted.blocks.remove(&Block(905));
    omitted.blocks.remove(&Block(901));
    assert_eq!(
        scan_refusal(&source, &omitted),
        format!(
            "{SCAN}block Block(920) row (not laid out) index 2, AddRR with operands {:?} (2 such \
             rows)",
            bare(907).operands
        )
    );
    omitted.blocks.remove(&Block(920));
    assert_eq!(
        scan_refusal(&source, &omitted),
        format!(
            "{SCAN}block Block(950) row (not laid out) index 0, AddRR with operands {:?} (1 such \
             row)",
            bare(904).operands
        )
    );
    omitted.blocks.remove(&Block(950));
    assert_eq!(unmodelled_stack_slot_rows(&omitted), None);
}

/// Volatile memory stays outside the lane, by name, on real selections.
/// (Direct calls are slice 3; their out-of-domain forms are in
/// [`calls_outside_the_slice_three_domain_are_unsupported`]. A branch-free
/// compare whose `bool` is returned is slice 5, acyclic branches are slice
/// 6, an indirect call through a register is slice 10 and a natural loop is
/// slice 12, which this test now checks are admitted.)
#[test]
fn calls_memory_flags_and_loops_stay_unsupported() {
    let mut builder = ModuleBuilder::new("x86_source_bound_body");
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let load_ty = builder.add_func_type(vec![Ty::PtrConst(Box::new(Ty::U64))], vec![Ty::U64]);
    let indirect_ty = builder.add_func_type(vec![Ty::Func(unary), Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("calls", indirect_ty);
    let entry = f.create_block();
    let callee = f.add_block_param(entry, Ty::Func(unary));
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let y = f.call_indirect(callee, unary, vec![x]);
    f.ret(vec![y]);
    f.build();
    // A loop (slice 12 admits it): count up to `n`.
    let mut f = builder.function("loops", unary);
    let entry = f.create_block();
    let header = f.create_block();
    let body = f.create_block();
    let exit = f.create_block();
    let n = f.add_block_param(entry, Ty::U64);
    let i = f.add_block_param(header, Ty::U64);
    f.switch_to_block(entry);
    let zero = f.iconst(Ty::U64, 0);
    f.br(header, vec![zero]);
    f.switch_to_block(header);
    let lt = f.icmp(trust_ir::ICmpOp::Ult, Ty::U64, i, n);
    f.condbr(lt, body, vec![], exit, vec![]);
    f.switch_to_block(body);
    let one = f.iconst(Ty::U64, 1);
    let next = f.add(Ty::U64, i, one);
    f.br(header, vec![next]);
    f.switch_to_block(exit);
    f.ret(vec![i]);
    f.build();
    // Scalar loads are admitted (slice 4); a volatile load stays outside.
    let mut f = builder.function("volatile_loads", load_ty);
    let entry = f.create_block();
    let p = f.add_block_param(entry, Ty::PtrConst(Box::new(Ty::U64)));
    f.switch_to_block(entry);
    let v = f.load_volatile(Ty::U64, p);
    f.ret(vec![v]);
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let lir = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap();
    for (source, _) in &lir {
        if source.name == "callee" {
            continue;
        }
        // Slice 10: a call through a function pointer is admitted; slice
        // 12: so is the loop.
        assert_eq!(
            source_admits_x86_body_owner(source, SYSV),
            source.name == "calls" || source.name == "loops",
            "{}: only the indirect call and the loop are in the lane",
            source.name
        );
    }
}

// ---------------------------------------------------------------------------
// Slice 3: direct calls (no solver)
// ---------------------------------------------------------------------------

/// The walk ordinal of the last row before the `n`-th `Call` whose
/// destination is the 64-bit root `root` (through any width alias).
fn setup_row(machine: &X86ISelFunction, call: usize, root: u16) -> usize {
    let call_row = find(machine, X86Opcode::Call)[call];
    (0..call_row)
        .rev()
        .find(|ordinal| {
            let inst = inst(machine, *ordinal);
            inst.opcode != X86Opcode::Call
                && inst
                    .operands
                    .first()
                    .and_then(gpr)
                    .is_some_and(|reg| reg.root == Root::Physical(root))
        })
        .unwrap_or_else(|| panic!("no set-up of root {root} before call {call}"))
}

/// Insert `inserted` so that it becomes walk ordinal `ordinal`.
fn insert_at(machine: &mut X86ISelFunction, ordinal: usize, inserted: X86ISelInst) {
    let (_, block, index) = rows(machine)[ordinal];
    machine
        .blocks
        .get_mut(&block)
        .unwrap()
        .insts
        .insert(index, inserted);
}

fn remove_at(machine: &mut X86ISelFunction, ordinal: usize) -> X86ISelInst {
    let (_, block, index) = rows(machine)[ordinal];
    machine.blocks.get_mut(&block).unwrap().insts.remove(index)
}

/// A wrong call lowering that the exact Rust checks cannot judge must build
/// a theorem the replayed query refutes; one they can judge must be a typed
/// mismatch AND, with the Rust refusal bypassed, a refutable query.
#[track_caller]
fn assert_call_argument_mutant_refused(source: &Function, machine: &X86ISelFunction, what: &str) {
    expect_mismatch(source, machine, what, |m| {
        matches!(m, X86BodyMismatch::CallArgument { .. })
    });
    let theorem = theorem_without_affine_refusal(source, machine, SYSV)
        .unwrap_or_else(|refusal| panic!("{what}: {refusal}"));
    assert!(
        refuted_on_samples(&theorem),
        "{what}: the replayed query must itself be refutable"
    );
}

#[test]
fn call_fixtures_have_the_expected_pre_ra_shapes() {
    use X86Opcode::*;
    assert_eq!(
        opcodes(&pair(Shape::CallWrap).1),
        vec![MovRR, MovRR, Call, MovRR, MovRR, Ret]
    );
    assert_eq!(
        opcodes(&pair(Shape::CallDiverge).1),
        vec![MovRR, MovRR, Call, Ud2]
    );
    let (source, machine) = pair(Shape::CallWrap);
    let call = inst(&machine, find(&machine, Call)[0]);
    assert_eq!(call.operands, vec![O::Symbol("g1".into())]);
    assert_eq!(
        call.call_arg_regs,
        vec![X86CallArgReg::new(X86PReg::new(RDI), 64)]
    );
    assert_eq!(
        call.call_result_regs,
        Some(vec![X86CallResultReg::new(X86PReg::new(RAX), 64)])
    );
    assert!(
        source.blocks[&source.entry_block]
            .instructions
            .iter()
            .any(|inst| matches!(&inst.opcode, L::Call { name, .. } if name == "g1"))
    );
    // The diverging body is `Call; Trap` in LIR and `CALL; UD2` pre-RA.
    let (diverge, _) = pair(Shape::CallDiverge);
    let flat: Vec<_> = diverge
        .layout_order()
        .iter()
        .flat_map(|block| diverge.blocks[block].instructions.iter())
        .map(|inst| std::mem::discriminant(&inst.opcode))
        .collect();
    assert_eq!(flat.last(), Some(&std::mem::discriminant(&L::Trap)));
    assert!(diverge.signature.returns.is_empty());
    // A narrow result is copied from its exact ABI bits (AL through MOVZX).
    let narrow = opcodes(&pair(Shape::CallNarrow).1);
    assert!(narrow.contains(&Movzx), "{narrow:?}");
    // So is a `bool` result: a callee defines only AL (psABI; LLVM returns
    // `setcc %al`), so the caller re-extends it and declares 8 bits.
    let (_, bool_result) = pair(Shape::CallBoolResult);
    let call = find(&bool_result, Call)[0];
    assert_eq!(
        inst(&bool_result, call).call_result_regs,
        Some(vec![X86CallResultReg::new(X86PReg::new(RAX), 8)])
    );
    assert_eq!(inst(&bool_result, call + 1).opcode, Movzx);
    assert_eq!(
        inst(&bool_result, call + 1).operands[1],
        O::PReg(trust_cg_ir::x86_64_regs::AL)
    );
}

/// Every slice-3 negative control: each wrong call lowering is refused by a
/// typed mismatch or refuted by the replayed query; none builds a Valid
/// theorem.
#[test]
fn wrong_call_lowerings_are_refused() {
    // Wrong argument register: `a` goes to RDX instead of RSI, so the callee
    // reads the caller's `b` (still in RSI) as its second argument.
    let (source, mut machine) = pair(Shape::CallSwap);
    let rsi = setup_row(&machine, 0, RSI);
    inst_mut(&mut machine, rsi).operands[0] = preg(RDX);
    assert_call_argument_mutant_refused(&source, &machine, "argument in RDX for RSI");
    // ... and where the intended register holds nothing, an undefined read.
    let (source, mut machine) = pair(Shape::CallDivergeConst);
    let rdi = setup_row(&machine, 0, RDI);
    inst_mut(&mut machine, rdi).operands[0] = preg(RDX);
    expect_mismatch(
        &source,
        &machine,
        "argument in RDX for RDI",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rdi"),
    );

    // Swapped arguments.
    let (source, mut machine) = pair(Shape::CallSwap);
    let (rdi, rsi) = (setup_row(&machine, 0, RDI), setup_row(&machine, 0, RSI));
    let (first, second) = (
        inst(&machine, rdi).operands[1].clone(),
        inst(&machine, rsi).operands[1].clone(),
    );
    inst_mut(&mut machine, rdi).operands[1] = second;
    inst_mut(&mut machine, rsi).operands[1] = first;
    assert_call_argument_mutant_refused(&source, &machine, "swapped arguments");

    // A stale value read from a caller-saved register after the call: the
    // parameter `x` still sat in RDI before the call; after it, RDI is
    // clobbered.
    let (source, mut machine) = pair(Shape::CallAfter);
    let add = find(&machine, X86Opcode::AddRR)[0];
    let reads_x = inst(&machine, add)
        .operands
        .iter()
        .position(|operand| operand == &inst(&machine, 0).operands[0])
        .expect("the add reads the parameter's vreg");
    inst_mut(&mut machine, add).operands[reads_x] = preg(RDI);
    expect_mismatch(
        &source,
        &machine,
        "RDI read after the call",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rdi"),
    );
    // The same for an argument register the function received its second
    // parameter in.
    let (source, mut machine) = pair(Shape::CallSwap);
    let after = find(&machine, X86Opcode::Call)[0] + 1;
    insert_at(
        &mut machine,
        after,
        X86ISelInst::new(X86Opcode::MovRR, vec![vreg(90), preg(RSI)]),
    );
    expect_mismatch(
        &source,
        &machine,
        "RSI read after the call",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rsi"),
    );
    // RAX's bits above a narrow result are undefined. Reading them into a
    // dead row is harmless ...
    let (source, mut machine) = pair(Shape::CallI16);
    let after = find(&machine, X86Opcode::Call)[0] + 1;
    insert_at(
        &mut machine,
        after,
        X86ISelInst::new(X86Opcode::MovRR, vec![vreg(90), preg(RAX)]),
    );
    let owner = source_bound_x86_body(&source, &machine, SYSV).expect("dead RAX read");
    assert!(holds_on_samples(owner.obligation()));
    // ... but returning them as the upper half of a widened u32 result is
    // refuted by the theorem (no Rust check can judge it).
    let (source, mut machine) = pair(Shape::CallWiden);
    let after = find(&machine, X86Opcode::Call)[0] + 1;
    insert_at(
        &mut machine,
        after,
        X86ISelInst::new(X86Opcode::MovRR, vec![vreg(90), preg(RAX)]),
    );
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    inst_mut(&mut machine, ret_copy).operands[1] = vreg(90);
    assert_theorem_refutes(&source, &machine, "RAX garbage returned");
    // A `bool` call result copied from EAX (the lowering before slice 3)
    // carries the callee's stale bits 8..31 into the returned clean bool:
    // refuted by the theorem.
    let (source, mut machine) = pair(Shape::CallBoolResult);
    let copy = find(&machine, X86Opcode::Call)[0] + 1;
    *inst_mut(&mut machine, copy) = X86ISelInst::new(
        X86Opcode::MovRR32,
        vec![
            inst(&machine, copy).operands[0].clone(),
            O::PReg(trust_cg_ir::x86_64_regs::EAX),
        ],
    );
    assert_theorem_refutes(&source, &machine, "bool call result copied from EAX");
    // A result register declared at another width is wrong metadata.
    let (source, mut machine) = pair(Shape::CallWrap);
    let call = find(&machine, X86Opcode::Call)[0];
    inst_mut(&mut machine, call).call_result_regs =
        Some(vec![X86CallResultReg::new(X86PReg::new(RAX), 32)]);
    expect_mismatch(&source, &machine, "result declared 32-bit", |m| {
        matches!(m, X86BodyMismatch::CallMetadata { .. })
    });

    // Calls reordered: a different callee first is a pairing mismatch ...
    let (source, mut machine) = pair(Shape::CallThenCall);
    let calls = find(&machine, X86Opcode::Call);
    let (first, second) = (
        inst(&machine, calls[0]).clone(),
        inst(&machine, calls[1]).clone(),
    );
    *inst_mut(&mut machine, calls[0]) = second;
    *inst_mut(&mut machine, calls[1]) = first;
    expect_mismatch(&source, &machine, "calls reordered", |m| {
        matches!(m, X86BodyMismatch::CallTarget { .. })
    });
    // ... and the same callee called with its arguments in the other order
    // is refuted.
    let (source, mut machine) = pair(Shape::CallSeq);
    let (a, b) = (setup_row(&machine, 0, RDI), setup_row(&machine, 1, RDI));
    let (first, second) = (
        inst(&machine, a).operands[1].clone(),
        inst(&machine, b).operands[1].clone(),
    );
    inst_mut(&mut machine, a).operands[1] = second;
    inst_mut(&mut machine, b).operands[1] = first;
    assert_call_argument_mutant_refused(&source, &machine, "same-callee calls reordered");

    // Wrong callee symbol, and a binding that disagrees with the source.
    let (source, mut machine) = pair(Shape::CallWrap);
    let call = find(&machine, X86Opcode::Call)[0];
    inst_mut(&mut machine, call).operands[0] = O::Symbol("g0".into());
    expect_mismatch(
        &source,
        &machine,
        "wrong callee",
        |m| matches!(m, X86BodyMismatch::CallTarget { found, .. } if found.contains("`g0`")),
    );
    let (source, mut machine) = pair(Shape::CallWrap);
    inst_mut(&mut machine, call)
        .flags
        .insert(InstFlags::EXACT_MODULE_CALL);
    expect_mismatch(&source, &machine, "exact-module binding", |m| {
        matches!(m, X86BodyMismatch::CallTarget { .. })
    });

    // A missing argument: the set-up of RSI is dropped, so the callee reads
    // the caller's `b` ...
    let (source, mut machine) = pair(Shape::CallSwap);
    let rsi = setup_row(&machine, 0, RSI);
    remove_at(&mut machine, rsi);
    assert_call_argument_mutant_refused(&source, &machine, "missing RSI set-up");
    // ... or nothing at all ...
    let (source, mut machine) = pair(Shape::CallDivergeConst);
    let rsi = setup_row(&machine, 0, RSI);
    remove_at(&mut machine, rsi);
    expect_mismatch(
        &source,
        &machine,
        "missing RSI set-up",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rsi"),
    );
    // ... and a call that no longer declares the register is wrong metadata.
    let (source, mut machine) = pair(Shape::CallSwap);
    let call = find(&machine, X86Opcode::Call)[0];
    inst_mut(&mut machine, call).call_arg_regs.pop();
    expect_mismatch(&source, &machine, "missing argument register", |m| {
        matches!(m, X86BodyMismatch::CallMetadata { .. })
    });

    // An argument clobbered between its set-up and the call.
    let (source, mut machine) = pair(Shape::CallWrap);
    let call = find(&machine, X86Opcode::Call)[0];
    insert_at(
        &mut machine,
        call,
        X86ISelInst::new(X86Opcode::MovRI, vec![preg(RDI), O::Imm(0)]),
    );
    assert_call_argument_mutant_refused(&source, &machine, "clobbered RDI");
    // A clobber the affine check cannot judge (a narrow argument).
    let (source, mut machine) = pair(Shape::CallNarrow);
    let call = find(&machine, X86Opcode::Call)[0];
    insert_at(
        &mut machine,
        call,
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![O::PReg(trust_cg_ir::x86_64_regs::EDI), O::Imm(7)],
        ),
    );
    assert_theorem_refutes(&source, &machine, "clobbered EDI");

    // A call too many, or too few.
    let (source, mut machine) = pair(Shape::CallWrap);
    let call = find(&machine, X86Opcode::Call)[0];
    let extra = inst(&machine, call).clone();
    insert_at(&mut machine, call, extra);
    expect_mismatch(&source, &machine, "an extra call", |m| {
        matches!(m, X86BodyMismatch::CallCount { lir: 1, machine: 2 })
    });
    let (source, mut machine) = pair(Shape::CallVoid);
    let call = find(&machine, X86Opcode::Call)[0];
    remove_at(&mut machine, call);
    expect_mismatch(&source, &machine, "a dropped call", |m| {
        matches!(m, X86BodyMismatch::CallCount { lir: 1, machine: 0 })
    });

    // The result read before the call defines it.
    let (source, mut machine) = pair(Shape::CallWrap);
    let call = find(&machine, X86Opcode::Call)[0];
    let copy = remove_at(&mut machine, call + 1);
    insert_at(&mut machine, call, copy);
    expect_mismatch(
        &source,
        &machine,
        "result read before the call",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rax"),
    );
    // The result of the wrong call: the first call's result copied after the
    // second call reads the second result, which the theorem refutes.
    let (source, mut machine) = pair(Shape::CallSeq);
    let calls = find(&machine, X86Opcode::Call);
    // Removing the copy shifts the second call down by one, so inserting at
    // its old ordinal places the copy right after it.
    let first_copy = remove_at(&mut machine, calls[0] + 1);
    insert_at(&mut machine, calls[1], first_copy);
    assert_theorem_refutes(&source, &machine, "first result read after the second call");

    // Divergence must match: a diverging source whose machine returns, and a
    // returning source whose machine traps.
    let (source, mut machine) = pair(Shape::CallDiverge);
    let trap = find(&machine, X86Opcode::Ud2)[0];
    *inst_mut(&mut machine, trap) = X86ISelInst::new(X86Opcode::Ret, vec![]);
    expect_mismatch(
        &source,
        &machine,
        "returns for a trap",
        |m| matches!(m, X86BodyMismatch::Control { detail, .. } if detail.contains("diverges")),
    );
    let (source, mut machine) = pair(Shape::CallVoid);
    let ret = find(&machine, X86Opcode::Ret)[0];
    *inst_mut(&mut machine, ret) = X86ISelInst::new(X86Opcode::Ud2, vec![]);
    expect_mismatch(
        &source,
        &machine,
        "traps for a return",
        |m| matches!(m, X86BodyMismatch::Control { detail, .. } if detail.contains("returns")),
    );

    // A callee-saved register is preserved across the call: a value parked
    // in RBX would survive, but writing RBX is refused before any theorem.
    let (source, mut machine) = pair(Shape::CallWrap);
    insert_at(
        &mut machine,
        0,
        X86ISelInst::new(X86Opcode::MovRR, vec![preg(RBX), preg(RDI)]),
    );
    expect_mismatch(&source, &machine, "RBX write", |m| {
        matches!(
            m,
            X86BodyMismatch::PreservedWrite {
                register: "rbx",
                ..
            }
        )
    });
}

/// The callee-saved registers survive a call: reading RBX after a call reads
/// the caller's RBX, and the returned value is then that entry value, which
/// the theorem refutes (it is not the callee's result).
#[test]
fn callee_saved_registers_survive_a_call_and_are_judged_by_the_theorem() {
    let (source, mut machine) = pair(Shape::CallWrap);
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    inst_mut(&mut machine, ret_copy).operands[1] = preg(RBX);
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .expect("RBX holds a defined value after the call");
    assert!(refuted_on_samples(owner.obligation()));
}

/// The walk's call clobber set is the IR's System V caller-saved set, and
/// its two register tables partition the sixteen GPR roots: every root a
/// callee may change is clobbered, every other root is preserved (and never
/// written by the body). A narrower clobber set would let a stale read after
/// a call through; the controls in
/// [`a_call_clobbers_every_caller_saved_register`] show that per root.
#[test]
fn the_call_clobber_table_is_the_system_v_caller_saved_set() {
    use trust_cg_ir::x86_64_regs as regs;
    assert_eq!(
        SYSV_CALLER_SAVED_ROOTS.map(X86PReg::new),
        regs::X86_CALLER_SAVED_GPRS
    );
    assert_eq!(
        SYSV_CALLER_SAVED_ROOTS.map(X86PReg::new),
        regs::X86_CALL_CLOBBER_GPRS
    );
    let callee_saved: Vec<X86PReg> = SYSV_PRESERVED_ROOTS
        .iter()
        .filter(|root| **root != RSP)
        .map(|root| X86PReg::new(*root))
        .collect();
    assert_eq!(callee_saved, regs::X86_CALLEE_SAVED_GPRS);
    assert_eq!(regs::RSP.encoding(), RSP);
    for root in 0..16u16 {
        assert_ne!(
            SYSV_CALLER_SAVED_ROOTS.contains(&root),
            SYSV_PRESERVED_ROOTS.contains(&root),
            "{} must be exactly one of clobbered and preserved",
            ROOT_NAMES[root as usize]
        );
    }
    // Every argument register is caller-saved.
    assert!(
        SYSV_ARGUMENT_ROOTS
            .iter()
            .all(|root| SYSV_CALLER_SAVED_ROOTS.contains(root))
    );
}

/// The mismatch predicate of an undefined read of `root` (through any alias).
fn reads_undefined(root: u16) -> impl Fn(&X86BodyMismatch) -> bool {
    move |mismatch| {
        matches!(mismatch, X86BodyMismatch::UndefinedRead { operand, .. }
            if operand == ROOT_NAMES[root as usize])
    }
}

/// After a call every caller-saved register holds nothing but the result
/// bits the call defines: reading one is an undefined read, whether it held
/// an argument, a parameter or a scratch value before the call, and through
/// every width alias. Each control fails if the clobber set loses its root:
/// the read would then see the pre-call value, and a lowering that uses it
/// would be judged as if the callee had preserved it.
#[test]
fn a_call_clobbers_every_caller_saved_register() {
    use trust_cg_ir::x86_64_regs as regs;
    let read_after_call = |shape: Shape, read: X86ISelInst| {
        let (source, mut machine) = pair(shape);
        let after = find(&machine, X86Opcode::Call)[0] + 1;
        insert_at(&mut machine, after, read);
        (source, machine)
    };
    // Each argument register holds an argument at the call (all six are set
    // up for `g6`), and none of them survives it.
    for root in SYSV_ARGUMENT_ROOTS {
        let (source, machine) = read_after_call(
            Shape::CallSix,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(90), preg(root)]),
        );
        expect_mismatch(
            &source,
            &machine,
            &format!("{} read after the call", ROOT_NAMES[root as usize]),
            reads_undefined(root),
        );
    }
    // The same through the 32-, 16- and 8-bit aliases.
    for (opcode, alias, root) in [
        (X86Opcode::MovRR32, regs::ECX, RCX),
        (X86Opcode::MovzxW, regs::DX, RDX),
        (X86Opcode::Movzx, regs::R8B, R8),
        (X86Opcode::MovsxB, regs::R9B, R9),
    ] {
        let (source, machine) = read_after_call(
            Shape::CallSix,
            X86ISelInst::new(opcode, vec![vreg(90), O::PReg(alias)]),
        );
        expect_mismatch(
            &source,
            &machine,
            &format!("{opcode:?} from {alias:?} after the call"),
            reads_undefined(root),
        );
    }
    // A live stale read: `g1(a) + c` with `c` taken from RDX after the call
    // (the selector keeps `c` in a virtual register copied at entry). With
    // RDX preserved this would compute exactly the source's value.
    let (source, mut machine) = pair(Shape::CallAfterThird);
    let add = find(&machine, X86Opcode::AddRR)[0];
    let copy_of_c = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| inst(&machine, *ordinal).operands.get(1) == Some(&preg(RDX)))
        .expect("the entry copy of RDX");
    let c = inst(&machine, copy_of_c).operands[0].clone();
    let reads_c = inst(&machine, add)
        .operands
        .iter()
        .rposition(|operand| *operand == c)
        .expect("the add reads c");
    inst_mut(&mut machine, add).operands[reads_c] = preg(RDX);
    expect_mismatch(
        &source,
        &machine,
        "c read from RDX after the call",
        reads_undefined(RDX),
    );
    // Scratch registers written before the call: R10 and R11 hold a defined
    // value until the call and nothing after it.
    for root in [R10, R11] {
        let (source, mut machine) = pair(Shape::CallSix);
        let call = find(&machine, X86Opcode::Call)[0];
        insert_at(
            &mut machine,
            call,
            X86ISelInst::new(X86Opcode::MovRI, vec![preg(root), O::Imm(1)]),
        );
        let read = X86ISelInst::new(X86Opcode::MovRR, vec![vreg(90), preg(root)]);
        let mut before = machine.clone();
        insert_at(&mut before, call + 1, read.clone());
        source_bound_x86_body(&source, &before, SYSV)
            .unwrap_or_else(|refusal| panic!("{root}: read before the call: {refusal}"));
        insert_at(&mut machine, call + 2, read);
        expect_mismatch(
            &source,
            &machine,
            &format!("{} read after the call", ROOT_NAMES[root as usize]),
            reads_undefined(root),
        );
    }
    // RAX after a call with no result.
    let (source, mut machine) = pair(Shape::CallVoid);
    let call = find(&machine, X86Opcode::Call)[0];
    insert_at(
        &mut machine,
        call,
        X86ISelInst::new(X86Opcode::MovRI, vec![preg(RAX), O::Imm(1)]),
    );
    insert_at(
        &mut machine,
        call + 2,
        X86ISelInst::new(X86Opcode::MovRR, vec![vreg(90), preg(RAX)]),
    );
    expect_mismatch(
        &source,
        &machine,
        "RAX read after a void call",
        reads_undefined(RAX),
    );
}

/// A callee's `u16` result defines AX only: bits 16..63 of RAX are the free
/// input `g{k}`. The correct lowering (MOVZX from AX) certifies; returning
/// RAX, or sign-extending the result, is refuted; a wider copy that is
/// re-extended before use is correct; a result declared at another width is
/// wrong metadata.
#[test]
fn a_u16_call_result_defines_only_ax() {
    use trust_cg_ir::x86_64_regs as regs;
    let (source, machine) = pair(Shape::CallU16Widen);
    let call = find(&machine, X86Opcode::Call)[0];
    assert_eq!(
        inst(&machine, call).call_result_regs,
        Some(vec![X86CallResultReg::new(X86PReg::new(RAX), 16)])
    );
    let copy = call + 1;
    assert_eq!(inst(&machine, copy).opcode, X86Opcode::MovzxW);
    assert_eq!(inst(&machine, copy).operands[1], O::PReg(regs::AX));
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert!(holds_on_samples(owner.obligation()));

    // RAX returned as the widened result: bits 16..63 are not the zero
    // extension the source returns.
    let mut garbage = machine.clone();
    insert_at(
        &mut garbage,
        copy,
        X86ISelInst::new(X86Opcode::MovRR, vec![vreg(90), preg(RAX)]),
    );
    let ret_copy = *find(&garbage, X86Opcode::MovRR).last().unwrap();
    inst_mut(&mut garbage, ret_copy).operands[1] = vreg(90);
    assert_theorem_refutes(&source, &garbage, "RAX of a u16 result returned");
    // The result sign-extended where the source zero-extends it.
    let mut signed = machine.clone();
    let widen = find(&signed, X86Opcode::MovzxW)[1];
    inst_mut(&mut signed, widen).opcode = X86Opcode::MovsxW;
    assert_theorem_refutes(&source, &signed, "a u16 result sign-extended");
    // EAX copied, then re-extended from its low 16 bits: the garbage is
    // masked before anything observes it, so the lowering is correct.
    let mut wide_copy = machine.clone();
    *inst_mut(&mut wide_copy, copy) = X86ISelInst::new(
        X86Opcode::MovRR32,
        vec![inst(&machine, copy).operands[0].clone(), O::PReg(regs::EAX)],
    );
    let owner = source_bound_x86_body(&source, &wide_copy, SYSV).unwrap();
    assert!(holds_on_samples(owner.obligation()));
    // Declared as a 32-bit result.
    let mut declared = machine.clone();
    inst_mut(&mut declared, call).call_result_regs =
        Some(vec![X86CallResultReg::new(X86PReg::new(RAX), 32)]);
    expect_mismatch(&source, &declared, "u16 result declared 32-bit", |m| {
        matches!(m, X86BodyMismatch::CallMetadata { .. })
    });
    // The undefined bits above AX are their own free input.
    assert!(
        owner
            .obligation()
            .inputs
            .contains(&(call_garbage_name(0, 0), 48))
    );
}

/// An 8- or 16-bit physical alias is admitted only as the source operand of
/// an extension that reads exactly its bits, and it names the root the IR
/// encodes: AL..R15B and AX..R15W. Any other use makes no claim, and a read
/// through an alias is judged like a read of its root (a clobbered root is an
/// undefined read; a preserved root's entry value is refuted as a result).
#[test]
fn narrow_aliases_are_admitted_only_as_their_exact_extension_source() {
    use trust_cg_ir::x86_64_regs as regs;
    for root in 0..16u16 {
        let reg = X86PReg::new(root);
        let byte = O::PReg(regs::x86_gpr64_to_gpr8(reg).unwrap());
        let word = O::PReg(regs::x86_gpr64_to_gpr16(reg).unwrap());
        let dword = O::PReg(regs::x86_gpr64_to_gpr32(reg).unwrap());
        let name = ROOT_NAMES[root as usize];
        assert_eq!(narrow_alias(&byte, 8), Some(Root::Physical(root)), "{name}");
        assert_eq!(
            narrow_alias(&word, 16),
            Some(Root::Physical(root)),
            "{name}"
        );
        // The other width, a 32-bit alias and a full register are not
        // narrow aliases.
        assert_eq!(narrow_alias(&byte, 16), None, "{name}");
        assert_eq!(narrow_alias(&word, 8), None, "{name}");
        assert_eq!(narrow_alias(&dword, 8), None, "{name}");
        assert_eq!(narrow_alias(&O::PReg(reg), 16), None, "{name}");
        assert_eq!(extension_source(&byte, 16), None, "{name}");
        assert_eq!(extension_source(&word, 8), None, "{name}");
        assert_eq!(extension_source(&byte, 32), None, "{name}");
        assert_eq!(extension_source(&word, 32), None, "{name}");
        // Never a destination or an ALU operand.
        assert_eq!(gpr(&byte), None, "{name}");
        assert_eq!(gpr(&word), None, "{name}");
    }
    assert_eq!(regs::AL, X86PReg::new(GPR8_ALIAS_BASE));
    assert_eq!(regs::AX, X86PReg::new(GPR16_ALIAS_BASE));
    assert_eq!(regs::DIL.encoding(), GPR8_ALIAS_BASE + RDI);
    assert_eq!(regs::R15W.encoding(), GPR16_ALIAS_BASE + R15);

    // The byte copy of a u8 call result (`Movzx v, AL`) and the word copy of
    // a u16 one (`MovzxW v, AX`), mutated.
    let (narrow_source, narrow) = pair(Shape::CallNarrow);
    let byte_copy = find(&narrow, X86Opcode::Call)[0] + 1;
    assert_eq!(inst(&narrow, byte_copy).operands[1], O::PReg(regs::AL));
    let (word_source, word) = pair(Shape::CallU16Widen);
    let word_copy = find(&word, X86Opcode::Call)[0] + 1;
    assert_eq!(inst(&word, word_copy).operands[1], O::PReg(regs::AX));
    let with_source = |machine: &X86ISelFunction, row: usize, operand: O| {
        let mut machine = machine.clone();
        inst_mut(&mut machine, row).operands[1] = operand;
        machine
    };
    // A width that is not the extension's own: no claim.
    expect_unsupported(
        &narrow_source,
        &with_source(&narrow, byte_copy, O::PReg(regs::AX)),
        "Movzx from AX",
    );
    expect_unsupported(
        &word_source,
        &with_source(&word, word_copy, O::PReg(regs::AL)),
        "MovzxW from AL",
    );
    // An alias as the destination: no claim.
    let mut alias_destination = narrow.clone();
    inst_mut(&mut alias_destination, byte_copy).operands[0] = O::PReg(regs::CL);
    expect_unsupported(&narrow_source, &alias_destination, "Movzx into CL");
    // A clobbered root through its alias: an undefined read.
    for (machine, source, row, alias, root) in [
        (&narrow, &narrow_source, byte_copy, regs::CL, RCX),
        (&narrow, &narrow_source, byte_copy, regs::DIL, RDI),
        (&word, &word_source, word_copy, regs::CX, RCX),
        (&word, &word_source, word_copy, regs::R11W, R11),
    ] {
        expect_mismatch(
            source,
            &with_source(machine, row, O::PReg(alias)),
            &format!("{alias:?} after the call"),
            reads_undefined(root),
        );
    }
    // A preserved root through its alias reads the caller's value, which is
    // not the callee's result.
    assert_theorem_refutes(
        &narrow_source,
        &with_source(&narrow, byte_copy, O::PReg(regs::BL)),
        "BL for AL",
    );
    assert_theorem_refutes(
        &word_source,
        &with_source(&word, word_copy, O::PReg(regs::R12W)),
        "R12W for AX",
    );
}

/// Direct calls outside slice 3 make no claim: they keep today's rows.
#[test]
fn calls_outside_the_slice_three_domain_are_unsupported() {
    let mut cases: Vec<(&str, Function)> = Vec::new();
    let mut builder = ModuleBuilder::new("x86_source_bound_body");
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let variadic = builder.add_vararg_func_type(vec![Ty::U64], vec![Ty::U64]);
    let seven = builder.add_func_type(vec![Ty::U64; 7], vec![Ty::U64]);
    let seven_bool = {
        let mut params = vec![Ty::U64; 6];
        params.push(Ty::Bool);
        builder.add_func_type(params, vec![Ty::U64])
    };
    let wide = builder.add_func_type(vec![Ty::U128], vec![Ty::U64]);
    let floats = builder.add_func_type(vec![Ty::F64], vec![Ty::U64]);
    let bool_arg = builder.add_func_type(vec![Ty::Bool], vec![Ty::U64]);
    let nothing = builder.add_func_type(vec![], vec![]);
    let loc = Ty::PtrConst(Box::new(Ty::U8));
    let printf = builder.declare_function("printf_like", variadic);
    let g7 = builder.declare_function("g7", seven);
    let g7b = builder.declare_function("g7b", seven_bool);
    let g128 = builder.declare_function("g128", wide);
    let gf = builder.declare_function("gf", floats);
    let bg = builder.declare_function("bg", bool_arg);
    let abort = builder.declare_function("abort", nothing);
    let g1 = builder.declare_function("g1", unary);
    let mut function = |name: &str,
                        params: Vec<Ty>,
                        result: Option<Ty>,
                        body: &dyn Fn(
        &mut trust_ir_build::FunctionBuilder<'_>,
        &[trust_ir::ValueId],
    ) -> Option<trust_ir::ValueId>| {
        let signature = builder.add_func_type(params.clone(), result.into_iter().collect());
        let mut f = builder.function(name, signature);
        let entry = f.create_block();
        let args: Vec<_> = params
            .into_iter()
            .map(|ty| f.add_block_param(entry, ty))
            .collect();
        f.switch_to_block(entry);
        match body(&mut f, &args) {
            Some(value) => f.ret(vec![value]),
            None => f.unreachable(),
        }
        f.build();
    };
    function("varargs", vec![Ty::U64], Some(Ty::U64), &|f, a| {
        Some(f.call(printf, vec![a[0], a[0]]))
    });
    function("seven_args", vec![Ty::U64], Some(Ty::U64), &|f, a| {
        Some(f.call(g7, vec![a[0]; 7]))
    });
    // A `bool` argument past the six registers (on the stack) stays outside.
    function(
        "seventh_bool",
        vec![Ty::U64, Ty::Bool],
        Some(Ty::U64),
        &|f, a| {
            let mut args = vec![a[0]; 6];
            args.push(a[1]);
            Some(f.call(g7b, args))
        },
    );
    function("i128_arg", vec![Ty::U64], Some(Ty::U64), &|f, a| {
        let wide = f.zext(Ty::U64, Ty::U128, a[0]);
        Some(f.call(g128, vec![wide]))
    });
    function("f64_arg", vec![Ty::F64], Some(Ty::U64), &|f, a| {
        Some(f.call(gf, vec![a[0]]))
    });
    function("bool_forward", vec![Ty::Bool], Some(Ty::U64), &|f, a| {
        Some(f.call(bg, vec![a[0]]))
    });
    // The census's `#[track_caller]` panic helpers under panic=abort: a dead
    // hidden location parameter, then `abort()`.
    function("panic_helper", vec![loc.clone()], None, &|f, _| {
        f.call_void(abort, vec![]);
        None
    });
    // A load then a call is admitted (slice 4), and so is a private stack
    // slot's address passed to a callee (slice 7: the slot escapes to the
    // call, `slice7::a_cast_slot_address_passed_to_a_call_is_admitted`);
    // the same address also returned stays outside.
    function("slot_escapes", vec![Ty::U64], Some(Ty::U64), &|f, a| {
        let slot = f.alloca(Ty::U64);
        f.store(Ty::U64, slot, a[0]);
        let address = f.cast(trust_ir::CastOp::PtrToInt, Ty::Ptr, Ty::U64, slot);
        f.call(g1, vec![address]);
        Some(address)
    });
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let lir = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap();
    // Slice 11 admits an `i128` argument (a register pair) and a float one
    // (an SSE register), slice 13 a seventh integer argument (on the stack)
    // and slice 15 a `bool` parameter forwarded as a `bool` argument (the
    // selector zero-extends the parameter's low byte at entry): each builds a
    // theorem that holds.
    for name in ["i128_arg", "f64_arg", "seven_args", "bool_forward"] {
        let source = lir
            .iter()
            .map(|(function, _)| function)
            .find(|function| function.name == name)
            .unwrap_or_else(|| panic!("{name} translates"));
        let machine = select(source, X86CallAbi::SystemV);
        let owner = source_bound_x86_body(source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{name}: {refusal}"));
        assert!(holds_on_samples(owner.obligation()), "{name}");
    }
    for name in ["varargs", "seventh_bool", "panic_helper", "slot_escapes"] {
        let source = lir
            .iter()
            .map(|(function, _)| function)
            .find(|function| function.name == name)
            .unwrap_or_else(|| panic!("{name} translates"))
            .clone();
        cases.push((name, source));
    }
    // The panic helper's refusal names the missing observable.
    let (_, helper) = cases
        .iter()
        .find(|(name, _)| *name == "panic_helper")
        .unwrap();
    let helper_machine = select(helper, X86CallAbi::SystemV);
    assert_eq!(
        opcodes(&helper_machine),
        vec![X86Opcode::MovRR, X86Opcode::Call, X86Opcode::Ud2]
    );
    assert!(matches!(
        source_bound_x86_body(helper, &helper_machine, SYSV),
        Err(X86BodyRefusal::Unsupported(
            X86BodyUnsupported::NoObservable
        ))
    ));
    // LIR-level forms the trust-ir builder does not produce here: an invoke,
    // an sret callee, a call whose result type is unknown, a native
    // dependency binding.
    let (wrap, wrap_machine) = pair(Shape::CallWrap);
    let replace_call = |opcode: L| {
        let mut changed = wrap.clone();
        let entry = changed.entry_block;
        for inst in &mut changed.blocks.get_mut(&entry).unwrap().instructions {
            if matches!(inst.opcode, L::Call { .. }) {
                inst.opcode = opcode.clone();
            }
        }
        changed
    };
    cases.push((
        "invoke",
        replace_call(L::Invoke {
            binding: DirectCallBinding::Interposable,
            name: "g1".into(),
            normal_dest: Block(1),
            unwind_dest: Block(2),
        }),
    ));
    cases.push((
        "native dependency",
        replace_call(L::Call {
            name: "g1".into(),
            binding: DirectCallBinding::DeclaredExternalFunction { function: 0 },
        }),
    ));
    let mut sret = wrap.clone();
    sret.sret_arg_callees.insert("g1".into());
    cases.push(("sret callee", sret));
    let mut untyped = wrap.clone();
    untyped.value_types.clear();
    cases.push(("untyped call result", untyped));
    for (what, source) in &cases {
        assert!(!source_admits_x86_body_owner(source, SYSV), "{what}");
        expect_unsupported(source, &wrap_machine, what);
    }
    // Win64 is outside the lane by its convention.
    let win64 = select(&wrap, X86CallAbi::WindowsX64);
    assert!(matches!(
        source_bound_x86_body(&wrap, &win64, Some(X86SourceBoundAbi::WindowsX64)),
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::Abi(_)))
    ));
    // Machine calls outside the register-argument form: an XMM argument
    // register, a variadic AL count. (An indirect call row where the source
    // calls a symbol is a named call-target mismatch, slice 10.)
    let (source, mut machine) = pair(Shape::CallWrap);
    let call = find(&machine, X86Opcode::Call)[0];
    let mut indirect = inst(&machine, call).clone();
    indirect.opcode = X86Opcode::CallR;
    indirect.flags = X86Opcode::CallR.default_flags();
    indirect.operands = vec![vreg(0)];
    *inst_mut(&mut machine, call) = indirect;
    expect_mismatch(&source, &machine, "CallR row", |m| {
        matches!(m, X86BodyMismatch::CallTarget { .. })
    });
    // Slice 11 admits the SSE argument registers, so an XMM register where
    // the source passes an integer is a wrong call row, named.
    let (source, mut machine) = pair(Shape::CallWrap);
    inst_mut(&mut machine, call).call_arg_regs =
        vec![X86CallArgReg::new(trust_cg_ir::x86_64_regs::XMM0, 64)];
    expect_mismatch(&source, &machine, "XMM argument", |m| {
        matches!(m, X86BodyMismatch::CallMetadata { .. })
    });
    let (source, mut machine) = pair(Shape::CallWrap);
    inst_mut(&mut machine, call)
        .call_arg_regs
        .push(X86CallArgReg::new(trust_cg_ir::x86_64_regs::AL, 8));
    expect_unsupported(&source, &machine, "variadic AL");
}

// ---------------------------------------------------------------------------
// Verifier integration (no solver)
// ---------------------------------------------------------------------------

fn promotion_verifier() -> X86FunctionVerifier {
    X86FunctionVerifier::with_config(VerificationConfig::for_proof_promotion())
}

fn without_replay<T>(f: impl FnOnce() -> T) -> T {
    trust_cg_process_env::with_env_edits(|env| {
        env.set("TCG_REFINE_SOLVER", "0");
        env.set("TCG_NO_VERDICT_DB", "1");
        env.set("TCG_CANARY_NO_CACHE", "1");
        f()
    })
}

fn results(report: &crate::FunctionVerificationReport) -> Vec<String> {
    report
        .instructions
        .iter()
        .map(|row| format!("{:?}|{:?}", row.opcode, row.result))
        .collect()
}

#[test]
fn a_mismatch_is_a_named_precondition_failure_under_enforce() {
    without_replay(|| {
        let verifier = promotion_verifier();
        let (source, mut machine) = pair(Shape::Add);
        let add = find(&machine, X86Opcode::AddRR)[0];
        inst_mut(&mut machine, add).opcode = X86Opcode::SubRR;
        let report = verifier.verify_with_lir_source_abi_and_mode(
            &machine,
            Some(&source),
            SYSV,
            ProvenanceXCheckMode::Enforce,
        );
        let Some(FunctionVerificationPreconditionFailure::SourceBoundX86BodyMismatch(
            X86BodyMismatch::ReturnValue { lane: 0 },
        )) = &report.precondition_failure
        else {
            panic!("{:?}", report.precondition_failure)
        };
        assert!(report.instructions.is_empty());
        let text = report.precondition_failure.as_ref().unwrap().to_string();
        assert!(
            text.starts_with("[TCG-SOURCE-BOUND-X86-MISMATCH]"),
            "{text}"
        );
        let inventory = report.emitted_opcode_inventory();
        assert!(!inventory.is_promotable());
        assert!(
            inventory
                .promotion_rejection_reason()
                .unwrap()
                .contains("[TCG-SOURCE-BOUND-X86-MISMATCH]")
        );
        // Warn reports, but never rejects and never credits; Off does not
        // classify. Both keep today's rows.
        for mode in [ProvenanceXCheckMode::Warn, ProvenanceXCheckMode::Off] {
            let report =
                verifier.verify_with_lir_source_abi_and_mode(&machine, Some(&source), SYSV, mode);
            assert!(report.precondition_failure.is_none());
            assert_eq!(report.formally_credited_count(), 0);
        }
    });
}

#[test]
fn replay_refused_leaves_bound_rows_unverified_and_the_inventory_blocked() {
    without_replay(|| {
        let verifier = promotion_verifier();
        for shape in all_shapes() {
            let (source, machine) = pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let report = verifier.verify_with_lir_source_abi_and_mode(
                &machine,
                Some(&source),
                SYSV,
                ProvenanceXCheckMode::Enforce,
            );
            assert!(report.precondition_failure.is_none(), "{shape:?}");
            for row in &report.instructions {
                if owner.covers(row.inst_index) {
                    assert!(
                        matches!(&row.result, InstructionVerificationResult::Unverified { reason }
                            if reason == X86_BODY_NEEDS_REPLAY),
                        "{shape:?} row {}: {:?}",
                        row.inst_index,
                        row.result
                    );
                }
            }
            assert_eq!(report.formally_credited_count(), 0);
            assert_eq!(report.genuinely_verified_count(), 0);
            assert!(
                !report.emitted_opcode_inventory().is_promotable(),
                "{shape:?}"
            );
        }
    });
}

/// The `x86-body-dump` diagnostic writes the query the replay renders, byte
/// for byte: the same obligation under the replay's own configuration, so
/// its budget header follows `TCG_RECON_SOLVER_MS` like the replay's, and
/// not another default.
#[test]
fn the_body_dump_is_the_replayed_query() {
    let dir = tempfile::tempdir().unwrap();
    without_replay(|| {
        trust_cg_process_env::with_env_edits(|env| {
            env.set("TCG_X86_BODY_DUMP", dir.path());
            env.set("TCG_RECON_SOLVER_MS", "1234");
            env.set("TRUST_CG_AY_TIMEOUT_MS", "4321");
            let (source, machine) = pair(Shape::Add);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let report = promotion_verifier().verify_with_lir_source_abi_and_mode(
                &machine,
                Some(&source),
                SYSV,
                ProvenanceXCheckMode::Enforce,
            );
            assert_eq!(report.formally_credited_count(), 0);
            let dumped = std::fs::read_to_string(dir.path().join(format!("{}.smt2", source.name)))
                .expect("a body theorem that did not replay Valid is dumped");
            let replayed = generate_smt2_query_raw(
                owner.obligation(),
                &crate::verdict_db::live_source_bound_config(),
            );
            assert_eq!(dumped, replayed);
            assert!(
                dumped.contains("(set-option :timeout 1234)"),
                "{}",
                dumped.lines().take(3).collect::<Vec<_>>().join("\n")
            );
        })
    });
}

#[test]
fn recording_or_unavailable_tools_never_credit() {
    let verifier = promotion_verifier();
    for shape in [Shape::Add, Shape::BoolIdent, Shape::PtrCast] {
        let (source, machine) = pair(shape);
        // A request captured while tier-0 recording is armed refuses replay.
        let recording = verifier
            .capture_request_with_mode(ProvenanceXCheckMode::Enforce)
            .captured_while_recording();
        let report = verifier.verify_with_request_and_abi(
            &machine,
            Some(&source),
            SYSV,
            &slice22::fixture_module(&source),
            &recording,
        );
        assert_eq!(report.report().formally_credited_count(), 0);
        assert!(!report.report().emitted_opcode_inventory().is_promotable());
        // Unavailable AY and Clean: nothing is credited, nothing fails.
        trust_cg_process_env::with_env_edits(|env| {
            env.set("AY_SOLVER_PATH", "/nonexistent/x86-body-ay");
            env.set("TCG_EXTERNAL_CLEAN_CHECKER", "/nonexistent/x86-body-clean");
            env.set("TCG_NO_VERDICT_DB", "1");
            env.set("TCG_CANARY_NO_CACHE", "1");
            env.set("TCG_NO_CERT_STORE", "1");
            env.remove("TCG_REFINE_SOLVER");
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let report = verifier.verify_with_request_and_abi(
                &machine,
                Some(&source),
                SYSV,
                &slice22::fixture_module(&source),
                &request,
            );
            assert!(!report.report().has_failures(), "{shape:?}");
            assert_eq!(report.report().formally_credited_count(), 0);
            assert!(
                report
                    .report()
                    .instructions
                    .iter()
                    .filter(|row| matches!(&row.result,
                        InstructionVerificationResult::Unverified { reason } if reason == X86_BODY_NEEDS_REPLAY))
                    .count()
                    > 0
            );
            assert!(!report.report().emitted_opcode_inventory().is_promotable());
        });
    }
}

#[test]
fn unsupported_pairs_keep_exactly_todays_rows() {
    without_replay(|| {
        let verifier = promotion_verifier();
        let (add, machine) = pair(Shape::Add);
        let legacy = verifier.verify_with_lir_source_and_mode(
            &machine,
            Some(&add),
            ProvenanceXCheckMode::Enforce,
        );
        for abi in [None, Some(X86SourceBoundAbi::WindowsX64)] {
            let report = verifier.verify_with_lir_source_abi_and_mode(
                &machine,
                Some(&add),
                abi,
                ProvenanceXCheckMode::Enforce,
            );
            assert_eq!(results(&report), results(&legacy), "{abi:?}");
        }
        // An out-of-domain source (an irreducible cycle: slice 12 admits
        // natural loops only) gets no weaker credit either.
        let less = slice12::irreducible_loop();
        let less_machine = select(&less, X86CallAbi::SystemV);
        assert!(!source_admits_x86_body_owner(&less, SYSV));
        let legacy = verifier.verify_with_lir_source_and_mode(
            &less_machine,
            Some(&less),
            ProvenanceXCheckMode::Enforce,
        );
        let report = verifier.verify_with_lir_source_abi_and_mode(
            &less_machine,
            Some(&less),
            SYSV,
            ProvenanceXCheckMode::Enforce,
        );
        assert_eq!(results(&report), results(&legacy));
        assert_eq!(report.formally_credited_count(), 0);
    });
}

// ---------------------------------------------------------------------------
// Transport plumbing (fixture solver/checker; no proof content)
// ---------------------------------------------------------------------------

/// Write an executable fixture script admitted by the `ay_identity` test
/// fixture rule. It is a new file, so it is started once before the solver
/// deadline of [`with_fixture_replay`] (`test_fixtures::warm`).
#[cfg(unix)]
fn fixture_script(dir: &std::path::Path, name: &str, body: &str) -> std::path::PathBuf {
    use crate::ay_identity::test_fixtures::{bind_self, warm, warm_guard};
    use std::os::unix::fs::PermissionsExt;
    let path = dir.join(name);
    std::fs::write(
        &path,
        bind_self(&path, &format!("#!/bin/sh\n{}\n{body}\n", warm_guard())),
    )
    .unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
    warm(&path);
    path
}

/// A fixture checker that accepts every proof it is shown.
#[cfg(unix)]
const FIXTURE_CHECKER_ACCEPTS: &str = "printf 'External certificate verification: PASSED\\nType: \
     Alethe SMT proof\\nProof status: fully verified\\n'";

/// A fixture checker that rejects every proof it is shown.
#[cfg(unix)]
const FIXTURE_CHECKER_REJECTS: &str =
    "printf 'External certificate verification: FAILED\\n'; exit 1";

/// The test-only build record of a fixture AY/checker pair: an overlay record
/// that pins this fixture checker's digest, with the AY bytes declared
/// explicitly (ruling OD-60). A test under it behaves the same in an
/// ordinary build and in an overlay build, whose own record pins the
/// overlay's real Clean and so refuses a fixture checker.
#[cfg(unix)]
fn fixture_pair_record(
    solver: &std::path::Path,
    checker: &std::path::Path,
) -> crate::ay_identity::ToolchainAyRecord {
    let overlay = crate::ay_identity::ToolchainOverlay::new(
        &"f".repeat(64),
        &crate::ay_identity::test_fixtures::sha256_of(checker),
        &"c".repeat(40),
    )
    .expect("the transport fixture has a valid checker digest");
    crate::ay_identity::ToolchainAyRecord::new_overlay(
        solver.parent().unwrap().to_path_buf(),
        Err("transport-only fixture; AY bytes are explicitly declared".into()),
        Some(overlay),
    )
}

/// Run `f` with an explicitly bound transport-fixture pair, every persistent
/// cache off and live replay on. The test-only record pins this fixture's
/// checker, so the building toolchain's real overlay policy is not borrowed
/// for a different pair of executable bytes.
#[cfg(unix)]
fn with_fixture_replay<T>(
    solver: &std::path::Path,
    checker: &std::path::Path,
    f: impl FnOnce() -> T,
) -> T {
    let declaration = crate::ay_identity::test_fixtures::declare(&[solver]);
    let record = fixture_pair_record(solver, checker);
    trust_cg_process_env::with_env_edits(|env| {
        env.set("AY_SOLVER_PATH", solver);
        env.set(
            crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV,
            &declaration,
        );
        env.set("TCG_EXTERNAL_CLEAN_CHECKER", checker);
        env.set("TCG_NO_SOLVER_SERVER", "1");
        env.set("TCG_NO_CERT_STORE", "1");
        env.set("TCG_NO_PROOF_CACHE", "1");
        env.set("TCG_CANARY_NO_CACHE", "1");
        env.set("TCG_NO_VERDICT_DB", "1");
        env.set("TCG_REFINE_SOLVER", "1");
        env.set("TCG_RECON_SOLVER_MS", "5000");
        crate::ay_identity::test_fixtures::with_recorded(record, f)
    })
}

/// Rows the body theorem covers whose result is exactly `expected`.
fn covered_rows_matching(
    owner: &SourceBoundX86Body<'_>,
    report: &crate::FunctionVerificationReport,
    expected: impl Fn(&InstructionVerificationResult) -> bool,
) -> usize {
    report
        .instructions
        .iter()
        .filter(|row| owner.covers(row.inst_index) && expected(&row.result))
        .count()
}

fn is_body_credit(result: &InstructionVerificationResult) -> bool {
    matches!(result, InstructionVerificationResult::Verified {
        strength: VerificationStrength::Formal, degenerate: false, proof_name, ..
    } if proof_name == X86_BODY_OBLIGATION_NAME)
}

fn is_needs_replay(result: &InstructionVerificationResult) -> bool {
    matches!(result, InstructionVerificationResult::Unverified { reason }
        if reason == X86_BODY_NEEDS_REPLAY)
}

/// The mapping from a replay outcome to the row verdict: only `Valid`
/// credits; a refutation fails the rows; no independently checked proof
/// leaves them unverified. `Unknown` (never produced by live replay today)
/// fails closed.
#[test]
fn only_a_valid_replay_outcome_credits_the_covered_rows() {
    use crate::verify::VerificationResult;
    let (source, machine) = pair(Shape::Add);
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    let row = |verdict| {
        crate::x86_64_function_verifier::x86_body_row_result(
            owner.obligation(),
            verdict,
            owner.is_fp_abstract(),
        )
    };
    assert!(is_body_credit(&row(Some(VerificationResult::Valid))));
    assert!(matches!(
        row(Some(VerificationResult::Valid)),
        InstructionVerificationResult::Verified {
            category: crate::proof_database::ProofCategory::X8664Lowering,
            ..
        }
    ));
    assert!(matches!(
        row(Some(VerificationResult::Invalid { counterexample: "e_rdi = 1".into() })),
        InstructionVerificationResult::Failed { proof_name, detail }
            if proof_name == X86_BODY_OBLIGATION_NAME && detail == "e_rdi = 1"
    ));
    assert!(matches!(
        row(Some(VerificationResult::Unknown { reason: "budget".into() })),
        InstructionVerificationResult::Failed { proof_name, detail }
            if proof_name == X86_BODY_OBLIGATION_NAME && detail == "Unknown: budget"
    ));
    assert!(is_needs_replay(&row(None)));
}

/// A fixture AY that reports `unsat` with a proof file, paired with a fixture
/// checker that accepts or rejects, and a fixture AY that reports `unknown`.
/// Only the accepted pair credits: an AY UNSAT without an independently
/// accepted proof, or an inconclusive solve, is never Formal and leaves the
/// covered rows unverified (not failed).
///
/// With the credited pair, two PLAN negative controls run on every host:
/// a stale TV-1 stamp still fails its row through TV-2 although the theorem
/// replays Valid, and the same source paired with another function's stream
/// matches neither the report nor its exports.
#[cfg(unix)]
#[test]
fn only_an_independently_accepted_proof_credits_the_body() {
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dir = tempfile::tempdir().unwrap();
    let proving = fixture_script(
        dir.path(),
        "ay",
        r#"test "$#" = 7 && test "$1" = -smt2 && test "$3" = --strict-proofs || exit 91
printf 'x86 body transport-only fixture proof\n' > "$5"
printf 'unsat\n'"#,
    );
    let inconclusive = fixture_script(
        dir.path(),
        "ay-unknown",
        r#"test "$1" = -smt2 || exit 91
printf 'unknown\n'"#,
    );
    let accept = fixture_script(dir.path(), "clean-accept", FIXTURE_CHECKER_ACCEPTS);
    let reject = fixture_script(dir.path(), "clean-reject", FIXTURE_CHECKER_REJECTS);
    let (source, machine) = pair(Shape::Add);
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    let verifier = promotion_verifier();
    for (solver, checker, credited) in [
        (&proving, &accept, true),
        (&proving, &reject, false),
        (&inconclusive, &accept, false),
    ] {
        with_fixture_replay(solver, checker, || {
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            // The certificate lane's entry point yields the same report and
            // exports (it hashes the verifier input only when it exports).
            let (lane_report, lane_exports) = verifier.verify_for_certificates(
                &machine,
                Some(&source),
                SYSV,
                &slice22::fixture_module(&source),
                &request,
            );
            assert_eq!(format!("{lane_report:?}"), format!("{:?}", report.report()));
            assert_eq!(lane_exports, exports);
            let credited_rows = covered_rows_matching(&owner, report.report(), is_body_credit);
            if !credited {
                assert_eq!(credited_rows, 0, "{:?}", report.report());
                assert_eq!(
                    covered_rows_matching(&owner, report.report(), is_needs_replay),
                    owner.bound_rows().len(),
                    "an unchecked or inconclusive replay leaves every covered row unverified: \
                     {:?}",
                    report.report()
                );
                assert!(!report.report().has_failures(), "{:?}", report.report());
                assert!(!report.report().emitted_opcode_inventory().is_promotable());
                assert!(exports.is_empty());
                return;
            }
            assert_eq!(
                credited_rows,
                owner.bound_rows().len(),
                "{:?}",
                report.report()
            );
            assert!(report.report().emitted_opcode_inventory().is_promotable());
            assert_eq!(exports.len(), owner.bound_rows().len());
            for export in &exports {
                assert_eq!(export.kind(), crate::SourceBoundObligationKind::X86Body);
                assert!(owner.covers(export.instruction_index()));
                assert!(export.matches_x86_input(&machine, Some(&source), SYSV));
                assert!(!export.matches_x86_input(&machine, Some(&source), None));
                assert!(!export.matches_x86_input(
                    &machine,
                    Some(&source),
                    Some(X86SourceBoundAbi::WindowsX64)
                ));
                assert!(!export.matches_aarch64_input(
                    &trust_cg_ir::MachFunction::new(
                        machine.name.clone(),
                        trust_cg_ir::Signature::new(vec![], vec![])
                    ),
                    Some(&source)
                ));
            }

            // The same source paired with another function's stream (renamed
            // so the name guard cannot tell them apart): neither the report
            // nor any export binds it.
            let (_, mut foreign) = pair(Shape::Sub);
            foreign.name = machine.name.clone();
            assert!(!report.matches_x86_input(&foreign, Some(&source), SYSV));
            for export in &exports {
                assert!(!export.matches_x86_input(&foreign, Some(&source), SYSV));
            }

            // A stale TV-1 stamp: the body theorem does not read stamps, so it
            // still replays Valid, and TV-2 still fails the stamped row. A
            // failed report exports nothing and cannot promote.
            let mut stale = machine.clone();
            let add = find(&stale, X86Opcode::AddRR)[0];
            let LoweringProvenance::SourceInst { digest, .. } =
                &mut inst_mut(&mut stale, add).lowering_provenance
            else {
                panic!("the ADD row is source-attributed");
            };
            *digest = SourceInstDigest(digest.0 ^ 1);
            let (report, exports) =
                verifier.verify_with_request_for_export(&stale, Some(&source), SYSV, &request);
            let row = &report.report().instructions[add];
            assert!(
                matches!(&row.result, InstructionVerificationResult::Failed { proof_name, .. }
                    if proof_name == "provenance-crosscheck (TV-2)"),
                "{:?}",
                row.result
            );
            assert_eq!(
                covered_rows_matching(&owner, report.report(), is_body_credit),
                owner.bound_rows().len() - 1,
                "every other covered row keeps the replayed credit: {:?}",
                report.report()
            );
            assert!(report.report().has_failures());
            assert!(!report.report().emitted_opcode_inventory().is_promotable());
            assert!(exports.is_empty(), "a failed report exports nothing");
        });
    }
}

/// A wrong lowering the exact Rust affine check cannot judge (the return copy
/// reads RBX's entry value) builds a theorem; only the replayed refutation
/// keeps it from credit. A fixture AY that refutes the query with a model
/// must FAIL every covered row on every ABI-aware verifier entry point: the
/// rows are neither Formal nor merely unverified, the report has failures,
/// the inventory is not promotable and nothing is exported.
#[cfg(unix)]
#[test]
fn a_refuted_body_fails_its_rows_on_every_verifier_entry_point() {
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dir = tempfile::tempdir().unwrap();
    let refuting = fixture_script(
        dir.path(),
        "ay-refutes",
        r#"test "$1" = -smt2 || exit 91
case "$#" in 2|7) ;; *) exit 92 ;; esac
printf 'sat\n((e_rbx #x0000000000000001))\n'"#,
    );
    let accept = fixture_script(dir.path(), "clean-accept", FIXTURE_CHECKER_ACCEPTS);
    let (source, mut machine) = pair(Shape::Ident);
    let ret_copy = find(&machine, X86Opcode::MovRR)[1];
    inst_mut(&mut machine, ret_copy).operands[1] = preg(RBX);
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .expect("an RBX-dependent value cannot be judged exactly; the theorem decides");
    let verifier = promotion_verifier();
    with_fixture_replay(&refuting, &accept, || {
        let assert_refuted = |report: &crate::FunctionVerificationReport, entry: &str| {
            let failed = covered_rows_matching(&owner, report, |result| {
                matches!(result, InstructionVerificationResult::Failed { proof_name, .. }
                    if proof_name == X86_BODY_OBLIGATION_NAME)
            });
            assert_eq!(failed, owner.bound_rows().len(), "{entry}: {report:?}");
            assert!(report.has_failures(), "{entry}");
            assert_eq!(report.formally_credited_count(), 0, "{entry}");
            assert!(
                !report.emitted_opcode_inventory().is_promotable(),
                "{entry}"
            );
        };
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let (report, exports) =
            verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
        assert_refuted(report.report(), "verify_with_request_for_export");
        assert!(exports.is_empty());
        let report = verifier.verify_with_request_and_abi(
            &machine,
            Some(&source),
            SYSV,
            &slice22::fixture_module(&source),
            &request,
        );
        assert_refuted(report.report(), "verify_with_request_and_abi");
        let (report, exports) = verifier.verify_for_certificates(
            &machine,
            Some(&source),
            SYSV,
            &slice22::fixture_module(&source),
            &request,
        );
        assert_refuted(&report, "verify_for_certificates");
        assert!(exports.is_empty());
        let report = verifier.verify_with_lir_source_abi_and_mode(
            &machine,
            Some(&source),
            SYSV,
            ProvenanceXCheckMode::Enforce,
        );
        assert_refuted(&report, "verify_with_lir_source_abi_and_mode");
    });
}

// ---------------------------------------------------------------------------
// Host qualification and verifier credit (tool-gated: real AY + Clean)
// ---------------------------------------------------------------------------

/// Environment under which the identity-admitted AY and the Clean/Carcara
/// checker this build accepts as its proof authority replay. When either is
/// absent the lane cannot judge, so this fails it, naming what is missing and
/// how to provide it: a lane that cannot replay never passes as a skip
/// (DR-PER-HOST-QUALIFIED-PAIR-20261015, "Every lane fails closed").
///
/// The checker is `TCG_EXTERNAL_CLEAN_CHECKER` when set, otherwise the one
/// production default discovery selects after its capability probe (the
/// `clean` of the Trust toolchain that owns the admitted AY, then aterm's
/// `store/clean/current`); either way the edits pin that exact path, and the
/// authority path must then accept it ([`authorized_checker`]): an overlay
/// build accepts only its overlay's Clean, whatever else is capable. The
/// recorded replayer gaps ([`KNOWN_UNCERTIFIED`]) were measured with Clean
/// 5f09e36c (`store/clean/current` on the qualification host). A test build
/// by the stage-1 toolchain discovers that toolchain's own `clean` first,
/// which accepts the `bitblast_ashr` steps Clean 5f09e36c rejects (measured
/// 2026-09-28); since slice 11 every arithmetic shift by a constant is
/// stated as a sign extension ([`ShiftOp::by_constant`]), whose proof has no
/// such step, and `AshrImm` and `AshrI8Imm` certify under both. The AY is the one `ay_identity` admits:
/// the toolchain AY recorded by this crate's build. A stock (non-Trust) build
/// records none; then, in this crate's unit-test build only,
/// `TCG_X86_BODY_QUALIFY_AY` may name the exact toolchain AY file, whose
/// bytes are admitted through the same digest-compare rule
/// (`ay_identity::test_fixtures`). Both identities are printed.
#[track_caller]
pub(crate) fn replay_environment(test: &str) -> Vec<(&'static str, std::ffi::OsString)> {
    let inputs = ReplayInputs {
        explicit_checker: std::env::var_os("TCG_EXTERNAL_CLEAN_CHECKER"),
        unrecorded_ay: crate::ay_identity::recorded_toolchain_ay_identity()
            .err()
            .map(|refusal| refusal.to_string()),
        qualify_ay: std::env::var_os("TCG_X86_BODY_QUALIFY_AY"),
    };
    let admitted = admit_replay(
        inputs,
        || {
            crate::obligation_cert_store::clean_checker_path().ok_or_else(|| {
                crate::obligation_cert_store::clean_checker_unavailable_reason()
                    .unwrap_or_else(|| "it selected none".to_owned())
            })
        },
        crate::obligation_cert_store::resolve_proof_checker,
        |edits| {
            replay_identity(edits).ok_or_else(|| {
                let detail =
                    with_edits(edits, crate::ay_bridge::proof_toolchain_unavailable_reason)
                        .unwrap_or_else(|| "no reason given".to_owned());
                format!(
                    "no AY is admitted under this environment ({detail}). Provide the AY: the \
                     toolchain AY this build recorded must be present with the bytes it \
                     recorded; rebuild through scripts/trust_cargo.sh with the toolchain that \
                     owns it"
                )
            })
        },
    );
    // A `match`, not a closure, so the panic names the lane's line.
    let (edits, checker, identity) = match admitted {
        Ok(admitted) => admitted,
        Err(missing) => cannot_replay(test, &missing),
    };
    eprintln!(
        "X86_BODY_REPLAY_IDENTITY test={test} ay=[{}] ay_banner=[{}] clean={} \
         clean_sha256={}",
        identity.ay,
        identity.ay_banner,
        checker.display(),
        identity.clean_sha256
    );
    edits
}

/// What [`replay_environment`] admits, in the order a lane relies on: the
/// edits ([`replay_edits`], whose `discover_checker` runs only when no
/// checker is named), then the checker the build's proof authority accepts
/// ([`authorized_checker`] over `resolve_checker`), then the AY
/// (`identify`). The checker comes before the AY because the AY's admission
/// ([`replay_identity`]) probes only the checker's capability: under a
/// checker the authority refuses it would read as a missing AY, or replay
/// with no checker to accept a proof. [`replay_environment`] passes the
/// production discovery, authority and AY admission; the tool-free test
/// `replay_environment_admits_the_ay_only_under_a_checker_the_authority_accepts`
/// holds the order.
fn admit_replay<I>(
    inputs: ReplayInputs,
    discover_checker: impl FnOnce() -> Result<std::path::PathBuf, String>,
    resolve_checker: impl FnOnce() -> Result<(std::path::PathBuf, String), String>,
    identify: impl FnOnce(&[(&'static str, std::ffi::OsString)]) -> Result<I, String>,
) -> Result<AdmittedReplay<I>, String> {
    let edits = replay_edits(inputs, discover_checker)?;
    let (checker, _) = authorized_checker(&edits, resolve_checker)?;
    let identity = identify(&edits)?;
    Ok((edits, checker, identity))
}

/// What [`admit_replay`] admitted: the edits, the checker the build's proof
/// authority accepts, and the AY step's result.
type AdmittedReplay<I> = (
    Vec<(&'static str, std::ffi::OsString)>,
    std::path::PathBuf,
    I,
);

/// Fail a lane that cannot replay, naming what it lacks.
#[track_caller]
fn cannot_replay(test: &str, missing: &str) -> ! {
    panic!(
        "{test} cannot judge: {missing}. A lane that cannot replay fails; it never passes \
         unjudged"
    )
}

/// The checker `edits` name, as `(path, sha256)`, when this build accepts it
/// as its proof authority; otherwise why not and how to provide one.
/// `resolve` is the authority's own discovery
/// ([`crate::obligation_cert_store::resolve_proof_checker`]), run under the
/// edits.
///
/// A capable checker is not enough. An overlay build accepts only the Clean
/// its overlay names and treats any other as ABSENT, while the AY admission
/// ([`replay_identity`]) probes only capability. Under a capable Clean of
/// another revision every lane therefore replayed with no checker to accept
/// a proof: the `MulI16` migration lane compared two absent checker digests
/// and passed, and so did the mutant-envelope lane, whose refutations need no
/// checker (DR-PER-HOST-QUALIFIED-PAIR-20261015, "Every lane fails closed").
fn authorized_checker(
    edits: &[(&'static str, std::ffi::OsString)],
    resolve: impl FnOnce() -> Result<(std::path::PathBuf, String), String>,
) -> Result<(std::path::PathBuf, String), String> {
    with_edits(edits, resolve).map_err(|refused| {
        format!(
            "no Clean/Carcara checker this build accepts as its proof authority: {refused}. \
             Provide the checker: set TCG_EXTERNAL_CLEAN_CHECKER to the one this build \
             accepts ({QUALIFIED_CHECKER_HINT})"
        )
    })
}

/// What [`replay_environment`] reads from the process and the build, apart
/// from the checker discovery it runs only when no checker is named.
struct ReplayInputs {
    /// `TCG_EXTERNAL_CLEAN_CHECKER`, when set.
    explicit_checker: Option<std::ffi::OsString>,
    /// Why this build recorded no toolchain AY; `None` when it recorded one.
    unrecorded_ay: Option<String>,
    /// `TCG_X86_BODY_QUALIFY_AY`, when set.
    qualify_ay: Option<std::ffi::OsString>,
}

/// Where a lane that reads a host's qualification record finds the checker
/// it needs.
const QUALIFIED_CHECKER_HINT: &str = "a lane that reads a host's qualification record needs \
     that host's qualified Clean, the bytes QUALIFIED_CLEAN_SHA256_BY_HOST names for it; on \
     aarch64-apple-darwin that is the bin/clean of the overlay its qualification report names, \
     which the report's commands/qualify.sh sets, and the x86-64 hosts' entries name the Clean \
     their records were measured with";

/// The environment edits a replay runs under, or what is missing and how to
/// provide it. `discover_checker` is consulted only when no checker is named.
fn replay_edits(
    inputs: ReplayInputs,
    discover_checker: impl FnOnce() -> Result<std::path::PathBuf, String>,
) -> Result<Vec<(&'static str, std::ffi::OsString)>, String> {
    let checker = match inputs.explicit_checker {
        Some(checker) if std::path::Path::new(&checker).is_file() => checker,
        Some(checker) => {
            return Err(format!(
                "no Clean/Carcara checker: TCG_EXTERNAL_CLEAN_CHECKER={} names no file. Provide \
                 the checker: set it to the path of a Clean built with carcara-verify \
                 ({QUALIFIED_CHECKER_HINT})",
                std::path::Path::new(&checker).display()
            ));
        }
        None => discover_checker()
            .map_err(|reason| {
                format!(
                    "no Clean/Carcara checker: TCG_EXTERNAL_CLEAN_CHECKER is unset and checker \
                     discovery (the legacy TCG_CLEAN_CHECKER when set, else the default \
                     candidates) found no capable one ({reason}). Provide the checker: set \
                     TCG_EXTERNAL_CLEAN_CHECKER to the path of a Clean built with \
                     carcara-verify ({QUALIFIED_CHECKER_HINT})"
                )
            })?
            .into_os_string(),
    };
    let mut edits: Vec<(&'static str, std::ffi::OsString)> = vec![
        ("TCG_EXTERNAL_CLEAN_CHECKER", checker),
        ("TCG_NO_SOLVER_SERVER", "1".into()),
        ("TCG_NO_CERT_STORE", "1".into()),
        ("TCG_NO_VERDICT_DB", "1".into()),
        ("TCG_CANARY_NO_CACHE", "1".into()),
        ("TCG_REFINE_SOLVER", "1".into()),
    ];
    if let Some(unrecorded) = inputs.unrecorded_ay {
        let provide = "Provide the AY: build through scripts/trust_cargo.sh with a Trust \
                       toolchain (TRUST_TARGO=<toolchain>/bin/targo; a host qualification uses \
                       its overlay's), whose build records the toolchain's bin/ay, or, in a \
                       build that records none, set TCG_X86_BODY_QUALIFY_AY to the absolute \
                       path of the toolchain AY file";
        let Some(ay) = inputs.qualify_ay else {
            return Err(format!(
                "no AY: this build recorded no toolchain AY ({unrecorded}) and \
                 TCG_X86_BODY_QUALIFY_AY is unset. {provide}"
            ));
        };
        let path = std::path::PathBuf::from(&ay);
        if !path.is_absolute() || !path.is_file() {
            return Err(format!(
                "no AY: this build recorded no toolchain AY ({unrecorded}) and \
                 TCG_X86_BODY_QUALIFY_AY={} is not an absolute path to a file. {provide}",
                path.display()
            ));
        }
        edits.push((
            crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV,
            crate::ay_identity::test_fixtures::declare(&[&path]).into(),
        ));
        edits.push((crate::ay_identity::AY_OVERRIDE_ENV, ay));
    }
    Ok(edits)
}

/// A lane that cannot replay is refused, by what it lacks and how to provide
/// it, before anything replays; and the edits pin the checker and the AY it
/// was given. Needs no tool: the inputs are injected.
#[test]
fn replay_environment_names_what_is_missing() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("tool");
    std::fs::write(&file, b"tool").unwrap();
    let missing = dir.path().join("absent");
    let inputs = |checker: Option<&std::path::Path>,
                  unrecorded: Option<&str>,
                  qualify_ay: Option<&std::path::Path>| ReplayInputs {
        explicit_checker: checker.map(|path| path.as_os_str().to_owned()),
        unrecorded_ay: unrecorded.map(str::to_owned),
        qualify_ay: qualify_ay.map(|path| path.as_os_str().to_owned()),
    };
    let none_found = || Err("every candidate was refused".to_owned());
    let unreachable = || -> Result<std::path::PathBuf, String> {
        panic!("discovery runs only when no checker is named")
    };
    let pinned = |edits: &[(&'static str, std::ffi::OsString)], key: &str| {
        edits
            .iter()
            .find(|(name, _)| *name == key)
            .map(|(_, value)| value.clone())
    };

    let refused = replay_edits(inputs(None, None, None), none_found).unwrap_err();
    assert!(
        refused.contains("TCG_EXTERNAL_CLEAN_CHECKER is unset")
            && refused.contains("every candidate was refused")
            && refused.contains("commands/qualify.sh"),
        "{refused}"
    );
    let refused = replay_edits(inputs(Some(&missing), None, None), unreachable).unwrap_err();
    assert!(
        refused.contains("names no file") && refused.contains(&missing.display().to_string()),
        "{refused}"
    );
    let refused =
        replay_edits(inputs(Some(&file), Some("stock build"), None), unreachable).unwrap_err();
    assert!(
        refused.contains("recorded no toolchain AY (stock build)")
            && refused.contains("TCG_X86_BODY_QUALIFY_AY is unset")
            && refused.contains("TRUST_TARGO"),
        "{refused}"
    );
    for ay in [std::path::Path::new("ay"), missing.as_path()] {
        let refused = replay_edits(
            inputs(Some(&file), Some("stock build"), Some(ay)),
            unreachable,
        )
        .unwrap_err();
        assert!(
            refused.contains("is not an absolute path to a file"),
            "{refused}"
        );
    }

    let discovered = file.clone();
    let edits = replay_edits(inputs(None, None, None), move || Ok(discovered)).unwrap();
    assert_eq!(
        pinned(&edits, "TCG_EXTERNAL_CLEAN_CHECKER"),
        Some(file.as_os_str().to_owned())
    );
    assert_eq!(pinned(&edits, crate::ay_identity::AY_OVERRIDE_ENV), None);
    let edits = replay_edits(
        inputs(Some(&file), Some("stock build"), Some(&file)),
        unreachable,
    )
    .unwrap();
    assert_eq!(
        pinned(&edits, crate::ay_identity::AY_OVERRIDE_ENV),
        Some(file.as_os_str().to_owned())
    );
    assert!(
        pinned(
            &edits,
            crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV
        )
        .is_some()
    );
}

/// A capable checker that this build's proof authority refuses fails the lane
/// before anything replays, naming the checker and the bytes the authority
/// wants; the authority accepting it admits it. The authority is the real
/// discovery under an overlay build's pin
/// (`obligation_cert_store::resolve_proof_checker_pinned_for_tests`), so this
/// holds on a build of any kind, and the checker is a stub that passes the
/// control-proof probe. Before [`authorized_checker`] such a checker met
/// every check a lane made: [`replay_edits`]'s presence check and the AY
/// admission's capability probe.
#[cfg(unix)]
#[test]
fn replay_environment_refuses_a_checker_the_proof_authority_refuses() {
    let dir = tempfile::tempdir().unwrap();
    let checker = crate::obligation_cert_store::capable_checker_stub_for_tests(dir.path());
    let digest = crate::lrat_cert::checker_binary_sha256(&checker).expect("the stub's digest");
    let edits = replay_edits(
        ReplayInputs {
            explicit_checker: Some(checker.as_os_str().to_owned()),
            unrecorded_ay: None,
            qualify_ay: None,
        },
        || -> Result<std::path::PathBuf, String> {
            panic!("discovery runs only when no checker is named")
        },
    )
    .expect("a named file passes the presence check");

    let overlay_clean = "0".repeat(64);
    let refused = authorized_checker(&edits, || {
        crate::obligation_cert_store::resolve_proof_checker_pinned_for_tests(&overlay_clean)
    })
    .unwrap_err();
    assert!(
        refused.contains("no Clean/Carcara checker this build accepts as its proof authority")
            && refused.contains(&checker.display().to_string())
            && refused.contains(&format!("names the Clean with sha256 {overlay_clean}"))
            && refused.contains(&format!("this file's sha256 is {digest}"))
            && refused.contains("commands/qualify.sh"),
        "{refused}"
    );

    let accepted = authorized_checker(&edits, || {
        crate::obligation_cert_store::resolve_proof_checker_pinned_for_tests(&digest)
    })
    .expect("the checker the overlay names is the authority");
    assert_eq!(accepted, (checker, digest));
}

/// [`replay_environment`]'s admission ([`admit_replay`]) asks the proof
/// authority before it admits the AY: under a capable checker the authority
/// refuses, the lane's refusal names the checker and the AY step never runs;
/// under the one it accepts, the AY step runs under the edits that pin that
/// checker, and its refusal is the lane's. Needs no tool: the authority is
/// the real discovery under an overlay build's pin, the checker the stub of
/// the test above, the AY step injected. Without the authority step in
/// [`admit_replay`] the first arm admits the AY and this fails.
#[cfg(unix)]
#[test]
fn replay_environment_admits_the_ay_only_under_a_checker_the_authority_accepts() {
    let dir = tempfile::tempdir().unwrap();
    let checker = crate::obligation_cert_store::capable_checker_stub_for_tests(dir.path());
    let digest = crate::lrat_cert::checker_binary_sha256(&checker).expect("the stub's digest");
    let inputs = || ReplayInputs {
        explicit_checker: Some(checker.as_os_str().to_owned()),
        unrecorded_ay: None,
        qualify_ay: None,
    };
    let no_discovery = || -> Result<std::path::PathBuf, String> {
        panic!("discovery runs only when no checker is named")
    };
    let pinned_to = |pin: &str| {
        let pin = pin.to_owned();
        move || crate::obligation_cert_store::resolve_proof_checker_pinned_for_tests(&pin)
    };
    let ay_steps = std::cell::Cell::new(0_u32);

    let refused = admit_replay(inputs(), no_discovery, pinned_to(&"0".repeat(64)), |_| {
        ay_steps.set(ay_steps.get() + 1);
        Ok(())
    })
    .expect_err("a checker the authority refuses fails the lane");
    assert_eq!(
        ay_steps.get(),
        0,
        "the AY was admitted under a checker the authority refuses"
    );
    assert!(
        refused.contains("no Clean/Carcara checker this build accepts as its proof authority")
            && refused.contains(&format!("this file's sha256 is {digest}")),
        "{refused}"
    );

    let (edits, accepted, identity) = admit_replay(
        inputs(),
        no_discovery,
        pinned_to(&digest),
        |edits: &[(&'static str, std::ffi::OsString)]| {
            ay_steps.set(ay_steps.get() + 1);
            Ok(edits
                .iter()
                .find(|(key, _)| *key == "TCG_EXTERNAL_CLEAN_CHECKER")
                .map(|(_, value)| value.clone()))
        },
    )
    .expect("the checker the authority accepts admits the AY step");
    assert_eq!(ay_steps.get(), 1);
    assert_eq!(accepted, checker);
    assert_eq!(identity, Some(checker.as_os_str().to_owned()));
    assert!(
        edits.iter().any(
            |(key, value)| *key == "TCG_EXTERNAL_CLEAN_CHECKER" && value == checker.as_os_str()
        )
    );

    let refused = admit_replay(inputs(), no_discovery, pinned_to(&digest), |_| {
        Err::<(), _>("no AY is admitted under this environment (stub)".to_owned())
    })
    .expect_err("the AY step's refusal fails the lane");
    assert_eq!(refused, "no AY is admitted under this environment (stub)");
}

/// The replayer pair a [`replay_environment`] admits.
pub(crate) struct ReplayIdentity {
    /// The admitted AY as `PinnedAy::describe` prints it: its route, path and
    /// identity (version, build, commit and digest).
    ay: String,
    /// The admitted AY's build identity alone (`ay <version> build <n>
    /// commit <sha>`), the form [`QUALIFIED_AY`] records; `None` for a
    /// fixture with no build.
    ay_build: Option<String>,
    /// Its `--version` banner.
    ay_banner: String,
    /// SHA-256 of the Clean/Carcara checker binary.
    clean_sha256: String,
}

/// The identity of the AY and the checker admitted under `edits`, or `None`
/// when no AY is admitted.
pub(crate) fn replay_identity(
    edits: &[(&'static str, std::ffi::OsString)],
) -> Option<ReplayIdentity> {
    let ay = trust_cg_process_env::with_env_edits(|env| {
        for (key, value) in edits {
            env.set(key, value);
        }
        crate::ay_bridge::admitted_proof_solver()
    })?;
    let ay_banner = ay
        .command()
        .ok()
        .and_then(|mut command| command.arg("--version").output().ok())
        .map(|output| {
            String::from_utf8_lossy(&output.stdout)
                .lines()
                .next()
                .unwrap_or("")
                .to_owned()
        })
        .unwrap_or_default();
    let checker = edits
        .iter()
        .find(|(key, _)| *key == "TCG_EXTERNAL_CLEAN_CHECKER")
        .map(|(_, value)| value.clone())
        .unwrap_or_default();
    let clean_sha256 = std::fs::read(&checker)
        .map(|bytes| {
            use sha2::{Digest, Sha256};
            format!("{:x}", Sha256::digest(bytes))
        })
        .unwrap_or_else(|error| format!("unreadable: {error}"));
    Some(ReplayIdentity {
        ay: ay.describe(),
        ay_build: ay
            .identity()
            .build()
            .map(crate::ay_identity::AyBuildIdentity::describe),
        ay_banner,
        clean_sha256,
    })
}

/// The replayer pair every pinned host-qualification outcome (recorded
/// replayer gaps, encoding evidence) was measured with: AY 0.27.0 build
/// 13556 (`ebde49de3`, binary SHA-256 `55d348f4…`), the `bin/ay` of the
/// local overlay `x86-stage1-ay13556` (`scripts/assemble_trust_overlay.py`
/// over the native stage-1 build; rulings OD-85 and OD-190), and Clean
/// 5f09e36c (`~/clean-5f09`, identified by its binary's SHA-256). Those
/// outcomes are evidence about this pair only. From 2026-10-05 to 2026-10-19
/// the AY was build 12713 (`b1b0b9de0`), and before that the stage-1
/// toolchain's own build 10530 (`d14080122`); the outcomes that moved are in
/// `reports/perf/2026-10-19-darwin-x86-64-ay13556-requalification/` and
/// `reports/perf/2026-10-05-darwin-x86-64-ay12713-requalification/`.
pub(crate) const QUALIFIED_AY: &str =
    "ay 0.27.0 build 13556 commit ebde49de3c2c3b03f3b1a4e5dc60a5b37aa870a0";
/// The qualified checker's binary SHA-256, **per host triple**.
///
/// [`QUALIFIED_AY`] is compared with the AY's build identity (version, build
/// and commit) by equality, which is host independent: one AY revision built
/// on two hosts answers to the same identity.
/// A checker BINARY cannot be, because a Mach-O and an ELF build of one
/// revision are different bytes. Keeping one digest therefore pinned the whole
/// qualification to whichever host recorded it — Darwin, from `~/clean-5f09`
/// (`reports/perf/2026-10-05-darwin-x86-64-ay12713-requalification/`) — and
/// made every `*_qualification::*` test unpassable anywhere else, at any Clean
/// revision. One entry per host, each recorded by a real run on that host.
///
/// This is not a relaxation: each entry is still exact equality against the
/// bytes that ran. Identifying the checker by REVISION instead would be
/// strictly weaker, because two different binaries of one revision would both
/// qualify, and is refused on that ground
/// (DR-QUALIFIED-PAIR-IS-DARWIN-ONLY-20261015).
///
/// An unlisted host has no recorded pair, so its outcomes are not evidence
/// about anything and the assertion refuses rather than comparing them.
///
/// [`QUALIFIED_AY`] is one string for every host. Linux x86-64 requalified
/// its recorded outcomes with build 13556 on 2026-10-20, retaining the same
/// checker bytes. Darwin AArch64 still records build 12713 and remains
/// refused until it re-measures with build 13556; see the per-host records
/// in `x86_source_bound_body_qualified_pair_tests.rs`.
const QUALIFIED_CLEAN_SHA256_BY_HOST: &[(&str, &str)] = &[
    // Darwin x86-64: Clean 5f09e36c at `~/clean-5f09`, the pair every outcome
    // recorded before 2026-10-15 was measured with, and the Clean half of the
    // AY build 13556 pair since 2026-10-19 (the same binary, unchanged).
    (
        "x86_64-apple-darwin",
        "949365b61779ed281fc65677517fa333ab17e91dffa33396746e6a493bf00ac9",
    ),
    // Linux x86-64: the carcara-verify Clean this host's discovery selects
    // (`first-party/clean/target/release/clean` through the aterm store
    // symlink), measured 2026-10-15 with AY build 12713 and retained
    // during the 2026-10-20 build-13556 requalification.
    (
        "x86_64-unknown-linux-gnu",
        "9547de6425a0a520fa40493a03e7307c5ef15f5616b397fdd7392e9f361d6cb8",
    ),
    // Darwin AArch64: Clean `92bcc8979` (`clean 0.9.0+g92bcc8979`, the
    // revision this tree's `Cargo.lock` pinned when the pair was measured;
    // the lock has since moved to `e05c6fdd6`, LD-PIN6382-2), built here with
    // `carcara-verify` and run as the `bin/clean` of a scratch overlay of
    // package 9192 whose `bin/ay` is AY build 12713 built from `b1b0b9de0`
    // (`scripts/assemble_trust_overlay.py`); measured 2026-10-16. Not the
    // package's own Clean 8606, which an ordinary build here selects: it has
    // no rule for this AY's `zero_extend` spelling, its `poly_simp`
    // normalization or three of its `bitblast_*` steps, and rejected 246 of
    // the 396 proofs a newer Clean accepts (DR-PER-HOST-QUALIFIED-PAIR-20261015,
    // "Applied: Darwin AArch64").
    (
        "aarch64-apple-darwin",
        "80090967fcad609d43f42af52d22198702d186e3be8d88656e7658e4cf307116",
    ),
];

/// The qualified checker digest for the host this test binary runs on, or
/// `None` when the host has no recorded pair.
pub(crate) fn qualified_clean_sha256() -> Option<&'static str> {
    let host = current_host_triple();
    QUALIFIED_CLEAN_SHA256_BY_HOST
        .iter()
        .find(|(triple, _)| *triple == host)
        .map(|(_, sha)| *sha)
}

/// This build's target triple, which is the host for a test binary.
fn current_host_triple() -> &'static str {
    // `cfg!` rather than a runtime probe: the digest is a property of the
    // binary format the test binary itself was built for.
    if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        "x86_64-unknown-linux-gnu"
    } else if cfg!(all(target_arch = "x86_64", target_os = "macos")) {
        "x86_64-apple-darwin"
    } else if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
        "aarch64-apple-darwin"
    } else if cfg!(all(target_arch = "aarch64", target_os = "linux")) {
        "aarch64-unknown-linux-gnu"
    } else {
        "unknown"
    }
}

/// This host's qualification record and the witness every reader of it
/// takes. The record's items are private to that module, so no lane here or
/// in a sibling module can read it without first checking the pair.
#[path = "x86_source_bound_body_qualified_pair_tests.rs"]
mod qualified_pair;
pub(crate) use qualified_pair::{
    assert_qualification_replayer, deadline_answer_here, deadline_bound_entries_here,
    gap_applies_here, gap_branch_here, recorded_gap_labels, recorded_gaps, recorded_outcome,
    recorded_proof_gate_class, settle_here,
};

pub(crate) fn with_edits<T>(
    edits: &[(&'static str, std::ffi::OsString)],
    f: impl FnOnce() -> T,
) -> T {
    trust_cg_process_env::with_env_edits(|env| {
        for (key, value) in edits {
            env.set(key, value);
        }
        env.remove("TCG_NO_PROOF_CACHE");
        f()
    })
}

/// Alternative correct machine bodies for admitted sources: the forms the
/// x86 optimizer and other selections produce (immediate ALU forms, LEA as
/// arithmetic, commuted operands). The owner judges any machine body; these
/// are qualified exactly like the selector's own output.
pub(crate) fn machine_variants() -> Vec<(String, Function, X86ISelFunction)> {
    let mut variants = Vec::new();
    // `x + 5` / `x - 5` through the immediate forms, and `x + 5` as LEA.
    for (shape, opcode) in [
        (Shape::AddImm, X86Opcode::AddRI),
        (Shape::SubImm, X86Opcode::SubRI),
    ] {
        let (source, mut machine) = pair(shape);
        let from = if opcode == X86Opcode::AddRI {
            X86Opcode::AddRR
        } else {
            X86Opcode::SubRR
        };
        let row = find(&machine, from)[0];
        let operands = inst(&machine, row).operands.clone();
        *inst_mut(&mut machine, row) = X86ISelInst::new(
            opcode,
            vec![operands[0].clone(), operands[1].clone(), O::Imm(5)],
        );
        variants.push((
            format!("{shape:?}/{opcode:?}"),
            source.clone(),
            machine.clone(),
        ));
        if opcode == X86Opcode::AddRI {
            *inst_mut(&mut machine, row) = X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    operands[0].clone(),
                    O::MemAddr {
                        base: Box::new(operands[1].clone()),
                        disp: 5,
                    },
                ],
            );
            variants.push((format!("{shape:?}/Lea"), source, machine));
        }
    }
    // `a + b` as an unscaled LEA.
    let (source, mut machine) = pair(Shape::Add);
    let row = find(&machine, X86Opcode::AddRR)[0];
    let operands = inst(&machine, row).operands.clone();
    *inst_mut(&mut machine, row) = X86ISelInst::new(
        X86Opcode::LeaSib,
        vec![
            operands[0].clone(),
            O::SibMemAddr {
                base: Box::new(operands[1].clone()),
                index: Box::new(operands[2].clone()),
                scale: 1,
                disp: 0,
            },
        ],
    );
    variants.push(("Add/LeaSib".into(), source, machine));
    // `a + (b << 2)` as a scaled LEA; the shift stays as a dead row.
    let (source, mut machine) = pair(Shape::AddShl2);
    let shl = find(&machine, X86Opcode::ShlRI)[0];
    let shifted = inst(&machine, shl).operands[1].clone();
    let row = find(&machine, X86Opcode::AddRR)[0];
    let operands = inst(&machine, row).operands.clone();
    *inst_mut(&mut machine, row) = X86ISelInst::new(
        X86Opcode::LeaSib,
        vec![
            operands[0].clone(),
            O::SibMemAddr {
                base: Box::new(operands[1].clone()),
                index: Box::new(shifted),
                scale: 4,
                disp: 0,
            },
        ],
    );
    variants.push(("AddShl2/LeaSib".into(), source, machine));
    // Immediate logic forms.
    for (shape, from, to) in [
        (Shape::And, X86Opcode::AndRR, X86Opcode::AndRI),
        (Shape::Or, X86Opcode::OrRR, X86Opcode::OrRI),
        (Shape::Xor, X86Opcode::XorRR, X86Opcode::XorRI),
    ] {
        // `x OP 0x55` from `x OP 0x55` with the constant in a MovRI.
        let mut builder = ModuleBuilder::new("x86_source_bound_body");
        let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut f = builder.function(format!("{}_imm", shape.name()), signature);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let k = f.iconst(Ty::U64, 0x55);
        let op = match shape {
            Shape::And => BinOp::And,
            Shape::Or => BinOp::Or,
            _ => BinOp::Xor,
        };
        let y = f.binop(op, Ty::U64, x, k);
        f.ret(vec![y]);
        f.build();
        let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &builder.build().expect("ModuleBuilder::build: test fixture"),
            trust_cg_lower::GuardCarrierArch::X86_64,
            trust_cg_lower::TlsDialect::default(),
            &permit_unlicensed(),
        )
        .unwrap()
        .remove(0)
        .0;
        let mut machine = select(&source, X86CallAbi::SystemV);
        let row = find(&machine, from)[0];
        let operands = inst(&machine, row).operands.clone();
        *inst_mut(&mut machine, row) = X86ISelInst::new(
            to,
            vec![operands[0].clone(), operands[1].clone(), O::Imm(0x55)],
        );
        variants.push((format!("{shape:?}/{to:?}"), source, machine));
    }
    variants
}

/// Correct lowerings with commuted operands: admitted (the theorem is
/// true), and each is replayed; the host's AY decides which certify.
pub(crate) fn commuted_variants() -> Vec<(String, Function, X86ISelFunction)> {
    let mut variants = Vec::new();
    for (shape, opcode) in [
        (Shape::Add, X86Opcode::AddRR),
        (Shape::And, X86Opcode::AndRR),
        (Shape::Or, X86Opcode::OrRR),
        (Shape::Xor, X86Opcode::XorRR),
        (Shape::Mul, X86Opcode::ImulRR),
        (Shape::AddI32, X86Opcode::AddRR),
    ] {
        let (source, mut machine) = pair(shape);
        let row = find(&machine, opcode)[0];
        inst_mut(&mut machine, row).operands.swap(1, 2);
        variants.push((format!("{shape:?}/commuted"), source, machine));
    }
    variants
}

/// One admitted theorem the qualified AY/Clean pair does NOT certify today:
/// a recorded replayer gap. Each is a correct lowering (it holds on samples),
/// is never refuted, and its rows stay Unverified. The list is the measured
/// outcome on the qualification host ([`QUALIFIED_AY`], Clean 5f09e36c); it
/// is not a credit route and never widens what is admitted.
pub(crate) struct Uncertified {
    /// The case label (shape, or `shape/variant`).
    pub(crate) label: &'static str,
    /// The exact outcome the lane received, `format!("{:?}", AYResult)`.
    pub(crate) outcome: &'static str,
    /// The class `proof_gate` assigns that outcome. A proof-authority
    /// rejection is a SOUNDNESS-class outcome there; the live source-bound
    /// lanes (AArch64 and x86) leave such rows Unverified, never credited
    /// and never Failed (`verdict_db::live_formal_outcome`).
    pub(crate) proof_gate_class: &'static str,
    /// The exact tool output behind the outcome, from replaying the dumped
    /// query (`TCG_X86_BODY_QUALIFY_DUMP`) with
    /// `ay -smt2 Q --strict-proofs --proof P --proof-format alethe` and, when
    /// AY writes a proof, `clean cert verify-external`. For a `Timeout` (the
    /// replay's 30 s deadline expired), what AY answers when the same query
    /// is replayed offline with a 300 s budget.
    pub(crate) tool_output: &'static str,
}

const SELF_CHECK_REJECTED: &str = "Unknown(\"(:reason-unknown (incomplete self-check-rejected))\")";

/// The narrow and commuted multiplies of slice 1. With AY build 10530
/// `MulU32`, `MulI16` and `Mul/commuted` were strict self-check rejections
/// (11.8 s for `MulI16`) and `AddShl2/LeaSib` an incomplete certificate (a
/// `hole` the printer had no pinned-checker spelling for); with build 12713
/// `MulU32` and `AddShl2/LeaSib` certify, and the two that remain run past
/// the 30 s deadline before AY reaches the same rejection. [`QUALIFIED_AY`]
/// (build 13556, 2026-10-19) answers both the same way at the deadline, and
/// offline rejects its own proof of each sooner than build 12713 did (45 s
/// and 151 s, against 84 s and no answer within 297 s). Since slice 19's
/// spelling (OD-195), which spells a one-path theorem's two sides as its one
/// claim, `Mul/commuted` certifies in 0.07 s (one test per process,
/// 2026-10-26, `reports/perf/2026-10-26-darwin-x86-64-slice19-spelling/`)
/// and is no longer a gap; `MulI16` still runs past the deadline.
pub(crate) const KNOWN_UNCERTIFIED: &[Uncertified] = &[Uncertified {
    label: "MulI16",
    outcome: "Timeout",
    proof_gate_class: "PENDING(solver-capacity)",
    tool_output: "ay: no answer within the 30 s deadline; offline with a 300 s budget it \
             computes UNSAT and rejects its own proof after 44.4 s of CPU (build 12713: 83.7 s): \
             `c !! MODEL-UNCONFIRMED [UNCONFIRMED/withheld] (not a refutation — see [AY SOUNDNESS \
             GATE] for caught invalid models) computed UNSAT rejected by mandatory strict \
             certification: strict UNSAT proof validation failed: step t1 uses unsupported hole \
             rule` / `unknown` / `(:reason-unknown (incomplete self-check-rejected))`; no proof for \
             clean",
}];

/// The measured outcome of each call body's UF + world form
/// ([`uf_world_form`]) on the qualification host ([`QUALIFIED_AY`], Clean
/// 5f09e36c), in [`CALLS`] order: evidence for the call encoding, never a
/// credit route. Every form certifies but the `bool`-argument call's (AY's
/// strict certification rejects its own proof: `step t1 uses unverified
/// trust rule`). With AY build 10530, which chose the Ackermann-reduced
/// encoding, none certified: AY rejected its own proof of every form with an
/// argument and gave the no-argument wrapper's an unproved step. The
/// canonical encoding is kept; it is never chosen per AY.
const UF_WORLD_OUTCOMES: &[(&str, &str)] = &[
    ("CallWrap", VERIFIED),
    ("CallSwap", VERIFIED),
    ("CallAfter", VERIFIED),
    ("CallChain", VERIFIED),
    ("CallSeq", VERIFIED),
    ("CallThenCall", VERIFIED),
    ("CallVoid", VERIFIED),
    ("CallDiverge", VERIFIED),
    ("CallDivergeConst", VERIFIED),
    ("CallNarrow", VERIFIED),
    ("CallBoolResult", VERIFIED),
    ("CallBoolArg", SELF_CHECK_REJECTED),
    ("CallI16", VERIFIED),
    ("CallNoArgs", VERIFIED),
    ("CallDeadResult", VERIFIED),
    ("CallSix", VERIFIED),
    ("CallWiden", VERIFIED),
    ("CallU16Widen", VERIFIED),
    ("CallAfterThird", VERIFIED),
];

/// The measured outcome of each several-item theorem's concatenated form
/// ([`concatenated_form`]) on the qualification host, with its item count,
/// in qualification-case order: evidence for the conjunction encoding, never
/// a credit route. Every concatenation certifies, the seven items of the
/// six-argument wrapper included (with AY build 10530 that one was a strict
/// self-check rejection, while its conjunction certified).
const CONCATENATED_OUTCOMES: &[(&str, usize, &str)] = &[
    ("BoolIdent", 2, VERIFIED),
    ("BoolAnd", 2, VERIFIED),
    ("BoolXor", 2, VERIFIED),
    ("CallWrap", 2, VERIFIED),
    ("CallSwap", 3, VERIFIED),
    ("CallAfter", 2, VERIFIED),
    ("CallChain", 3, VERIFIED),
    ("CallSeq", 3, VERIFIED),
    ("CallThenCall", 3, VERIFIED),
    ("CallDivergeConst", 2, VERIFIED),
    ("CallNarrow", 2, VERIFIED),
    ("CallBoolResult", 2, VERIFIED),
    ("CallBoolArg", 2, VERIFIED),
    ("CallI16", 2, VERIFIED),
    ("CallDeadResult", 2, VERIFIED),
    ("CallSix", 7, VERIFIED),
    ("CallWiden", 2, VERIFIED),
    ("CallU16Widen", 2, VERIFIED),
    ("CallAfterThird", 2, VERIFIED),
];

/// The measured outcome of a theorem restated with slice 1's preserved tail
/// ([`append_preserved_tail`]) on the qualification host: evidence for
/// stating the return bits alone, never a credit route. Both theorems
/// certify without the tail. With the tail the commuted add kept a trusted
/// step, so AY published no proof (with AY build 10530, which measured the
/// choice, both were strict self-check rejections); since slice 19's
/// spelling (OD-195), which spells a one-path theorem's two sides as its one
/// claim, it certifies with the tail too (one test per process, 2026-10-26,
/// `reports/perf/2026-10-26-darwin-x86-64-slice19-spelling/`).
const PRESERVED_TAIL_OUTCOMES: &[(&str, &str)] =
    &[("U8Ident", VERIFIED), ("Add/commuted", VERIFIED)];

const VERIFIED: &str = "Verified";

/// The lane's outcome with host paths (temporary proof files, the checker's
/// location) replaced, so the recorded text does not depend on the host.
fn stable_outcome(result: &AYResult) -> String {
    format!("{result:?}")
        .split(' ')
        .map(|word| {
            if word.starts_with('/') {
                "<path>".to_owned()
            } else if word.starts_with("path=/") {
                "path=<path>".to_owned()
            } else {
                word.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn known_uncertified(label: &str) -> Option<&'static Uncertified> {
    KNOWN_UNCERTIFIED.iter().find(|gap| gap.label == label)
}

/// `proof_gate`'s class of a non-passing outcome.
fn proof_gate_class(result: &AYResult) -> &'static str {
    crate::proof_gate::failure_class_of(result).map_or("PASS", |class| class.label())
}

/// Slice 1's observable tail: the seven preserved entry variables, right-
/// nested, appended to both sides (the encoding slice 2 dropped).
fn append_preserved_tail(obligation: &mut ProofObligation) {
    let names: Vec<String> = SYSV_PRESERVED_ROOTS
        .iter()
        .map(|root| entry_name(*root))
        .collect();
    let tail = names
        .iter()
        .rev()
        .map(|name| E::var(name, 64))
        .reduce(|inner, outer| outer.concat(inner))
        .unwrap();
    obligation.trust_ir_expr = obligation.trust_ir_expr.clone().concat(tail.clone());
    obligation.aarch64_expr = obligation.aarch64_expr.clone().concat(tail);
    let declared: Vec<String> = obligation
        .inputs
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let missing: Vec<(String, u32)> = names
        .into_iter()
        .filter(|name| !declared.contains(name))
        .map(|name| (name, 64))
        .collect();
    let arguments = obligation
        .inputs
        .iter()
        .take_while(|(name, _)| name.starts_with("e_"))
        .count();
    obligation.inputs.splice(arguments..arguments, missing);
}

/// The canonical theorem of a call body restated in the form it reduces
/// (module documentation): each callee an uninterpreted function of a world
/// token and its arguments (`uf_r_<callee>` for the result, `uf_w_<callee>`
/// for the next world, one pair per callee symbol), applied on each side to
/// that side's own argument values and world, starting from the one free
/// world `e_world`; the observable is the returned value (when there is one)
/// and the final world, with no argument term. The source's call result is
/// its side's application; the machine's `r{k}` becomes the definition of its
/// side's application. Built only as qualification evidence: it is never an
/// owner and never replayed for credit.
fn uf_world_form(source: &Function, obligation: &ProofObligation) -> ProofObligation {
    use crate::smt::SmtSort;
    let program = admitted_source(source).unwrap();
    assert!(
        !takes_and_returns_bool(source),
        "one walk: the items are the return and the call arguments"
    );
    assert!(!program.calls.is_empty(), "a call body");
    let items = observable_items(obligation);
    let returned = program.return_tys.len();
    assert_eq!(
        items.len(),
        returned
            + program
                .calls
                .iter()
                .map(|call| call.args.len())
                .sum::<usize>()
    );
    let mut definitions: Vec<(String, E)> = obligation
        .preconditions
        .iter()
        .rev()
        .map(|premise| {
            let E::Eq { lhs, rhs } = premise else {
                panic!("premise {premise} is not an equation")
            };
            let E::Var { name, .. } = lhs.as_ref() else {
                panic!("premise {premise} defines no name")
            };
            (name.clone(), rhs.as_ref().clone())
        })
        .collect();
    let is_source_result = |name: &str| {
        name.strip_prefix('s')
            .is_some_and(|k| !k.is_empty() && k.chars().all(|c| c.is_ascii_digit()))
    };
    let world = |side: char, k: usize| {
        if k == 0 {
            E::var("e_world", 64)
        } else {
            E::var(format!("{side}w{k}"), 64)
        }
    };
    let mut offset = returned;
    let calls = program.calls.len();
    for (k, call) in program.calls.iter().enumerate() {
        let arguments = &items[offset..offset + call.args.len()];
        offset += call.args.len();
        let symbol: String = call
            .name
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect();
        let apply = |kind: &str, world: E, side_arguments: Vec<E>, width: u32| E::UF {
            name: format!("uf_{kind}_{symbol}"),
            args: std::iter::once(world).chain(side_arguments).collect(),
            ret_sort: SmtSort::BitVec(width),
        };
        let source_arguments: Vec<E> = arguments.iter().map(|(s, _)| s.clone()).collect();
        let machine_arguments: Vec<E> = arguments.iter().map(|(_, m)| m.clone()).collect();
        for (lane, result) in call.results.iter().enumerate() {
            let bits = result.value_bits;
            let kind = if lane == 0 { "r" } else { "q" };
            let shared = E::var(call_result_name(k, lane), bits);
            let source_result = definitions
                .iter_mut()
                .find(|(name, expr)| is_source_result(name) && *expr == shared)
                .expect("the source defines the call result");
            source_result.1 = apply(kind, world('s', k), source_arguments.clone(), bits);
            definitions.push((
                call_result_name(k, lane),
                apply(kind, world('m', k), machine_arguments.clone(), bits),
            ));
        }
        definitions.push((
            format!("sw{}", k + 1),
            apply("w", world('s', k), source_arguments, 64),
        ));
        definitions.push((
            format!("mw{}", k + 1),
            apply("w", world('m', k), machine_arguments, 64),
        ));
    }
    // Each definition after every definition it reads.
    let defined: HashSet<String> = definitions.iter().map(|(name, _)| name.clone()).collect();
    let mut emitted: HashSet<String> = HashSet::new();
    let mut ordered: Vec<(String, E)> = Vec::new();
    while !definitions.is_empty() {
        let next = definitions
            .iter()
            .position(|(_, expr)| {
                expr.free_vars()
                    .iter()
                    .all(|used| !defined.contains(used) || emitted.contains(used))
            })
            .expect("the definitions are acyclic");
        let (name, expr) = definitions.remove(next);
        emitted.insert(name.clone());
        ordered.push((name, expr));
    }
    let final_world = (world('s', calls), world('m', calls));
    let (trust_ir_expr, aarch64_expr) = if returned == 1 {
        let (source_value, machine_value) = items[0].clone();
        (
            E::bool_const(true),
            source_value
                .eq_expr(machine_value)
                .and_expr(final_world.0.eq_expr(final_world.1)),
        )
    } else {
        final_world
    };
    let inputs = free_inputs_of(obligation)
        .into_iter()
        .filter(|(name, _)| !defined.contains(name))
        .chain(std::iter::once(("e_world".to_owned(), 64)))
        .chain(
            ordered
                .iter()
                .map(|(name, expr)| (name.clone(), expr.bv_width())),
        )
        .collect();
    ProofObligation {
        name: obligation.name.clone(),
        trust_ir_expr,
        aarch64_expr,
        inputs,
        preconditions: ordered
            .into_iter()
            .rev()
            .map(|(name, expr)| {
                let width = expr.bv_width();
                E::var(name, width).eq_expr(expr)
            })
            .collect(),
        fp_inputs: Vec::new(),
        category: obligation.category,
        machine_side_provenance: obligation.machine_side_provenance.clone(),
    }
}

/// A several-item canonical theorem restated as one right-nested
/// concatenation of its items on each side (the encoding slices 1 and 2 used
/// before the conjunction): the same fact in a different query.
fn concatenated_form(obligation: &ProofObligation) -> ProofObligation {
    let items = observable_items(obligation);
    assert!(items.len() > 1, "a several-item theorem");
    let nest = |terms: Vec<E>| {
        terms
            .into_iter()
            .rev()
            .reduce(|tail, head| head.concat(tail))
            .unwrap()
    };
    let mut form = obligation.clone();
    form.trust_ir_expr = nest(items.iter().map(|(source, _)| source.clone()).collect());
    form.aarch64_expr = nest(items.into_iter().map(|(_, machine)| machine).collect());
    form
}

/// Every qualification case: the admitted shapes, the alternative machine
/// forms and the commuted forms.
fn qualification_cases() -> Vec<(String, Function, X86ISelFunction)> {
    let mut cases: Vec<(String, Function, X86ISelFunction)> = all_shapes()
        .into_iter()
        .map(|shape| {
            let (source, machine) = pair(shape);
            (format!("{shape:?}"), source, machine)
        })
        .collect();
    cases.extend(machine_variants());
    cases.extend(commuted_variants());
    cases
}

/// The actual wrong lowerings replayed by host qualification and exported
/// for candidate-cohort diagnostics. The production Rust refusal is bypassed
/// only when constructing their negative-control theorems.
fn qualification_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut refutations: Vec<(&'static str, Function, X86ISelFunction)> = Vec::new();
    let (source, mut machine) = pair(Shape::Add);
    let add = find(&machine, X86Opcode::AddRR)[0];
    inst_mut(&mut machine, add).opcode = X86Opcode::SubRR;
    refutations.push(("SubRR for AddRR", source, machine));
    let (source, mut machine) = pair(Shape::BoolFalse);
    let movri = find(&machine, X86Opcode::MovRI)[0];
    inst_mut(&mut machine, movri).operands[1] = O::Imm(0xfe);
    refutations.push(("bool with bits 1..7 set", source, machine));
    let (source, mut machine) = pair(Shape::ZextU8);
    let movzx = find(&machine, X86Opcode::Movzx)[0];
    inst_mut(&mut machine, movzx).opcode = X86Opcode::MovsxB;
    refutations.push(("MovsxB for Movzx", source, machine));
    let (source, mut machine) = pair(Shape::ZextBool);
    let movzx = find(&machine, X86Opcode::Movzx)[0];
    inst_mut(&mut machine, movzx).opcode = X86Opcode::MovRR32;
    refutations.push(("bool param widened from 32 bits", source, machine));
    let (source, mut machine) = pair(Shape::PtrCast);
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    inst_mut(&mut machine, ret_copy).opcode = X86Opcode::MovRR32;
    refutations.push(("pointer returned through MovRR32", source, machine));
    let (source, mut machine) = pair(Shape::ShlImm);
    let shl = find(&machine, X86Opcode::ShlRI)[0];
    inst_mut(&mut machine, shl).operands[2] = O::Imm(4);
    refutations.push(("shift count 4 for 3", source, machine));
    let (source, mut machine) = pair(Shape::BoolFalse);
    let movri = find(&machine, X86Opcode::MovRI)[0];
    inst_mut(&mut machine, movri).operands[1] = O::Imm(0x100);
    refutations.push(("bool false with EAX bit 8 set", source, machine));
    // Wrong lowerings of an arithmetic shift (certified since slice 11)
    // and of a shape whose correct theorem does not certify.
    let (source, mut machine) = pair(Shape::AshrImm);
    let sar = find(&machine, X86Opcode::SarRI)[0];
    inst_mut(&mut machine, sar).opcode = X86Opcode::ShrRI;
    refutations.push(("ShrRI for SarRI", source, machine));
    let (source, mut machine) = pair(Shape::MulU32);
    let imul = find(&machine, X86Opcode::ImulRR)[0];
    inst_mut(&mut machine, imul).opcode = X86Opcode::AddRR;
    refutations.push(("AddRR for a 32-bit ImulRR", source, machine));
    // Slice 3: wrong call lowerings (with the Rust refusal bypassed).
    let (source, mut machine) = pair(Shape::CallSwap);
    let (rdi, rsi) = (setup_row(&machine, 0, RDI), setup_row(&machine, 0, RSI));
    let (first, second) = (
        inst(&machine, rdi).operands[1].clone(),
        inst(&machine, rsi).operands[1].clone(),
    );
    inst_mut(&mut machine, rdi).operands[1] = second;
    inst_mut(&mut machine, rsi).operands[1] = first;
    refutations.push(("swapped call arguments", source, machine));
    let (source, mut machine) = pair(Shape::CallNarrow);
    let call = find(&machine, X86Opcode::Call)[0];
    insert_at(
        &mut machine,
        call,
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![O::PReg(trust_cg_ir::x86_64_regs::EDI), O::Imm(7)],
        ),
    );
    refutations.push(("argument clobbered before the call", source, machine));
    let (source, mut machine) = pair(Shape::CallWiden);
    let after = find(&machine, X86Opcode::Call)[0] + 1;
    insert_at(
        &mut machine,
        after,
        X86ISelInst::new(X86Opcode::MovRR, vec![vreg(90), preg(RAX)]),
    );
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    inst_mut(&mut machine, ret_copy).operands[1] = vreg(90);
    refutations.push(("undefined RAX bits returned", source, machine));
    let (source, mut machine) = pair(Shape::CallSeq);
    let calls = find(&machine, X86Opcode::Call);
    let first_copy = remove_at(&mut machine, calls[0] + 1);
    insert_at(&mut machine, calls[1], first_copy);
    refutations.push(("first result read after the second call", source, machine));
    let (source, mut machine) = pair(Shape::CallSeq);
    let (a, b) = (setup_row(&machine, 0, RDI), setup_row(&machine, 1, RDI));
    let (first, second) = (
        inst(&machine, a).operands[1].clone(),
        inst(&machine, b).operands[1].clone(),
    );
    inst_mut(&mut machine, a).operands[1] = second;
    inst_mut(&mut machine, b).operands[1] = first;
    refutations.push(("same-callee calls reordered", source, machine));
    let (source, mut machine) = pair(Shape::CallBoolResult);
    let copy = find(&machine, X86Opcode::Call)[0] + 1;
    *inst_mut(&mut machine, copy) = X86ISelInst::new(
        X86Opcode::MovRR32,
        vec![
            inst(&machine, copy).operands[0].clone(),
            O::PReg(trust_cg_ir::x86_64_regs::EAX),
        ],
    );
    refutations.push(("bool call result copied from EAX", source, machine));
    let (source, mut machine) = pair(Shape::CallU16Widen);
    let after = find(&machine, X86Opcode::Call)[0] + 1;
    insert_at(
        &mut machine,
        after,
        X86ISelInst::new(X86Opcode::MovRR, vec![vreg(90), preg(RAX)]),
    );
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    inst_mut(&mut machine, ret_copy).operands[1] = vreg(90);
    refutations.push((
        "undefined RAX bits above a u16 result returned",
        source,
        machine,
    ));
    refutations
}

/// `MulI16`'s legacy right-spine query and its canonical query are inspected
/// under one captured authority: the same solver, checker and deadline, and
/// neither refutes the correct lowering.
///
/// It needs no [`QualifiedPair`](qualified_pair::QualifiedPair): it reads no
/// recorded outcome. Its one pinned answer applies only when the captured
/// solver and checker are the exact binaries it was measured with (their
/// SHA-256 digests, compared below), so under any other pair it asserts only
/// what every admitted pair must show.
#[test]
fn canonical_migration_pairs_original_mul_i16_under_one_captured_authority() {
    let test = "canonical_migration_pairs_original_mul_i16_under_one_captured_authority";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        assert!(!request.recording_active());
        request.with_policy(|| {
            let (source, machine) = pair(Shape::MulI16);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let config = replay_config();
            let legacy = request
                .ay()
                .inspect_legacy_right_spine_for_test(&owner, &config)
                .unwrap();
            let canonical = request
                .ay()
                .inspect_fresh_source_bound(&owner, &config)
                .unwrap();
            assert_eq!(legacy.solver_sha256, canonical.solver_sha256);
            // The same checker by its digest: two absent checkers would
            // compare equal and say nothing.
            assert!(
                legacy.checker_sha256.is_some(),
                "the captured authority binds no checker (checker_path {:?})",
                legacy.checker_path
            );
            assert_eq!(legacy.checker_sha256, canonical.checker_sha256);
            assert_eq!(legacy.timeout_ms, canonical.timeout_ms);
            assert_eq!(legacy.timeout_ms, 30_000);
            assert_eq!(legacy.smt2.len(), canonical.smt2.len());
            assert_ne!(legacy.smt2, canonical.smt2);
            for (form, diagnostic) in [("legacy", &legacy), ("canonical", &canonical)] {
                assert!(!diagnostic.producer_compact);
                assert_eq!(diagnostic.smt2, diagnostic.producer_smt2);
                assert!(
                    !diagnostic.candidate_debug.contains("CounterExample"),
                    "correct original {form} lowering was refuted: {diagnostic:?}"
                );
                println!(
                    "X86_CANONICAL_MIGRATION_DIAGNOSTIC form={form} proof_credit=false {}",
                    serde_json::to_string(diagnostic).unwrap()
                );
            }
            // Pin this measured pair's baseline attribution, not another
            // host's QUALIFIED_AY/Clean ledger and not a proof-positive gate.
            if legacy.solver_sha256
                == "40e852cc7fa3a3289f17a47b5a8d6d1a5218177b4a95087538ff2c3d702ac7a8"
                && legacy.checker_sha256.as_deref()
                    == Some("9c594e838ff7e73815977c2d675238828f82417e77986abfe38d75b8ab060e16")
            {
                for diagnostic in [&legacy, &canonical] {
                    assert!(diagnostic.output_available);
                    assert!(diagnostic.solve_error.is_none());
                    assert_eq!(diagnostic.stdout.trim(), "unknown");
                    assert!(
                        diagnostic
                            .stderr
                            .contains("(:reason-unknown (incomplete self-check-rejected))")
                    );
                    assert!(
                        diagnostic
                            .stderr
                            .contains("strict UNSAT proof validation failed")
                    );
                    assert!(diagnostic.proof.is_none());
                    assert_eq!(diagnostic.checker_accepted, None);
                }
            }
        });
    });
}

/// Step 1 of each slice: the canonical queries, generated THROUGH THE REAL
/// BUILDER, replay on this host's admitted AY with a Clean-accepted proof (or
/// are recorded gaps with their exact outcome and class), the rejected
/// encodings replay to their recorded outcomes, and wrong lowerings (the same
/// builder, with the Rust refusal bypassed) are refuted by AY with a
/// counterexample. Every replay runs and prints first; the recorded outcomes
/// are then compared only under the replayer pair they were measured with
/// ([`assert_qualification_replayer`]), so under another pair the lane still
/// checks that no correct lowering is refuted and every wrong one is, then
/// fails naming the pair.
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there, so
/// the exact AY/Clean output of a gap can be reproduced outside the test.
#[test]
fn host_qualification_replays_the_canonical_body_theorems() {
    let test = "host_qualification_replays_the_canonical_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let (uncertified, tail_outcomes, uf_outcomes, concatenated) = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let cases = qualification_cases();
        let mut uncertified: Vec<(String, String, &'static str)> = Vec::new();
        for (label, source, machine) in &cases {
            let owner = source_bound_x86_body(source, machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            assert!(holds_on_samples(owner.obligation()), "{label}");
            if let Some(dir) = &dump {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(
                    dir.join(format!("{}.smt2", label.replace('/', "__"))),
                    generate_smt2_query_raw(owner.obligation(), &replay_config()),
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let result = request
                .ay()
                .verify_fresh_source_bound(&owner, &replay_config());
            eprintln!(
                "X86_BODY_QUALIFICATION shape={label} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            if result != AYResult::Verified {
                eprintln!(
                    "X86_BODY_QUALIFICATION gap={label} outcome={result:?} proof_gate_class={}",
                    proof_gate_class(&result)
                );
                if let Some(gap) = known_uncertified(label) {
                    eprintln!(
                        "X86_BODY_QUALIFICATION gap={label} recorded tool output: {}",
                        gap.tool_output
                    );
                }
                uncertified.push((
                    label.clone(),
                    stable_outcome(&result),
                    proof_gate_class(&result),
                ));
            }
        }
        // Evidence for the one canonical encoding (module documentation):
        // slice 1 appended the seven preserved entry variables to both
        // sides. The tail-free forms are among the cases above; the tailed
        // forms replay to their recorded outcomes.
        let mut tail_outcomes = Vec::new();
        for (label, _) in PRESERVED_TAIL_OUTCOMES {
            let (_, source, machine) = cases.iter().find(|(case, ..)| case == label).unwrap();
            let mut tailed = theorem_without_affine_refusal(source, machine, SYSV).unwrap();
            append_preserved_tail(&mut tailed);
            let result =
                crate::ay_bridge::verify_with_cli_raw_attributed(&tailed, &replay_config()).result;
            eprintln!("X86_BODY_QUALIFICATION preserved-tail={label} result={result:?}");
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: the preserved tail of a correct lowering was refuted: {result:?}"
            );
            tail_outcomes.push(((*label).to_owned(), stable_outcome(&result)));
        }
        // Evidence for the call encoding (module documentation): every call
        // body's theorem restated with each callee as an uninterpreted
        // function of a world token and its arguments, and no argument
        // observable. The canonical (Ackermann-reduced) form of each body
        // certifies above; the recorded outcome of each UF + world form is
        // this host's.
        let mut uf_outcomes = Vec::new();
        for shape in CALLS {
            let label = format!("{shape:?}");
            let (_, source, machine) = cases.iter().find(|(case, ..)| *case == label).unwrap();
            // The plain spelling's claims (slice 18 value-numbers the
            // canonical one's).
            let plain = plain_theorem(source, machine);
            let form = uf_world_form(source, &plain);
            let result =
                crate::ay_bridge::verify_with_cli_raw_attributed(&form, &replay_config()).result;
            eprintln!("X86_BODY_QUALIFICATION uf-world={label} result={result:?}");
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: the UF + world form of a correct lowering was refuted: {result:?}"
            );
            uf_outcomes.push((label, stable_outcome(&result)));
        }
        // The UF + world form is a statement AY can refute: swapped call
        // arguments make the two sides apply the callee to different values.
        let (source, mut machine) = pair(Shape::CallSwap);
        let (rdi, rsi) = (setup_row(&machine, 0, RDI), setup_row(&machine, 0, RSI));
        let (first, second) = (
            inst(&machine, rdi).operands[1].clone(),
            inst(&machine, rsi).operands[1].clone(),
        );
        inst_mut(&mut machine, rdi).operands[1] = second;
        inst_mut(&mut machine, rsi).operands[1] = first;
        let swapped = uf_world_form(&source, &plain_theorem(&source, &machine));
        let result =
            crate::ay_bridge::verify_with_cli_raw_attributed(&swapped, &replay_config()).result;
        eprintln!("X86_BODY_QUALIFICATION uf-world-refutation=swapped result={result:?}");
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "the UF + world form of swapped arguments must be refuted: {result:?}"
        );
        // Evidence for the conjunction (`build_theorem`): every theorem
        // with several observed items restated as one concatenation of its
        // items, the encoding slices 1 and 2 used.
        let mut concatenated = Vec::new();
        for (label, source, machine) in &cases {
            // The plain spelling's items (slice 18 value-numbers the
            // canonical one's), without slice 23's operand claims, which are
            // no observable item (OD-205): this is slices 1 and 2's
            // evidence for their encoding.
            let theorem = with_arithmetic_pairing(false, || plain_theorem(source, machine));
            let items = observable_items(&theorem).len();
            if items < 2 {
                continue;
            }
            let result = crate::ay_bridge::verify_with_cli_raw_attributed(
                &concatenated_form(&theorem),
                &replay_config(),
            )
            .result;
            eprintln!(
                "X86_BODY_QUALIFICATION concatenated={label} items={items} result={result:?}"
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: the concatenated form of a correct lowering was refuted: {result:?}"
            );
            concatenated.push((label.clone(), items, stable_outcome(&result)));
        }
        // Refutation through the real builder: wrong lowerings in every
        // slice-2 and slice-3 class.
        let refutations = qualification_refutations();
        for (label, source, machine) in &refutations {
            let theorem = theorem_without_affine_refusal(source, machine, SYSV).unwrap();
            let refuted =
                crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config());
            eprintln!(
                "X86_BODY_QUALIFICATION refutation={label} result={:?}",
                refuted.result
            );
            assert!(
                matches!(refuted.result, AYResult::CounterExample(_)),
                "{label} must be refuted: {:?}",
                refuted.result
            );
        }
        (uncertified, tail_outcomes, uf_outcomes, concatenated)
    });
    // Every outcome below is compared with a record of one replayer pair:
    // only under that pair.
    let qualified = assert_qualification_replayer(&edits);
    for (label, outcome, class) in &uncertified {
        let Some(gap) = known_uncertified(label) else {
            continue;
        };
        assert!(
            !gap.tool_output.is_empty(),
            "{label}: the exact tool output must be recorded"
        );
        if let Some(measured) =
            deadline_answer_here("KNOWN_UNCERTIFIED", label, outcome, class, &qualified)
        {
            // Deadline-bound on this host: any answer measured for it
            // there, and no other.
            assert!(
                measured,
                "{label}: {outcome} / {class} is not an answer measured for it at the deadline \
                 on this host"
            );
        } else {
            assert_eq!(
                outcome,
                recorded_outcome(gap, &qualified),
                "{label}: recorded outcome"
            );
            assert_eq!(
                *class,
                recorded_proof_gate_class(gap, &qualified),
                "{label}: recorded proof_gate class"
            );
        }
    }
    let labels: Vec<&str> = uncertified
        .iter()
        .map(|(label, ..)| label.as_str())
        .collect();
    let recorded: Vec<&str> =
        recorded_gap_labels(KNOWN_UNCERTIFIED, "KNOWN_UNCERTIFIED", &qualified);
    assert_eq!(
        labels, recorded,
        "the certified set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
    let recorded: Vec<(String, String)> = PRESERVED_TAIL_OUTCOMES
        .iter()
        .map(|(label, outcome)| ((*label).to_owned(), (*outcome).to_owned()))
        .collect();
    assert_eq!(
        tail_outcomes, recorded,
        "the slice-1 preserved tail changed outcome on this host; review the encoding note"
    );
    let recorded: Vec<(String, String)> = UF_WORLD_OUTCOMES
        .iter()
        .map(|(label, outcome)| ((*label).to_owned(), (*outcome).to_owned()))
        .collect();
    assert_eq!(
        uf_outcomes, recorded,
        "the UF + world call encoding changed outcome on this host; review the call \
         encoding note"
    );
    let recorded: Vec<(String, usize, String)> = CONCATENATED_OUTCOMES
        .iter()
        .map(|(label, items, outcome)| ((*label).to_owned(), *items, (*outcome).to_owned()))
        .collect();
    assert_eq!(
        concatenated, recorded,
        "the concatenated encoding changed outcome on this host; review the encoding note \
         in build_theorem"
    );
}

/// With the real tools, every covered row is Formal under the body theorem,
/// the function is promotable, exports bind the ABI, a stale TV-1 stamp
/// still fails its row although the theorem is valid, a wrong value the
/// Rust check cannot judge is refuted by the replayed query (rows Failed),
/// and a correct body whose theorem the host AY cannot certify stays
/// Unverified (never Failed, never Formal). The fixture-transport tests above
/// run the stale-stamp, foreign-stream and refutation controls on every host.
#[test]
fn host_qualification_verifier_credits_every_bound_row_with_the_replayed_body_theorem() {
    let test = "host_qualification_verifier_credits_every_bound_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    // Which shapes must carry credit is the recorded gap set of one replayer
    // pair: check the pair before the first replay.
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in all_shapes() {
            let label = format!("{shape:?}");
            if gap_applies_here(KNOWN_UNCERTIFIED, "KNOWN_UNCERTIFIED", &label, &qualified) {
                continue;
            }
            let (source, machine) = pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            let rows = &report.report().instructions;
            for row in rows {
                if owner.covers(row.inst_index) {
                    assert!(
                        matches!(&row.result, InstructionVerificationResult::Verified {
                            proof_name, strength: VerificationStrength::Formal,
                            degenerate: false, ..
                        } if proof_name == X86_BODY_OBLIGATION_NAME),
                        "{shape:?} row {}: {:?}",
                        row.inst_index,
                        row.result
                    );
                }
            }
            assert!(report.report().genuinely_verified_count() > 0);
            let inventory = report.report().emitted_opcode_inventory();
            assert!(inventory.is_promotable(), "{shape:?}: {inventory:?}");
            assert!(
                inventory
                    .entries
                    .iter()
                    .filter(|entry| matches!(
                        entry.opcode,
                        crate::function_verifier::InstructionOpcode::X86_64(
                            X86Opcode::Jmp | X86Opcode::Ret
                        )
                    ))
                    .all(|entry| entry.status == OpcodeInventoryStatus::CoveredElsewhere)
            );
            assert_eq!(exports.len(), owner.bound_rows().len());
            assert!(report.matches_x86_input(&machine, Some(&source), SYSV));
            assert!(!report.matches_x86_input(&machine, Some(&source), None));
            assert!(!report.matches_x86_input(
                &machine,
                Some(&source),
                Some(X86SourceBoundAbi::WindowsX64)
            ));
            for export in &exports {
                assert!(export.matches_x86_input(&machine, Some(&source), SYSV));
            }
            // The same source paired with another function's stream.
            let (_, other) = pair(if shape == Shape::Add {
                Shape::Sub
            } else {
                Shape::Add
            });
            let mut other = other;
            other.name = machine.name.clone();
            assert!(!report.matches_x86_input(&other, Some(&source), SYSV));
        }

        // A stale TV-1 stamp: TV-2 fails the row although the theorem holds.
        let (source, mut machine) = pair(Shape::Add);
        let add = find(&machine, X86Opcode::AddRR)[0];
        let LoweringProvenance::SourceInst { digest, .. } =
            &mut inst_mut(&mut machine, add).lowering_provenance
        else {
            panic!("the ADD row is source-attributed");
        };
        *digest = SourceInstDigest(digest.0 ^ 1);
        let (report, exports) =
            verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
        let row = &report.report().instructions[add];
        assert!(
            matches!(&row.result, InstructionVerificationResult::Failed { proof_name, .. }
                if proof_name == "provenance-crosscheck (TV-2)"),
            "{:?}",
            row.result
        );
        assert!(report.report().has_failures());
        assert!(exports.is_empty(), "a failed report exports nothing");

        // Wrong values the exact Rust affine check cannot judge: the return
        // copy reads RBX's entry value, and a bool result keeps bits 1..7
        // set. The admitted AY refutes the theorem, so every covered row
        // fails.
        let (source, mut ident) = pair(Shape::Ident);
        let ret_copy = find(&ident, X86Opcode::MovRR)[1];
        inst_mut(&mut ident, ret_copy).operands[1] = preg(RBX);
        let (bool_source, mut dirty_bool) = pair(Shape::BoolFalse);
        let movri = find(&dirty_bool, X86Opcode::MovRI)[0];
        inst_mut(&mut dirty_bool, movri).operands[1] = O::Imm(0xfe);
        for (source, machine) in [(&source, &ident), (&bool_source, &dirty_bool)] {
            let owner = source_bound_x86_body(source, machine, SYSV).unwrap();
            let (report, exports) =
                verifier.verify_with_request_for_export(machine, Some(source), SYSV, &request);
            assert_eq!(
                covered_rows_matching(&owner, report.report(), |result| matches!(
                    result,
                    InstructionVerificationResult::Failed { proof_name, .. }
                        if proof_name == X86_BODY_OBLIGATION_NAME
                )),
                owner.bound_rows().len(),
                "{:?}",
                report.report()
            );
            assert!(report.report().has_failures());
            assert!(exports.is_empty());
        }

        // A correct body the host AY cannot certify: Unverified, not Failed.
        for (label, source, machine) in qualification_cases() {
            if !gap_applies_here(KNOWN_UNCERTIFIED, "KNOWN_UNCERTIFIED", &label, &qualified) {
                continue;
            }
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            assert_eq!(
                covered_rows_matching(&owner, report.report(), is_needs_replay),
                owner.bound_rows().len(),
                "{label}: {:?}",
                report.report()
            );
            assert!(!report.report().has_failures(), "{label}");
            assert!(!report.report().emitted_opcode_inventory().is_promotable());
            assert!(exports.is_empty());
        }
    });
}

/// The budget of the deadline-bound record's offline replays (the report's
/// `commands/offline_replay.py --budget-ms 300000`), ten times the lanes' 30 s
/// deadline.
const DEADLINE_BOUND_BUDGET_MS: u64 = 300_000;

/// The qualification case `label` of `table_name`, for the tables whose gap
/// lanes read the deadline-bound record (slices 1, 12, 14, 20 and 24c). Any other
/// table's lane keeps its exact comparison and fails closed on an entry for
/// it, and so does this.
fn deadline_bound_case(table_name: &str, label: &str) -> (Function, X86ISelFunction) {
    let found = match table_name {
        "KNOWN_UNCERTIFIED" => qualification_cases()
            .into_iter()
            .find(|(case, ..)| case == label)
            .map(|(_, source, machine)| (source, machine)),
        "KNOWN_UNCERTIFIED_SLICE_TWELVE" => slice12::SLICE_TWELVE
            .into_iter()
            .find(|shape| format!("{shape:?}") == label)
            .map(slice12::slice12_pair),
        "KNOWN_UNCERTIFIED_SLICE_FOURTEEN" => slice14::SLICE_FOURTEEN
            .into_iter()
            .find(|shape| format!("{shape:?}") == label)
            .map(slice14::slice14_pair),
        "KNOWN_UNCERTIFIED_SLICE_TWENTY" => slice20::SLICE_TWENTY
            .into_iter()
            .find(|shape| format!("{shape:?}") == label)
            .map(slice20::slice20_pair),
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR_C" => slice24c_qualification::qualification_subjects()
            .into_iter()
            .find(|(subject, ..)| subject == label)
            .map(|(_, source, machine)| (source, machine)),
        other => panic!(
            "{other}: no lane of this table reads DEADLINE_BOUND_HERE_BY_HOST, so the record \
             may hold no entry for it ({label})"
        ),
    };
    found.unwrap_or_else(|| panic!("{table_name} has no qualification case {label}"))
}

/// Each label deadline-bound on this host (`DEADLINE_BOUND_HERE_BY_HOST`, in
/// [`qualified_pair`]), replayed once more through the lanes' own route (AY,
/// then Clean's check of its proof), with the 300 s budget the record's
/// offline replays used ([`DEADLINE_BOUND_BUDGET_MS`]). The 30 s lanes accept
/// `Timeout` for a label that some runs certify, so they cannot notice one
/// ceasing to certify on this host altogether; this lane does:
///
/// * a label the record says some runs certify must certify with the budget.
///   One that answers anything else no longer certifies here, and the record
///   is wrong; one that runs past the budget may instead have met a host
///   loaded beyond the record's measurements (`GuardThenCall` has taken
///   92.8 s and 224.9 s of it at 1-minute loads in the twenties), so the
///   message says to re-run it on a quieter host before re-qualifying;
/// * a label the record says no run certifies (`MulI16` on
///   `aarch64-apple-darwin`) must not certify, and must give one of the
///   answers measured for it: one that certifies is a strengthening the
///   record must take, and one that answers otherwise is an unmeasured
///   answer the record must take.
///
/// Every label replays before the lane judges any, except that a refuted
/// label fails the lane at once, and it fails naming each label that broke
/// the record. It checks the pair before anything else (every lane that
/// reads a record checks it before reading; some replay first); on a host
/// whose record holds no deadline-bound label it then
/// passes, saying so, because there is nothing that could stop certifying
/// unnoticed. `#[ignore]`d because it takes minutes per label. On
/// `aarch64-apple-darwin` the qualification command
/// (`reports/perf/2026-10-16-darwin-aarch64-ay12713-qualification/commands/qualify.sh`)
/// runs it after `--lib _qualification`; the x86-64 hosts' records have no
/// such command, and this lane runs there by the same exact name with that
/// host's qualified Clean named. Alone, on the Darwin AArch64 pair (`OV` is
/// its overlay), it is:
///
/// ```text
/// env TRUST_TARGO="$OV/bin/targo" TCG_EXTERNAL_CLEAN_CHECKER="$OV/bin/clean" \
///     scripts/trust_cargo.sh test --locked -p trust-cg-verify --lib \
///     x86_source_bound_body::tests::host_qualification_replays_each_deadline_bound_label_with_the_recorded_budget \
///     -- --ignored --exact --nocapture
/// ```
#[test]
#[ignore = "explicit lane: replays each deadline-bound label with a 300 s budget"]
fn host_qualification_replays_each_deadline_bound_label_with_the_recorded_budget() {
    let test = "host_qualification_replays_each_deadline_bound_label_with_the_recorded_budget";
    let edits = replay_environment(test);
    let qualified = assert_qualification_replayer(&edits);
    let entries = deadline_bound_entries_here(&qualified);
    if entries.is_empty() {
        // Judged, not skipped: the pair is the qualified one, and this
        // host's record names no label whose 30 s answer varies, so no
        // label of it can stop certifying unnoticed.
        eprintln!(
            "X86_DEADLINE_BOUND_BUDGET host={} labels=0: this host's record holds no \
             deadline-bound label",
            current_host_triple()
        );
        return;
    }
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let budget = AYConfig {
        timeout_ms: DEADLINE_BOUND_BUDGET_MS,
        ..replay_config()
    };
    let seconds = DEADLINE_BOUND_BUDGET_MS / 1000;
    let findings = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut findings = Vec::new();
        for (table_name, bound) in &entries {
            let label = bound.label;
            let (source, machine) = deadline_bound_case(table_name, label);
            let owner = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let started = std::time::Instant::now();
            let result = request.ay().verify_fresh_source_bound(&owner, &budget);
            let (outcome, class) = (stable_outcome(&result), proof_gate_class(&result));
            eprintln!(
                "X86_BODY_DEADLINE_BOUND_BUDGET table={table_name} label={label} \
                 budget_ms={DEADLINE_BOUND_BUDGET_MS} result={outcome} proof_gate_class={class} \
                 ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            let certifies = result == AYResult::Verified;
            if bound.some_runs_certify() {
                if result == AYResult::Timeout {
                    findings.push(format!(
                        "{label} ({table_name}): the record says some runs certify it at the \
                         30 s deadline, and it ran past the {seconds} s budget. On a host \
                         loaded beyond the record's measurements that can be load, not \
                         capability: re-run this lane on a quieter host first. If it runs past \
                         the budget there too, it no longer certifies on this host: re-qualify \
                         it, updating DEADLINE_BOUND_HERE_BY_HOST, LIMITATIONS.md and the \
                         host's report together"
                    ));
                } else if !certifies {
                    findings.push(format!(
                        "{label} ({table_name}): the record says some runs certify it at the \
                         30 s deadline, and with a {seconds} s budget it answered {outcome} / \
                         {class}: it no longer certifies on this host. Re-qualify it: review \
                         the outcome, then update DEADLINE_BOUND_HERE_BY_HOST, LIMITATIONS.md \
                         and the host's report together"
                    ));
                }
            } else if certifies {
                findings.push(format!(
                    "{label} ({table_name}): the record says no run certifies it, and with a \
                     {seconds} s budget it certifies: a strengthening the record must take. \
                     Measure it at the 30 s deadline, then record what it answers there \
                     (CERTIFIED_HERE_BY_HOST, or this entry with the Verified answer), with \
                     LIMITATIONS.md and the host's report"
                ));
            } else if !bound.is_measured(&outcome, class) {
                findings.push(format!(
                    "{label} ({table_name}): the record says no run certifies it, and with a \
                     {seconds} s budget it answered {outcome} / {class}, none of the answers \
                     measured for it ({:?}). Re-qualify it: review the outcome, then record \
                     it in DEADLINE_BOUND_HERE_BY_HOST, LIMITATIONS.md and the host's report \
                     together",
                    bound.answers
                ));
            }
        }
        findings
    });
    assert!(
        findings.is_empty(),
        "the deadline-bound record no longer holds on host {}:\n{}",
        current_host_triple(),
        findings.join("\n")
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its lowerings state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

// ---------------------------------------------------------------------------
// Slice 4: private stack slots and incoming memory
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_memory_tests.rs"]
mod memory;

// ---------------------------------------------------------------------------
// Slice 5: scalar pairs, symbol addresses and branch-free compares
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice5_tests.rs"]
mod slice5;

#[path = "x86_source_bound_body_slice5_qualification_tests.rs"]
mod slice5_qualification;

// ---------------------------------------------------------------------------
// Slice 6: acyclic control flow
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice6_tests.rs"]
mod slice6;

#[path = "x86_source_bound_body_slice6_qualification_tests.rs"]
mod slice6_qualification;

// ---------------------------------------------------------------------------
// Slice 7: calls through memory (return buffers and out-parameters)
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice7_tests.rs"]
mod slice7;

#[path = "x86_source_bound_body_slice7_qualification_tests.rs"]
mod slice7_qualification;

// ---------------------------------------------------------------------------
// Slice 8: aggregates in general-purpose registers
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice8_tests.rs"]
mod slice8;

#[path = "x86_source_bound_body_slice8_qualification_tests.rs"]
mod slice8_qualification;

// ---------------------------------------------------------------------------
// Slice 9: acyclic control flow over the DAG
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice9_tests.rs"]
mod slice9;

#[path = "x86_source_bound_body_slice9_qualification_tests.rs"]
mod slice9_qualification;

// ---------------------------------------------------------------------------
// Slice 10: instruction coverage (checked arithmetic, not, popcount and
// indirect calls)
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice10_tests.rs"]
mod slice10;

#[path = "x86_source_bound_body_slice10_qualification_tests.rs"]
mod slice10_qualification;

// ---------------------------------------------------------------------------
// Slice 11: `I128` register pairs and float bit patterns in SSE registers
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice11_tests.rs"]
mod slice11;

#[path = "x86_source_bound_body_slice11_qualification_tests.rs"]
mod slice11_qualification;

// ---------------------------------------------------------------------------
// Slice 12: loops, cut at their headers
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice12_tests.rs"]
mod slice12;

#[path = "x86_source_bound_body_slice12_qualification_tests.rs"]
mod slice12_qualification;

// ---------------------------------------------------------------------------
// Slice 13: private addresses stored as data, the stack argument areas, the
// C memory routines and scalar atomics
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice13_tests.rs"]
mod slice13;

#[path = "x86_source_bound_body_slice13_qualification_tests.rs"]
mod slice13_qualification;

// ---------------------------------------------------------------------------
// Slice 14: definedness and dispatch (division, the divide-by-zero guard, a
// switch's shared targets and jump tables)
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice14_tests.rs"]
mod slice14;

#[path = "x86_source_bound_body_slice14_qualification_tests.rs"]
mod slice14_qualification;

// ---------------------------------------------------------------------------
// Slice 15: the value, call and observable residue (float constants and
// sign-bit operations, mixed-width registers, a forwarded `bool` parameter,
// accesses through a derived address and `I128` in the stack areas)
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice15_tests.rs"]
mod slice15;

#[path = "x86_source_bound_body_slice15_qualification_tests.rs"]
mod slice15_qualification;

// ---------------------------------------------------------------------------
// Slice 16: past the single-query bounds, one theorem replayed in parts
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice16_tests.rs"]
mod slice16;

#[path = "x86_source_bound_body_slice16_qualification_tests.rs"]
mod slice16_qualification;

// ---------------------------------------------------------------------------
// Slice 17: private stack accesses at a non-constant offset, and the bytes a
// cut point leaves out as dead
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice17_tests.rs"]
mod slice17;

#[path = "x86_source_bound_body_slice17_qualification_tests.rs"]
mod slice17_qualification;

// ---------------------------------------------------------------------------
// OD-185: array element addresses (LIR `ArrayGep`)
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_arraygep_tests.rs"]
mod arraygep;

#[path = "x86_source_bound_body_arraygep_qualification_tests.rs"]
mod arraygep_qualification;

// ---------------------------------------------------------------------------
// OD-BODY-SEXT-BOOL-20261016: the sign extension of a `bool` (LIR `Sextend`
// from `B1`)
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_sext_bool_tests.rs"]
mod sext_bool;

#[path = "x86_source_bound_body_sext_bool_qualification_tests.rs"]
mod sext_bool_qualification;

// ---------------------------------------------------------------------------
// Slice 18 (OD-187): the value-numbered spelling of every conjunctive
// single-query theorem, swept against evaluation
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice18_tests.rs"]
mod slice18;

// ---------------------------------------------------------------------------
// Slice 19 (OD-195): the full canonical spelling, swept against evaluation
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice19_tests.rs"]
mod slice19;

// ---------------------------------------------------------------------------
// Slice 20 (OD-191 to OD-194): a switch's binary-search blocks, a stored
// address dead at a DAG join, `I128` items as two halves, three singleton
// rules and two bounds
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice20_tests.rs"]
mod slice20;

#[path = "x86_source_bound_body_slice20_qualification_tests.rs"]
mod slice20_qualification;

// ---------------------------------------------------------------------------
// Slice 21 (OD-198 to OD-201): floating-point operations as paired rounding
// events, the saturating conversion, an abstract theorem's satisfying model,
// and the `I128` atomic load and the atomic exchange
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice21_tests.rs"]
mod slice21;

#[path = "x86_source_bound_body_slice21_qualification_tests.rs"]
mod slice21_qualification;

// ---------------------------------------------------------------------------
// Slice 22 (OD-202): the `i128` division class
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice22_tests.rs"]
mod slice22;

#[path = "x86_source_bound_body_slice22_qualification_tests.rs"]
mod slice22_qualification;

// ---------------------------------------------------------------------------
// Slice 23 (OD-205, OD-206): arithmetic congruence pairing and the
// generalization over arithmetic leaves
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice23_tests.rs"]
mod slice23;

#[path = "x86_source_bound_body_slice23_qualification_tests.rs"]
mod slice23_qualification;

// ---------------------------------------------------------------------------
// Slice 24a (OD-226): the exact merged-chain quotient
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice24_tests.rs"]
mod slice24;

#[path = "x86_source_bound_body_slice24_qualification_tests.rs"]
mod slice24_qualification;

// ---------------------------------------------------------------------------
// Slice 25 (OD-227): scaled-index memory rows and memory-destination
// `add`/`xor`
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice25_tests.rs"]
mod slice25;

#[path = "x86_source_bound_body_slice25_qualification_tests.rs"]
mod slice25_qualification;

// ---------------------------------------------------------------------------
// Slice 24c (OD-228): segments, the if-converted regions
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_slice24c_tests.rs"]
mod slice24c;

#[path = "x86_source_bound_body_slice24c_qualification_tests.rs"]
mod slice24c_qualification;

// ---------------------------------------------------------------------------
// OD-233: cut inputs the source fixes for the run, defined and claimed on
// every edge (the theorem in parts)
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_od233_tests.rs"]
mod od233;

#[path = "x86_source_bound_body_od233_qualification_tests.rs"]
mod od233_qualification;

// ---------------------------------------------------------------------------
// OD-215: the selector's constant-amount `I128` shift fold
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_i128_const_shift_tests.rs"]
mod i128_const_shift;

#[path = "x86_source_bound_body_i128_const_shift_qualification_tests.rs"]
mod i128_const_shift_qualification;

// ---------------------------------------------------------------------------
// OD-224: the division-free 128-bit checked multiply
// ---------------------------------------------------------------------------

#[path = "x86_source_bound_body_i128_mulo_tests.rs"]
mod i128_mulo;

#[path = "x86_source_bound_body_i128_mulo_qualification_tests.rs"]
mod i128_mulo_qualification;

// ---------------------------------------------------------------------------
// The source-bound negative memo on the body replay path
// ---------------------------------------------------------------------------

#[cfg(unix)]
#[path = "x86_source_bound_body_negative_memo_tests.rs"]
mod negative_memo;

#[path = "x86_source_bound_body_qualification_matrix_tests.rs"]
mod qualification_matrix;

// ---------------------------------------------------------------------------
// Dead source blocks (a block no entry-to-end path reaches)
// ---------------------------------------------------------------------------

/// `source` with one block that nothing branches to, and that block's id.
///
/// Shaped so [`source_cfg`]'s per-block admission still holds for it: a lone
/// `Trap` terminator, named by `block_order` the way the LIR names every
/// block it lays out (`Function::layout_order` appends the unreachable ones
/// deliberately, and the canonical verifier identity counts them).
fn with_dead_block(source: &Function) -> (Function, Block) {
    let mut source = source.clone();
    let dead = Block(77);
    assert!(!source.blocks.contains_key(&dead), "the id must be fresh");
    source.blocks.insert(
        dead,
        trust_cg_lower::function::BasicBlock {
            params: Vec::new(),
            instructions: vec![Instruction {
                opcode: L::Trap,
                args: Vec::new(),
                results: Vec::new(),
            }],
            source_locs: Vec::new(),
        },
    );
    if !source.block_order.is_empty() {
        source.block_order.push(dead);
    }
    (source, dead)
}

#[test]
fn a_dead_source_block_is_excluded_from_the_region_not_refused() {
    // A block no entry-to-end path reaches lies outside a theorem stated path
    // by path: it constrains nothing and is needed by nothing. It used to
    // refuse the WHOLE function, which cost real credit on bodies whose live
    // code is fully supported (a dead loop-setup block a pass left behind).
    let (base, machine) = pair(Shape::Add);
    let (source, dead) = with_dead_block(&base);

    let cfg = source_cfg(&source).expect("a dead block is no longer a refusal");
    assert_eq!(
        cfg.dead,
        std::collections::BTreeSet::from([dead]),
        "the dead block is named",
    );
    assert!(
        !cfg.order.contains(&dead),
        "and is outside the region the theorem is stated over",
    );
    assert_eq!(
        cfg.order.len() + cfg.dead.len(),
        source.blocks.len(),
        "every block is either in the region or named dead",
    );

    // The machine selected before the dead block existed has no block lowering
    // it -- the case where a pass pruned the dead machine code. The theorem is
    // not merely still credited: it is the SAME theorem.
    let live = source_bound_x86_body(&base, &machine, SYSV).expect("the live body is credited");
    let with_dead =
        source_bound_x86_body(&source, &machine, SYSV).expect("dead source code withdraws nothing");
    let query = |owner: &SourceBoundX86Body<'_>| {
        generate_smt2_query_raw(owner.obligation(), &replay_config())
    };
    assert_eq!(
        query(&with_dead),
        query(&live),
        "dead source code must not change the theorem",
    );
}

/// A machine block off the chain whose single `Ret` row is stamped to `lir`.
fn off_chain_block(machine: &X86ISelFunction, source: &Function, lir: Block) -> X86ISelFunction {
    let mut machine = machine.clone();
    let extra = Block(99);
    machine.ensure_block(extra);
    let mut row = X86ISelInst::new(X86Opcode::Ret, vec![]);
    row.lowering_provenance = LoweringProvenance::SourceInst {
        id: trust_cg_ir::provenance::SourceInstId {
            block: lir.0,
            index: 0,
        },
        digest: source.blocks[&lir].instructions[0].lowering_digest(),
        trust_ir_inst: None,
    };
    machine.blocks.get_mut(&extra).unwrap().insts.push(row);
    machine
}

#[test]
fn a_laid_out_dead_block_is_accounted_for_by_what_it_lowers() {
    // The selector lays dead blocks out, so the machine can carry one. It is
    // accounted for by its origin, never by its shape: the correspondence's
    // own conditions put every machine block reachable from the machine entry
    // on a LIVE origin, so a dead-origin block cannot run.
    let (base, machine) = pair(Shape::Add);
    let (source, dead) = with_dead_block(&base);
    let machine = off_chain_block(&machine, &source, dead);
    source_bound_x86_body(&source, &machine, SYSV)
        .expect("a machine block lowering dead source code is accounted for");
}

#[test]
fn an_off_chain_block_the_dead_set_does_not_account_for_is_not_credited() {
    let (base, machine) = pair(Shape::Add);

    // No dead source block: the committed slice 1-5 contract stands, and an
    // off-chain machine block is still a named mismatch.
    let entry = base.block_order[0];
    let stamped_live = off_chain_block(&machine, &base, entry);
    expect_mismatch(
        &base,
        &stamped_live,
        "off-chain block, no dead source code",
        |m| matches!(m, X86BodyMismatch::UnreachableBlock { .. }),
    );

    // With dead source code, an off-chain block whose origin is LIVE is not
    // accounted for. It duplicates a live origin, so there is no
    // correspondence and no claim -- never credit.
    let (source, _dead) = with_dead_block(&base);
    let stamped_live = off_chain_block(&machine, &source, entry);
    expect_unsupported(&source, &stamped_live, "off-chain block on a live origin");

    // And a LIVE block that transfers INTO the dead machine block breaks the
    // induction: whatever its origin branched to is stranded off the chain,
    // and the live block's successors' origins are no longer exactly its LIR
    // block's successors. Which typed refusal reports it first is not the
    // property -- that it is never credit is.
    let (base, machine) = pair(Shape::BlackBox);
    let (source, dead) = with_dead_block(&base);
    let mut reaching = off_chain_block(&machine, &source, dead);
    let jmp = find(&reaching, X86Opcode::Jmp)[0];
    let home = rows(&reaching)[jmp].1;
    inst_mut(&mut reaching, jmp).operands[0] = O::Block(Block(99));
    reaching.blocks.get_mut(&home).unwrap().successors = vec![Block(99)];
    assert!(
        source_bound_x86_body(&source, &reaching, SYSV).is_err(),
        "a live block reaching the dead machine block must never be credit",
    );
}

// ---------------------------------------------------------------------------
// Restated rows, and `imul r, r, imm32`
// ---------------------------------------------------------------------------

#[test]
fn restated_rows_are_the_rows_they_compute() {
    let v1 = O::VReg(VReg::new(1, RegClass::Gpr64));
    let v2 = O::VReg(VReg::new(2, RegClass::Gpr64));
    let narrow = O::VReg(VReg::new(1, RegClass::Gpr32));
    let restated = |opcode, operands: Vec<O>| {
        restated_row(&X86ISelInst::new(opcode, operands)).map(|row| (row.opcode, row.operands))
    };

    // `xor d, d` is `mov d, 0` -- at ONE register and ONE width only, so the
    // admission cannot reach a real two-operand xor of distinct values.
    assert_eq!(
        restated(X86Opcode::XorRR, vec![v1.clone(), v1.clone()]),
        Some((X86Opcode::MovRI, vec![v1.clone(), O::Imm(0)])),
    );
    assert!(restated(X86Opcode::XorRR, vec![v1.clone(), v2.clone()]).is_none());
    assert!(restated(X86Opcode::XorRR, vec![v1.clone(), narrow]).is_none());

    // The in-place `inc d` / `dec d` are `add` / `sub d, d, 1`.
    assert_eq!(
        restated(X86Opcode::Inc, vec![v1.clone()]),
        Some((X86Opcode::AddRI, vec![v1.clone(), v1.clone(), O::Imm(1)])),
    );
    assert_eq!(
        restated(X86Opcode::Dec, vec![v1.clone()]),
        Some((X86Opcode::SubRI, vec![v1.clone(), v1.clone(), O::Imm(1)])),
    );
    assert!(restated(X86Opcode::Inc, vec![v1.clone(), v2.clone()]).is_none());
    assert!(restated(X86Opcode::Inc, vec![O::Imm(1)]).is_none());

    // Every other row is itself.
    assert!(restated(X86Opcode::AddRR, vec![v1, v2.clone(), v2]).is_none());
}

#[test]
fn imul_by_an_immediate_is_the_exact_product() {
    // `Shape::ShlImm` is `x << 3`, so `imul d, s, 8` is the SAME function and
    // `imul d, s, 9` is not. That pair is what makes this admission EXACT
    // rather than merely accepted: an arity arm that computed a sum, or
    // dropped the immediate, would credit both.
    let (source, base) = pair(Shape::ShlImm);
    let shl = find(&base, X86Opcode::ShlRI)[0];
    let operands = inst(&base, shl).operands.clone();
    let [destination, value, O::Imm(3)] = operands.as_slice() else {
        panic!("ShlImm shifts by 3: {operands:?}");
    };
    // Mutate in place so the row keeps its TV-1 stamp and its flags.
    let retarget = |machine: &mut X86ISelFunction, factor: i64| {
        let row = inst_mut(machine, shl);
        row.opcode = X86Opcode::ImulRRI;
        row.operands = vec![destination.clone(), value.clone(), O::Imm(factor)];
    };

    let mut machine = base.clone();
    retarget(&mut machine, 8);
    source_bound_x86_body(&source, &machine, SYSV)
        .expect("imul by 8 is the shift by 3 it replaces");

    let mut machine = base;
    retarget(&mut machine, 9);
    assert_theorem_refutes(&source, &machine, "imul by 9 where the source shifts by 3");
}

#[test]
fn a_rotate_is_not_a_shift() {
    // `Shape::ShlImm` is `x << 3`. `rol d, s, 3` agrees with it on every input
    // whose top three bits are clear and differs on every other, so putting it
    // in place of the shift must be REFUTED. A model that dropped the
    // wrap-around half would credit it.
    let (source, mut machine) = pair(Shape::ShlImm);
    let shl = find(&machine, X86Opcode::ShlRI)[0];
    inst_mut(&mut machine, shl).opcode = X86Opcode::RolRI;
    assert_theorem_refutes(&source, &machine, "rol where the source shifts left");
}
