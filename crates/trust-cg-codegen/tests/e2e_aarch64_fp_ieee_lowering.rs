// Copyright 2026 Andrew Yates | Apache-2.0
//! The TrustIR floating-point conversions, rounding operations and scalar
//! arithmetic, compiled by trust-cg and run against the independent IEEE 754
//! reference (ledger `L04-P3`).
//!
//! Each TrustIR operation below becomes one function
//! `extern "C" fn(u64, u64, u64) -> u64` that bit-casts its integer-carried
//! operands, performs the operation and returns the result's bits (an integer
//! result sign- or zero-extended to 64 bits), so binary16 needs no Rust type
//! and no narrow argument relies on an extension convention:
//!
//! * `FPToSISat`/`FPToUISat` (Rust's saturating `as`) from F16/F32/F64 to
//!   8/16/32/64-bit integers, and the raw `FPToSI`/`FPToUI` on the inputs
//!   whose truncation is in range (the rest is source-level undefined
//!   behaviour and is counted, not compared);
//! * `SIToFP`/`UIToFP` from 8/16/32/64-bit integers to F16/F32/F64;
//! * `FPExt`/`FPTrunc` between every pair of F16/F32/F64, and each widening
//!   followed by the narrowing back (the identity on every non-NaN value);
//! * `FFloor`/`FCeil`/`FTrunc` at F16/F32/F64, and the
//!   `trust-cg-aarch64-fp` dialect's `frintn` at F32/F64;
//! * `FAdd`/`FSub`/`FMul`/`FDiv`/`FMin`/`FMax`, `FNeg`/`FAbs`/`FSqrt` at
//!   F16/F32/F64, and `llvm.fma.f32`/`llvm.fma.f64` calls.
//!
//! Every function is compiled on two routes and run in process:
//!
//! * **AOT**: `Pipeline` (Darwin or Linux GNU triple of the host) at O0-O3 on
//!   the PROOF-GRADE publication route, which refuses any emitted word ENC-5
//!   does not decode. Every FP conversion, rounding or arithmetic instruction of
//!   the final machine function is re-encoded, decoded by ENC-5 (a match is
//!   required) and found in the object's bytes; the object is linked into a
//!   shared library with the host `cc` and loaded with `dlopen`.
//! * **JIT**: `Compiler::compile_module_to_jit` with the host profile at O1
//!   (`jit_fast`) and O2, whose emission runs ENC-5 in enforce mode; each
//!   function's published bytes must contain the instruction family the AOT
//!   route selected.
//!
//! Inputs come from the shared sets of the instruction-level differential
//! (`trust-cg-verify/tests/support/fp_ieee_inputs.rs`): every binary16 encoding
//! and every 8- and 16-bit integer EXHAUSTIVELY on every route; binary32,
//! 32-bit integer and binary16-pair sets structured plus stratified random
//! (STATISTICAL) on AOT O2 and JIT O1, and over all 2^32 values with
//! `TRUST_CG_FP_IEEE_EXHAUSTIVE=1`; binary64, 64-bit integer, wide-pair and
//! fused-triple sets statistical. O0, O1, O3 and JIT O2 run the binary16 and
//! narrow-integer spaces plus each set's first 50,000 entries.
//!
//! Results are compared with the TrustIR semantics the reference states: bit
//! for bit, except that a NaN result of an arithmetic, rounding or conversion
//! operation is compared by class (TrustIR, like Rust, does not fix NaN
//! payloads; how many also match the Arm propagation rule bit for bit is
//! reported), and `FMin`/`FMax` of two zeros of opposite sign may return
//! either zero (TrustIR follows Rust here). `FNeg`/`FAbs` must preserve every
//! payload. This is testing evidence for the compiled code on this host, not a
//! proof.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use std::collections::{BTreeMap, HashMap};
use std::ffi::{CStr, CString, c_char, c_int, c_void};
use std::time::Instant;

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::AArch64IsaProfile;
use trust_cg_ir::{AArch64Opcode as Op, MachInst};
use trust_cg_lower::aarch64_fp_dialect::{Operation, instruction};
use trust_cg_verify::ieee754_reference::{self as ieee, Format, Rounding};
use trust_ir::{BinOp, CastOp, Ty, UnOp, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

#[path = "../../trust-cg-verify/tests/support/fp_ieee_inputs.rs"]
mod inputs;
use inputs::*;

#[path = "common/pinned_target.rs"]
mod pinned_target;

const RNE: Rounding = Rounding::TiesToEven;

// ===========================================================================
// Cases
// ===========================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Arith {
    Add,
    Sub,
    Mul,
    Div,
    Min,
    Max,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Unary {
    Neg,
    Abs,
    Sqrt,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Round {
    Floor,
    Ceil,
    Trunc,
    /// The `trust-cg-aarch64-fp` dialect's `frintn` (ties to even).
    Nearest,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    SatToInt {
        src: Format,
        width: u32,
        signed: bool,
    },
    RawToInt {
        src: Format,
        width: u32,
        signed: bool,
    },
    FromInt {
        dst: Format,
        width: u32,
        signed: bool,
    },
    Cvt {
        src: Format,
        dst: Format,
    },
    /// `FPTrunc(FPExt(x))` from `fmt` through the wider `via`: the identity on
    /// every non-NaN value.
    RoundTrip {
        fmt: Format,
        via: Format,
    },
    Round {
        fmt: Format,
        op: Round,
    },
    Arith {
        fmt: Format,
        op: Arith,
    },
    Unary {
        fmt: Format,
        op: Unary,
    },
    Fma {
        fmt: Format,
    },
}

/// The inputs a case reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Space {
    Fp(Format),
    Int(u32),
    Pair(Format),
    Triple(Format),
}

fn int_ty(width: u32, signed: bool) -> Ty {
    match (width, signed) {
        (8, true) => Ty::I8,
        (16, true) => Ty::I16,
        (32, true) => Ty::I32,
        (64, true) => Ty::I64,
        (8, false) => Ty::U8,
        (16, false) => Ty::U16,
        (32, false) => Ty::U32,
        (64, false) => Ty::U64,
        _ => unreachable!("integer width {width}"),
    }
}

fn fp_ty(f: Format) -> Ty {
    match f {
        Format::Half => Ty::F16,
        Format::Single => Ty::F32,
        Format::Double => Ty::F64,
    }
}

fn bits_ty(f: Format) -> Ty {
    match f {
        Format::Half => Ty::U16,
        Format::Single => Ty::U32,
        Format::Double => Ty::U64,
    }
}

impl Case {
    fn all() -> Vec<Case> {
        let mut cases = Vec::new();
        for fmt in Format::ALL {
            for width in [8, 16, 32, 64] {
                for signed in [true, false] {
                    cases.push(Case::SatToInt {
                        src: fmt,
                        width,
                        signed,
                    });
                    cases.push(Case::RawToInt {
                        src: fmt,
                        width,
                        signed,
                    });
                    cases.push(Case::FromInt {
                        dst: fmt,
                        width,
                        signed,
                    });
                }
            }
            for dst in Format::ALL {
                if dst != fmt {
                    cases.push(Case::Cvt { src: fmt, dst });
                }
            }
            for via in Format::ALL {
                if via.width() > fmt.width() {
                    cases.push(Case::RoundTrip { fmt, via });
                }
            }
            for op in [Round::Floor, Round::Ceil, Round::Trunc] {
                cases.push(Case::Round { fmt, op });
            }
            if fmt != Format::Half {
                cases.push(Case::Round {
                    fmt,
                    op: Round::Nearest,
                });
                cases.push(Case::Fma { fmt });
            }
            for op in [
                Arith::Add,
                Arith::Sub,
                Arith::Mul,
                Arith::Div,
                Arith::Min,
                Arith::Max,
            ] {
                cases.push(Case::Arith { fmt, op });
            }
            for op in [Unary::Neg, Unary::Abs, Unary::Sqrt] {
                cases.push(Case::Unary { fmt, op });
            }
        }
        cases
    }

    fn name(self) -> String {
        let sign = |s: bool| if s { 's' } else { 'u' };
        match self {
            Case::SatToInt { src, width, signed } => {
                format!("sat_{}{width}_{}", sign(signed), src.name())
            }
            Case::RawToInt { src, width, signed } => {
                format!("raw_{}{width}_{}", sign(signed), src.name())
            }
            Case::FromInt { dst, width, signed } => {
                format!("{}_from_{}{width}", dst.name(), sign(signed))
            }
            Case::Cvt { src, dst } => format!("cvt_{}_{}", dst.name(), src.name()),
            Case::RoundTrip { fmt, via } => format!("trip_{}_{}", fmt.name(), via.name()),
            Case::Round { fmt, op } => format!("{op:?}_{}", fmt.name()).to_lowercase(),
            Case::Arith { fmt, op } => format!("{op:?}_{}", fmt.name()).to_lowercase(),
            Case::Unary { fmt, op } => format!("{op:?}_{}", fmt.name()).to_lowercase(),
            Case::Fma { fmt } => format!("fma_{}", fmt.name()),
        }
    }

    fn space(self) -> Space {
        match self {
            Case::SatToInt { src, .. } | Case::RawToInt { src, .. } | Case::Cvt { src, .. } => {
                Space::Fp(src)
            }
            Case::FromInt { width, .. } => Space::Int(width),
            Case::Round { fmt, .. } | Case::Unary { fmt, .. } | Case::RoundTrip { fmt, .. } => {
                Space::Fp(fmt)
            }
            Case::Arith { fmt, .. } => Space::Pair(fmt),
            Case::Fma { fmt } => Space::Triple(fmt),
        }
    }

    fn arity(self) -> usize {
        match self.space() {
            Space::Fp(_) | Space::Int(_) => 1,
            Space::Pair(_) => 2,
            Space::Triple(_) => 3,
        }
    }

    /// The machine opcodes the case's operation selects (any one suffices).
    fn opcodes(self) -> &'static [Op] {
        match self {
            Case::SatToInt { signed: true, .. } | Case::RawToInt { signed: true, .. } => {
                &[Op::FcvtzsRR]
            }
            Case::SatToInt { .. } | Case::RawToInt { .. } => &[Op::FcvtzuRR],
            Case::FromInt { signed: true, .. } => &[Op::ScvtfRR],
            Case::FromInt { .. } => &[Op::UcvtfRR],
            Case::Cvt { src, dst } => match (src, dst) {
                (Format::Single, Format::Double) => &[Op::FcvtSD],
                (Format::Double, Format::Single) => &[Op::FcvtDS],
                (Format::Half, Format::Single) => &[Op::FcvtHS],
                (Format::Half, Format::Double) => &[Op::FcvtHD],
                (Format::Single, Format::Half) => &[Op::FcvtSH],
                _ => &[Op::FcvtDH],
            },
            // Either conversion of the pair identifies the case.
            Case::RoundTrip { fmt, via } => match (fmt, via) {
                (Format::Single, Format::Double) => &[Op::FcvtSD, Op::FcvtDS],
                (Format::Half, Format::Single) => &[Op::FcvtHS, Op::FcvtSH],
                _ => &[Op::FcvtHD, Op::FcvtDH],
            },
            Case::Round { op, .. } => match op {
                Round::Floor => &[Op::FrintmRR],
                Round::Ceil => &[Op::FrintpRR],
                Round::Trunc => &[Op::FrintzRR],
                Round::Nearest => &[Op::FrintnRR],
            },
            Case::Arith { op, .. } => match op {
                Arith::Add => &[Op::FaddRR],
                Arith::Sub => &[Op::FsubRR],
                Arith::Mul => &[Op::FmulRR],
                Arith::Div => &[Op::FdivRR],
                Arith::Min => &[Op::FminnmRR],
                Arith::Max => &[Op::FmaxnmRR],
            },
            Case::Unary { op, .. } => match op {
                Unary::Neg => &[Op::FnegRR],
                Unary::Abs => &[Op::FabsRR],
                Unary::Sqrt => &[Op::FsqrtRR],
            },
            Case::Fma { .. } => &[Op::FmaddRR],
        }
    }
}

/// Every FP conversion, rounding or arithmetic opcode the cases can select;
/// each such instruction in a compiled case is checked by ENC-5.
const FP_VALUE_OPCODES: &[Op] = &[
    Op::FcvtzsRR,
    Op::FcvtzuRR,
    Op::ScvtfRR,
    Op::UcvtfRR,
    Op::FcvtSD,
    Op::FcvtDS,
    Op::FcvtHS,
    Op::FcvtHD,
    Op::FcvtSH,
    Op::FcvtDH,
    Op::FrintmRR,
    Op::FrintpRR,
    Op::FrintzRR,
    Op::FrintnRR,
    Op::FaddRR,
    Op::FsubRR,
    Op::FmulRR,
    Op::FdivRR,
    Op::FminnmRR,
    Op::FmaxnmRR,
    Op::FnegRR,
    Op::FabsRR,
    Op::FsqrtRR,
    Op::FmaddRR,
];

// ===========================================================================
// TrustIR
// ===========================================================================

/// The FP value carried in the low bits of a `u64` parameter.
fn fp_in(f: &mut FunctionBuilder<'_>, value: ValueId, fmt: Format) -> ValueId {
    let bits = if fmt == Format::Double {
        value
    } else {
        f.trunc(Ty::U64, bits_ty(fmt), value)
    };
    f.cast(CastOp::Bitcast, bits_ty(fmt), fp_ty(fmt), bits)
}

/// The bits of an FP value, zero-extended to `u64`.
fn fp_out(f: &mut FunctionBuilder<'_>, value: ValueId, fmt: Format) -> ValueId {
    let bits = f.cast(CastOp::Bitcast, fp_ty(fmt), bits_ty(fmt), value);
    if fmt == Format::Double {
        bits
    } else {
        f.zext(bits_ty(fmt), Ty::U64, bits)
    }
}

fn build_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("fp_ieee_lowering");
    let fma32 = {
        let ty = mb.add_func_type(vec![Ty::F32, Ty::F32, Ty::F32], vec![Ty::F32]);
        mb.declare_function("llvm.fma.f32", ty)
    };
    let fma64 = {
        let ty = mb.add_func_type(vec![Ty::F64, Ty::F64, Ty::F64], vec![Ty::F64]);
        mb.declare_function("llvm.fma.f64", ty)
    };
    for case in Case::all() {
        let sig = mb.add_func_type(vec![Ty::U64; case.arity()], vec![Ty::U64]);
        let mut f = mb.function(case.name(), sig);
        let entry = f.create_block();
        let params: Vec<ValueId> = (0..case.arity())
            .map(|_| f.add_block_param(entry, Ty::U64))
            .collect();
        f.switch_to_block(entry);
        let result = match case {
            Case::SatToInt { src, width, signed } | Case::RawToInt { src, width, signed } => {
                let x = fp_in(&mut f, params[0], src);
                let op = match (matches!(case, Case::SatToInt { .. }), signed) {
                    (true, true) => CastOp::FPToSISat,
                    (true, false) => CastOp::FPToUISat,
                    (false, true) => CastOp::FPToSI,
                    (false, false) => CastOp::FPToUI,
                };
                let ty = int_ty(width, signed);
                let v = f.cast(op, fp_ty(src), ty.clone(), x);
                match (width, signed) {
                    (64, true) => f.cast(CastOp::Bitcast, Ty::I64, Ty::U64, v),
                    (64, false) => v,
                    (_, true) => {
                        let wide = f.sext(ty, Ty::I64, v);
                        f.cast(CastOp::Bitcast, Ty::I64, Ty::U64, wide)
                    }
                    (_, false) => f.zext(ty, Ty::U64, v),
                }
            }
            Case::FromInt { dst, width, signed } => {
                let ty = int_ty(width, signed);
                let wide_ty = int_ty(64, signed);
                let wide = if signed {
                    f.cast(CastOp::Bitcast, Ty::U64, Ty::I64, params[0])
                } else {
                    params[0]
                };
                let v = if width == 64 {
                    wide
                } else {
                    f.trunc(wide_ty, ty.clone(), wide)
                };
                let op = if signed {
                    CastOp::SIToFP
                } else {
                    CastOp::UIToFP
                };
                let r = f.cast(op, ty, fp_ty(dst), v);
                fp_out(&mut f, r, dst)
            }
            Case::Cvt { src, dst } => {
                let x = fp_in(&mut f, params[0], src);
                let op = if dst.width() > src.width() {
                    CastOp::FPExt
                } else {
                    CastOp::FPTrunc
                };
                let r = f.cast(op, fp_ty(src), fp_ty(dst), x);
                fp_out(&mut f, r, dst)
            }
            Case::RoundTrip { fmt, via } => {
                let x = fp_in(&mut f, params[0], fmt);
                let wide = f.cast(CastOp::FPExt, fp_ty(fmt), fp_ty(via), x);
                let back = f.cast(CastOp::FPTrunc, fp_ty(via), fp_ty(fmt), wide);
                fp_out(&mut f, back, fmt)
            }
            Case::Round { fmt, op } => {
                let x = fp_in(&mut f, params[0], fmt);
                let r = match op {
                    Round::Floor => f.unop(UnOp::FFloor, fp_ty(fmt), x),
                    Round::Ceil => f.unop(UnOp::FCeil, fp_ty(fmt), x),
                    Round::Trunc => f.unop(UnOp::FTrunc, fp_ty(fmt), x),
                    Round::Nearest => {
                        f.dialect_op(instruction(Operation::Frintn, fp_ty(fmt), &[x]))[0]
                    }
                };
                fp_out(&mut f, r, fmt)
            }
            Case::Arith { fmt, op } => {
                let a = fp_in(&mut f, params[0], fmt);
                let b = fp_in(&mut f, params[1], fmt);
                let op = match op {
                    Arith::Add => BinOp::FAdd,
                    Arith::Sub => BinOp::FSub,
                    Arith::Mul => BinOp::FMul,
                    Arith::Div => BinOp::FDiv,
                    Arith::Min => BinOp::FMin,
                    Arith::Max => BinOp::FMax,
                };
                let r = f.binop(op, fp_ty(fmt), a, b);
                fp_out(&mut f, r, fmt)
            }
            Case::Unary { fmt, op } => {
                let x = fp_in(&mut f, params[0], fmt);
                let op = match op {
                    Unary::Neg => UnOp::FNeg,
                    Unary::Abs => UnOp::FAbs,
                    Unary::Sqrt => UnOp::FSqrt,
                };
                let r = f.unop(op, fp_ty(fmt), x);
                fp_out(&mut f, r, fmt)
            }
            Case::Fma { fmt } => {
                let a = fp_in(&mut f, params[0], fmt);
                let b = fp_in(&mut f, params[1], fmt);
                let c = fp_in(&mut f, params[2], fmt);
                let callee = if fmt == Format::Single { fma32 } else { fma64 };
                let r = f.call(callee, vec![a, b, c]);
                fp_out(&mut f, r, fmt)
            }
        };
        f.ret(vec![result]);
        f.build();
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    // The `llvm.fma` declarations are bodyless externals, an FFI boundary
    // trust-ir's validator admits only under a pinned target
    // (`TargetInfoRequired`), and every ingestion entry refuses what that
    // validator refuses since WS7.3. Both routes compile for the host triple.
    pinned_target::pin(&mut module, host_triple());
    module
}

// ===========================================================================
// The TrustIR semantics, from the reference
// ===========================================================================

/// What a case must return for one input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Expect {
    /// Exactly these bits.
    Bits(u64),
    /// Any NaN of the format (upper bits zero); the Arm reference's bits are
    /// carried for the bit-exact count.
    Nan(Format, u64),
    /// Either zero of the format.
    EitherZero(Format),
    /// Source-level undefined behaviour: not compared.
    Undefined,
}

fn sign_extend(value: u128, width: u32) -> u64 {
    let shift = 128 - width;
    (((value << shift) as i128) >> shift) as u64
}

fn fp_expect(fmt: Format, bits: u64) -> Expect {
    if ieee::is_nan(fmt, bits) {
        Expect::Nan(fmt, bits)
    } else {
        Expect::Bits(bits)
    }
}

fn expect(case: Case, [a, b, c]: [u64; 3]) -> Expect {
    match case {
        Case::SatToInt { src, width, signed } => {
            let v = ieee::to_int(src, a, Rounding::TowardZero, width, signed).value;
            Expect::Bits(if signed {
                sign_extend(v, width)
            } else {
                v as u64
            })
        }
        Case::RawToInt { src, width, signed } => {
            // Defined exactly when the conversion neither saturates nor sees
            // a NaN: Invalid Operation marks both.
            let o = ieee::to_int(src, a, Rounding::TowardZero, width, signed);
            if o.flags.contains(ieee::Flags::INVALID) {
                return Expect::Undefined;
            }
            Expect::Bits(if signed {
                sign_extend(o.value, width)
            } else {
                o.value as u64
            })
        }
        Case::FromInt { dst, width, signed } => {
            Expect::Bits(ieee::from_int_bits(dst, u128::from(a), width, signed, RNE).value)
        }
        Case::Cvt { src, dst } => fp_expect(dst, ieee::convert(src, dst, a, RNE).value),
        Case::RoundTrip { fmt, via } => {
            let wide = ieee::convert(fmt, via, a, RNE).value;
            let back = ieee::convert(via, fmt, wide, RNE).value;
            if !ieee::is_nan(fmt, a) {
                assert_eq!(back, a, "the reference's round trip is not the identity");
            }
            fp_expect(fmt, back)
        }
        Case::Round { fmt, op } => {
            let rm = match op {
                Round::Floor => Rounding::TowardNegative,
                Round::Ceil => Rounding::TowardPositive,
                Round::Trunc => Rounding::TowardZero,
                Round::Nearest => RNE,
            };
            fp_expect(fmt, ieee::round_to_integral(fmt, a, rm, false).value)
        }
        Case::Arith { fmt, op } => match op {
            Arith::Add => fp_expect(fmt, ieee::add(fmt, a, b, RNE).value),
            Arith::Sub => fp_expect(fmt, ieee::sub(fmt, a, b, RNE).value),
            Arith::Mul => fp_expect(fmt, ieee::mul(fmt, a, b, RNE).value),
            Arith::Div => fp_expect(fmt, ieee::div(fmt, a, b, RNE).value),
            Arith::Min | Arith::Max => {
                // TrustIR FMin/FMax: IEEE 754-2019 minimumNumber/maximumNumber
                // with a lone NaN of either kind yielding the other operand,
                // and either zero allowed for two zeros of opposite sign.
                let (na, nb) = (ieee::is_nan(fmt, a), ieee::is_nan(fmt, b));
                match (na, nb) {
                    (true, true) => Expect::Nan(fmt, ieee::quiet(fmt, a)),
                    (true, false) => Expect::Bits(b),
                    (false, true) => Expect::Bits(a),
                    (false, false) => {
                        let zero = |v| ieee::classify(fmt, v) == ieee::Class::Zero;
                        if zero(a) && zero(b) && a != b {
                            Expect::EitherZero(fmt)
                        } else if op == Arith::Min {
                            Expect::Bits(ieee::min_num(fmt, a, b).value)
                        } else {
                            Expect::Bits(ieee::max_num(fmt, a, b).value)
                        }
                    }
                }
            }
        },
        Case::Unary { fmt, op } => match op {
            Unary::Neg => Expect::Bits(ieee::neg(fmt, a).value),
            Unary::Abs => Expect::Bits(ieee::abs(fmt, a).value),
            Unary::Sqrt => fp_expect(fmt, ieee::sqrt(fmt, a, RNE).value),
        },
        // llvm.fma(a, b, c) = a * b + c.
        Case::Fma { fmt } => fp_expect(fmt, ieee::fma(fmt, a, b, c, RNE).value),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Verdict {
    Exact,
    /// NaN by class, and bit-identical to the Arm reference.
    NanArmBits,
    /// NaN by class only.
    NanClass,
    EitherZero,
    Undefined,
    Mismatch,
}

fn judge(got: u64, want: Expect) -> Verdict {
    match want {
        Expect::Bits(bits) if got == bits => Verdict::Exact,
        Expect::Nan(f, arm) if got & !f.mask() == 0 && ieee::is_nan(f, got) => {
            if got == arm {
                Verdict::NanArmBits
            } else {
                Verdict::NanClass
            }
        }
        Expect::EitherZero(f) if got == 0 || got == f.sign_bit() => Verdict::EitherZero,
        Expect::Undefined => Verdict::Undefined,
        _ => Verdict::Mismatch,
    }
}

// ===========================================================================
// Routes
// ===========================================================================

type Entry = unsafe extern "C" fn(u64, u64, u64) -> u64;

/// One compiled route: a name and, per case, the entry point.
struct Route {
    name: String,
    full_sets: bool,
    entries: Vec<usize>,
}

fn host_triple() -> &'static str {
    if cfg!(target_os = "macos") {
        "aarch64-apple-darwin"
    } else {
        "aarch64-unknown-linux-gnu"
    }
}

fn opt_level_name(level: OptLevel) -> &'static str {
    match level {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
        _ => "O3",
    }
}

unsafe extern "C" {
    fn dlopen(path: *const c_char, mode: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
    fn dlerror() -> *const c_char;
    #[cfg(target_os = "macos")]
    fn sysctlbyname(
        name: *const c_char,
        oldp: *mut c_void,
        oldlenp: *mut usize,
        newp: *mut c_void,
        newlen: usize,
    ) -> c_int;
    #[cfg(target_os = "linux")]
    fn getauxval(kind: std::ffi::c_ulong) -> std::ffi::c_ulong;
}

/// Require FEAT_FP16, which the binary16 cases select natively (every Apple
/// arm64 part has it; a Linux host must report FPHP and ASIMDHP).
fn require_fp16() {
    #[cfg(target_os = "macos")]
    {
        let mut value: c_int = 0;
        let mut len = std::mem::size_of::<c_int>();
        // SAFETY: a read of an integer sysctl into a correctly sized buffer.
        let status = unsafe {
            sysctlbyname(
                c"hw.optional.arm.FEAT_FP16".as_ptr(),
                (&mut value as *mut c_int).cast(),
                &mut len,
                std::ptr::null_mut(),
                0,
            )
        };
        assert!(
            status == 0 && value == 1,
            "this host does not report FEAT_FP16"
        );
    }
    #[cfg(target_os = "linux")]
    {
        const AT_HWCAP: std::ffi::c_ulong = 16;
        const FPHP_ASIMDHP: std::ffi::c_ulong = (1 << 9) | (1 << 10);
        // SAFETY: getauxval has no preconditions.
        let hwcap = unsafe { getauxval(AT_HWCAP) };
        assert_eq!(
            hwcap & FPHP_ASIMDHP,
            FPHP_ASIMDHP,
            "this host does not report FEAT_FP16"
        );
    }
}

const RTLD_NOW: c_int = 2;

/// The AOT pipeline: the Apple target contract admits FEAT_FP16; the generic
/// Linux profile does not, so the Linux route states it explicitly.
fn pipeline(config: PipelineConfig) -> Pipeline {
    let pipeline = Pipeline::new(config);
    if cfg!(target_os = "linux") {
        pipeline.with_aarch64_isa_profile(AArch64IsaProfile::FP16)
    } else {
        pipeline
    }
}

/// The ENC-5 evidence for one AOT compile.
#[derive(Default)]
struct WordCheck {
    checked: usize,
    by_opcode: BTreeMap<String, usize>,
}

/// Compile every case on the proof-grade AOT route at `level`, check every FP
/// value instruction's word with ENC-5 against the object, link a shared
/// library and load it. Returns the route and, per case, the AOT words of
/// the case's own opcodes (for the JIT family check).
fn aot_route(
    module: &trust_ir::Module,
    level: OptLevel,
    full_sets: bool,
) -> (Route, WordCheck, Vec<Vec<u32>>) {
    let config = PipelineConfig {
        target_triple: host_triple().to_owned(),
        opt_level: level,
        verify: false,
        ..Default::default()
    };
    let cases = Case::all();
    let mut prepared = Vec::new();
    for case in &cases {
        let name = case.name();
        let ir = module
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("no TrustIR function {name}"));
        let (lir, _) =
            trust_cg_lower::translate_function_with_license(ir, module, &permit_unlicensed())
                .unwrap_or_else(|e| panic!("{name}: translate: {e:?}"));
        prepared.push(
            pipeline(config.clone())
                .prepare_function(&lir)
                .unwrap_or_else(|e| panic!("{name} at {level:?}: prepare: {e:?}")),
        );
    }
    let object = pipeline(config)
        .with_proof_grade_aarch64_publication()
        .compile_module(&prepared)
        .unwrap_or_else(|e| panic!("proof-grade route at {level:?}: {e:?}"));
    let object_words: std::collections::HashSet<u32> = object
        .as_chunks::<4>()
        .0
        .iter()
        .map(|w| u32::from_le_bytes(*w))
        .collect();
    let mut check = WordCheck::default();
    let mut own_words = Vec::new();
    for (case, function) in cases.iter().zip(&prepared) {
        let insts: Vec<MachInst> = function
            .block_order
            .iter()
            .flat_map(|&block| function.block(block).insts.iter())
            .map(|&id| function.inst(id).clone())
            .collect();
        let mut own = Vec::new();
        for inst in insts
            .iter()
            .filter(|i| FP_VALUE_OPCODES.contains(&i.opcode))
        {
            let word = encode_instruction(inst)
                .unwrap_or_else(|e| panic!("{}: encode {inst:?}: {e:?}", case.name()));
            assert!(
                matches!(
                    A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None),
                    DecodeCheckOutcome::Match
                ),
                "{}: ENC-5 does not match {word:#010x} for {inst:?}",
                case.name()
            );
            assert!(
                object_words.contains(&word),
                "{}: {word:#010x} ({:?}) is not in the object",
                case.name(),
                inst.opcode
            );
            check.checked += 1;
            *check
                .by_opcode
                .entry(format!("{:?}", inst.opcode))
                .or_default() += 1;
            if case.opcodes().contains(&inst.opcode) {
                own.push(word);
            }
        }
        assert!(
            !own.is_empty(),
            "{} at {level:?}: no {:?} in {:?}",
            case.name(),
            case.opcodes(),
            insts.iter().map(|i| i.opcode).collect::<Vec<_>>()
        );
        own_words.push(own);
    }
    // Link and load. Every call gets its own directory: the tests of this
    // target compile their routes concurrently under the default harness, and
    // a shared path would let one test's link or removal race another's (and
    // dyld would hand back an already loaded image for a reused path).
    static LINKS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_fp_ieee_{}_{}_{}",
        opt_level_name(level),
        std::process::id(),
        LINKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("scratch directory");
    let obj = dir.join("cases.o");
    let lib = dir.join(if cfg!(target_os = "macos") {
        "libcases.dylib"
    } else {
        "libcases.so"
    });
    std::fs::write(&obj, &object).expect("write object");
    let shared = if cfg!(target_os = "macos") {
        "-dynamiclib"
    } else {
        "-shared"
    };
    let link = std::process::Command::new("cc")
        .args([shared, obj.to_str().unwrap(), "-o", lib.to_str().unwrap()])
        .output()
        .expect("cc available");
    assert!(
        link.status.success(),
        "link: {}",
        String::from_utf8_lossy(&link.stderr)
    );
    let path = CString::new(lib.to_str().unwrap()).unwrap();
    // SAFETY: loading a library this test just linked; it stays loaded.
    let handle = unsafe { dlopen(path.as_ptr(), RTLD_NOW) };
    if handle.is_null() {
        // SAFETY: dlerror returns a NUL-terminated message after a failure.
        let message = unsafe { CStr::from_ptr(dlerror()) }.to_string_lossy();
        panic!("dlopen {lib:?}: {message}");
    }
    // The loaded image no longer needs its files.
    std::fs::remove_dir_all(&dir).expect("remove scratch directory");
    let entries = cases
        .iter()
        .map(|case| {
            let name = CString::new(case.name()).unwrap();
            // SAFETY: `handle` is a live dlopen handle.
            let address = unsafe { dlsym(handle, name.as_ptr()) };
            assert!(!address.is_null(), "the library lacks {}", case.name());
            address as usize
        })
        .collect();
    (
        Route {
            name: format!("AOT {} proof-grade", opt_level_name(level)),
            full_sets,
            entries,
        },
        check,
        own_words,
    )
}

/// The register fields of an FP data-processing or FP/integer conversion
/// word: Rd [4:0], Rn [9:5], Ra [14:10] (3-source only) and Rm [20:16].
fn family(word: u32, opcode: Op) -> u32 {
    let mut fields = 0x1f | (0x1f << 5) | (0x1f << 16);
    if opcode == Op::FmaddRR {
        fields |= 0x1f << 10;
    }
    word & !fields
}

/// Compile every case through the host JIT at `level`; each published
/// function must contain the instruction family the AOT route selected.
fn jit_route(
    module: &trust_ir::Module,
    level: OptLevel,
    full_sets: bool,
    own_words: &[Vec<u32>],
) -> (Route, trust_cg_codegen::jit::ExecutableBuffer) {
    for knob in ["TCG_NO_DECODE_CHECK", "TCG_DECODE_CHECK_A64"] {
        assert!(
            std::env::var_os(knob).is_none(),
            "{knob} would relax the JIT's ENC-5 enforcement"
        );
    }
    let config = CompilerConfig {
        opt_level: level,
        ..CompilerConfig::for_host_jit()
    };
    let buffer = Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|e| panic!("JIT at {level:?}: {e:?}"))
        .buffer;
    buffer.ensure_current_thread_execute_mode();
    let code = buffer.code_slice();
    let ranges: HashMap<&str, std::ops::Range<u64>> = buffer
        .function_ranges()
        .iter()
        .map(|(name, range)| (name.as_str(), range.clone()))
        .collect();
    let cases = Case::all();
    let mut entries = Vec::new();
    for (case, own) in cases.iter().zip(own_words) {
        let name = case.name();
        let range = ranges
            .get(name.as_str())
            .unwrap_or_else(|| panic!("JIT has no range for {name}"));
        let words: Vec<u32> = code[range.start as usize..range.end as usize]
            .as_chunks::<4>()
            .0
            .iter()
            .map(|w| u32::from_le_bytes(*w))
            .collect();
        let found = own.iter().any(|&aot| {
            case.opcodes()
                .iter()
                .any(|&op| words.iter().any(|&w| family(w, op) == family(aot, op)))
        });
        assert!(
            found,
            "JIT {level:?} {name}: no word of the AOT family {own:x?}"
        );
        let ptr = buffer
            .get_fn_ptr_bound(&name)
            .unwrap_or_else(|| panic!("JIT symbol {name}"))
            .as_ptr();
        entries.push(ptr as usize);
    }
    (
        Route {
            name: format!("JIT {}", opt_level_name(level)),
            full_sets,
            entries,
        },
        buffer,
    )
}

// ===========================================================================
// Sweeps
// ===========================================================================

#[derive(Default, Clone)]
struct Tally {
    calls: u64,
    verdicts: BTreeMap<Verdict, u64>,
    examples: Vec<String>,
}

const SMALL_PREFIX: u64 = 50_000;

fn set_for(space: Space) -> InputSet {
    match space {
        Space::Fp(f) => single_set(f),
        Space::Int(width) => int_set(width),
        Space::Pair(f) => pair_set(f),
        Space::Triple(f) => triple_set(f),
    }
}

/// Run `case` (index `index`) on every route over `set`.
fn sweep(routes: &[Route], index: usize, case: Case, set: &InputSet) -> BTreeMap<String, Tally> {
    let workers = threads() as u64;
    let lanes: Vec<(usize, u64)> = routes
        .iter()
        .enumerate()
        .map(|(r, route)| {
            let len = if route.full_sets || set.exhaustive && set.len <= 1 << 17 {
                set.len
            } else {
                set.len.min(SMALL_PREFIX)
            };
            (r, len)
        })
        .collect();
    let total = set.len;
    let per = total.div_ceil(workers);
    let results: Vec<Vec<Tally>> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|worker| {
                let lanes = &lanes;
                scope.spawn(move || {
                    let mut tallies = vec![Tally::default(); routes.len()];
                    let start = worker * per;
                    let end = (start + per).min(total);
                    for i in start..end {
                        let inputs = set.get(i);
                        let want = expect(case, inputs);
                        for &(r, len) in lanes {
                            if i >= len {
                                continue;
                            }
                            // SAFETY: the entry is a compiled case function
                            // with this signature; the route keeps its code
                            // mapped for the whole test.
                            let got = unsafe {
                                let entry: Entry = std::mem::transmute(routes[r].entries[index]);
                                entry(inputs[0], inputs[1], inputs[2])
                            };
                            let verdict = judge(got, want);
                            let tally = &mut tallies[r];
                            tally.calls += 1;
                            *tally.verdicts.entry(verdict).or_default() += 1;
                            if verdict == Verdict::Mismatch && tally.examples.len() < 6 {
                                tally.examples.push(format!(
                                    "{} {}: {inputs:x?} -> {got:#x}, want {want:x?}",
                                    routes[r].name,
                                    case.name()
                                ));
                            }
                        }
                    }
                    tallies
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("worker"))
            .collect()
    });
    let mut merged = BTreeMap::new();
    for tallies in results {
        for (r, tally) in tallies.into_iter().enumerate() {
            let entry: &mut Tally = merged.entry(routes[r].name.clone()).or_default();
            entry.calls += tally.calls;
            for (k, v) in tally.verdicts {
                *entry.verdicts.entry(k).or_default() += v;
            }
            for e in tally.examples {
                if entry.examples.len() < 6 {
                    entry.examples.push(e);
                }
            }
        }
    }
    for (r, route) in routes.iter().enumerate() {
        assert_eq!(
            merged[&route.name].calls,
            lanes[r].1,
            "{} {}",
            route.name,
            case.name()
        );
    }
    merged
}

fn compile_routes() -> (
    Vec<Route>,
    Vec<trust_cg_codegen::jit::ExecutableBuffer>,
    Vec<WordCheck>,
) {
    require_fp16();
    let module = build_module();
    let mut routes = Vec::new();
    let mut checks = Vec::new();
    let mut own = Vec::new();
    for level in [OptLevel::O2, OptLevel::O0, OptLevel::O1, OptLevel::O3] {
        let (route, check, words) = aot_route(&module, level, level == OptLevel::O2);
        if level == OptLevel::O2 {
            own = words;
        }
        routes.push(route);
        checks.push(check);
    }
    let mut buffers = Vec::new();
    for level in [OptLevel::O1, OptLevel::O2] {
        let (route, buffer) = jit_route(&module, level, level == OptLevel::O1, &own);
        routes.push(route);
        buffers.push(buffer);
    }
    (routes, buffers, checks)
}

/// Run every case whose space `select` accepts on every route.
fn run(select: impl Fn(Space) -> bool) {
    let (routes, buffers, checks) = compile_routes();
    for (route, check) in routes.iter().zip(&checks) {
        println!(
            "{}: {} FP value words re-encoded, ENC-5 match and present in the object: {:?}",
            route.name, check.checked, check.by_opcode
        );
    }
    let mut failures = Vec::new();
    let mut sets: BTreeMap<Space, InputSet> = BTreeMap::new();
    for (index, case) in Case::all().into_iter().enumerate() {
        if !select(case.space()) {
            continue;
        }
        let set = sets
            .entry(case.space())
            .or_insert_with(|| set_for(case.space()))
            .clone();
        let started = Instant::now();
        let tallies = sweep(&routes, index, case, &set);
        let secs = started.elapsed().as_secs_f64();
        let mut parts = Vec::new();
        for (route, tally) in &tallies {
            let counts = tally
                .verdicts
                .iter()
                .map(|(k, v)| format!("{k:?}={v}"))
                .collect::<Vec<_>>()
                .join(" ");
            parts.push(format!("{route}: {counts}"));
            for e in &tally.examples {
                println!("    {e}");
            }
            let mismatches = tally.verdicts.get(&Verdict::Mismatch).copied().unwrap_or(0);
            if mismatches != 0 {
                failures.push(format!(
                    "{route} {}: {mismatches} mismatches, e.g. {:?}",
                    case.name(),
                    tally.examples
                ));
            }
        }
        let strength = if set.exhaustive {
            "exhaustive"
        } else {
            "statistical"
        };
        println!(
            "{:<12} {strength:<11} {:<11} {secs:.1}s | {} | {}",
            case.name(),
            set.len,
            parts.join(" | "),
            set.name
        );
        record(case, &set, &tallies, secs);
    }
    drop(buffers);
    assert!(
        failures.is_empty(),
        "lowering mismatches:\n{}",
        failures.join("\n")
    );
}

/// Append one JSON line per case when `TRUST_CG_FP_IEEE_RECORD` names a file.
fn record(case: Case, set: &InputSet, tallies: &BTreeMap<String, Tally>, secs: f64) {
    let Ok(path) = std::env::var("TRUST_CG_FP_IEEE_RECORD") else {
        return;
    };
    let routes: BTreeMap<&String, BTreeMap<String, u64>> = tallies
        .iter()
        .map(|(route, tally)| {
            (
                route,
                tally
                    .verdicts
                    .iter()
                    .map(|(k, v)| (format!("{k:?}"), *v))
                    .collect(),
            )
        })
        .collect();
    let line = serde_json::json!({
        "case": case.name(),
        "set": set.name,
        "strength": if set.exhaustive { "exhaustive" } else { "statistical" },
        "inputs": set.len,
        "routes": routes,
        "seconds": (secs * 10.0).round() / 10.0,
        "threads": threads(),
    });
    use std::io::Write as _;
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .unwrap_or_else(|e| panic!("open {path}: {e}"));
    writeln!(file, "{line}").expect("record line");
}

// ===========================================================================
// Tests
// ===========================================================================

/// Every case compiles on the proof-grade AOT route at O0-O3 and through the
/// JIT at O1 and O2; every FP value word decodes under ENC-5 and is in the
/// object, and the JIT publishes the same instruction family.
#[test]
fn every_case_compiles_with_enc5_checked_words() {
    let (routes, _buffers, checks) = compile_routes();
    assert_eq!(routes.len(), 6);
    let cases = Case::all().len();
    assert_eq!(cases, 3 * (24 + 2 + 3 + 6 + 3) + 2 * 2 + 3);
    for check in &checks {
        assert!(
            check.checked >= cases,
            "{} words for {cases} cases",
            check.checked
        );
    }
}

/// Conversions, rounding and unary operations from binary16, binary32 and
/// binary64 sources.
#[test]
fn fp_source_cases() {
    run(|space| matches!(space, Space::Fp(_)));
}

/// Integer-to-FP conversions from every 8- and 16-bit integer, and the 32-
/// and 64-bit sets.
#[test]
fn integer_source_cases() {
    run(|space| matches!(space, Space::Int(_)));
}

/// Binary arithmetic and min/max pairs, and the fused multiply-add triples.
#[test]
fn pair_and_triple_cases() {
    run(|space| matches!(space, Space::Pair(_) | Space::Triple(_)));
}

/// The committed record of the recorded release run
/// (`trust-cg-verify/tests/fixtures/fp_ieee_exhaustive/lowering.jsonl`,
/// revision and command in `run.json` there) holds every case on every route
/// with no mismatch, every binary16, binary32, 8-, 16- and 32-bit integer and
/// binary16-pair space EXHAUSTIVE on the AOT O2 and JIT O1 routes, and the
/// others statistical.
#[test]
fn recorded_exhaustive_run_covers_every_case() {
    let lines: Vec<serde_json::Value> =
        include_str!("../../trust-cg-verify/tests/fixtures/fp_ieee_exhaustive/lowering.jsonl")
            .lines()
            .map(|line| serde_json::from_str(line).expect("record line"))
            .collect();
    let cases = Case::all();
    assert_eq!(lines.len(), cases.len(), "one record line per case");
    for case in cases {
        let name = case.name();
        let line = lines
            .iter()
            .find(|l| l["case"] == name.as_str())
            .unwrap_or_else(|| panic!("the record lacks {name}"));
        let exhaustive_size: Option<u64> = match case.space() {
            Space::Fp(Format::Half) => Some(1 << 16),
            Space::Int(width) if width <= 16 => Some(1 << width),
            Space::Fp(Format::Single) | Space::Int(32) | Space::Pair(Format::Half) => Some(1 << 32),
            _ => None,
        };
        let inputs = line["inputs"].as_u64().expect("inputs");
        match exhaustive_size {
            Some(size) => {
                assert_eq!(line["strength"], "exhaustive", "{name}");
                assert_eq!(inputs, size, "{name}");
            }
            None => assert_eq!(line["strength"], "statistical", "{name}"),
        }
        let routes = line["routes"].as_object().expect("routes");
        assert_eq!(routes.len(), 6, "{name}: {routes:?}");
        for (route, verdicts) in routes {
            let verdicts = verdicts.as_object().expect("verdicts");
            assert!(
                !verdicts.contains_key("Mismatch"),
                "{name} {route}: {verdicts:?}"
            );
            let calls: u64 = verdicts.values().map(|v| v.as_u64().expect("count")).sum();
            if route == "AOT O2 proof-grade" || route == "JIT O1" {
                assert_eq!(calls, inputs, "{name} {route}");
            }
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
