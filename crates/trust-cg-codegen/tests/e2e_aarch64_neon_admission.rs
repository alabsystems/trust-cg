// Copyright 2026 Andrew Yates | Apache-2.0
//! Native differential of the NEON vector operations the lowering front end
//! admits since L04-P6, against clang -O3 NEON intrinsics.
//!
//! * Unsigned integer-lane vectors (`<16 x u8>`, `<8 x u16>`, `<4 x u32>`,
//!   `<2 x u64>`) take the lane-signedness-independent lowerings the signed
//!   shapes had: wrapping Add/Sub/Mul, And/Or/Xor, Neg/Not, every compare
//!   predicate feeding a select, and on `<4 x u32>` the three shifts by a
//!   uniform constant; `<8 x u8>` the V64 And/Or/Xor; integer-lane constants
//!   materialize at 64 bits (V64, every one of the eight D-register shapes)
//!   as well as 128 (`<4 x u32>`/`<2 x u64>` high-bit constants through the
//!   lane-pack path, uniform and mixed).
//! * Vector OR-NOT (`BorNot`, V128 and V64) lowers to NOT + ORR.
//!
//! Each TrustIR (or, for OR-NOT, LIR) function is compiled at O0-O3 into an
//! object, linked with a C driver whose references are NEON intrinsics compiled
//! by the host C compiler at -O3, and run: every function over edge-value and
//! pseudo-random vectors, byte for byte. The refusals that stay are checked by
//! name. Testing evidence on this host; no proof claim.
//!
//! Not covered here: the `<8 x u8>` compare is admitted (it lowers to the
//! `<8 x i8>` compare's typed op) but its V64 mask has no TrustIR consumer a
//! native test can observe (a select, store or return of it is refused), so
//! only the adapter tests in `trust-cg-lower/tests/vector_type_admission.rs`
//! cover it.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature};
use trust_cg_lower::instructions::{Block as LirBlock, Instruction, Opcode, Value};
use trust_cg_lower::types::Type;
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode,
    Module, Ty, UnOp, ValueId,
};

#[path = "common/native_host.rs"]
mod native_host;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn vector(lane: Ty, lanes: u32) -> Ty {
    Ty::Vector(Box::new(lane), lanes)
}

/// `fn name(a: *const V, b: *const V, out: *mut V)`: the body computes from the
/// two loaded vectors `v3` and `v4` and returns the value to store.
fn add_function(
    module: &mut Module,
    name: &str,
    ty: &Ty,
    body: impl FnOnce(&mut Vec<InstrNode>) -> ValueId,
) {
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, ft, BlockId::new(0));
    let mut nodes = vec![
        InstrNode::new(Inst::Load {
            ty: ty.clone(),
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_result(v(3)),
        InstrNode::new(Inst::Load {
            ty: ty.clone(),
            ptr: v(1),
            volatile: false,
            align: None,
        })
        .with_result(v(4)),
    ];
    let result = body(&mut nodes);
    nodes.push(InstrNode::new(Inst::Store {
        ty: ty.clone(),
        ptr: v(2),
        value: result,
        volatile: false,
        align: None,
    }));
    nodes.push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr), (v(2), Ty::Ptr)],
        body: nodes,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn binop(module: &mut Module, name: &str, ty: &Ty, op: BinOp) {
    add_function(module, name, ty, |nodes| {
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op,
                ty: ty.clone(),
                lhs: v(3),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        v(5)
    });
}

/// `select(icmp pred a b, a, b)`.
fn compare_select(module: &mut Module, name: &str, ty: &Ty, op: ICmpOp) {
    add_function(module, name, ty, |nodes| {
        nodes.push(
            InstrNode::new(Inst::ICmp {
                op,
                ty: ty.clone(),
                lhs: v(3),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: ty.clone(),
                cond: v(5),
                then_val: v(3),
                else_val: v(4),
            })
            .with_result(v(6)),
        );
        v(6)
    });
}

fn unop(module: &mut Module, name: &str, ty: &Ty, op: UnOp) {
    add_function(module, name, ty, |nodes| {
        nodes.push(
            InstrNode::new(Inst::UnOp {
                op,
                ty: ty.clone(),
                operand: v(3),
            })
            .with_result(v(5)),
        );
        v(5)
    });
}

/// `op(a, constant)` for a vector constant of `lanes`.
fn constant_binop(module: &mut Module, name: &str, ty: &Ty, op: BinOp, lanes: &[i128]) {
    add_function(module, name, ty, |nodes| {
        nodes.push(
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Vector(lanes.iter().map(|&lane| Constant::Int(lane)).collect()),
            })
            .with_result(v(5)),
        );
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op,
                ty: ty.clone(),
                lhs: v(3),
                rhs: v(5),
            })
            .with_result(v(6)),
        );
        v(6)
    });
}

/// `out = constant` for a vector constant of `lanes` (the loaded operands
/// are unused).
fn constant_store(module: &mut Module, name: &str, ty: &Ty, lanes: &[i128]) {
    add_function(module, name, ty, |nodes| {
        nodes.push(
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Vector(lanes.iter().map(|&lane| Constant::Int(lane)).collect()),
            })
            .with_result(v(5)),
        );
        v(5)
    });
}

/// The 64-bit (V64) constants `_c64_<shape>` stores, one per integer-lane
/// D-register shape: lanes at and across each sign boundary. The C driver
/// spells the same values as typed arrays.
fn v64_constants() -> [(&'static str, Ty, Vec<i128>); 8] {
    [
        (
            "i8x8",
            vector(Ty::I8, 8),
            vec![-128, -1, 0, 1, 127, -77, 55, -2],
        ),
        (
            "u8x8",
            vector(Ty::U8, 8),
            vec![0x80, 0xff, 0, 1, 0x7f, 0xb3, 0x37, 0xfe],
        ),
        ("i16x4", vector(Ty::I16, 4), vec![-32768, -1, 12345, 32767]),
        (
            "u16x4",
            vector(Ty::U16, 4),
            vec![0x8000, 0xffff, 0x3039, 0x7fff],
        ),
        (
            "i32x2",
            vector(Ty::I32, 2),
            vec![i128::from(i32::MIN), 0x1234_5678],
        ),
        ("u32x2", vector(Ty::U32, 2), vec![0x8000_0000, 0xdead_beef]),
        ("i64x1", vector(Ty::I64, 1), vec![i128::from(i64::MIN) + 5]),
        ("u64x1", vector(Ty::U64, 1), vec![0xfedc_ba98_7654_3210]),
    ]
}

/// The `<4 x u32>` constant `_u32x4_add_const` adds (mixed lanes, two of them
/// above `i32::MAX`: the lane-pack path, not the mask image).
const U32X4_CONSTANT: [i128; 4] = [0x8000_0000, 0xffff_ffff, 7, 0xdead_beef];
/// The `<2 x u64>` constant `_u64x2_add_const` adds (both lanes above
/// `i64::MAX`).
const U64X2_CONSTANT: [i128; 2] = [0x8000_0000_0000_0001, 0xfedc_ba98_7654_3210];

/// The byte constant `_u8x16_add_const` adds, every lane above `i8::MAX`.
const U8X16_CONSTANT: [i128; 16] = [
    128, 129, 200, 255, 254, 170, 171, 191, 192, 224, 240, 248, 252, 130, 131, 133,
];
/// The V64 byte constant `_u8x8_and_const` and `_u8x8_xor_const` use.
const U8X8_CONSTANT: [i128; 8] = [0x0f, 0xf0, 0x55, 0xaa, 0x01, 0x80, 0xff, 0x00];

const PREDICATES: [(ICmpOp, &str); 10] = [
    (ICmpOp::Eq, "eq"),
    (ICmpOp::Ne, "ne"),
    (ICmpOp::Ult, "ult"),
    (ICmpOp::Ule, "ule"),
    (ICmpOp::Ugt, "ugt"),
    (ICmpOp::Uge, "uge"),
    (ICmpOp::Slt, "slt"),
    (ICmpOp::Sle, "sle"),
    (ICmpOp::Sgt, "sgt"),
    (ICmpOp::Sge, "sge"),
];

/// The 128-bit unsigned shapes, by C element type name.
fn wide_shapes() -> [(&'static str, Ty); 4] {
    [
        ("u8x16", vector(Ty::U8, 16)),
        ("u16x8", vector(Ty::U16, 8)),
        ("u32x4", vector(Ty::U32, 4)),
        ("u64x2", vector(Ty::U64, 2)),
    ]
}

fn build_module() -> Module {
    let mut module = Module::new("neon_admission");
    for (shape, ty) in wide_shapes() {
        for (op, name) in [
            (BinOp::Add, "add"),
            (BinOp::Sub, "sub"),
            (BinOp::Mul, "mul"),
            (BinOp::And, "and"),
            (BinOp::Or, "or"),
            (BinOp::Xor, "xor"),
        ] {
            binop(&mut module, &format!("_{shape}_{name}"), &ty, op);
        }
        for (op, name) in PREDICATES {
            compare_select(&mut module, &format!("_{shape}_sel_{name}"), &ty, op);
        }
        unop(&mut module, &format!("_{shape}_neg"), &ty, UnOp::Neg);
        unop(&mut module, &format!("_{shape}_not"), &ty, UnOp::Not);
    }
    let u32x4 = vector(Ty::U32, 4);
    for (op, name, amount) in [
        (BinOp::Shl, "shl", 3),
        (BinOp::LShr, "lshr", 5),
        (BinOp::AShr, "ashr", 7),
    ] {
        constant_binop(
            &mut module,
            &format!("_u32x4_{name}"),
            &u32x4,
            op,
            &[amount; 4],
        );
    }
    constant_binop(
        &mut module,
        "_u8x16_add_const",
        &vector(Ty::U8, 16),
        BinOp::Add,
        &U8X16_CONSTANT,
    );
    let u64x2 = vector(Ty::U64, 2);
    constant_binop(
        &mut module,
        "_u32x4_add_const",
        &u32x4,
        BinOp::Add,
        &U32X4_CONSTANT,
    );
    constant_binop(
        &mut module,
        "_u64x2_add_const",
        &u64x2,
        BinOp::Add,
        &U64X2_CONSTANT,
    );
    constant_binop(
        &mut module,
        "_u32x4_xor_splat",
        &u32x4,
        BinOp::Xor,
        &[0x8000_0001; 4],
    );
    constant_binop(
        &mut module,
        "_u64x2_xor_splat",
        &u64x2,
        BinOp::Xor,
        &[0xffff_ffff_0000_0001; 2],
    );
    for (shape, ty, lanes) in v64_constants() {
        constant_store(&mut module, &format!("_c64_{shape}"), &ty, &lanes);
    }
    let u8x8 = vector(Ty::U8, 8);
    for (op, name) in [(BinOp::And, "and"), (BinOp::Or, "or"), (BinOp::Xor, "xor")] {
        binop(&mut module, &format!("_u8x8_{name}"), &u8x8, op);
    }
    constant_binop(
        &mut module,
        "_u8x8_and_const",
        &u8x8,
        BinOp::And,
        &U8X8_CONSTANT,
    );
    constant_binop(
        &mut module,
        "_u8x8_xor_const",
        &u8x8,
        BinOp::Xor,
        &U8X8_CONSTANT,
    );
    module
}

/// The C driver: every function above against its clang -O3 NEON intrinsic
/// reference, over edge-value and pseudo-random vectors.
const DRIVER: &str = r#"
#include <arm_neon.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef void (*fn3)(const void *, const void *, void *);
#define TRIALS 4096

static uint64_t state = 0x243f6a8885a308d3ull;
static uint64_t next64(void) {
    state ^= state << 13; state ^= state >> 7; state ^= state << 17;
    return state;
}
static const uint8_t EDGE[] = {0x00, 0x01, 0x02, 0x7f, 0x80, 0x81, 0xfe, 0xff, 0x55, 0xaa};
/* Early trials draw every byte from edge values, so lanes of every width
   meet 0, 1, the sign boundary and all-ones; later ones are random. */
static void fill(uint8_t *p, int n, int trial, int salt) {
    for (int i = 0; i < n; i++) {
        if (trial < 512) {
            unsigned k = (unsigned)(trial * 7 + i * (salt + 3) + (trial >> 3) * salt);
            p[i] = EDGE[k % sizeof EDGE];
        } else {
            p[i] = (uint8_t)next64();
        }
    }
}

static int failures = 0;
static void report(const char *name, int trial, const uint8_t *a, const uint8_t *b,
                   const uint8_t *got, const uint8_t *want, int n) {
    if (failures++ > 8) return;
    printf("MISMATCH %s trial %d\n a=", name, trial);
    for (int i = 0; i < n; i++) printf("%02x", a[i]);
    printf("\n b=");
    for (int i = 0; i < n; i++) printf("%02x", b[i]);
    printf("\n got=");
    for (int i = 0; i < n; i++) printf("%02x", got[i]);
    printf("\n want=");
    for (int i = 0; i < n; i++) printf("%02x", want[i]);
    printf("\n");
}

#define CHECK(NAME, BYTES, REF)                                              \
    do {                                                                     \
        for (int t = 0; t < TRIALS; t++) {                                   \
            uint8_t a[BYTES], b[BYTES], got[BYTES], want[BYTES];             \
            fill(a, BYTES, t, 1);                                            \
            fill(b, BYTES, t, 2);                                            \
            memset(got, 0xcc, BYTES);                                        \
            NAME(a, b, got);                                                 \
            REF(a, b, want);                                                 \
            if (memcmp(got, want, BYTES)) {                                  \
                report(#NAME, t, a, b, got, want, BYTES);                    \
                break;                                                       \
            }                                                                \
        }                                                                    \
        checked++;                                                           \
    } while (0)

/* q-register references: load both operands, apply OP, store. */
#define QREF(NAME, T, LD, ST, EXPR)                                          \
    static void NAME(const uint8_t *pa, const uint8_t *pb, uint8_t *out) {   \
        T a = LD((const void *)pa); T b = LD((const void *)pb);              \
        (void)b; ST((void *)out, EXPR);                                      \
    }

#define SHAPE(S, T, LD, ST, SUF, SSUF, ST_T)                                 \
    QREF(r_##S##_add, T, LD, ST, vaddq_##SUF(a, b))                          \
    QREF(r_##S##_sub, T, LD, ST, vsubq_##SUF(a, b))                          \
    QREF(r_##S##_and, T, LD, ST, vandq_##SUF(a, b))                          \
    QREF(r_##S##_or, T, LD, ST, vorrq_##SUF(a, b))                           \
    QREF(r_##S##_xor, T, LD, ST, veorq_##SUF(a, b))                          \
    QREF(r_##S##_sel_eq, T, LD, ST, vbslq_##SUF(vceqq_##SUF(a, b), a, b))    \
    QREF(r_##S##_sel_ne, T, LD, ST, vbslq_##SUF(vceqq_##SUF(a, b), b, a))    \
    QREF(r_##S##_sel_ult, T, LD, ST, vbslq_##SUF(vcltq_##SUF(a, b), a, b))   \
    QREF(r_##S##_sel_ule, T, LD, ST, vbslq_##SUF(vcleq_##SUF(a, b), a, b))   \
    QREF(r_##S##_sel_ugt, T, LD, ST, vbslq_##SUF(vcgtq_##SUF(a, b), a, b))   \
    QREF(r_##S##_sel_uge, T, LD, ST, vbslq_##SUF(vcgeq_##SUF(a, b), a, b))   \
    QREF(r_##S##_sel_slt, T, LD, ST,                                         \
         vbslq_##SUF(vcltq_##SSUF(vreinterpretq_##SSUF##_##SUF(a),          \
                                   vreinterpretq_##SSUF##_##SUF(b)), a, b))  \
    QREF(r_##S##_sel_sle, T, LD, ST,                                         \
         vbslq_##SUF(vcleq_##SSUF(vreinterpretq_##SSUF##_##SUF(a),          \
                                   vreinterpretq_##SSUF##_##SUF(b)), a, b))  \
    QREF(r_##S##_sel_sgt, T, LD, ST,                                         \
         vbslq_##SUF(vcgtq_##SSUF(vreinterpretq_##SSUF##_##SUF(a),          \
                                   vreinterpretq_##SSUF##_##SUF(b)), a, b))  \
    QREF(r_##S##_sel_sge, T, LD, ST,                                         \
         vbslq_##SUF(vcgeq_##SSUF(vreinterpretq_##SSUF##_##SUF(a),          \
                                   vreinterpretq_##SSUF##_##SUF(b)), a, b))  \
    QREF(r_##S##_neg, T, LD, ST,                                             \
         vreinterpretq_##SUF##_##SSUF(vnegq_##SSUF(                          \
             vreinterpretq_##SSUF##_##SUF(a))))                             \
    QREF(r_##S##_not, T, LD, ST, veorq_##SUF(a, vdupq_n_##SUF((ST_T)~(ST_T)0)))

SHAPE(u8x16, uint8x16_t, vld1q_u8, vst1q_u8, u8, s8, uint8_t)
SHAPE(u16x8, uint16x8_t, vld1q_u16, vst1q_u16, u16, s16, uint16_t)
SHAPE(u32x4, uint32x4_t, vld1q_u32, vst1q_u32, u32, s32, uint32_t)
SHAPE(u64x2, uint64x2_t, vld1q_u64, vst1q_u64, u64, s64, uint64_t)

QREF(r_u8x16_mul, uint8x16_t, vld1q_u8, vst1q_u8, vmulq_u8(a, b))
QREF(r_u16x8_mul, uint16x8_t, vld1q_u16, vst1q_u16, vmulq_u16(a, b))
QREF(r_u32x4_mul, uint32x4_t, vld1q_u32, vst1q_u32, vmulq_u32(a, b))
/* NEON has no 64-bit lane multiply; clang -O3 scalarizes this. */
static void r_u64x2_mul(const uint8_t *pa, const uint8_t *pb, uint8_t *out) {
    uint64_t a[2], b[2], o[2];
    memcpy(a, pa, 16); memcpy(b, pb, 16);
    o[0] = a[0] * b[0]; o[1] = a[1] * b[1];
    memcpy(out, o, 16);
}
QREF(r_u32x4_shl, uint32x4_t, vld1q_u32, vst1q_u32, vshlq_n_u32(a, 3))
QREF(r_u32x4_lshr, uint32x4_t, vld1q_u32, vst1q_u32, vshrq_n_u32(a, 5))
QREF(r_u32x4_ashr, uint32x4_t, vld1q_u32, vst1q_u32,
     vreinterpretq_u32_s32(vshrq_n_s32(vreinterpretq_s32_u32(a), 7)))
static const uint8_t K16[16] = {128, 129, 200, 255, 254, 170, 171, 191,
                                192, 224, 240, 248, 252, 130, 131, 133};
QREF(r_u8x16_add_const, uint8x16_t, vld1q_u8, vst1q_u8, vaddq_u8(a, vld1q_u8(K16)))
static const uint32_t K32[4] = {0x80000000u, 0xffffffffu, 7u, 0xdeadbeefu};
QREF(r_u32x4_add_const, uint32x4_t, vld1q_u32, vst1q_u32, vaddq_u32(a, vld1q_u32(K32)))
static const uint64_t K64[2] = {0x8000000000000001ull, 0xfedcba9876543210ull};
QREF(r_u64x2_add_const, uint64x2_t, vld1q_u64, vst1q_u64, vaddq_u64(a, vld1q_u64(K64)))
QREF(r_u32x4_xor_splat, uint32x4_t, vld1q_u32, vst1q_u32,
     veorq_u32(a, vdupq_n_u32(0x80000001u)))
QREF(r_u64x2_xor_splat, uint64x2_t, vld1q_u64, vst1q_u64,
     veorq_u64(a, vdupq_n_u64(0xffffffff00000001ull)))
/* The V64 constants, one per D-register shape, as typed arrays. */
static const int8_t C_i8x8[8] = {-128, -1, 0, 1, 127, -77, 55, -2};
static const uint8_t C_u8x8[8] = {0x80, 0xff, 0, 1, 0x7f, 0xb3, 0x37, 0xfe};
static const int16_t C_i16x4[4] = {-32768, -1, 12345, 32767};
static const uint16_t C_u16x4[4] = {0x8000, 0xffff, 0x3039, 0x7fff};
static const int32_t C_i32x2[2] = {INT32_MIN, 0x12345678};
static const uint32_t C_u32x2[2] = {0x80000000u, 0xdeadbeefu};
static const int64_t C_i64x1[1] = {INT64_MIN + 5};
static const uint64_t C_u64x1[1] = {0xfedcba9876543210ull};
QREF(r_c64_i8x8, int8x8_t, vld1_s8, vst1_s8, vld1_s8(C_i8x8))
QREF(r_c64_u8x8, uint8x8_t, vld1_u8, vst1_u8, vld1_u8(C_u8x8))
QREF(r_c64_i16x4, int16x4_t, vld1_s16, vst1_s16, vld1_s16(C_i16x4))
QREF(r_c64_u16x4, uint16x4_t, vld1_u16, vst1_u16, vld1_u16(C_u16x4))
QREF(r_c64_i32x2, int32x2_t, vld1_s32, vst1_s32, vld1_s32(C_i32x2))
QREF(r_c64_u32x2, uint32x2_t, vld1_u32, vst1_u32, vld1_u32(C_u32x2))
QREF(r_c64_i64x1, int64x1_t, vld1_s64, vst1_s64, vld1_s64(C_i64x1))
QREF(r_c64_u64x1, uint64x1_t, vld1_u64, vst1_u64, vld1_u64(C_u64x1))
QREF(r_u8x8_and, uint8x8_t, vld1_u8, vst1_u8, vand_u8(a, b))
QREF(r_u8x8_or, uint8x8_t, vld1_u8, vst1_u8, vorr_u8(a, b))
QREF(r_u8x8_xor, uint8x8_t, vld1_u8, vst1_u8, veor_u8(a, b))
static const uint8_t K8[8] = {0x0f, 0xf0, 0x55, 0xaa, 0x01, 0x80, 0xff, 0x00};
QREF(r_u8x8_and_const, uint8x8_t, vld1_u8, vst1_u8, vand_u8(a, vld1_u8(K8)))
QREF(r_u8x8_xor_const, uint8x8_t, vld1_u8, vst1_u8, veor_u8(a, vld1_u8(K8)))

#define DECL(S)                                                              \
    extern void _##S##_add(const void *, const void *, void *);              \
    extern void _##S##_sub(const void *, const void *, void *);              \
    extern void _##S##_mul(const void *, const void *, void *);              \
    extern void _##S##_and(const void *, const void *, void *);              \
    extern void _##S##_or(const void *, const void *, void *);               \
    extern void _##S##_xor(const void *, const void *, void *);              \
    extern void _##S##_sel_eq(const void *, const void *, void *);           \
    extern void _##S##_sel_ne(const void *, const void *, void *);           \
    extern void _##S##_sel_ult(const void *, const void *, void *);          \
    extern void _##S##_sel_ule(const void *, const void *, void *);          \
    extern void _##S##_sel_ugt(const void *, const void *, void *);          \
    extern void _##S##_sel_uge(const void *, const void *, void *);          \
    extern void _##S##_sel_slt(const void *, const void *, void *);          \
    extern void _##S##_sel_sle(const void *, const void *, void *);          \
    extern void _##S##_sel_sgt(const void *, const void *, void *);          \
    extern void _##S##_sel_sge(const void *, const void *, void *);          \
    extern void _##S##_neg(const void *, const void *, void *);              \
    extern void _##S##_not(const void *, const void *, void *);
DECL(u8x16)
DECL(u16x8)
DECL(u32x4)
DECL(u64x2)
extern void _u32x4_shl(const void *, const void *, void *);
extern void _u32x4_lshr(const void *, const void *, void *);
extern void _u32x4_ashr(const void *, const void *, void *);
extern void _u8x16_add_const(const void *, const void *, void *);
extern void _u32x4_add_const(const void *, const void *, void *);
extern void _u64x2_add_const(const void *, const void *, void *);
extern void _u32x4_xor_splat(const void *, const void *, void *);
extern void _u64x2_xor_splat(const void *, const void *, void *);
extern void _c64_i8x8(const void *, const void *, void *);
extern void _c64_u8x8(const void *, const void *, void *);
extern void _c64_i16x4(const void *, const void *, void *);
extern void _c64_u16x4(const void *, const void *, void *);
extern void _c64_i32x2(const void *, const void *, void *);
extern void _c64_u32x2(const void *, const void *, void *);
extern void _c64_i64x1(const void *, const void *, void *);
extern void _c64_u64x1(const void *, const void *, void *);
extern void _u8x8_and(const void *, const void *, void *);
extern void _u8x8_or(const void *, const void *, void *);
extern void _u8x8_xor(const void *, const void *, void *);
extern void _u8x8_and_const(const void *, const void *, void *);
extern void _u8x8_xor_const(const void *, const void *, void *);

#define RUN(S)                                                               \
    CHECK(_##S##_add, 16, r_##S##_add);                                      \
    CHECK(_##S##_sub, 16, r_##S##_sub);                                      \
    CHECK(_##S##_mul, 16, r_##S##_mul);                                      \
    CHECK(_##S##_and, 16, r_##S##_and);                                      \
    CHECK(_##S##_or, 16, r_##S##_or);                                        \
    CHECK(_##S##_xor, 16, r_##S##_xor);                                      \
    CHECK(_##S##_sel_eq, 16, r_##S##_sel_eq);                                \
    CHECK(_##S##_sel_ne, 16, r_##S##_sel_ne);                                \
    CHECK(_##S##_sel_ult, 16, r_##S##_sel_ult);                              \
    CHECK(_##S##_sel_ule, 16, r_##S##_sel_ule);                              \
    CHECK(_##S##_sel_ugt, 16, r_##S##_sel_ugt);                              \
    CHECK(_##S##_sel_uge, 16, r_##S##_sel_uge);                              \
    CHECK(_##S##_sel_slt, 16, r_##S##_sel_slt);                              \
    CHECK(_##S##_sel_sle, 16, r_##S##_sel_sle);                              \
    CHECK(_##S##_sel_sgt, 16, r_##S##_sel_sgt);                              \
    CHECK(_##S##_sel_sge, 16, r_##S##_sel_sge);                              \
    CHECK(_##S##_neg, 16, r_##S##_neg);                                      \
    CHECK(_##S##_not, 16, r_##S##_not);

int main(void) {
    int checked = 0;
    RUN(u8x16)
    RUN(u16x8)
    RUN(u32x4)
    RUN(u64x2)
    CHECK(_u32x4_shl, 16, r_u32x4_shl);
    CHECK(_u32x4_lshr, 16, r_u32x4_lshr);
    CHECK(_u32x4_ashr, 16, r_u32x4_ashr);
    CHECK(_u8x16_add_const, 16, r_u8x16_add_const);
    CHECK(_u32x4_add_const, 16, r_u32x4_add_const);
    CHECK(_u64x2_add_const, 16, r_u64x2_add_const);
    CHECK(_u32x4_xor_splat, 16, r_u32x4_xor_splat);
    CHECK(_u64x2_xor_splat, 16, r_u64x2_xor_splat);
    CHECK(_c64_i8x8, 8, r_c64_i8x8);
    CHECK(_c64_u8x8, 8, r_c64_u8x8);
    CHECK(_c64_i16x4, 8, r_c64_i16x4);
    CHECK(_c64_u16x4, 8, r_c64_u16x4);
    CHECK(_c64_i32x2, 8, r_c64_i32x2);
    CHECK(_c64_u32x2, 8, r_c64_u32x2);
    CHECK(_c64_i64x1, 8, r_c64_i64x1);
    CHECK(_c64_u64x1, 8, r_c64_u64x1);
    CHECK(_u8x8_and, 8, r_u8x8_and);
    CHECK(_u8x8_or, 8, r_u8x8_or);
    CHECK(_u8x8_xor, 8, r_u8x8_xor);
    CHECK(_u8x8_and_const, 8, r_u8x8_and_const);
    CHECK(_u8x8_xor_const, 8, r_u8x8_xor_const);
    printf("neon admission: %d functions x %d vectors checked, %d mismatching\n",
           checked, TRIALS, failures);
    return failures ? 1 : 0;
}
"#;

/// The driver for the LIR OR-NOT functions: `a | ~b` at 16 and 8 bytes,
/// against `vornq_u8` / `vorn_u8`.
const ORN_DRIVER: &str = r#"
#include <arm_neon.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern void _neon_bornot_q(const void *, const void *, void *);
extern void _neon_bornot_d(const void *, const void *, void *);

static uint64_t state = 0x9e3779b97f4a7c15ull;
static uint64_t next64(void) {
    state ^= state << 13; state ^= state >> 7; state ^= state << 17;
    return state;
}

int main(void) {
    int checked = 0;
    for (int t = 0; t < 8192; t++) {
        uint8_t a[16], b[16], got[16], want[16];
        for (int i = 0; i < 16; i++) {
            a[i] = t < 256 ? (uint8_t)t : (uint8_t)next64();
            b[i] = t < 256 ? (uint8_t)(t * 37 + i) : (uint8_t)next64();
        }
        memset(got, 0xcc, 16);
        _neon_bornot_q(a, b, got);
        vst1q_u8(want, vornq_u8(vld1q_u8(a), vld1q_u8(b)));
        if (memcmp(got, want, 16)) { printf("MISMATCH q trial %d\n", t); return 1; }
        memset(got, 0xcc, 16);
        _neon_bornot_d(a, b, got);
        vst1_u8(want, vorn_u8(vld1_u8(a), vld1_u8(b)));
        if (memcmp(got, want, 8) || got[8] != 0xcc) { printf("MISMATCH d trial %d\n", t); return 2; }
        checked += 2;
    }
    printf("neon or-not: %d calls checked\n", checked);
    return 0;
}
"#;

/// A fresh scratch directory, removed when dropped (also on failure).
struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Scratch {
        let dir = std::env::temp_dir().join(format!(
            "trust_cg_neon_admission_{tag}_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create scratch directory");
        Scratch(dir)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Link `object` with `driver` (compiled at -O3 by the host C compiler) and
/// run it; returns its stdout, panicking with the transcript on failure.
fn link_and_run(dir: &Path, tag: &str, object: &[u8], driver: &str) -> String {
    let object_path = dir.join(format!("{tag}.o"));
    let driver_path = dir.join(format!("{tag}_driver.c"));
    let binary = dir.join(format!("{tag}_bin"));
    fs::write(&object_path, object).expect("write object");
    fs::write(&driver_path, driver).expect("write driver");
    let link = Command::new(native_host::C_COMPILER)
        .arg("-O3")
        .arg(&driver_path)
        .arg(&object_path)
        .arg("-o")
        .arg(&binary)
        .args(native_host::link_hardening_args())
        .output()
        .expect("run the host C compiler");
    assert!(
        link.status.success(),
        "{tag}: link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&binary)
        .output()
        .expect("run the linked binary");
    let stdout = String::from_utf8_lossy(&run.stdout).into_owned();
    assert!(
        run.status.success(),
        "{tag}: native differential failed ({:?}):\n{stdout}{}",
        run.status,
        String::from_utf8_lossy(&run.stderr)
    );
    stdout
}

#[test]
fn unsigned_and_v64_vector_operations_match_clang_neon_intrinsics() {
    let module = build_module();
    let scratch = Scratch::new("ops");
    for level in LEVELS {
        let compiled = Compiler::new(CompilerConfig {
            opt_level: level,
            ..CompilerConfig::default()
        })
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .unwrap_or_else(|error| panic!("{level:?}: the admitted operations must compile: {error}"));
        let stdout = link_and_run(
            &scratch.0,
            &format!("ops_{level:?}"),
            &compiled.object_code,
            DRIVER,
        );
        eprintln!("{level:?}: {}", stdout.trim());
        assert!(
            stdout.contains("93 functions x 4096 vectors checked, 0 mismatching"),
            "{level:?}: {stdout}"
        );
    }
}

/// `fn name(a: *const V, b: *const V, out: *mut V) { *out = a | !b }` in LIR,
/// the only route a vector `BorNot` reaches the selector by.
fn bornot_lir(name: &str, ty: Type) -> LirFunction {
    let mut function = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64, Type::I64],
            returns: vec![],
        },
    );
    let entry = LirBlock(0);
    function.entry_block = entry;
    function.block_order.push(entry);
    function.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: ty.clone(),
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::Load {
                        ty: ty.clone(),
                        align: None,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::BorNot,
                    args: vec![Value(3), Value(4)],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Store { ty, align: None },
                    args: vec![Value(5), Value(2)],
                    results: vec![],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    function
}

#[test]
fn vector_or_not_matches_vorn() {
    let scratch = Scratch::new("orn");
    for level in LEVELS {
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: level,
            target_triple: native_host::TRIPLE.into(),
            ..PipelineConfig::default()
        });
        let mut objects = Vec::new();
        for (name, ty) in [
            ("_neon_bornot_q", Type::V128),
            ("_neon_bornot_d", Type::V64),
        ] {
            let object = pipeline
                .compile_function(&bornot_lir(name, ty))
                .unwrap_or_else(|error| panic!("{level:?} {name}: {error}"));
            objects.push((name, object));
        }
        // Two objects, one driver: link them together.
        let dir = &scratch.0;
        let mut paths = Vec::new();
        for (name, object) in &objects {
            let path = dir.join(format!("{name}_{level:?}.o"));
            fs::write(&path, object).expect("write object");
            paths.push(path);
        }
        let driver_path = dir.join("orn_driver.c");
        fs::write(&driver_path, ORN_DRIVER).expect("write driver");
        let binary = dir.join(format!("orn_{level:?}"));
        let link = Command::new(native_host::C_COMPILER)
            .arg("-O3")
            .arg(&driver_path)
            .args(&paths)
            .arg("-o")
            .arg(&binary)
            .args(native_host::link_hardening_args())
            .output()
            .expect("run the host C compiler");
        assert!(
            link.status.success(),
            "{level:?}: link failed:\n{}",
            String::from_utf8_lossy(&link.stderr)
        );
        let run = Command::new(&binary).output().expect("run");
        let stdout = String::from_utf8_lossy(&run.stdout);
        assert!(run.status.success(), "{level:?}: {stdout}");
        assert!(
            stdout.contains("16384 calls checked"),
            "{level:?}: {stdout}"
        );
    }
}

/// `fn f(params..) -> result { instruction }` with the parameters as values
/// `0..`, the instruction's result as value 10.
fn single_instruction(module: &mut Module, params: Vec<Ty>, result: Ty, instruction: Inst) {
    let ft = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![result],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, "_single", ft, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (v(index as u32), ty))
            .collect(),
        body: vec![
            InstrNode::new(instruction).with_result(v(10)),
            InstrNode::new(Inst::Return {
                values: vec![v(10)],
            }),
        ],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

/// The vector operations that stay refused, by name, through the whole
/// compiler: shifts on 8-, 16- and 64-bit lanes, V64 arithmetic, operations
/// on the remaining 64-bit shapes, lane division, a select whose condition no
/// compare produced (a parameter), and vector conversions.
#[test]
fn the_remaining_vector_operations_are_refused_by_name() {
    let refused = |name: &str, build: &dyn Fn(&mut Module)| {
        let mut module = Module::new("neon_refusal");
        build(&mut module);
        let error = Compiler::new(CompilerConfig::default())
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .err()
            .unwrap_or_else(|| panic!("{name}: must be refused"));
        format!("{error}")
    };
    for (shape, ty) in [
        ("u8x16", vector(Ty::U8, 16)),
        ("u16x8", vector(Ty::U16, 8)),
        ("u64x2", vector(Ty::U64, 2)),
        ("i8x16", vector(Ty::I8, 16)),
    ] {
        let message = refused(shape, &|module| binop(module, "_shl", &ty, BinOp::Shl));
        assert!(
            message.contains("BinOp::Shl is not supported"),
            "{shape} shl: {message}"
        );
    }
    for ty in [vector(Ty::U8, 8), vector(Ty::I8, 8)] {
        let message = refused("v64 add", &|module| binop(module, "_add", &ty, BinOp::Add));
        assert!(
            message.contains("BinOp::Add is not supported by V64 vector lowering"),
            "{ty:?}: {message}"
        );
    }
    for ty in [vector(Ty::U16, 4), vector(Ty::U32, 2)] {
        let message = refused("v64 shape", &|module| {
            binop(module, "_and", &ty, BinOp::And)
        });
        assert!(
            message.contains("over unsupported vector shape"),
            "{ty:?}: {message}"
        );
    }
    let message = refused("udiv", &|module| {
        binop(module, "_udiv", &vector(Ty::U32, 4), BinOp::UDiv)
    });
    assert!(
        message.contains("BinOp::UDiv is not supported"),
        "{message}"
    );
    for ty in [vector(Ty::U32, 4), vector(Ty::U8, 16), vector(Ty::I64, 2)] {
        let message = refused("parameter select", &|module| {
            single_instruction(
                module,
                vec![ty.clone(), ty.clone(), ty.select_condition_ty()],
                ty.clone(),
                Inst::Select {
                    ty: ty.clone(),
                    cond: v(2),
                    then_val: v(0),
                    else_val: v(1),
                },
            )
        });
        assert!(
            message.contains("condition ValueId(2) must be produced by a"),
            "{ty:?}: {message}"
        );
    }
    // A lane-wise vector conversion is not valid trust-ir: its validator types
    // every conversion over scalars (`check_cast_compatibility`), so the
    // compiler's ingestion admission (WS7.3) refuses each one by trust-ir's
    // own finding, `CastIncompatible`, naming the cast and both types, before
    // any lowering. The adapter's own by-name refusal of the same casts
    // (`AdapterError::UnsupportedInstruction`) stays pinned below that
    // admission by trust-cg-lower's `tests/vector_type_admission.rs`
    // (`well_shaped_vector_conversions_stay_refused_instead_of_using_scalar_casts`).
    // Decision record LD-79.
    for (op, source, destination) in [
        (CastOp::UIToFP, vector(Ty::U32, 4), vector(Ty::F32, 4)),
        (CastOp::SIToFP, vector(Ty::I32, 4), vector(Ty::F32, 4)),
        (CastOp::FPToSI, vector(Ty::F32, 4), vector(Ty::I32, 4)),
        (CastOp::ZExt, vector(Ty::U8, 8), vector(Ty::U16, 8)),
    ] {
        let mut module = Module::new("neon_refusal");
        single_instruction(
            &mut module,
            vec![source.clone()],
            destination.clone(),
            Inst::Cast {
                op,
                src_ty: source.clone(),
                dst_ty: destination.clone(),
                operand: v(0),
            },
        );
        let error = Compiler::new(CompilerConfig::default())
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .err()
            .unwrap_or_else(|| panic!("{op:?} {source:?} -> {destination:?}: must be refused"));
        let (op_name, src_name, dst_name) =
            (op.to_string(), source.to_string(), destination.to_string());
        assert!(
            matches!(
                &error,
                trust_cg_codegen::compiler::CompileError::InvalidTrustIr(refusal)
                    if refusal.any(|finding| matches!(
                        finding,
                        trust_ir_build::ValidationError::CastIncompatible { op, src, dst, .. }
                            if *op == op_name && *src == src_name && *dst == dst_name
                    ))
            ),
            "{op:?} {source:?} -> {destination:?}: {error}"
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes, and no refusal is the license's, by accident.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
