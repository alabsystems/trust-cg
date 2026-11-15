// Copyright 2026 Andrew Yates | Apache-2.0
//! Construct sweep, CASTS (ledger L05-P2, Darwin row D05): `CastOp::PtrToPtr`,
//! `CastOp::Bitcast` and `CastOp::Transmute` executed natively on
//! aarch64-apple-darwin at O0-O3.
//!
//! `Transmute` is an equal-size reinterpretation of the source's byte image
//! under trust-ir's own layouts (`Module::layout_sensitive_cast_evidence`
//! must answer `SameSize`). The pinned reference interpreter executes the
//! `Transmute` spelling only over the integer/pointer scalars (the Lean
//! `semCast` scalar partial); every other shape here is checked against the
//! interpreter's run of a TWIN that spells the same reinterpretation in
//! constructs it executes — the `Bitcast` of an integer/float pair, or the
//! store/load memory lane (store the source, load the destination at the
//! same address) — and against the C `memcpy` meaning. The test also pins
//! that the interpreter refuses those `Transmute` spellings, so the twin is
//! a stated substitution, not a hidden one. What stays refused (unequal
//! sizes, validity-carrying leaves, source padding, undeclared layouts) is
//! refused by name.
//!
//! Execution evidence on this host only (Mach-O objects linked by the host
//! `cc`); not a proof of any lowering.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

#[path = "common/construct_sweep.rs"]
mod sweep;

#[path = "common/admission_expect.rs"]
mod admission_expect;

use sweep::{Arg, Body, Call, compile, define, interpret, sweep, sweep_module};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::interpret::InterpretErrorCode;
use trust_ir::{
    BinOp, CastOp, Constant, FieldDef, Inst, Module, StructDef, StructId, StructRepr, Ty, UnOp,
    ValueId,
};

fn binop(body: &mut Body, op: BinOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
    body.emit(Inst::BinOp { op, ty, lhs, rhs })
}

fn int_const(body: &mut Body, ty: Ty, value: i128) -> ValueId {
    body.emit(Inst::Const {
        ty,
        value: Constant::Int(value),
    })
}

fn ret(body: &mut Body, values: Vec<ValueId>) {
    body.effect(Inst::Return { values });
}

fn cast(body: &mut Body, op: CastOp, src_ty: Ty, dst_ty: Ty, operand: ValueId) -> ValueId {
    body.emit(Inst::Cast {
        op,
        src_ty,
        dst_ty,
        operand,
    })
}

/// `Transmute src -> dst`.
fn transmute(body: &mut Body, src_ty: Ty, dst_ty: Ty, operand: ValueId) -> ValueId {
    cast(body, CastOp::Transmute, src_ty, dst_ty, operand)
}

/// The memory-lane twin of `Transmute src -> dst`: store, then load.
fn through_memory(body: &mut Body, src_ty: Ty, dst_ty: Ty, operand: ValueId) -> ValueId {
    let slot = body.emit(Inst::Alloca {
        ty: src_ty.clone(),
        count: None,
        align: Some(16),
    });
    body.effect(Inst::Store {
        ty: src_ty,
        ptr: slot,
        value: operand,
        volatile: false,
        align: None,
    });
    body.emit(Inst::Load {
        ty: dst_ty,
        ptr: slot,
        volatile: false,
        align: None,
    })
}

fn field(name: &str, ty: Ty, offset: u64) -> FieldDef {
    FieldDef {
        name: name.to_string(),
        ty,
        offset: Some(offset),
    }
}

/// Pointer retypes and `Bitcast`s.
fn pointer_and_bitcast_module() -> Module {
    let mut module = sweep_module("construct_sweep_ptr_bitcast");

    // A stack cell written through `*mut u64`, read through `&u64` and back
    // through the untyped pointer.
    let mut body = Body::new();
    let x = body.param(Ty::U64);
    let slot = body.emit(Inst::Alloca {
        ty: Ty::U64,
        count: None,
        align: None,
    });
    let unique = cast(
        &mut body,
        CastOp::PtrToPtr,
        Ty::Ptr,
        Ty::PtrMut(Box::new(Ty::U64)),
        slot,
    );
    body.effect(Inst::Store {
        ty: Ty::U64,
        ptr: unique,
        value: x,
        volatile: false,
        align: None,
    });
    let shared = cast(
        &mut body,
        CastOp::PtrToPtr,
        Ty::PtrMut(Box::new(Ty::U64)),
        Ty::Ref(Box::new(Ty::U64)),
        unique,
    );
    let raw = cast(
        &mut body,
        CastOp::PtrToPtr,
        Ty::Ref(Box::new(Ty::U64)),
        Ty::Ptr,
        shared,
    );
    let read = body.emit(Inst::Load {
        ty: Ty::U64,
        ptr: raw,
        volatile: false,
        align: None,
    });
    let five = int_const(&mut body, Ty::U64, 5);
    let next = binop(&mut body, BinOp::Add, Ty::U64, read, five);
    ret(&mut body, vec![next]);
    define(
        &mut module,
        "sweep_retype",
        vec![Ty::U64],
        vec![Ty::U64],
        body,
    );

    for (name, src, dst) in [
        ("sweep_bitcast_f64_u64", Ty::F64, Ty::U64),
        ("sweep_bitcast_u32_f32", Ty::U32, Ty::F32),
        ("sweep_bitcast_f32_i32", Ty::F32, Ty::I32),
        ("sweep_bitcast_i64_f64", Ty::I64, Ty::F64),
    ] {
        let mut body = Body::new();
        let x = body.param(src.clone());
        let y = cast(&mut body, CastOp::Bitcast, src.clone(), dst.clone(), x);
        ret(&mut body, vec![y]);
        define(&mut module, name, vec![src], vec![dst], body);
    }

    // i64 -> f64 -> fneg -> i64 flips exactly the sign bit.
    let mut body = Body::new();
    let x = body.param(Ty::I64);
    let as_float = cast(&mut body, CastOp::Bitcast, Ty::I64, Ty::F64, x);
    let negated = body.emit(Inst::UnOp {
        op: UnOp::FNeg,
        ty: Ty::F64,
        operand: as_float,
    });
    let back = cast(&mut body, CastOp::Bitcast, Ty::F64, Ty::I64, negated);
    ret(&mut body, vec![back]);
    define(
        &mut module,
        "sweep_bitcast_sign_flip",
        vec![Ty::I64],
        vec![Ty::I64],
        body,
    );
    module
}

#[test]
fn native_ptr_to_ptr_and_bitcast_match_the_interpreter_and_c_o0_through_o3() {
    let module = pointer_and_bitcast_module();
    let u64a = |value: u64| Arg(Ty::U64, u128::from(value));
    let i64a = |value: i64| Arg(Ty::I64, u128::from(value as u64));
    let calls = vec![
        Call::new(
            "retype",
            "sweep_retype",
            vec![u64a(0xFFFF_0000_1234)],
            Ty::U64,
        )
        .c("a0 + 5"),
        Call::new(
            "bitcast_f64_u64",
            "sweep_bitcast_f64_u64",
            vec![Arg(Ty::F64, u128::from((-0.1f64).to_bits()))],
            Ty::U64,
        )
        .c("bits_f64(a0)"),
        Call::new(
            "bitcast_f64_nan",
            "sweep_bitcast_f64_u64",
            vec![Arg(Ty::F64, 0x7FF8_0000_DEAD_BEEF)],
            Ty::U64,
        )
        .c("bits_f64(a0)"),
        Call::new(
            "bitcast_u32_f32",
            "sweep_bitcast_u32_f32",
            vec![Arg(Ty::U32, 0x4049_0FDB)],
            Ty::F32,
        )
        .c("f32_of(a0)"),
        Call::new(
            "bitcast_f32_i32",
            "sweep_bitcast_f32_i32",
            vec![Arg(Ty::F32, u128::from((-2.5f32).to_bits()))],
            Ty::I32,
        )
        .c("(int32_t)bits_f32(a0)"),
        Call::new(
            "bitcast_i64_f64",
            "sweep_bitcast_i64_f64",
            vec![i64a(0x4000_0000_0000_0001)],
            Ty::F64,
        )
        .c("f64_of((uint64_t)a0)"),
        Call::new(
            "bitcast_sign_flip",
            "sweep_bitcast_sign_flip",
            vec![i64a(0x3FF0_0000_0000_0000)],
            Ty::I64,
        )
        .c("(int64_t)((uint64_t)a0 ^ 0x8000000000000000ULL)"),
    ];
    let compared = sweep("ptr-bitcast", &module, &calls, &[], "", "");
    assert_eq!(compared, calls.len());
}

const PAIR: u32 = 0;
const QUAD: u32 = 1;

/// Scalar, vector and aggregate `Transmute`s with their interpreter twins.
fn transmute_module() -> Module {
    let mut module = sweep_module("construct_sweep_transmute");
    // Declared layouts: trust-ir states every offset, size and alignment.
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(PAIR),
        name: "Pair".to_string(),
        fields: vec![
            field("a", Ty::U32, 0),
            field("b", Ty::U16, 4),
            field("c", Ty::U16, 6),
        ],
        size: Some(8),
        align: Some(4),
        repr: StructRepr::C,
    });
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(QUAD),
        name: "Quad".to_string(),
        fields: vec![
            field("w", Ty::U16, 0),
            field("x", Ty::U16, 2),
            field("y", Ty::U16, 4),
            field("z", Ty::U16, 6),
        ],
        size: Some(8),
        align: Some(2),
        repr: StructRepr::C,
    });
    let pair = Ty::Struct(StructId::new(PAIR));
    let quad = Ty::Struct(StructId::new(QUAD));
    let u8_id = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let pair_id = module
        .add_type(pair.clone())
        .expect("Module::add_type: test fixture");
    let bytes8 = Ty::Array(u8_id, 8);
    let pairs2 = Ty::Array(pair_id, 2);
    let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
    let v16i8 = Ty::Vector(Box::new(Ty::I8), 16);
    let v2f64 = Ty::Vector(Box::new(Ty::F64), 2);
    let v8i8 = Ty::Vector(Box::new(Ty::I8), 8);

    // Integer/pointer scalars: the interpreter executes these spellings.
    for (name, src, dst) in [
        ("sweep_tm_i64_u64", Ty::I64, Ty::U64),
        ("sweep_tm_u32_i32", Ty::U32, Ty::I32),
        ("sweep_tm_u128_i128", Ty::U128, Ty::I128),
    ] {
        let mut body = Body::new();
        let x = body.param(src.clone());
        let y = transmute(&mut body, src.clone(), dst.clone(), x);
        ret(&mut body, vec![y]);
        define(&mut module, name, vec![src], vec![dst], body);
    }
    let mut body = Body::new();
    let x = body.param(Ty::U64);
    let pointer = transmute(&mut body, Ty::U64, Ty::Ptr, x);
    let back = transmute(&mut body, Ty::Ptr, Ty::U64, pointer);
    ret(&mut body, vec![back]);
    define(
        &mut module,
        "sweep_tm_u64_ptr_u64",
        vec![Ty::U64],
        vec![Ty::U64],
        body,
    );

    // Integer <-> float, with `Bitcast` twins.
    for (name, twin, src, dst) in [
        ("sweep_tm_u64_f64", "sweep_bc_u64_f64", Ty::U64, Ty::F64),
        ("sweep_tm_f32_u32", "sweep_bc_f32_u32", Ty::F32, Ty::U32),
        ("sweep_tm_f64_i64", "sweep_bc_f64_i64", Ty::F64, Ty::I64),
        ("sweep_tm_i16_f16", "sweep_bc_i16_f16", Ty::I16, Ty::F16),
    ] {
        for (function, op) in [(name, CastOp::Transmute), (twin, CastOp::Bitcast)] {
            let mut body = Body::new();
            let x = body.param(src.clone());
            let y = cast(&mut body, op, src.clone(), dst.clone(), x);
            ret(&mut body, vec![y]);
            define(
                &mut module,
                function,
                vec![src.clone()],
                vec![dst.clone()],
                body,
            );
        }
    }

    // u128 -> <4 x i32> / <16 x i8> / <2 x f64>, every lane read at a
    // constant index and folded with a lane-distinguishing weight.
    for (name, twin, vector_ty, lanes) in [
        (
            "sweep_tm_u128_i32s",
            "sweep_mem_u128_i32s",
            v4i32.clone(),
            4u32,
        ),
        ("sweep_tm_u128_i8s", "sweep_mem_u128_i8s", v16i8.clone(), 16),
        (
            "sweep_tm_u128_f64s",
            "sweep_mem_u128_f64s",
            v2f64.clone(),
            2,
        ),
    ] {
        for (function, via_memory) in [(name, false), (twin, true)] {
            let mut body = Body::new();
            let x = body.param(Ty::U128);
            let vector = if via_memory {
                through_memory(&mut body, Ty::U128, vector_ty.clone(), x)
            } else {
                transmute(&mut body, Ty::U128, vector_ty.clone(), x)
            };
            let Ty::Vector(lane_ty, _) = &vector_ty else {
                unreachable!("a vector type")
            };
            let lane_ty = (**lane_ty).clone();
            let read: Vec<ValueId> = (0..lanes)
                .map(|lane| {
                    let at = int_const(&mut body, Ty::I64, i128::from(lane));
                    body.emit(Inst::ExtractElement {
                        ty: lane_ty.clone(),
                        array: vector,
                        index: at,
                    })
                })
                .collect();
            let (ret_ty, folded) = match lane_ty {
                // l0 - l1: one IEEE operation, no contraction to disagree on.
                Ty::F64 => (
                    Ty::F64,
                    binop(&mut body, BinOp::FSub, Ty::F64, read[0], read[1]),
                ),
                // sum over k of (2k + 1) * sext(l_k), at 64 bits.
                _ => {
                    let mut total = int_const(&mut body, Ty::I64, 0);
                    for (k, lane) in read.into_iter().enumerate() {
                        let wide = cast(&mut body, CastOp::SExt, lane_ty.clone(), Ty::I64, lane);
                        let weight = int_const(&mut body, Ty::I64, 2 * k as i128 + 1);
                        let term = binop(&mut body, BinOp::Mul, Ty::I64, wide, weight);
                        total = binop(&mut body, BinOp::Add, Ty::I64, total, term);
                    }
                    (Ty::I64, total)
                }
            };
            ret(&mut body, vec![folded]);
            define(&mut module, function, vec![Ty::U128], vec![ret_ty], body);
        }
    }

    // <4 x i32> built lane by lane -> u128.
    for (name, via_memory) in [
        ("sweep_tm_lanes_u128", false),
        ("sweep_mem_lanes_u128", true),
    ] {
        let mut body = Body::new();
        let lanes: Vec<ValueId> = (0..4).map(|_| body.param(Ty::I32)).collect();
        let mut vector = body.emit(Inst::Const {
            ty: v4i32.clone(),
            value: Constant::Vector(vec![Constant::Int(0); 4]),
        });
        for (index, lane) in lanes.into_iter().enumerate() {
            let at = int_const(&mut body, Ty::I64, index as i128);
            vector = body.emit(Inst::InsertElement {
                ty: v4i32.clone(),
                array: vector,
                index: at,
                value: lane,
            });
        }
        let wide = if via_memory {
            through_memory(&mut body, v4i32.clone(), Ty::U128, vector)
        } else {
            transmute(&mut body, v4i32.clone(), Ty::U128, vector)
        };
        ret(&mut body, vec![wide]);
        define(
            &mut module,
            name,
            vec![Ty::I32, Ty::I32, Ty::I32, Ty::I32],
            vec![Ty::U128],
            body,
        );
    }

    // u64 <-> <8 x i8> (a D-register vector) around a lane-wise xor with a
    // key that is itself a reinterpreted word.
    for (name, via_memory) in [
        ("sweep_tm_u64_v8_xor", false),
        ("sweep_mem_u64_v8_xor", true),
    ] {
        let mut body = Body::new();
        let x = body.param(Ty::U64);
        let key_word = int_const(&mut body, Ty::U64, 0x0807_0605_0403_0201);
        let (vector, key) = if via_memory {
            (
                through_memory(&mut body, Ty::U64, v8i8.clone(), x),
                through_memory(&mut body, Ty::U64, v8i8.clone(), key_word),
            )
        } else {
            (
                transmute(&mut body, Ty::U64, v8i8.clone(), x),
                transmute(&mut body, Ty::U64, v8i8.clone(), key_word),
            )
        };
        let mixed = binop(&mut body, BinOp::Xor, v8i8.clone(), vector, key);
        let back = if via_memory {
            through_memory(&mut body, v8i8.clone(), Ty::U64, mixed)
        } else {
            transmute(&mut body, v8i8.clone(), Ty::U64, mixed)
        };
        ret(&mut body, vec![back]);
        define(&mut module, name, vec![Ty::U64], vec![Ty::U64], body);
    }

    // A struct built by `MakeAggregate`, reinterpreted as a word and as
    // bytes.
    for (name, via_memory) in [("sweep_tm_pair_u64", false), ("sweep_mem_pair_u64", true)] {
        let mut body = Body::new();
        let fields = vec![
            body.param(Ty::U32),
            body.param(Ty::U16),
            body.param(Ty::U16),
        ];
        let value = body.emit(Inst::MakeAggregate {
            ty: pair.clone(),
            variant: None,
            fields,
        });
        let word = if via_memory {
            through_memory(&mut body, pair.clone(), Ty::U64, value)
        } else {
            transmute(&mut body, pair.clone(), Ty::U64, value)
        };
        ret(&mut body, vec![word]);
        define(
            &mut module,
            name,
            vec![Ty::U32, Ty::U16, Ty::U16],
            vec![Ty::U64],
            body,
        );
    }
    for (name, via_memory) in [("sweep_tm_pair_byte", false), ("sweep_mem_pair_byte", true)] {
        let mut body = Body::new();
        let fields = vec![
            body.param(Ty::U32),
            body.param(Ty::U16),
            body.param(Ty::U16),
        ];
        let index = body.param(Ty::U64);
        let value = body.emit(Inst::MakeAggregate {
            ty: pair.clone(),
            variant: None,
            fields,
        });
        let bytes = if via_memory {
            through_memory(&mut body, pair.clone(), bytes8.clone(), value)
        } else {
            transmute(&mut body, pair.clone(), bytes8.clone(), value)
        };
        let read = body.emit(Inst::ExtractElement {
            ty: Ty::U8,
            array: bytes,
            index,
        });
        ret(&mut body, vec![read]);
        define(
            &mut module,
            name,
            vec![Ty::U32, Ty::U16, Ty::U16, Ty::U64],
            vec![Ty::U8],
            body,
        );
    }

    // u64 -> [u8; 8] -> Pair -> Quad: bytes into structs and between two
    // struct shapes of one size.
    for (name, via_memory) in [
        ("sweep_tm_word_structs", false),
        ("sweep_mem_word_structs", true),
    ] {
        let mut body = Body::new();
        let x = body.param(Ty::U64);
        let (pair_value, quad_value) = if via_memory {
            let slot = body.emit(Inst::Alloca {
                ty: Ty::U64,
                count: None,
                align: None,
            });
            body.effect(Inst::Store {
                ty: Ty::U64,
                ptr: slot,
                value: x,
                volatile: false,
                align: None,
            });
            let pair_value = body.emit(Inst::Load {
                ty: pair.clone(),
                ptr: slot,
                volatile: false,
                align: None,
            });
            let quad_value = body.emit(Inst::Load {
                ty: quad.clone(),
                ptr: slot,
                volatile: false,
                align: None,
            });
            (pair_value, quad_value)
        } else {
            let bytes = transmute(&mut body, Ty::U64, bytes8.clone(), x);
            let pair_value = transmute(&mut body, bytes8.clone(), pair.clone(), bytes);
            let quad_value = transmute(&mut body, pair.clone(), quad.clone(), pair_value);
            (pair_value, quad_value)
        };
        let a = body.emit(Inst::ExtractField {
            ty: Ty::U32,
            aggregate: pair_value,
            field: 0,
        });
        let c = body.emit(Inst::ExtractField {
            ty: Ty::U16,
            aggregate: pair_value,
            field: 2,
        });
        let qx = body.emit(Inst::ExtractField {
            ty: Ty::U16,
            aggregate: quad_value,
            field: 1,
        });
        let a64 = cast(&mut body, CastOp::ZExt, Ty::U32, Ty::U64, a);
        let c64 = cast(&mut body, CastOp::ZExt, Ty::U16, Ty::U64, c);
        let qx64 = cast(&mut body, CastOp::ZExt, Ty::U16, Ty::U64, qx);
        let shift32 = int_const(&mut body, Ty::U64, 32);
        let shift48 = int_const(&mut body, Ty::U64, 48);
        let c_placed = binop(&mut body, BinOp::Shl, Ty::U64, c64, shift32);
        let qx_placed = binop(&mut body, BinOp::Shl, Ty::U64, qx64, shift48);
        let partial = binop(&mut body, BinOp::Xor, Ty::U64, a64, c_placed);
        let total = binop(&mut body, BinOp::Xor, Ty::U64, partial, qx_placed);
        ret(&mut body, vec![total]);
        define(&mut module, name, vec![Ty::U64], vec![Ty::U64], body);
    }

    // [Pair; 2] (aggregate elements) -> u128.
    for (name, via_memory) in [
        ("sweep_tm_pairs_u128", false),
        ("sweep_mem_pairs_u128", true),
    ] {
        let mut body = Body::new();
        let mut pairs = Vec::new();
        for _ in 0..2 {
            let fields = vec![
                body.param(Ty::U32),
                body.param(Ty::U16),
                body.param(Ty::U16),
            ];
            pairs.push(body.emit(Inst::MakeAggregate {
                ty: pair.clone(),
                variant: None,
                fields,
            }));
        }
        let array = body.emit(Inst::MakeAggregate {
            ty: pairs2.clone(),
            variant: None,
            fields: pairs,
        });
        let wide = if via_memory {
            through_memory(&mut body, pairs2.clone(), Ty::U128, array)
        } else {
            transmute(&mut body, pairs2.clone(), Ty::U128, array)
        };
        ret(&mut body, vec![wide]);
        define(
            &mut module,
            name,
            vec![Ty::U32, Ty::U16, Ty::U16, Ty::U32, Ty::U16, Ty::U16],
            vec![Ty::U128],
            body,
        );
    }
    module
}

const TRANSMUTE_PRELUDE: &str = r#"
struct Pair { uint32_t a; uint16_t b; uint16_t c; };
struct Quad { uint16_t w, x, y, z; };
static u128 pair_image(uint32_t a, uint16_t b, uint16_t c) {
    struct Pair p = { a, b, c }; uint64_t w; memcpy(&w, &p, 8); return (u128)w;
}
static uint8_t pair_byte(uint32_t a, uint16_t b, uint16_t c, uint64_t i) {
    struct Pair p = { a, b, c }; uint8_t bytes[8]; memcpy(bytes, &p, 8); return bytes[i];
}
static uint64_t word_structs(uint64_t x) {
    struct Pair p; struct Quad q; memcpy(&p, &x, 8); memcpy(&q, &p, 8);
    return (uint64_t)p.a ^ ((uint64_t)p.c << 32) ^ ((uint64_t)q.x << 48);
}
static u128 pairs_image(uint32_t a0, uint16_t b0, uint16_t c0, uint32_t a1, uint16_t b1, uint16_t c1) {
    struct Pair p[2] = { { a0, b0, c0 }, { a1, b1, c1 } }; u128 w; memcpy(&w, p, 16); return w;
}
static int64_t i32_lanes(u128 x) {
    int32_t l[4]; memcpy(l, &x, 16); int64_t t = 0;
    for (int k = 0; k < 4; k++) t += (int64_t)l[k] * (2 * k + 1);
    return t;
}
static int64_t i8_lanes(u128 x) {
    int8_t l[16]; memcpy(l, &x, 16); int64_t t = 0;
    for (int k = 0; k < 16; k++) t += (int64_t)l[k] * (2 * k + 1);
    return t;
}
static double f64_lanes(u128 x) { double d[2]; memcpy(d, &x, 16); return d[0] - d[1]; }
static u128 lanes_u128(int32_t a, int32_t b, int32_t c, int32_t d) {
    int32_t l[4] = { a, b, c, d }; u128 w; memcpy(&w, l, 16); return w;
}
"#;

#[test]
fn native_transmute_reinterprets_scalars_vectors_and_structs_o0_through_o3() {
    let module = transmute_module();
    let a = |ty: Ty, bits: u128| Arg(ty, bits);
    let pair_args = |x: u32, y: u16, z: u16| {
        vec![
            a(Ty::U32, u128::from(x)),
            a(Ty::U16, u128::from(y)),
            a(Ty::U16, u128::from(z)),
        ]
    };
    let mut calls = vec![
        Call::new(
            "tm_i64_u64",
            "sweep_tm_i64_u64",
            vec![a(Ty::I64, u128::from((-2i64) as u64))],
            Ty::U64,
        )
        .c("(uint64_t)a0"),
        Call::new(
            "tm_u32_i32",
            "sweep_tm_u32_i32",
            vec![a(Ty::U32, 0xFFFF_FFF0)],
            Ty::I32,
        )
        .c("(int32_t)a0"),
        Call::new(
            "tm_u128_i128",
            "sweep_tm_u128_i128",
            vec![a(Ty::U128, 0xF000_0000_0000_0001_8000_0000_0000_0003)],
            Ty::I128,
        )
        .c("(__int128)a0"),
        Call::new(
            "tm_u64_ptr_u64",
            "sweep_tm_u64_ptr_u64",
            vec![a(Ty::U64, 0x0000_7FFF_DEAD_BEE8)],
            Ty::U64,
        )
        .c("a0"),
    ];
    for (key, func, twin, src, dst, bits, model) in [
        (
            "tm_u64_f64",
            "sweep_tm_u64_f64",
            "sweep_bc_u64_f64",
            Ty::U64,
            Ty::F64,
            0xC00F_FFFF_FFFF_FFFFu128,
            "f64_of(a0)",
        ),
        (
            "tm_f32_u32",
            "sweep_tm_f32_u32",
            "sweep_bc_f32_u32",
            Ty::F32,
            Ty::U32,
            u128::from((-0.0f32).to_bits()),
            "bits_f32(a0)",
        ),
        (
            "tm_f64_i64",
            "sweep_tm_f64_i64",
            "sweep_bc_f64_i64",
            Ty::F64,
            Ty::I64,
            u128::from(f64::MIN_POSITIVE.to_bits()),
            "(int64_t)bits_f64(a0)",
        ),
        (
            "tm_i16_f16",
            "sweep_tm_i16_f16",
            "sweep_bc_i16_f16",
            Ty::I16,
            Ty::F16,
            0x3C01,
            "f16_of((uint16_t)a0)",
        ),
    ] {
        calls.push(
            Call::new(key, func, vec![a(src.clone(), bits)], dst)
                .c(model)
                .twin(twin, vec![a(src, bits)]),
        );
    }
    for (index, x128) in [
        0xC00F_FFFF_FFFF_FFFF_8404_0403_8303_0302u128,
        0x3FF0_0000_0000_0001_7FEF_FFFF_FFFF_FFFF,
    ]
    .into_iter()
    .enumerate()
    {
        for (func, twin, ret_ty, model) in [
            (
                "sweep_tm_u128_i32s",
                "sweep_mem_u128_i32s",
                Ty::I64,
                "i32_lanes(a0)",
            ),
            (
                "sweep_tm_u128_i8s",
                "sweep_mem_u128_i8s",
                Ty::I64,
                "i8_lanes(a0)",
            ),
            (
                "sweep_tm_u128_f64s",
                "sweep_mem_u128_f64s",
                Ty::F64,
                "f64_lanes(a0)",
            ),
        ] {
            let args = vec![a(Ty::U128, x128)];
            calls.push(
                Call::new(format!("{func}_{index}"), func, args.clone(), ret_ty)
                    .c(model)
                    .twin(twin, args),
            );
        }
    }
    let lane_args: Vec<Arg> = [0xAAAA_0001u32, 0xBBBB_0002, 0x7CCC_0003, 0xDDDD_0004]
        .into_iter()
        .map(|value| a(Ty::I32, u128::from(value)))
        .collect();
    calls.push(
        Call::new(
            "tm_lanes_u128",
            "sweep_tm_lanes_u128",
            lane_args.clone(),
            Ty::U128,
        )
        .c("lanes_u128(a0, a1, a2, a3)")
        .twin("sweep_mem_lanes_u128", lane_args),
    );
    for word in [0x8877_6655_4433_2211u64, 0] {
        let args = vec![a(Ty::U64, u128::from(word))];
        calls.push(
            Call::new(
                format!("tm_u64_v8_xor_{word:x}"),
                "sweep_tm_u64_v8_xor",
                args.clone(),
                Ty::U64,
            )
            .c("a0 ^ 0x0807060504030201ULL")
            .twin("sweep_mem_u64_v8_xor", args),
        );
    }
    let pair = pair_args(0xDDCC_BBAA, 0x1122, 0xF0E1);
    calls.push(
        Call::new("tm_pair_u64", "sweep_tm_pair_u64", pair.clone(), Ty::U64)
            .c("(uint64_t)pair_image(a0, a1, a2)")
            .twin("sweep_mem_pair_u64", pair.clone()),
    );
    for index in [0u64, 3, 4, 7] {
        let mut args = pair.clone();
        args.push(a(Ty::U64, u128::from(index)));
        calls.push(
            Call::new(
                format!("tm_pair_byte_{index}"),
                "sweep_tm_pair_byte",
                args.clone(),
                Ty::U8,
            )
            .c("pair_byte(a0, a1, a2, a3)")
            .twin("sweep_mem_pair_byte", args),
        );
    }
    for word in [0x0123_4567_89AB_CDEFu64, u64::MAX, 0x8000_0000_0000_0001] {
        let args = vec![a(Ty::U64, u128::from(word))];
        calls.push(
            Call::new(
                format!("tm_word_structs_{word:x}"),
                "sweep_tm_word_structs",
                args.clone(),
                Ty::U64,
            )
            .c("word_structs(a0)")
            .twin("sweep_mem_word_structs", args),
        );
    }
    let mut pairs = pair_args(0x0101_0101, 0x0202, 0x0303);
    pairs.extend(pair_args(0xFFFF_0000, 0xABCD, 0x7FFF));
    calls.push(
        Call::new(
            "tm_pairs_u128",
            "sweep_tm_pairs_u128",
            pairs.clone(),
            Ty::U128,
        )
        .c("pairs_image(a0, a1, a2, a3, a4, a5)")
        .twin("sweep_mem_pairs_u128", pairs),
    );
    let compared = sweep("transmute", &module, &calls, &[], TRANSMUTE_PRELUDE, "");
    assert_eq!(compared, calls.len());
}

/// The twins above are a stated substitution: the pinned interpreter refuses
/// every non-integer/pointer `Transmute` spelling this file executes (all
/// thirteen twin-checked functions are listed here; the pinned
/// `transmute_scalar_ty` admits only `I8`-`I128`, `U8`-`U128` and `Ptr`).
#[test]
fn the_interpreter_refuses_the_transmute_spellings_the_twins_stand_in_for() {
    let module = transmute_module();
    let pair = || vec![Arg(Ty::U32, 1), Arg(Ty::U16, 2), Arg(Ty::U16, 3)];
    let with_index = {
        let mut args = pair();
        args.push(Arg(Ty::U64, 0));
        args
    };
    let two_pairs = {
        let mut args = pair();
        args.extend(pair());
        args
    };
    let mut checked = 0;
    for (func, args) in [
        ("sweep_tm_u64_f64", vec![Arg(Ty::U64, 1)]),
        ("sweep_tm_f32_u32", vec![Arg(Ty::F32, 1)]),
        ("sweep_tm_f64_i64", vec![Arg(Ty::F64, 1)]),
        ("sweep_tm_i16_f16", vec![Arg(Ty::I16, 1)]),
        ("sweep_tm_u128_i32s", vec![Arg(Ty::U128, 1)]),
        ("sweep_tm_u128_i8s", vec![Arg(Ty::U128, 1)]),
        ("sweep_tm_u128_f64s", vec![Arg(Ty::U128, 1)]),
        ("sweep_tm_lanes_u128", vec![Arg(Ty::I32, 1); 4]),
        ("sweep_tm_u64_v8_xor", vec![Arg(Ty::U64, 1)]),
        ("sweep_tm_pair_u64", pair()),
        ("sweep_tm_pair_byte", with_index),
        ("sweep_tm_word_structs", vec![Arg(Ty::U64, 1)]),
        ("sweep_tm_pairs_u128", two_pairs),
    ] {
        checked += 1;
        let refused = interpret(&module, func, &args).expect_err(func);
        assert_eq!(
            refused.code,
            InterpretErrorCode::UnsupportedCast,
            "{func}: {refused:?}"
        );
    }
    assert_eq!(checked, 13, "every twin-checked Transmute spelling");
    // The integer/pointer spellings execute in the interpreter itself.
    for (func, args) in [
        ("sweep_tm_i64_u64", vec![Arg(Ty::I64, 3)]),
        ("sweep_tm_u64_ptr_u64", vec![Arg(Ty::U64, 0x1000)]),
    ] {
        interpret(&module, func, &args).unwrap_or_else(|error| panic!("{func}: {error:?}"));
    }
}

/// One `Transmute src -> dst` function over `module`'s tables.
fn transmute_refusal(mut module: Module, src: Ty, dst: Ty) -> Module {
    let mut body = Body::new();
    let x = body.param(src.clone());
    let y = transmute(&mut body, src.clone(), dst.clone(), x);
    ret(&mut body, vec![y]);
    define(&mut module, "sweep_tm_refused", vec![src], vec![dst], body);
    module
}

#[test]
fn transmute_shapes_outside_the_reinterpretation_stay_refused_by_name() {
    let base = || sweep_module("construct_sweep_transmute_refusals");
    let mut padded = base();
    padded.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Padded".to_string(),
        fields: vec![field("a", Ty::U8, 0), field("b", Ty::U32, 4)],
        size: Some(8),
        align: Some(4),
        repr: StructRepr::C,
    });
    let mut undeclared = base();
    undeclared.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Undeclared".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::U32,
                offset: None,
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::U32,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    });
    let cases = [
        (
            "unequal sizes",
            transmute_refusal(base(), Ty::U64, Ty::U32),
            "layout sizes differ",
        ),
        (
            "char destination",
            transmute_refusal(base(), Ty::U32, Ty::Char),
            "reaches Char",
        ),
        (
            "reference destination",
            transmute_refusal(base(), Ty::U64, Ty::Ref(Box::new(Ty::U64))),
            "reaches Ref",
        ),
        (
            "bool lane",
            transmute_refusal(base(), Ty::U8, Ty::Bool),
            "trust-ir layout evidence refuses it",
        ),
        (
            "source padding",
            transmute_refusal(padded, Ty::Struct(StructId::new(0)), Ty::U64),
            "padding byte(s)",
        ),
        (
            "undeclared struct layout",
            transmute_refusal(undeclared, Ty::Struct(StructId::new(0)), Ty::U64),
            "trust-ir layout evidence refuses it",
        ),
    ];
    for (what, module, needle) in cases {
        for opt_level in [OptLevel::O0, OptLevel::O3] {
            let error = compile(&module, opt_level).expect_err(what);
            // A shape trust-ir itself refuses (`CastLayoutUnsupported`, ...) is
            // refused by that finding at ingestion since WS7.3, judged under
            // the policy `compile` states.
            match admission_expect::names_first_finding(
                &module,
                &error,
                &sweep::permit_unlicensed(),
            ) {
                Some(named) => assert!(named, "{what} {opt_level:?}: {error}"),
                None => assert!(
                    error.contains("CastOp::Transmute fail-closed") && error.contains(needle),
                    "{what} {opt_level:?}: `{needle}` not in {error}"
                ),
            }
        }
    }
}
