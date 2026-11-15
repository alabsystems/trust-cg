// Copyright 2026 Andrew Yates | Apache-2.0
//! Integer short-vector carrier admission, independent of operation support.
//! Expected lane widths/counts below are explicit, not computed by the adapter.
//!
//! Regression note (2026-09-21). `db2082e3f` pinned every cast family,
//! `Bitcast` included, as refused on a vector carrier even at equal total
//! width. `b98de7239` then admitted equal-width vector `Bitcast` in
//! `validate_cast_shape` ("both selectors lower it as one register move")
//! without touching these pins, so `main` carried two tests asserting the
//! opposite of the code. Ruling: a shape enters the lowering lane only if
//! (a) trust-ir's semantic model defines its meaning AND (b) trust-cg's
//! translation-validation / proof lane covers the lowering. Vector bitcast
//! fails both at trust-ir 283f1747 — the Lean `semCast` `.Bitcast` arm and
//! the reference interpreter's `eval_bitcast` both end in a type error for a
//! vector operand, and trust-cg-verify has no vector-typed `Bitcast_*`
//! obligation (`MOVDQA xmm,xmm` has no `opcode_to_proof_query` row) — so the
//! refusal was restored and these pins stand. Emitting one register move is a
//! claim about the emitter, not a proof about the semantics; lane order under
//! reinterpretation is a memory-layout question the model does not answer.
//! Re-admitting the shape requires new evidence for BOTH (a) and (b), not an
//! edit to these assertions.

use trust_cg_lower::adapter::{AdapterError, translate_type};
use trust_cg_lower::types::Type;
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode,
    Module, Ty, UnOp, ValueId,
};

#[path = "common/typed_refusal.rs"]
mod typed_refusal;
use typed_refusal::assert_typed_const_refusal;

#[path = "common/below_admission.rs"]
mod below_admission;
use below_admission::body_refusal_below_admission;

fn matrix() -> Vec<(Ty, u32, u32)> {
    [
        (Ty::I8, 8, 16),
        (Ty::U8, 8, 16),
        (Ty::I16, 4, 8),
        (Ty::U16, 4, 8),
        (Ty::I32, 2, 4),
        (Ty::U32, 2, 4),
        (Ty::I64, 1, 2),
        (Ty::U64, 1, 2),
    ]
    .into_iter()
    .collect()
}

#[test]
fn integer_short_vectors_have_exact_signedness_independent_carriers() {
    let mut failures = Vec::new();
    for (lane, narrow, wide) in matrix() {
        for (lanes, expected, bytes) in [(narrow, Type::V64, 8), (wide, Type::V128, 16)] {
            let ty = Ty::Vector(Box::new(lane.clone()), lanes);
            match translate_type(&ty) {
                Ok(actual)
                    if actual == expected && actual.bytes() == bytes && actual.align() == bytes => {
                }
                other => failures.push(format!("{ty:?}: expected {expected:?}, got {other:?}")),
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn byte_width_alone_does_not_admit_uncontracted_lane_types_or_shapes() {
    for ty in [
        Ty::Vector(Box::new(Ty::U8), 0),
        Ty::Vector(Box::new(Ty::U8), 7),
        Ty::Vector(Box::new(Ty::I16), 3),
        Ty::Vector(Box::new(Ty::U32), 8),
        Ty::Vector(Box::new(Ty::U64), u32::MAX),
        Ty::Vector(Box::new(Ty::I128), 1),
        Ty::Vector(Box::new(Ty::Ptr), 2),
        Ty::Vector(Box::new(Ty::F16), 8),
        Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::I32), 2)), 2),
    ] {
        assert!(
            matches!(translate_type(&ty), Err(AdapterError::UnsupportedType(_))),
            "{ty:?}"
        );
    }
    // Existing logical masks keep their own physical representation; do not
    // accidentally turn the eight-lane i16 mask into an eight-byte vector.
    assert_eq!(
        translate_type(&Ty::Vector(Box::new(Ty::Bool), 8)).unwrap(),
        Type::V128
    );
}

/// `operation(params) -> result` whose body is `instruction`, then a return.
fn operation_module(params: Vec<Ty>, result: Ty, instruction: Inst) -> Module {
    let mut module = Module::new("vector_operation_admission");
    let sig = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![result],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "operation", sig, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(i, ty)| (ValueId::new(i as u32), ty))
            .collect(),
        body: vec![
            InstrNode::new(instruction).with_result(ValueId::new(10)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)],
            }),
        ],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn translate(params: Vec<Ty>, result: Ty, instruction: Inst) -> Result<(), AdapterError> {
    let module = operation_module(params, result, instruction);
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .map(|_| ())
}

/// The operations an unsigned-lane carrier admits (L04-P6), pinned exactly:
/// the 128-bit unsigned shapes take the signed shapes' lane-signedness-
/// independent lowerings (wrapping Add/Sub/Mul, And/Or/Xor, every compare
/// predicate, Neg/Not, and on `<4 x u32>` the three shifts), `<8 x u8>` the
/// V64 And/Or/Xor and compares `<8 x i8>` has; nothing else. Division,
/// remainder, CtPop, lane extract/insert, a select on a condition no compare
/// produced and every cast stay refused, and the remaining 64-bit shapes admit
/// no operation at all.
#[test]
fn unsigned_carriers_admit_exactly_the_lane_signedness_independent_operations() {
    let mut shapes: Vec<Ty> = matrix()
        .into_iter()
        .filter(|(lane, _, _)| matches!(lane, Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64))
        .flat_map(|(lane, narrow, wide)| {
            [
                Ty::Vector(Box::new(lane.clone()), narrow),
                Ty::Vector(Box::new(lane), wide),
            ]
        })
        .collect();
    shapes.extend([
        Ty::Vector(Box::new(Ty::I16), 4),
        Ty::Vector(Box::new(Ty::I32), 2),
    ]);
    let wide_unsigned = |ty: &Ty| {
        matches!(ty, Ty::Vector(lane, n)
            if matches!((lane.as_ref(), *n),
                (Ty::U8, 16) | (Ty::U16, 8) | (Ty::U32, 4) | (Ty::U64, 2)))
    };
    let u8x8 = |ty: &Ty| matches!(ty, Ty::Vector(lane, 8) if lane.as_ref() == &Ty::U8);
    let u32x4 = |ty: &Ty| matches!(ty, Ty::Vector(lane, 4) if lane.as_ref() == &Ty::U32);
    let mut wrong = Vec::new();
    for ty in shapes {
        for op in [
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::And,
            BinOp::Or,
            BinOp::Xor,
            BinOp::SDiv,
            BinOp::UDiv,
            BinOp::SRem,
            BinOp::URem,
            BinOp::Shl,
            BinOp::LShr,
            BinOp::AShr,
        ] {
            let admitted = match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => wide_unsigned(&ty),
                BinOp::And | BinOp::Or | BinOp::Xor => wide_unsigned(&ty) || u8x8(&ty),
                BinOp::Shl | BinOp::LShr | BinOp::AShr => u32x4(&ty),
                _ => false,
            };
            let result = translate(
                vec![ty.clone(), ty.clone()],
                ty.clone(),
                Inst::BinOp {
                    op,
                    ty: ty.clone(),
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
            );
            match (admitted, &result) {
                (true, Ok(())) | (false, Err(AdapterError::UnsupportedInstruction(_))) => {}
                _ => wrong.push(format!("{ty:?} {op:?}: admitted={admitted}, {result:?}")),
            }
        }
        for op in [
            ICmpOp::Eq,
            ICmpOp::Ne,
            ICmpOp::Slt,
            ICmpOp::Sle,
            ICmpOp::Sgt,
            ICmpOp::Sge,
            ICmpOp::Ult,
            ICmpOp::Ule,
            ICmpOp::Ugt,
            ICmpOp::Uge,
        ] {
            let admitted = wide_unsigned(&ty) || u8x8(&ty);
            let result = translate(
                vec![ty.clone(), ty.clone()],
                ty.comparison_result_ty(),
                Inst::ICmp {
                    op,
                    ty: ty.clone(),
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
            );
            // The one-lane logical mask is itself unsupported; other refused
            // shapes reach the explicit operation refusal after type admission.
            // The `<8 x u8>` compare lowers, as `<8 x i8>`'s does, but its
            // register-only V64 mask is refused by name at this test's return
            // slot (a `<8 x bool>` slot is the `<8 x i16>` mask's V128).
            match (admitted, &result) {
                (true, Ok(()))
                | (
                    false,
                    Err(AdapterError::UnsupportedInstruction(_) | AdapterError::UnsupportedType(_)),
                ) => {}
                (true, Err(AdapterError::BoolMaskCarrierMismatch { .. })) if u8x8(&ty) => {}
                _ => wrong.push(format!("{ty:?} {op:?}: admitted={admitted}, {result:?}")),
            }
        }
        for op in [UnOp::Neg, UnOp::Not, UnOp::CtPop] {
            let admitted = wide_unsigned(&ty) && !matches!(op, UnOp::CtPop);
            let result = translate(
                vec![ty.clone()],
                ty.clone(),
                Inst::UnOp {
                    op,
                    ty: ty.clone(),
                    operand: ValueId::new(0),
                },
            );
            match (admitted, &result) {
                (true, Ok(())) | (false, Err(AdapterError::UnsupportedInstruction(_))) => {}
                _ => wrong.push(format!("{ty:?} {op:?}: admitted={admitted}, {result:?}")),
            }
        }
        let Ty::Vector(lane, _) = &ty else {
            unreachable!()
        };
        for (params, result, inst) in [
            (
                vec![ty.clone(), Ty::I64],
                lane.as_ref().clone(),
                Inst::ExtractElement {
                    ty: lane.as_ref().clone(),
                    array: ValueId::new(0),
                    index: ValueId::new(1),
                },
            ),
            (
                vec![ty.clone(), Ty::I64, lane.as_ref().clone()],
                ty.clone(),
                Inst::InsertElement {
                    ty: ty.clone(),
                    array: ValueId::new(0),
                    index: ValueId::new(1),
                    value: ValueId::new(2),
                },
            ),
            // A select whose condition is a parameter: no compare produced
            // it, so its carrier is not known to be a canonical mask.
            (
                vec![ty.clone(), ty.clone(), ty.select_condition_ty()],
                ty.clone(),
                Inst::Select {
                    ty: ty.clone(),
                    cond: ValueId::new(2),
                    then_val: ValueId::new(0),
                    else_val: ValueId::new(1),
                },
            ),
        ] {
            let result = translate(params, result, inst);
            if !matches!(
                result,
                Err(AdapterError::UnsupportedInstruction(_) | AdapterError::UnsupportedType(_))
            ) {
                wrong.push(format!(
                    "{ty:?}: lane access or parameter select: {result:?}"
                ));
            }
        }
        // Cast families remain explicitly scalar-only, even for equal-width
        // reinterpretation. This change must not reach scalar SIMD conversions.
        for op in [
            CastOp::SExt,
            CastOp::ZExt,
            CastOp::Trunc,
            CastOp::SIToFP,
            CastOp::UIToFP,
            CastOp::Bitcast,
        ] {
            let result = translate(
                vec![ty.clone()],
                ty.clone(),
                Inst::Cast {
                    op,
                    src_ty: ty.clone(),
                    dst_ty: ty.clone(),
                    operand: ValueId::new(0),
                },
            );
            if !matches!(result, Err(AdapterError::UnsupportedInstruction(_))) {
                wrong.push(format!("{ty:?} {op:?}: {result:?}"));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A select over an unsigned 128-bit carrier lowers when its condition is a
/// compare of the same lane shape (the canonical all-ones/zero mask), as the
/// signed shapes do.
#[test]
fn unsigned_selects_on_a_same_shape_compare_lower() {
    for (lane, lanes) in [(Ty::U8, 16), (Ty::U16, 8), (Ty::U32, 4), (Ty::U64, 2)] {
        let ty = Ty::Vector(Box::new(lane), lanes);
        let mut module = Module::new("unsigned_select");
        let sig = module
            .add_func_type(FuncTy {
                params: vec![ty.clone(), ty.clone()],
                returns: vec![ty.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "umin", sig, BlockId::new(0));
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ult,
                    ty: ty.clone(),
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Select {
                    ty: ty.clone(),
                    cond: ValueId::new(2),
                    then_val: ValueId::new(0),
                    else_val: ValueId::new(1),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(3)],
                }),
            ],
        }];
        trust_cg_lower::translate_function_with_license(&function, &module, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("{ty:?}: {e:?}"));
    }
}

#[test]
fn well_shaped_vector_conversions_stay_refused_instead_of_using_scalar_casts() {
    let vector = |lane, count| Ty::Vector(Box::new(lane), count);
    for (op, source, destination) in [
        (CastOp::ZExt, vector(Ty::U8, 8), vector(Ty::U16, 8)),
        (CastOp::SExt, vector(Ty::I8, 8), vector(Ty::I16, 8)),
        (CastOp::Trunc, vector(Ty::U16, 8), vector(Ty::U8, 8)),
        (CastOp::UIToFP, vector(Ty::U32, 4), vector(Ty::F32, 4)),
        (CastOp::SIToFP, vector(Ty::I32, 4), vector(Ty::F32, 4)),
        (CastOp::FPToUI, vector(Ty::F32, 4), vector(Ty::U32, 4)),
        (CastOp::FPToSI, vector(Ty::F32, 4), vector(Ty::I32, 4)),
        (CastOp::Bitcast, vector(Ty::U64, 2), vector(Ty::I32, 4)),
        (CastOp::Bitcast, vector(Ty::U8, 8), vector(Ty::U64, 1)),
    ] {
        assert!(matches!(
            translate(
                vec![source.clone()],
                destination.clone(),
                Inst::Cast {
                    op,
                    src_ty: source,
                    dst_ty: destination,
                    operand: ValueId::new(0)
                }
            ),
            Err(AdapterError::UnsupportedInstruction(_))
        ));
    }
}

/// Unsigned integer-lane constants are materialized at both widths (64-bit
/// constants since L04-P6, through their 8-byte stack image) and checked
/// against the lane's own unsigned range on every materialization path: the
/// all-ones/zero mask image (`-1`), the `<4 x u32>`/`<2 x u64>` lane-pack path
/// (any other value, uniform or mixed), and the stack image. Each refusal
/// names the unsigned lane type, not a signed stand-in. TrustIR's typed
/// admission now refuses an out-of-range lane first, at that lane's index, on
/// every codegen entry; the adapter's own range check on those paths is pinned
/// below that admission, naming the first out-of-range lane value.
#[test]
fn unsigned_constants_check_original_lane_range_at_both_widths() {
    for (lane, narrow, wide) in matrix()
        .into_iter()
        .filter(|(lane, _, _)| matches!(lane, Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64))
    {
        let bits = lane.bit_width().unwrap();
        let max = (1i128 << bits) - 1;
        let signed_min = -(1i128 << (bits - 1));
        let lane_name = lane.to_string();
        for lanes in [wide, narrow] {
            let n = lanes as usize;
            let uniform = |value| vec![Constant::Int(value); n];
            // A non-uniform vector with one bad lane among in-range ones.
            let mixed = |value| {
                let mut lanes: Vec<Constant> =
                    (0..n).map(|i| Constant::Int(i as i128 + 1)).collect();
                lanes[n / 2] = Constant::Int(value);
                lanes
            };
            let ty = Ty::Vector(Box::new(lane.clone()), lanes);
            let make = |elems: Vec<Constant>| Inst::Const {
                ty: ty.clone(),
                value: Constant::Vector(elems),
            };
            for valid in [uniform(max), uniform(max - 4), mixed(max), mixed(0)] {
                translate(vec![], ty.clone(), make(valid.clone()))
                    .unwrap_or_else(|e| panic!("{ty:?} {valid:?}: {e:?}"));
            }
            for invalid in [-1, -5, signed_min, signed_min + 7, max + 1] {
                for (elems, first_bad) in [(uniform(invalid), 0), (mixed(invalid), n / 2)] {
                    let error = translate(vec![], ty.clone(), make(elems.clone()))
                        .expect_err("an out-of-range unsigned lane must be refused");
                    assert_typed_const_refusal(
                        &error,
                        &format!("function 'operation' bb0[{first_bad}]"),
                        &lane_name,
                        "int",
                    );
                    assert_eq!(
                        body_refusal_below_admission(&operation_module(
                            vec![],
                            ty.clone(),
                            make(elems)
                        )),
                        format!(
                            "not lowerable: unsupported trust_ir instruction: \
                             Constant::Int({invalid}) does not fit in {lane:?} (range [0, {max}])"
                        ),
                        "{ty:?}"
                    );
                }
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
