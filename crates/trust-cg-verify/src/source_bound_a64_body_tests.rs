// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Unit tests of the AArch64 whole-body owner over hand-built LIR and
//! allocated machine functions. The real pipeline's outputs (every opt level)
//! and native execution are exercised by trust-cg-codegen's
//! `aarch64_source_bound_body` target.

use super::machine::{Flags, bitfield, condition, subs_flags};
use super::*;
use trust_cg_ir::function::{MachBlock, Signature as MSignature, Type as MType};
use trust_cg_ir::regs::PReg;
use trust_cg_ir::{AArch64Opcode as M, BlockId, MachInst, MachOperand as O};
use trust_cg_lower::Type;
use trust_cg_lower::function::{BasicBlock, Signature};
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode as L, Value};

fn ins(opcode: L, args: &[u32], results: &[u32]) -> Instruction {
    Instruction {
        opcode,
        args: args.iter().map(|v| Value(*v)).collect(),
        results: results.iter().map(|v| Value(*v)).collect(),
    }
}

/// One LIR block: its parameters (ignored for the entry block) and body.
type LirBlock = (Vec<(u32, Type)>, Vec<Instruction>);

/// A LIR function: block `i` is `Block(i)`, the entry is block 0 and its
/// parameters are the signature's.
fn lir(params: &[Type], ret: Type, blocks: Vec<LirBlock>) -> Function {
    let mut function = Function::new(
        "f",
        Signature {
            params: params.to_vec(),
            returns: vec![ret],
        },
    );
    for (index, (block_params, instructions)) in blocks.into_iter().enumerate() {
        let params = if index == 0 {
            params
                .iter()
                .enumerate()
                .map(|(i, ty)| (Value(i as u32), ty.clone()))
                .collect()
        } else {
            block_params
                .into_iter()
                .map(|(v, ty)| (Value(v), ty))
                .collect()
        };
        function.blocks.insert(
            Block(index as u32),
            BasicBlock {
                params,
                instructions,
                ..Default::default()
            },
        );
    }
    function.block_order = (0..function.blocks.len() as u32).map(Block).collect();
    function
}

fn four_i64() -> Vec<Type> {
    vec![Type::I64, Type::I64, Type::I64, Type::I64]
}

#[test]
fn pure_jump_cycle_binds_forward_and_negative_decoded_displacements() {
    let mut source = lir(
        &[],
        Type::I64,
        vec![
            (vec![], vec![ins(L::Jump { dest: Block(1) }, &[], &[])]),
            (vec![], vec![ins(L::Jump { dest: Block(0) }, &[], &[])]),
        ],
    );
    source.signature.returns.clear();
    let mut body = machine(
        &[],
        Type::I64,
        vec![
            (vec![mi(M::B, vec![imm(1)])], vec![1]),
            (vec![mi(M::B, vec![imm(-1)])], vec![0]),
        ],
    );
    body.signature.returns.clear();
    let owner = source_bound_a64_body(&source, &body).unwrap();
    assert_eq!(owner.covered(), &[InstId(0), InstId(1)]);
    assert!(!owner.obligation().is_degenerate());
    let query = crate::ay_bridge::generate_smt2_query_raw(
        owner.obligation(),
        &crate::ay_bridge::AYConfig::default(),
    );
    assert!(query.contains("sign_extend 36"));
    assert!(query.contains("concat"));
    for displacement in [0, 1, -4] {
        let mut wrong = body.clone();
        wrong.insts[1].operands[0] = imm(displacement);
        assert!(source_bound_a64_body(&source, &wrong).is_err());
    }
}

fn mtype(ty: &Type) -> MType {
    match ty {
        Type::I8 => MType::I8,
        Type::I16 => MType::I16,
        Type::I32 => MType::I32,
        Type::I64 => MType::I64,
        _ => MType::B1,
    }
}

/// A frameless allocated machine function: block `i` with its successors;
/// predecessors and the layout order are derived.
fn machine(params: &[Type], ret: Type, blocks: Vec<(Vec<MachInst>, Vec<u32>)>) -> MachFunction {
    let mut function = MachFunction::new(
        "f".into(),
        MSignature {
            params: params.iter().map(mtype).collect(),
            returns: vec![mtype(&ret)],
        },
    );
    function.insts.clear();
    function.blocks.clear();
    let count = blocks.len();
    let mut preds = vec![Vec::new(); count];
    for (index, (_, succs)) in blocks.iter().enumerate() {
        for succ in succs {
            preds[*succ as usize].push(BlockId(index as u32));
        }
    }
    for (index, (insts, succs)) in blocks.into_iter().enumerate() {
        let mut ids = Vec::new();
        for inst in insts {
            ids.push(InstId(function.insts.len() as u32));
            function.insts.push(inst);
        }
        function.blocks.push(MachBlock {
            insts: ids,
            preds: preds[index].clone(),
            succs: succs.into_iter().map(BlockId).collect(),
            loop_depth: 0,
        });
    }
    function.entry = BlockId(0);
    function.block_order = (0..count as u32).map(BlockId).collect();
    function
}

fn x(n: u16) -> O {
    O::PReg(PReg::new(n))
}
fn w(n: u16) -> O {
    O::PReg(PReg::new(32 + n))
}
fn imm(v: i64) -> O {
    O::Imm(v)
}
fn blk(n: u32) -> O {
    O::Block(BlockId(n))
}
fn mi(opcode: M, operands: Vec<O>) -> MachInst {
    MachInst::new(opcode, operands)
}
fn ret() -> MachInst {
    mi(M::Ret, vec![x(30)])
}

fn bind(source: &Function, machine: &MachFunction) -> SourceBoundA64Body<'static> {
    // Leak the pair: the owner borrows it and the tests inspect the owner.
    let source: &'static Function = Box::leak(Box::new(source.clone()));
    let machine: &'static MachFunction = Box::leak(Box::new(machine.clone()));
    match source_bound_a64_body(source, machine) {
        Ok(owner) => owner,
        Err(refusal) => panic!("expected a bound body, got {refusal}"),
    }
}

fn refusal(source: &Function, machine: &MachFunction) -> A64BodyRefusal {
    match source_bound_a64_body(source, machine) {
        Ok(_) => panic!("expected a refusal"),
        Err(refusal) => refusal,
    }
}

fn assert_return_mismatch(source: &Function, machine: &MachFunction) {
    let refusal = refusal(source, machine);
    assert!(
        matches!(
            refusal,
            A64BodyRefusal::Mismatch(A64BodyMismatch::ReturnValue { .. })
        ),
        "expected a return-value mismatch, got {refusal}"
    );
}

/// `f(a: B1, b: B1) -> B1 = a <op> b`.
fn bool_pair(op: L) -> Function {
    lir(
        &[Type::B1, Type::B1],
        Type::B1,
        vec![(
            vec![],
            vec![ins(op, &[0, 1], &[2]), ins(L::Return, &[2], &[])],
        )],
    )
}

/// The codegen's shape: UXTB both arguments, then the logic row.
fn bool_pair_machine(opcode: M) -> MachFunction {
    machine(
        &[Type::B1, Type::B1],
        Type::B1,
        vec![(
            vec![
                mi(M::Uxtb, vec![x(2), x(0)]),
                mi(M::Uxtb, vec![x(0), x(1)]),
                mi(opcode, vec![x(0), x(2), x(0)]),
                ret(),
            ],
            vec![],
        )],
    )
}

#[test]
fn boolean_parameters_and_connectives_bind() {
    for (op, opcode) in [(L::Band, M::AndRR), (L::Bor, M::OrrRR), (L::Bxor, M::EorRR)] {
        let source = bool_pair(op);
        let owner = bind(&source, &bool_pair_machine(opcode));
        // The two UXTBs and the logic row are in the returned value's slice.
        assert_eq!(owner.covered().len(), 3, "{opcode:?}");
        assert!(owner.copies_and_constants().is_empty());
    }
    // !a on B1: EOR with the 0/1 carrier's one bit.
    let source = lir(
        &[Type::B1],
        Type::B1,
        vec![(
            vec![],
            vec![ins(L::Bnot, &[0], &[1]), ins(L::Return, &[1], &[])],
        )],
    );
    let body = machine(
        &[Type::B1],
        Type::B1,
        vec![(
            vec![
                mi(M::Uxtb, vec![x(1), x(0)]),
                mi(M::EorRI, vec![w(0), w(1), imm(1)]),
                ret(),
            ],
            vec![],
        )],
    );
    bind(&source, &body);
    // A complement of the whole register is not the Boolean connective: W0
    // must hold exactly 0 or 1.
    let wrong = machine(
        &[Type::B1],
        Type::B1,
        vec![(
            vec![
                mi(M::Uxtb, vec![x(1), x(0)]),
                mi(M::OrnRR, vec![w(0), O::Special(SpecialReg::WZR), w(1)]),
                ret(),
            ],
            vec![],
        )],
    );
    assert_return_mismatch(&source, &wrong);
}

use trust_cg_ir::regs::SpecialReg;

#[test]
fn wrong_connective_and_unmasked_boolean_argument_are_mismatches() {
    assert_return_mismatch(&bool_pair(L::Band), &bool_pair_machine(M::OrrRR));
    assert_return_mismatch(&bool_pair(L::Bor), &bool_pair_machine(M::EorRR));
    // Without UXTB the caller's bits 8..63 reach W0.
    let unmasked = machine(
        &[Type::B1, Type::B1],
        Type::B1,
        vec![(vec![mi(M::AndRR, vec![x(0), x(0), x(1)]), ret()], vec![])],
    );
    assert_return_mismatch(&bool_pair(L::Band), &unmasked);
    // Testing only bit 0 is enough: the AAPCS64 byte has bits 1..7 clear.
    let source = lir(
        &[Type::B1, Type::I64, Type::I64],
        Type::I64,
        vec![(
            vec![],
            vec![
                ins(
                    L::Select {
                        cond: IntCC::NotEqual,
                    },
                    &[0, 1, 2],
                    &[3],
                ),
                ins(L::Return, &[3], &[]),
            ],
        )],
    );
    let tested = machine(
        &[Type::B1, Type::I64, Type::I64],
        Type::I64,
        vec![(
            vec![
                mi(M::Tst, vec![w(0), imm(1)]),
                mi(M::Csel, vec![x(0), x(1), x(2), imm(1)]),
                ret(),
            ],
            vec![],
        )],
    );
    bind(&source, &tested);
    // ... but a test of the whole W register reads the caller's bits 8..31.
    let whole = machine(
        &[Type::B1, Type::I64, Type::I64],
        Type::I64,
        vec![(
            vec![
                mi(M::CmpRI, vec![w(0), imm(0)]),
                mi(M::Csel, vec![x(0), x(1), x(2), imm(1)]),
                ret(),
            ],
            vec![],
        )],
    );
    assert_return_mismatch(&source, &whole);
}

fn int_binary(ty: Type, op: L) -> Function {
    lir(
        &[ty.clone(), ty.clone()],
        ty,
        vec![(
            vec![],
            vec![ins(op, &[0, 1], &[2]), ins(L::Return, &[2], &[])],
        )],
    )
}

fn binary_machine(ty: Type, opcode: M) -> MachFunction {
    let r = if ty == Type::I32 { w } else { x };
    machine(
        &[ty.clone(), ty.clone()],
        ty,
        vec![(vec![mi(opcode, vec![r(0), r(0), r(1)]), ret()], vec![])],
    )
}

#[test]
fn integer_bitwise_rows_bind_at_both_widths() {
    for ty in [Type::I32, Type::I64] {
        for (op, opcode) in [
            (L::Band, M::AndRR),
            (L::Bor, M::OrrRR),
            (L::Bxor, M::EorRR),
            (L::BandNot, M::BicRR),
            (L::BorNot, M::OrnRR),
            (L::Iadd, M::AddRR),
            (L::Isub, M::SubRR),
        ] {
            let owner = bind(
                &int_binary(ty.clone(), op),
                &binary_machine(ty.clone(), opcode),
            );
            assert_eq!(owner.covered().len(), 1);
        }
        assert_return_mismatch(
            &int_binary(ty.clone(), L::BandNot),
            &binary_machine(ty.clone(), M::OrnRR),
        );
        assert_return_mismatch(
            &int_binary(ty.clone(), L::Band),
            &binary_machine(ty.clone(), M::EorRR),
        );
    }
    // x & 0xff as a logical immediate, and the W view of an I32.
    let source = lir(
        &[Type::I32],
        Type::I32,
        vec![(
            vec![],
            vec![
                ins(
                    L::Iconst {
                        ty: Type::I32,
                        imm: 0xff,
                    },
                    &[],
                    &[1],
                ),
                ins(L::Band, &[0, 1], &[2]),
                ins(L::Return, &[2], &[]),
            ],
        )],
    );
    let body = |mask: i64| {
        machine(
            &[Type::I32],
            Type::I32,
            vec![(
                vec![mi(M::AndRI, vec![w(0), w(0), imm(mask)]), ret()],
                vec![],
            )],
        )
    };
    bind(&source, &body(0xff));
    assert_return_mismatch(&source, &body(0x7f));
}

/// `(= name expr)`: a definition premise.
fn is_definition(premise: &E) -> bool {
    matches!(premise, E::Eq { lhs, .. } if matches!(lhs.as_ref(), E::Var { .. }))
}

fn shift(ty: Type, op: L, masked: bool) -> Function {
    let mut instructions = Vec::new();
    let amount = if masked {
        let bits = if ty == Type::I32 { 31 } else { 63 };
        instructions.push(ins(
            L::Iconst {
                ty: ty.clone(),
                imm: bits,
            },
            &[],
            &[10],
        ));
        instructions.push(ins(L::Band, &[1, 10], &[11]));
        11
    } else {
        1
    };
    instructions.push(ins(op, &[0, amount], &[2]));
    instructions.push(ins(L::Return, &[2], &[]));
    lir(&[ty.clone(), ty.clone()], ty, vec![(vec![], instructions)])
}

#[test]
fn register_shifts_bind_under_the_shift_amount_rule() {
    for ty in [Type::I32, Type::I64] {
        for (op, opcode) in [
            (L::Ishl, M::LslRR),
            (L::Ushr, M::LsrRR),
            (L::Sshr, M::AsrRR),
        ] {
            // Bare: defined below the width, where LSLV's modulo agrees.
            let owner = bind(
                &shift(ty.clone(), op.clone(), false),
                &binary_machine(ty.clone(), opcode),
            );
            assert_eq!(owner.covered().len(), 1);
            assert!(
                owner
                    .obligation()
                    .preconditions
                    .iter()
                    .any(|premise| !is_definition(premise)),
                "an unmasked source shift states its definedness domain"
            );
            // Rust's masked shift (x << (y & (w - 1))) is LSLV alone, and its
            // amount is provably in range: no domain premise.
            let masked = bind(
                &shift(ty.clone(), op.clone(), true),
                &binary_machine(ty.clone(), opcode),
            );
            assert!(masked.obligation().preconditions.iter().all(is_definition));
        }
        // Wrong kind.
        assert_return_mismatch(
            &shift(ty.clone(), L::Ushr, true),
            &binary_machine(ty.clone(), M::AsrRR),
        );
        assert_return_mismatch(
            &shift(ty.clone(), L::Ishl, true),
            &binary_machine(ty.clone(), M::LsrRR),
        );
    }
    // Wrong amount mask: a 64-bit shift masked to five bits.
    let r = x;
    let narrow_mask = machine(
        &[Type::I64, Type::I64],
        Type::I64,
        vec![(
            vec![
                mi(M::AndRI, vec![r(2), r(1), imm(31)]),
                mi(M::LslRR, vec![r(0), r(0), r(2)]),
                ret(),
            ],
            vec![],
        )],
    );
    assert_return_mismatch(&shift(Type::I64, L::Ishl, false), &narrow_mask);
    assert_return_mismatch(&shift(Type::I64, L::Ishl, true), &narrow_mask);
}

#[test]
fn immediate_shifts_and_bitfield_moves_bind() {
    let source = |op: L, amount: i64| {
        lir(
            &[Type::I64],
            Type::I64,
            vec![(
                vec![],
                vec![
                    ins(
                        L::Iconst {
                            ty: Type::I64,
                            imm: amount,
                        },
                        &[],
                        &[1],
                    ),
                    ins(op, &[0, 1], &[2]),
                    ins(L::Return, &[2], &[]),
                ],
            )],
        )
    };
    let body = |row: MachInst| machine(&[Type::I64], Type::I64, vec![(vec![row, ret()], vec![])]);
    bind(
        &source(L::Ishl, 3),
        &body(mi(M::LslRI, vec![x(0), x(0), imm(3)])),
    );
    bind(
        &source(L::Ushr, 7),
        &body(mi(M::LsrRI, vec![x(0), x(0), imm(7)])),
    );
    bind(
        &source(L::Sshr, 9),
        &body(mi(M::AsrRI, vec![x(0), x(0), imm(9)])),
    );
    // The same shifts as the UBFM/SBFM words the encoder emits for them.
    bind(
        &source(L::Ishl, 3),
        &body(mi(M::Ubfm, vec![x(0), x(0), imm(61), imm(60)])),
    );
    bind(
        &source(L::Ushr, 7),
        &body(mi(M::Ubfm, vec![x(0), x(0), imm(7), imm(63)])),
    );
    bind(
        &source(L::Sshr, 9),
        &body(mi(M::Sbfm, vec![x(0), x(0), imm(9), imm(63)])),
    );
    // Wrong kind or amount.
    assert_return_mismatch(
        &source(L::Sshr, 9),
        &body(mi(M::LsrRI, vec![x(0), x(0), imm(9)])),
    );
    assert_return_mismatch(
        &source(L::Ishl, 3),
        &body(mi(M::LslRI, vec![x(0), x(0), imm(4)])),
    );
    // A shift by a constant at or above the width is undefined on every input:
    // a theorem over a definedness domain that is always empty would be vacuous,
    // so none is built.
    let undefined = source(L::Ishl, 64);
    assert!(matches!(
        refusal(&undefined, &body(mi(M::LslRI, vec![x(0), x(0), imm(1)]))),
        A64BodyRefusal::Unsupported(A64BodyUnsupported::NeverDefined)
    ));
}

/// `select(c1, select(c2, a, b), a) + 1` style nesting with arithmetic.
fn nested_select() -> Function {
    lir(
        &four_i64(),
        Type::I64,
        vec![(
            vec![],
            vec![
                ins(
                    L::Icmp {
                        cond: IntCC::SignedLessThan,
                    },
                    &[0, 1],
                    &[4],
                ),
                ins(L::Icmp { cond: IntCC::Equal }, &[2, 3], &[5]),
                ins(
                    L::Select {
                        cond: IntCC::NotEqual,
                    },
                    &[5, 2, 3],
                    &[6],
                ),
                ins(
                    L::Select {
                        cond: IntCC::NotEqual,
                    },
                    &[4, 6, 0],
                    &[7],
                ),
                ins(
                    L::Iconst {
                        ty: Type::I64,
                        imm: 1,
                    },
                    &[],
                    &[8],
                ),
                ins(L::Iadd, &[7, 8], &[9]),
                ins(L::Return, &[9], &[]),
            ],
        )],
    )
}

fn nested_select_machine(inner_cc: i64, outer_cc: i64, swapped: bool) -> MachFunction {
    let (t, e) = if swapped { (x(0), x(4)) } else { (x(4), x(0)) };
    machine(
        &four_i64(),
        Type::I64,
        vec![(
            vec![
                mi(M::CmpRR, vec![x(2), x(3)]),
                mi(M::Csel, vec![x(4), x(2), x(3), imm(inner_cc)]),
                mi(M::CmpRR, vec![x(0), x(1)]),
                mi(M::Csel, vec![x(1), t, e, imm(outer_cc)]),
                mi(M::AddRI, vec![x(0), x(1), imm(1)]),
                ret(),
            ],
            vec![],
        )],
    )
}

#[test]
fn nested_selects_and_arithmetic_on_selected_values_bind() {
    let owner = bind(&nested_select(), &nested_select_machine(0, 11, false));
    assert_eq!(owner.covered().len(), 5);
    // Wrong condition (GE for LT, NE for EQ) and swapped arms.
    assert_return_mismatch(&nested_select(), &nested_select_machine(0, 10, false));
    assert_return_mismatch(&nested_select(), &nested_select_machine(1, 11, false));
    assert_return_mismatch(&nested_select(), &nested_select_machine(0, 11, true));
    // Every signed/unsigned order against its own condition code.
    for (cond, cc) in [
        (IntCC::Equal, 0),
        (IntCC::NotEqual, 1),
        (IntCC::UnsignedGreaterThanOrEqual, 2),
        (IntCC::UnsignedLessThan, 3),
        (IntCC::UnsignedGreaterThan, 8),
        (IntCC::UnsignedLessThanOrEqual, 9),
        (IntCC::SignedGreaterThanOrEqual, 10),
        (IntCC::SignedLessThan, 11),
        (IntCC::SignedGreaterThan, 12),
        (IntCC::SignedLessThanOrEqual, 13),
    ] {
        let source = lir(
            &[Type::I32, Type::I32],
            Type::B1,
            vec![(
                vec![],
                vec![
                    ins(L::Icmp { cond }, &[0, 1], &[2]),
                    ins(L::Return, &[2], &[]),
                ],
            )],
        );
        let body = |cc: i64| {
            machine(
                &[Type::I32, Type::I32],
                Type::B1,
                vec![(
                    vec![
                        mi(M::CmpRR, vec![w(0), w(1)]),
                        mi(M::CSet, vec![w(0), imm(cc)]),
                        ret(),
                    ],
                    vec![],
                )],
            )
        };
        bind(&source, &body(cc));
        for other in (0..=13).filter(|other| *other != cc) {
            assert_return_mismatch(&source, &body(other));
        }
    }
}

/// `if c { a ^ b } else { b >> 5 } + 1` with a Boolean condition parameter.
fn diamond() -> Function {
    lir(
        &[Type::B1, Type::I64, Type::I64],
        Type::I64,
        vec![
            (
                vec![],
                vec![ins(
                    L::Brif {
                        cond: Value(0),
                        then_dest: Block(1),
                        else_dest: Block(2),
                    },
                    &[0],
                    &[],
                )],
            ),
            (
                vec![],
                vec![
                    ins(L::Bxor, &[1, 2], &[3]),
                    ins(L::Copy, &[3], &[4]),
                    ins(L::Jump { dest: Block(3) }, &[], &[]),
                ],
            ),
            (
                vec![],
                vec![
                    ins(
                        L::Iconst {
                            ty: Type::I64,
                            imm: 5,
                        },
                        &[],
                        &[5],
                    ),
                    ins(L::Ushr, &[2, 5], &[6]),
                    ins(L::Copy, &[6], &[4]),
                    ins(L::Jump { dest: Block(3) }, &[], &[]),
                ],
            ),
            (
                vec![(4, Type::I64)],
                vec![
                    ins(
                        L::Iconst {
                            ty: Type::I64,
                            imm: 1,
                        },
                        &[],
                        &[7],
                    ),
                    ins(L::Iadd, &[4, 7], &[8]),
                    ins(L::Return, &[8], &[]),
                ],
            ),
        ],
    )
}

/// The O2 shape: CBNZ on the masked Boolean, the else arm laid out first.
fn diamond_machine(else_row: MachInst) -> MachFunction {
    let mut function = machine(
        &[Type::B1, Type::I64, Type::I64],
        Type::I64,
        vec![
            (
                vec![
                    mi(M::Uxtb, vec![x(3), x(0)]),
                    mi(M::Cbnz, vec![x(3), blk(3)]),
                ],
                vec![3, 1],
            ),
            (vec![else_row], vec![2]),
            (vec![mi(M::AddRI, vec![x(0), x(0), imm(1)]), ret()], vec![]),
            (
                vec![mi(M::EorRR, vec![x(0), x(1), x(2)]), mi(M::B, vec![blk(2)])],
                vec![2],
            ),
        ],
    );
    function.block_order = vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)];
    function
}

#[test]
fn diamond_with_computed_arms_and_a_block_argument_binds() {
    let owner = bind(
        &diamond(),
        &diamond_machine(mi(M::LsrRI, vec![x(0), x(2), imm(5)])),
    );
    // UXTB, CBNZ, LSR, ADD, EOR and B: every row but RET.
    assert_eq!(owner.covered().len(), 6);
    // Swapped arms, a wrong arm and a dropped block argument (the else arm
    // writes another register, so the join reads X0's entry value).
    let mut swapped = diamond_machine(mi(M::LsrRI, vec![x(0), x(2), imm(5)]));
    swapped.insts[1] = mi(M::Cbz, vec![x(3), blk(3)]);
    assert_return_mismatch(&diamond(), &swapped);
    assert_return_mismatch(
        &diamond(),
        &diamond_machine(mi(M::AsrRI, vec![x(0), x(2), imm(5)])),
    );
    assert_return_mismatch(
        &diamond(),
        &diamond_machine(mi(M::LsrRI, vec![x(5), x(2), imm(5)])),
    );
}

/// Two join parameters fed from three predecessors, one through a split edge.
fn dag() -> Function {
    lir(
        &four_i64(),
        Type::I64,
        vec![
            (
                vec![],
                vec![
                    ins(
                        L::Icmp {
                            cond: IntCC::SignedLessThan,
                        },
                        &[0, 1],
                        &[4],
                    ),
                    ins(
                        L::Brif {
                            cond: Value(4),
                            then_dest: Block(1),
                            else_dest: Block(2),
                        },
                        &[4],
                        &[],
                    ),
                ],
            ),
            (
                vec![],
                vec![
                    ins(
                        L::Icmp {
                            cond: IntCC::UnsignedGreaterThan,
                        },
                        &[2, 3],
                        &[5],
                    ),
                    ins(
                        L::Brif {
                            cond: Value(5),
                            then_dest: Block(3),
                            else_dest: Block(4),
                        },
                        &[5],
                        &[],
                    ),
                ],
            ),
            (
                vec![],
                vec![
                    ins(L::Copy, &[3], &[6]),
                    ins(L::Copy, &[2], &[7]),
                    ins(L::Jump { dest: Block(5) }, &[], &[]),
                ],
            ),
            (
                vec![],
                vec![
                    ins(L::Copy, &[2], &[6]),
                    ins(L::Copy, &[3], &[7]),
                    ins(L::Jump { dest: Block(5) }, &[], &[]),
                ],
            ),
            (
                vec![],
                vec![
                    ins(L::Band, &[0, 3], &[8]),
                    ins(L::Copy, &[8], &[6]),
                    ins(L::Copy, &[1], &[7]),
                    ins(L::Jump { dest: Block(5) }, &[], &[]),
                ],
            ),
            (
                vec![(6, Type::I64), (7, Type::I64)],
                vec![ins(L::Isub, &[6, 7], &[9]), ins(L::Return, &[9], &[])],
            ),
        ],
    )
}

fn dag_machine(swap_first: bool) -> MachFunction {
    // Block layout: 0 (entry), 1, 3, 4, 2, 5 as the O0 output lays them out.
    let (a, b) = if swap_first {
        (x(2), x(3))
    } else {
        (x(3), x(2))
    };
    let mut function = machine(
        &four_i64(),
        Type::I64,
        vec![
            (
                vec![
                    mi(M::CmpRR, vec![x(0), x(1)]),
                    mi(M::BCond, vec![imm(11), blk(1)]),
                    mi(M::B, vec![blk(2)]),
                ],
                vec![1, 2],
            ),
            (
                vec![
                    mi(M::CmpRR, vec![x(2), x(3)]),
                    mi(M::BCond, vec![imm(8), blk(3)]),
                    mi(M::B, vec![blk(4)]),
                ],
                vec![3, 4],
            ),
            (
                vec![
                    mi(M::MOVXrr, vec![x(4), a]),
                    mi(M::MOVXrr, vec![x(3), b]),
                    mi(M::B, vec![blk(5)]),
                ],
                vec![5],
            ),
            (
                vec![mi(M::MOVXrr, vec![x(4), x(2)]), mi(M::B, vec![blk(5)])],
                vec![5],
            ),
            (
                vec![
                    mi(M::AndRR, vec![x(4), x(0), x(3)]),
                    mi(M::MOVXrr, vec![x(3), x(1)]),
                    mi(M::B, vec![blk(5)]),
                ],
                vec![5],
            ),
            (vec![mi(M::SubRR, vec![x(0), x(4), x(3)]), ret()], vec![]),
        ],
    );
    function.block_order = [0, 1, 3, 4, 2, 5].into_iter().map(BlockId).collect();
    function
}

#[test]
fn multi_block_dag_with_two_join_parameters_binds() {
    let owner = bind(&dag(), &dag_machine(false));
    // The four join copies are in the returned value's slice: the replayed
    // theorem credits them (OD-35 route C), apart from the computing rows.
    assert_eq!(owner.copies_and_constants().len(), 4);
    assert!(owner.covered().len() >= 8);
    for copy in owner.copies_and_constants() {
        assert!(owner.covers(*copy));
        assert!(!owner.covered().contains(copy));
    }
    // Swapped join arguments on one edge.
    assert_return_mismatch(&dag(), &dag_machine(true));
}

#[test]
fn an_if_converted_machine_binds_a_branching_source() {
    // The diamond without the join arithmetic, against a CSEL body.
    let source = lir(
        &[Type::B1, Type::I64, Type::I64],
        Type::I64,
        vec![
            (
                vec![],
                vec![ins(
                    L::Brif {
                        cond: Value(0),
                        then_dest: Block(1),
                        else_dest: Block(2),
                    },
                    &[0],
                    &[],
                )],
            ),
            (
                vec![],
                vec![
                    ins(L::Bxor, &[1, 2], &[3]),
                    ins(L::Copy, &[3], &[4]),
                    ins(L::Jump { dest: Block(3) }, &[], &[]),
                ],
            ),
            (
                vec![],
                vec![
                    ins(L::Copy, &[2], &[4]),
                    ins(L::Jump { dest: Block(3) }, &[], &[]),
                ],
            ),
            (vec![(4, Type::I64)], vec![ins(L::Return, &[4], &[])]),
        ],
    );
    let body = |cc: i64| {
        machine(
            &[Type::B1, Type::I64, Type::I64],
            Type::I64,
            vec![(
                vec![
                    mi(M::Uxtb, vec![x(3), x(0)]),
                    mi(M::EorRR, vec![x(4), x(1), x(2)]),
                    mi(M::CmpRI, vec![x(3), imm(0)]),
                    mi(M::Csel, vec![x(0), x(4), x(2), imm(cc)]),
                    ret(),
                ],
                vec![],
            )],
        )
    };
    bind(&source, &body(1));
    assert_return_mismatch(&source, &body(0));
}

#[test]
fn loops_are_refused_by_name_on_both_sides() {
    let looping = lir(
        &[Type::I64],
        Type::I64,
        vec![
            (
                vec![],
                vec![
                    ins(L::Copy, &[0], &[1]),
                    ins(L::Jump { dest: Block(1) }, &[], &[]),
                ],
            ),
            (
                vec![(1, Type::I64)],
                vec![
                    ins(L::Icmp { cond: IntCC::Equal }, &[1, 0], &[2]),
                    ins(
                        L::Brif {
                            cond: Value(2),
                            then_dest: Block(2),
                            else_dest: Block(1),
                        },
                        &[2],
                        &[],
                    ),
                ],
            ),
            (vec![], vec![ins(L::Return, &[0], &[])]),
        ],
    );
    let source_refusal = a64_body_source_refusal(&looping).expect("a loop is refused");
    assert!(
        source_refusal.to_string().contains("a loop"),
        "{source_refusal}"
    );
    assert!(!source_admits_a64_body_owner(&looping));
    let source = int_binary(Type::I64, L::Iadd);
    let machine_loop = machine(
        &[Type::I64, Type::I64],
        Type::I64,
        vec![
            (vec![mi(M::AddRR, vec![x(0), x(0), x(1)])], vec![1]),
            (vec![mi(M::Cbz, vec![x(0), blk(0)])], vec![0, 2]),
            (vec![ret()], vec![]),
        ],
    );
    let machine_refusal = refusal(&source, &machine_loop);
    assert!(
        matches!(&machine_refusal, A64BodyRefusal::Unsupported(A64BodyUnsupported::MachineControl(why)) if why.contains("a loop")),
        "{machine_refusal}"
    );
}

#[test]
fn preserved_writes_garbage_reads_and_frames_are_classified() {
    let source = int_binary(Type::I64, L::Iadd);
    let clobbers = machine(
        &[Type::I64, Type::I64],
        Type::I64,
        vec![(
            vec![
                mi(M::AddRR, vec![x(19), x(0), x(1)]),
                mi(M::AddRR, vec![x(0), x(0), x(1)]),
                ret(),
            ],
            vec![],
        )],
    );
    assert!(matches!(
        refusal(&source, &clobbers),
        A64BodyRefusal::Mismatch(A64BodyMismatch::PreservedWrite { .. })
    ));
    // Reading a register the body never wrote reads the caller's garbage.
    let garbage = machine(
        &[Type::I64, Type::I64],
        Type::I64,
        vec![(vec![mi(M::AddRR, vec![x(0), x(0), x(9)]), ret()], vec![])],
    );
    assert_return_mismatch(&source, &garbage);
    // The FP/LR envelope belongs to the frame owner.
    let framed = machine(
        &[Type::I64, Type::I64],
        Type::I64,
        vec![(
            vec![
                mi(
                    M::StpPreIndex,
                    vec![x(29), x(30), O::Special(SpecialReg::SP), imm(-16)],
                ),
                mi(M::AddRR, vec![x(0), x(0), x(1)]),
                ret(),
            ],
            vec![],
        )],
    );
    assert!(matches!(
        refusal(&source, &framed),
        A64BodyRefusal::Unsupported(A64BodyUnsupported::MachineRow { .. })
    ));
    // A signature that differs is a mismatch.
    let mut renamed = binary_machine(Type::I64, M::AddRR);
    renamed.signature.params = vec![MType::I32, MType::I64];
    assert!(matches!(
        refusal(&source, &renamed),
        A64BodyRefusal::Mismatch(A64BodyMismatch::Signature)
    ));
}

#[test]
fn identity_is_refused_and_live_constants_have_refutable_obligations() {
    let identity = lir(
        &[Type::I64],
        Type::I64,
        vec![(vec![], vec![ins(L::Return, &[0], &[])])],
    );
    let body = machine(&[Type::I64], Type::I64, vec![(vec![ret()], vec![])]);
    assert!(matches!(
        refusal(&identity, &body),
        A64BodyRefusal::Unsupported(A64BodyUnsupported::NoCoveredRow)
    ));
    let constant = lir(
        &[Type::I64],
        Type::I64,
        vec![(
            vec![],
            vec![
                ins(
                    L::Iconst {
                        ty: Type::I64,
                        imm: 42,
                    },
                    &[],
                    &[1],
                ),
                ins(L::Return, &[1], &[]),
            ],
        )],
    );
    let body = machine(
        &[Type::I64],
        Type::I64,
        vec![(vec![mi(M::Movz, vec![x(0), imm(42)]), ret()], vec![])],
    );
    let owner = source_bound_a64_body(&constant, &body).unwrap();
    assert!(owner.covered().is_empty());
    assert_eq!(owner.copies_and_constants(), &[InstId(0)]);
    assert!(!owner.obligation().is_degenerate());
    for operands in [vec![x(0), imm(43)], vec![x(1), imm(42)]] {
        let mut wrong = body.clone();
        wrong.insts[0].operands = operands;
        assert_return_mismatch(&constant, &wrong);
    }
    // A dead constant cannot turn an identity into an admissible body.
    let dead = machine(
        &[Type::I64],
        Type::I64,
        vec![(
            vec![
                mi(M::Movz, vec![x(5), imm(42)]),
                mi(M::MOVXrr, vec![x(0), x(0)]),
                ret(),
            ],
            vec![],
        )],
    );
    assert!(matches!(
        refusal(&identity, &dead),
        A64BodyRefusal::Unsupported(A64BodyUnsupported::NoCoveredRow)
    ));
}

#[test]
fn the_obligation_is_definitional_and_the_slice_excludes_dead_rows() {
    let source = int_binary(Type::I64, L::Bxor);
    let body = machine(
        &[Type::I64, Type::I64],
        Type::I64,
        vec![(
            vec![
                // Dead: its value never reaches X0.
                mi(M::AndRR, vec![x(5), x(0), x(1)]),
                mi(M::EorRR, vec![x(0), x(0), x(1)]),
                ret(),
            ],
            vec![],
        )],
    );
    let owner = bind(&source, &body);
    assert_eq!(owner.covered(), &[InstId(1)]);
    let obligation = owner.obligation();
    assert_eq!(obligation.name, A64_BODY_OBLIGATION_NAME);
    assert!(!obligation.is_degenerate());
    // Every premise defines a fresh declared name from earlier names.
    let declared: HashSet<&str> = obligation.inputs.iter().map(|(n, _)| n.as_str()).collect();
    let mut defined: HashSet<String> = HashSet::new();
    for premise in obligation.preconditions.iter().rev() {
        let E::Eq { lhs, rhs } = premise else {
            panic!("premise {premise} is not an equation")
        };
        let E::Var { name, .. } = lhs.as_ref() else {
            panic!("premise {premise} defines no name")
        };
        assert!(declared.contains(name.as_str()));
        for used in rhs.free_vars() {
            assert!(
                defined.contains(&used) || used.starts_with('e') || used.starts_with('g'),
                "{name} uses {used} before its definition"
            );
        }
        assert!(defined.insert(name.clone()), "{name} defined twice");
    }
    let smt2 = crate::serialize_to_smt2(obligation);
    assert!(smt2.contains("(check-sat)"));
    assert!(smt2.contains("(declare-const e0 (_ BitVec 64))"));
}

/// OD-35 route C credits a copy or wide-move constant only in the returned
/// value's backward slice: a dead `MOVZ`/`MOVK` pair, dead `MOV` copies at
/// both widths and a dead `MovR` receive nothing, while the live copy and
/// the live constant of the same bodies are credited (apart from the
/// computing rows). Each dead row here would be credited if the
/// copy-or-constant classification ran before the slice filter.
#[test]
fn dead_copies_and_constants_receive_no_route_c_credit() {
    // f(a, b) = a ^ b, its result moved into X0 by a live copy.
    let source = int_binary(Type::I64, L::Bxor);
    let body = machine(
        &[Type::I64, Type::I64],
        Type::I64,
        vec![(
            vec![
                mi(M::Movz, vec![x(5), imm(7)]),
                mi(M::Movk, vec![x(5), imm(1), imm(16)]),
                mi(M::MOVXrr, vec![x(6), x(1)]),
                mi(M::MOVWrr, vec![w(7), w(0)]),
                mi(M::MovR, vec![x(8), x(0)]),
                mi(M::EorRR, vec![x(2), x(0), x(1)]),
                mi(M::MOVXrr, vec![x(0), x(2)]),
                ret(),
            ],
            vec![],
        )],
    );
    let owner = bind(&source, &body);
    assert_eq!(owner.covered(), &[InstId(5)]);
    assert_eq!(owner.copies_and_constants(), &[InstId(6)]);
    for dead in 0..5 {
        let dead = InstId(dead);
        assert!(!owner.covers(dead), "dead row {dead:?} is credited");
        assert!(!owner.copies_and_constants().contains(&dead));
    }
    assert!(owner.covers(InstId(5)) && owner.covers(InstId(6)));
    assert!(!owner.covers(InstId(7)), "RET is credited");

    // f(a) = a ^ 7: the live MOVZ is credited, a dead one beside it is not.
    let source = lir(
        &[Type::I64],
        Type::I64,
        vec![(
            vec![],
            vec![
                ins(
                    L::Iconst {
                        ty: Type::I64,
                        imm: 7,
                    },
                    &[],
                    &[1],
                ),
                ins(L::Bxor, &[0, 1], &[2]),
                ins(L::Return, &[2], &[]),
            ],
        )],
    );
    let body = machine(
        &[Type::I64],
        Type::I64,
        vec![(
            vec![
                mi(M::Movz, vec![x(5), imm(3)]),
                mi(M::Movz, vec![x(9), imm(7)]),
                mi(M::MOVXrr, vec![x(10), x(9)]),
                mi(M::EorRR, vec![x(0), x(0), x(9)]),
                ret(),
            ],
            vec![],
        )],
    );
    let owner = bind(&source, &body);
    assert_eq!(owner.covered(), &[InstId(3)]);
    assert_eq!(owner.copies_and_constants(), &[InstId(1)]);
    for dead in [InstId(0), InstId(2)] {
        assert!(!owner.covers(dead), "dead row {dead:?} is credited");
        assert!(!owner.copies_and_constants().contains(&dead));
    }
}

#[test]
fn branch_displacements_resolve_like_the_encoder() {
    // The diamond with word displacements in place of block operands:
    // block 0 = [UXTB, CBNZ +4] (words 0-1), block 1 = [LSR] (word 2),
    // block 2 = [ADD, RET] (words 3-4), block 3 = [EOR, B -3] (words 5-6).
    let mut body = diamond_machine(mi(M::LsrRI, vec![x(0), x(2), imm(5)]));
    body.insts[1] = mi(M::Cbnz, vec![x(3), imm(4)]);
    let b_row = body.blocks[3].insts[1].0 as usize;
    body.insts[b_row] = mi(M::B, vec![imm(-3)]);
    bind(&diamond(), &body);
    // A displacement to the middle of a block is a definite defect.
    body.insts[1] = mi(M::Cbnz, vec![x(3), imm(5)]);
    assert!(matches!(
        refusal(&diamond(), &body),
        A64BodyRefusal::Mismatch(A64BodyMismatch::BranchTarget {
            defect: BranchTargetDefect::NoBlockStart { .. },
            ..
        })
    ));
}

fn eval(expr: &E, env: &HashMap<String, u64>) -> u64 {
    match expr.try_eval(env).expect("evaluable") {
        crate::smt::EvalResult::Bv(value) => value,
        crate::smt::EvalResult::Bool(value) => u64::from(value),
        other => panic!("unexpected {other:?}"),
    }
}

/// The alias definitions of UBFM/SBFM (Arm ARM UBFX/UBFIZ/SBFX/SBFIZ),
/// independent of `DecodeBitMasks`.
fn bitfield_reference(source: u64, r: u32, s: u32, signed: bool, width: u32) -> u64 {
    let mask = |bits: u32| {
        if bits >= 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        }
    };
    let sign_extend = |value: u64, bits: u32| {
        if bits >= 64 {
            value
        } else if value >> (bits - 1) & 1 == 1 {
            value | !mask(bits)
        } else {
            value
        }
    };
    let source = source & mask(width);
    let value = if s >= r {
        let field = (source >> r) & mask(s - r + 1);
        if signed {
            sign_extend(field, s - r + 1)
        } else {
            field
        }
    } else {
        let field = source & mask(s + 1);
        let field = if signed {
            sign_extend(field, s + 1)
        } else {
            field
        };
        field << (width - r)
    };
    value & mask(width)
}

#[test]
fn bitfield_moves_follow_the_architectural_aliases() {
    let samples = [
        0u64,
        1,
        0x80,
        0xff,
        0x8000_0000,
        0xdead_beef_0123_4567,
        u64::MAX,
        0x7fff_ffff_ffff_ffff,
    ];
    for width in [32u32, 64] {
        for r in 0..width {
            for s in 0..width {
                for signed in [false, true] {
                    let term = bitfield(E::var("v", width), r, s, signed, width);
                    for sample in samples {
                        let sample = sample & if width == 64 { u64::MAX } else { 0xffff_ffff };
                        let env = HashMap::from([("v".to_string(), sample)]);
                        assert_eq!(
                            eval(&term, &env),
                            bitfield_reference(sample, r, s, signed, width),
                            "{} r={r} s={s} w={width} v={sample:#x}",
                            if signed { "SBFM" } else { "UBFM" }
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn every_condition_code_follows_the_subs_flags() {
    let values = [
        0u64,
        1,
        2,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ffff,
        0x7fff_ffff_ffff_ffff,
        0x8000_0000_0000_0000,
        u64::MAX,
        5,
    ];
    for width in [32u32, 64] {
        let mut defs = Defs::default();
        let flags: Flags = subs_flags(
            &mut defs,
            InstId(0),
            E::var("a", width),
            E::var("b", width),
            width,
        );
        for &a in &values {
            for &b in &values {
                let m = if width == 64 { u64::MAX } else { 0xffff_ffff };
                let (a, b) = (a & m, b & m);
                let mut env = HashMap::from([("a".to_string(), a), ("b".to_string(), b)]);
                for definition in &defs.definitions {
                    let value = eval(&definition.expr, &env);
                    env.insert(definition.name.clone(), value);
                }
                let signed = |v: u64| ((v << (64 - width)) as i64) >> (64 - width);
                let (sa, sb) = (signed(a), signed(b));
                let expected = [
                    a == b,
                    a != b,
                    a >= b,
                    a < b,
                    (a.wrapping_sub(b) & m) >> (width - 1) == 1,
                    (a.wrapping_sub(b) & m) >> (width - 1) == 0,
                    sa.checked_sub(sb).is_none_or(|d| d != signed(d as u64 & m)),
                    !sa.checked_sub(sb).is_none_or(|d| d != signed(d as u64 & m)),
                    a > b,
                    a <= b,
                    sa >= sb,
                    sa < sb,
                    sa > sb,
                    sa <= sb,
                    true,
                    true,
                ];
                for (cc, expected) in expected.iter().enumerate() {
                    assert_eq!(
                        eval(&condition(&flags, cc as u8), &env) == 1,
                        *expected,
                        "cc {cc} w={width} a={a:#x} b={b:#x}"
                    );
                }
            }
        }
    }
}

#[test]
fn the_opcode_lists_are_the_admission_predicates() {
    // A sample of listed machine opcodes is admitted, and of others is not.
    for opcode in [
        M::MulRR,
        M::StrRI,
        M::LdrRI,
        M::Bl,
        M::StpPreIndex,
        M::Fcmp,
        M::Br,
    ] {
        assert!(!admits_machine_opcode(opcode), "{opcode:?}");
    }
    for opcode in [M::Csel, M::Ubfm, M::Tbnz, M::BicRR, M::LslRR] {
        assert!(admits_machine_opcode(opcode), "{opcode:?}");
        assert!(ADMITTED_MACHINE_OPCODES.contains(&format!("{opcode:?}").as_str()));
    }
    for opcode in [
        L::Imul,
        L::Udiv,
        L::Trap,
        L::Select {
            cond: IntCC::SignedLessThan,
        },
    ] {
        assert!(!admits_lir_opcode(&opcode), "{opcode:?}");
    }
    for opcode in [L::Bnot, L::Ishl, L::Select { cond: IntCC::Equal }] {
        assert!(admits_lir_opcode(&opcode));
        assert!(ADMITTED_LIR_OPCODES.contains(&source::opcode_name(&opcode).as_str()));
    }
}

/// Diagnostic: write the live-config query of each fixture (and of each
/// corruption) to `TCG_A64_BODY_QUERY_DIR`, for replay outside the crate.
#[test]
fn dump_fixture_queries_when_requested() {
    let Some(dir) = std::env::var_os("TCG_A64_BODY_QUERY_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    let mut cases: Vec<(&str, Function, MachFunction)> = vec![
        ("bool_and", bool_pair(L::Band), bool_pair_machine(M::AndRR)),
        (
            "bool_and_as_orr",
            bool_pair(L::Band),
            bool_pair_machine(M::OrrRR),
        ),
        (
            "i64_bic",
            int_binary(Type::I64, L::BandNot),
            binary_machine(Type::I64, M::BicRR),
        ),
        (
            "i64_bic_as_orn",
            int_binary(Type::I64, L::BandNot),
            binary_machine(Type::I64, M::OrnRR),
        ),
        (
            "i64_shl_bare",
            shift(Type::I64, L::Ishl, false),
            binary_machine(Type::I64, M::LslRR),
        ),
        (
            "i64_shl_masked",
            shift(Type::I64, L::Ishl, true),
            binary_machine(Type::I64, M::LslRR),
        ),
        (
            "i64_ushr_as_asr",
            shift(Type::I64, L::Ushr, true),
            binary_machine(Type::I64, M::AsrRR),
        ),
        (
            "i32_sshr",
            shift(Type::I32, L::Sshr, true),
            binary_machine(Type::I32, M::AsrRR),
        ),
        (
            "nested_select",
            nested_select(),
            nested_select_machine(0, 11, false),
        ),
        (
            "nested_select_wrong_cc",
            nested_select(),
            nested_select_machine(0, 10, false),
        ),
        (
            "nested_select_swapped",
            nested_select(),
            nested_select_machine(0, 11, true),
        ),
        (
            "diamond",
            diamond(),
            diamond_machine(mi(M::LsrRI, vec![x(0), x(2), imm(5)])),
        ),
        (
            "diamond_dropped_arg",
            diamond(),
            diamond_machine(mi(M::LsrRI, vec![x(5), x(2), imm(5)])),
        ),
        ("dag", dag(), dag_machine(false)),
        ("dag_swapped_args", dag(), dag_machine(true)),
    ];
    let narrow_mask = machine(
        &[Type::I64, Type::I64],
        Type::I64,
        vec![(
            vec![
                mi(M::AndRI, vec![x(2), x(1), imm(31)]),
                mi(M::LslRR, vec![x(0), x(0), x(2)]),
                ret(),
            ],
            vec![],
        )],
    );
    cases.push((
        "i64_shl_narrow_mask",
        shift(Type::I64, L::Ishl, false),
        narrow_mask,
    ));
    let config = crate::verdict_db::live_source_bound_config();
    for (name, source, body) in cases {
        let obligation = diagnostic_a64_body_obligation(&source, &body)
            .unwrap_or_else(|refusal| panic!("{name}: {refusal}"));
        let query = crate::ay_bridge::generate_smt2_query_raw(&obligation, &config);
        std::fs::write(dir.join(format!("{name}.smt2")), query).unwrap();
    }
}

#[path = "source_bound_a64_body_row_tests.rs"]
mod rows;

#[test]
fn inline_threshold_preserves_exact_boundary_and_large_terms() {
    let mut term = E::bv_const(0, 64);
    for nodes in 1..=4096 {
        assert_eq!(
            exceeds_inline_limit(&term),
            nodes > INLINE_LIMIT,
            "{nodes} nodes"
        );
        term = E::BvNeg {
            operand: term.into(),
            width: 64,
        };
    }
}

#[test]
fn inline_threshold_counts_all_ite_arms() {
    let mut arm = E::bv_const(0, 64);
    // Two nested ITEs, their conditions and three 170-node arms total 514 nodes.
    for _ in 1..170 {
        arm = E::BvNeg {
            operand: arm.into(),
            width: 64,
        };
    }
    let pair = E::Ite {
        cond: E::BoolConst(true).into(),
        then_expr: arm.clone().into(),
        else_expr: arm.clone().into(),
    };
    assert!(!exceeds_inline_limit(&pair));
    let term = E::Ite {
        cond: E::BoolConst(false).into(),
        then_expr: pair.into(),
        else_expr: arm.into(),
    };
    assert!(exceeds_inline_limit(&term));
}

#[test]
fn inline_threshold_bounds_shared_dag_expansion() {
    let mut term = E::bv_const(0, 64);
    for _ in 0..64 {
        let shared = std::sync::Arc::new(term);
        term = E::BvAdd {
            lhs: shared.clone(),
            rhs: shared,
            width: 64,
        };
    }
    // The expanded tree has more than usize::MAX nodes on a 64-bit host.
    // The threshold walk must finish without enumerating it or overflowing.
    assert!(exceeds_inline_limit(&term));
}

/// The adapter retains a narrow ABI signature while materializing its result
/// in an explicitly zero-extended I32 carrier (the captured Termination leaf).
#[test]
fn narrow_return_carriers_bind_the_source_extension_and_return_bits() {
    for (ty, extend, sign_extend, high) in [
        (Type::I8, M::Uxtb, M::Sxtb, 0x80),
        (Type::I16, M::Uxth, M::Sxth, 0x8000),
    ] {
        for returns in [ty.clone(), Type::I32] {
            let source = lir(
                std::slice::from_ref(&ty),
                returns.clone(),
                vec![(
                    vec![],
                    vec![
                        ins(
                            L::Uextend {
                                from_ty: ty.clone(),
                                to_ty: Type::I32,
                            },
                            &[0],
                            &[1],
                        ),
                        ins(L::Return, &[1], &[]),
                    ],
                )],
            );
            let body = machine(
                std::slice::from_ref(&ty),
                returns.clone(),
                vec![(
                    vec![
                        mi(extend, vec![w(1), w(0)]),
                        mi(M::MOVWrr, vec![w(0), w(1)]),
                        ret(),
                    ],
                    vec![],
                )],
            );
            let owner = source_bound_a64_body(&source, &body).unwrap();
            assert_eq!(owner.covered(), &[InstId(0)]);
            assert_eq!(owner.copies_and_constants(), &[InstId(1)]);
            assert!(!owner.obligation().is_degenerate());
            let mut wrong = body.clone();
            wrong.insts[1].operands[1] = w(2);
            assert_return_mismatch(&source, &wrong);
            // Even a narrow signature must preserve the I32 carrier's upper
            // bits: an ABI caller may consume W0 without another extension.
            let mut wrong = body.clone();
            wrong.insts[0].opcode = sign_extend;
            assert_return_mismatch(&source, &wrong);
            if returns == ty {
                let missing_carrier = lir(
                    std::slice::from_ref(&ty),
                    ty.clone(),
                    vec![(vec![], vec![ins(L::Return, &[0], &[])])],
                );
                assert!(matches!(
                    refusal(&missing_carrier, &body),
                    A64BodyRefusal::Unsupported(A64BodyUnsupported::SourceDomain(_))
                ));
            }
            if returns == ty {
                let unexplained = lir(
                    &[Type::I32],
                    ty.clone(),
                    vec![(vec![], vec![ins(L::Return, &[0], &[])])],
                );
                assert!(matches!(
                    refusal(&unexplained, &body),
                    A64BodyRefusal::Unsupported(A64BodyUnsupported::SourceDomain(_))
                ));
            }
            let mut malformed = source.clone();
            malformed.blocks.get_mut(&Block(0)).unwrap().instructions[0].opcode = L::Uextend {
                from_ty: Type::I32,
                to_ty: ty.clone(),
            };
            assert!(source_bound_a64_body(&malformed, &body).is_err());
            // A constant-valued captured leaf still contains a computing UXT
            // row; no change to the constant-only admission rule is needed.
            let constant = lir(
                &[],
                returns.clone(),
                vec![(
                    vec![],
                    vec![
                        ins(
                            L::Iconst {
                                ty: ty.clone(),
                                imm: high,
                            },
                            &[],
                            &[0],
                        ),
                        ins(
                            L::Uextend {
                                from_ty: ty.clone(),
                                to_ty: Type::I32,
                            },
                            &[0],
                            &[1],
                        ),
                        ins(L::Return, &[1], &[]),
                    ],
                )],
            );
            let body = machine(
                &[],
                returns,
                vec![(
                    vec![
                        mi(M::Movz, vec![w(0), imm(high)]),
                        mi(extend, vec![w(1), w(0)]),
                        mi(M::MOVWrr, vec![w(0), w(1)]),
                        ret(),
                    ],
                    vec![],
                )],
            );
            let owner = source_bound_a64_body(&constant, &body).unwrap();
            assert_eq!(owner.covered(), &[InstId(1)]);
            assert_eq!(owner.copies_and_constants(), &[InstId(0), InstId(2)]);
            let mut wrong = body.clone();
            wrong.insts[0].operands[1] = imm(high + 1);
            assert_return_mismatch(&constant, &wrong);
        }
    }
}

#[test]
fn all_integer_zero_extensions_bind_at_their_exact_widths() {
    // The 8/16 -> 32 pairs are covered by the return-carrier test above.
    for (from, extend, wrong_extend) in [
        (Type::I8, M::Uxtb, M::Sxtb),
        (Type::I16, M::Uxth, M::Sxth),
        (Type::I32, M::Uxtw, M::Sxtw),
    ] {
        let source = lir(
            std::slice::from_ref(&from),
            Type::I64,
            vec![(
                vec![],
                vec![
                    ins(
                        L::Uextend {
                            from_ty: from.clone(),
                            to_ty: Type::I64,
                        },
                        &[0],
                        &[1],
                    ),
                    ins(L::Return, &[1], &[]),
                ],
            )],
        );
        let operands = if from == Type::I32 {
            vec![x(0), x(0)]
        } else {
            vec![w(0), w(0)]
        };
        let body = machine(
            std::slice::from_ref(&from),
            Type::I64,
            vec![(vec![mi(extend, operands), ret()], vec![])],
        );
        let owner = source_bound_a64_body(&source, &body).unwrap();
        assert_eq!(owner.covered(), &[InstId(0)]);
        let mut wrong = body.clone();
        wrong.insts[0].opcode = wrong_extend;
        assert_return_mismatch(&source, &wrong);
    }
    // 8 -> 16, followed by the explicit 16 -> 32 ABI return carrier.
    let source = lir(
        &[Type::I8],
        Type::I16,
        vec![(
            vec![],
            vec![
                ins(
                    L::Uextend {
                        from_ty: Type::I8,
                        to_ty: Type::I16,
                    },
                    &[0],
                    &[1],
                ),
                ins(
                    L::Uextend {
                        from_ty: Type::I16,
                        to_ty: Type::I32,
                    },
                    &[1],
                    &[2],
                ),
                ins(L::Copy, &[2], &[3]),
                ins(L::Return, &[3], &[]),
            ],
        )],
    );
    let body = machine(
        &[Type::I8],
        Type::I16,
        vec![(vec![mi(M::Uxtb, vec![w(0), w(0)]), ret()], vec![])],
    );
    assert!(source_bound_a64_body(&source, &body).is_ok());
    let mut wrong = body.clone();
    wrong.insts[0].opcode = M::Sxtb;
    assert_return_mismatch(&source, &wrong);
}

#[test]
fn constant_only_bodies_bind_zero_registers_wide_words_and_partial_updates() {
    for (ty, zero, register, opcode) in [
        (Type::I32, O::Special(SpecialReg::WZR), w(0), M::MOVWrr),
        (Type::I64, O::Special(SpecialReg::XZR), x(0), M::MOVXrr),
    ] {
        let source = lir(
            &[],
            ty.clone(),
            vec![(
                vec![],
                vec![
                    ins(
                        L::Iconst {
                            ty: ty.clone(),
                            imm: 0,
                        },
                        &[],
                        &[0],
                    ),
                    ins(L::Return, &[0], &[]),
                ],
            )],
        );
        let body = machine(
            &[],
            ty,
            vec![(vec![mi(opcode, vec![register, zero]), ret()], vec![])],
        );
        let owner = source_bound_a64_body(&source, &body).unwrap();
        assert!(owner.covered().is_empty());
        assert_eq!(owner.copies_and_constants(), &[InstId(0)]);
        let mut wrong = body.clone();
        wrong.insts[0].operands[1] = x(1);
        assert_return_mismatch(&source, &wrong);
    }
    let source = lir(
        &[],
        Type::I64,
        vec![(
            vec![],
            vec![
                ins(
                    L::Iconst {
                        ty: Type::I64,
                        imm: 0x1234_5678_9abc_def0,
                    },
                    &[],
                    &[0],
                ),
                ins(L::Return, &[0], &[]),
            ],
        )],
    );
    let body = machine(
        &[],
        Type::I64,
        vec![(
            vec![
                mi(M::Movz, vec![x(0), imm(0xdef0)]),
                mi(M::Movk, vec![x(0), imm(0x9abc), imm(16)]),
                mi(M::Movk, vec![x(0), imm(0x5678), imm(32)]),
                mi(M::Movk, vec![x(0), imm(0x1234), imm(48)]),
                ret(),
            ],
            vec![],
        )],
    );
    let owner = source_bound_a64_body(&source, &body).unwrap();
    assert!(owner.covered().is_empty());
    assert_eq!(
        owner.copies_and_constants(),
        &[InstId(0), InstId(1), InstId(2), InstId(3)]
    );
    for row in 0..4 {
        let mut wrong = body.clone();
        wrong.insts[row].operands[1] = imm(1);
        assert_return_mismatch(&source, &wrong);
    }
    // MOVK alone computes a source-bound bit-field update, retaining all
    // other caller input bits. Admission cannot assume those bits are zero.
    let mask = !(0xffff_u64 << 16) as i64;
    let source = lir(
        &[Type::I64],
        Type::I64,
        vec![(
            vec![],
            vec![
                ins(
                    L::Iconst {
                        ty: Type::I64,
                        imm: mask,
                    },
                    &[],
                    &[1],
                ),
                ins(L::Band, &[0, 1], &[2]),
                ins(
                    L::Iconst {
                        ty: Type::I64,
                        imm: 0xbeef_0000,
                    },
                    &[],
                    &[3],
                ),
                ins(L::Bor, &[2, 3], &[4]),
                ins(L::Return, &[4], &[]),
            ],
        )],
    );
    let body = machine(
        &[Type::I64],
        Type::I64,
        vec![(
            vec![mi(M::Movk, vec![x(0), imm(0xbeef), imm(16)]), ret()],
            vec![],
        )],
    );
    let owner = source_bound_a64_body(&source, &body).unwrap();
    assert!(owner.covered().is_empty());
    assert_eq!(owner.copies_and_constants(), &[InstId(0)]);
    let mut wrong = body.clone();
    wrong.insts[0].operands[2] = imm(32);
    assert_return_mismatch(&source, &wrong);
}
