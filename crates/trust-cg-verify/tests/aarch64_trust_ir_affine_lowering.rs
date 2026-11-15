// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Independent mutations around the real TrustIR adapter and raw selector.
//! These checks bind three immutable inputs before optimization; they do not
//! establish final executable, optimizer, encoder or Trust-toolchain authority.

use trust_cg_ir::{AArch64Opcode, MachFunction};
use trust_cg_lower::Function as LirFunction;
use trust_cg_lower::abi::AArch64AbiVariant;

use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::isel::InstructionSelector;
use trust_cg_verify::aarch64_affine_lowering::{
    AffineLoweringError, TrustIrAffineLoweringError, check_aarch64_trust_ir_affine_lowering,
};
use trust_ir::proof::ProofContext;
use trust_ir::{
    BinOp, Block, BlockId, CallingConv, Constant, FuncId, FuncTy, FuncTyId, Function, Inst,
    InstrNode, Module, OverflowOp, ParamAttrs, ProofAnnotation, Ty, ValueId,
};

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}

fn select_fixture(ty: &Ty, op: trust_ir::ICmpOp, reused: bool) -> Module {
    let compare = InstrNode::new(Inst::ICmp {
        op,
        ty: ty.clone(),
        lhs: v(0),
        rhs: v(1),
    })
    .with_result(v(10));
    let selection = |result| {
        InstrNode::new(Inst::Select {
            ty: ty.clone(),
            cond: v(10),
            then_val: v(2),
            else_val: v(3),
        })
        .with_result(v(result))
    };
    let mut instructions = vec![compare, selection(11)];
    if reused {
        instructions.push(selection(12));
    }
    module(
        ty,
        &[0, 1, 2, 3],
        instructions,
        Some(if reused { 12 } else { 11 }),
    )
}

#[test]
fn source_bound_integer_selects_cover_real_folded_and_reused_conditions() {
    use trust_ir::ICmpOp::*;
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        for op in [Eq, Ne, Slt, Sle, Sgt, Sge, Ult, Ule, Ugt, Uge] {
            for reused in [false, true] {
                let source = select_fixture(&ty, op, reused);
                let (lir, machine) = lower(&source, 0);
                check_aarch64_trust_ir_affine_lowering(&source, 0, &lir, &machine).unwrap_or_else(
                    |error| panic!("{ty:?}/{op:?}/reused={reused}: {error}; {machine:#?}"),
                );
            }
        }
    }
}

#[test]
fn source_bound_integer_selects_reject_independent_source_lir_and_machine_mutations() {
    use trust_cg_ir::{InstFlags, MachOperand, RegClass};
    let source = select_fixture(&Ty::I64, trust_ir::ICmpOp::Slt, false);
    let (lir, machine) = lower(&source, 0);
    accept(&source, 0, &lir, &machine);
    for case in 0..5 {
        let mut wrong = source.clone();
        if let Inst::Select {
            cond,
            then_val,
            else_val,
            ty,
        } = &mut body(&mut wrong)[1].inst
        {
            match case {
                0 => std::mem::swap(then_val, else_val),
                1 => *then_val = v(0),
                2 => *cond = v(0),
                3 => *else_val = v(900),
                _ => *ty = Ty::U64,
            }
        }
        assert!(
            check_aarch64_trust_ir_affine_lowering(&wrong, 0, &lir, &machine).is_err(),
            "source mutation {case}"
        );
    }
    for case in 0..4 {
        let mut wrong = lir.clone();
        let inst = wrong
            .blocks
            .values_mut()
            .flat_map(|block| &mut block.instructions)
            .find(|inst| matches!(inst.opcode, Opcode::Select { .. }))
            .unwrap();
        match case {
            0 => inst.args.swap(1, 2),
            1 => {
                inst.opcode = Opcode::Select {
                    cond: trust_cg_lower::instructions::IntCC::Equal,
                }
            }
            2 => inst.args[0] = inst.args[1],
            _ => {
                inst.args.pop();
            }
        }
        assert!(
            check_aarch64_trust_ir_affine_lowering(&source, 0, &wrong, &machine).is_err(),
            "LIR mutation {case}"
        );
    }
    let select = machine
        .insts
        .iter()
        .position(|inst| inst.opcode == AArch64Opcode::Csel)
        .unwrap();
    for case in 0..9 {
        let mut wrong = machine.clone();
        let inst = &mut wrong.insts[select];
        match case {
            0 => inst.operands.swap(1, 2),
            1 => {
                if let MachOperand::Imm(cc) = &mut inst.operands[3] {
                    *cc ^= 1;
                }
            }
            2 => inst.opcode = AArch64Opcode::Csinc,
            3 => inst.opcode = AArch64Opcode::Csneg,
            4 => inst.opcode = AArch64Opcode::Csinv,
            5 => inst.operands[3] = MachOperand::Imm(14),
            6 => {
                if let MachOperand::VReg(reg) = &mut inst.operands[1] {
                    reg.class = RegClass::Gpr32;
                }
            }
            7 => inst.flags = InstFlags::HAS_SIDE_EFFECTS,
            _ => {
                inst.operands.pop();
            }
        }
        assert!(
            check_aarch64_trust_ir_affine_lowering(&source, 0, &lir, &wrong).is_err(),
            "machine mutation {case}"
        );
    }
}

#[test]
fn source_bound_integer_selects_keep_numeric_zero_one_distinct_from_source_bool() {
    for ty in [Ty::I32, Ty::I64] {
        let mut source = select_fixture(&ty, trust_ir::ICmpOp::Slt, false);
        let instructions = body(&mut source);
        instructions.insert(1, constant(&ty, 1, 20));
        instructions.insert(2, constant(&ty, 0, 21));
        if let Inst::Select {
            then_val, else_val, ..
        } = &mut instructions[3].inst
        {
            *then_val = v(20);
            *else_val = v(21);
        }
        let (lir, machine) = lower(&source, 0);
        accept(&source, 0, &lir, &machine);
        // Returning the comparison directly is ill-typed even though its
        // machine carrier contains those same numeric zero/one bits.
        *body(&mut source).last_mut().unwrap() = returned(Some(10));
        assert!(check_aarch64_trust_ir_affine_lowering(&source, 0, &lir, &machine).is_err());
    }
}

#[test]
fn source_bound_integer_selects_bind_raw_arithmetic_variants_and_refuse_nested_domain() {
    for ty in [Ty::I32, Ty::I64] {
        let base = select_fixture(&ty, trust_ir::ICmpOp::Slt, false);
        let (_, original_machine) = lower(&base, 0);
        for (variant, opcode) in [
            (1, AArch64Opcode::Csinc),
            (2, AArch64Opcode::Csinv),
            (3, AArch64Opcode::Csneg),
        ] {
            let mut source = base.clone();
            body(&mut source).insert(
                1,
                constant(
                    &ty,
                    match variant {
                        1 => 1,
                        2 => -1,
                        _ => 0,
                    },
                    20,
                ),
            );
            body(&mut source).insert(
                2,
                if variant == 1 {
                    binary(&ty, BinOp::Add, 3, 20, 21)
                } else {
                    binary(&ty, BinOp::Sub, 20, 3, 21)
                },
            );
            if let Inst::Select { else_val, .. } = &mut body(&mut source)[3].inst {
                *else_val = v(21);
            }
            let (lir, _) = lower(&source, 0);
            // Independently transformed raw stream: the conditional opcode
            // absorbs the source false-arm arithmetic. Its inputs remain the
            // base selector's real ABI copies and CMP operands.
            let mut machine = original_machine.clone();
            machine
                .insts
                .iter_mut()
                .find(|inst| inst.opcode == AArch64Opcode::Csel)
                .unwrap()
                .opcode = opcode;
            accept(&source, 0, &lir, &machine);
            assert!(
                check_aarch64_trust_ir_affine_lowering(&source, 0, &lir, &original_machine)
                    .is_err()
            );
        }
        for case in 0..3 {
            let mut source = base.clone();
            let instructions = body(&mut source);
            instructions.pop();
            instructions.push(match case {
                0 => InstrNode::new(Inst::Select {
                    ty: ty.clone(),
                    cond: v(10),
                    then_val: v(11),
                    else_val: v(3),
                })
                .with_result(v(12)),
                1 => binary(&ty, BinOp::Add, 11, 0, 12),
                _ => InstrNode::new(Inst::ICmp {
                    op: trust_ir::ICmpOp::Slt,
                    ty: ty.clone(),
                    lhs: v(11),
                    rhs: v(0),
                })
                .with_result(v(12)),
            });
            instructions.push(returned(Some(11)));
            let (base_lir, _) = lower(&base, 0);
            assert!(
                matches!(
                    reject(&source, 0, &base_lir, &original_machine),
                    TrustIrAffineLoweringError::UnsupportedTrustIr(_)
                ),
                "nested domain {case}"
            );
        }
    }
}

fn constant(ty: &Ty, value: i128, result: u32) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: ty.clone(),
        value: Constant::Int(value),
    })
    .with_result(v(result))
}

fn binary(ty: &Ty, op: BinOp, lhs: u32, rhs: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::BinOp {
        op,
        ty: ty.clone(),
        lhs: v(lhs),
        rhs: v(rhs),
    })
    .with_result(v(result))
}

fn copy(ty: &Ty, operand: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::Copy {
        ty: ty.clone(),
        operand: v(operand),
    })
    .with_result(v(result))
}

fn returned(value: Option<u32>) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: value.map(v).into_iter().collect(),
    })
}

fn module(ty: &Ty, params: &[u32], mut body: Vec<InstrNode>, result: Option<u32>) -> Module {
    let mut module = Module::new("canonical_affine_fixture");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![ty.clone(); params.len()],
            returns: result.map(|_| ty.clone()).into_iter().collect(),
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(17);
    let mut function = Function::new(FuncId::new(31), "affine", signature, entry);
    body.push(returned(result));
    function.blocks.push(Block {
        id: entry,
        params: params.iter().map(|&id| (v(id), ty.clone())).collect(),
        body,
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn body(module: &mut Module) -> &mut Vec<InstrNode> {
    &mut module.functions[0].blocks[0].body
}

/// Use the actual adapter exactly once, then the production-equivalent raw
/// selector setup. No independently checked result is used to steer selection.
fn lower(module: &Module, ordinal: usize) -> (LirFunction, MachFunction) {
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[ordinal],
        module,
        &permit_unlicensed(),
    )
    .expect("positive fixture must pass the actual TrustIR adapter");
    let mut selector = InstructionSelector::new(lir.name.clone(), lir.signature.clone());
    selector.set_abi_variant(AArch64AbiVariant::Darwin);
    selector.set_stack_slots(lir.stack_slots.clone());
    selector.seed_value_types(&lir.value_types);
    selector.seed_iconst_origins(
        lir.blocks
            .values()
            .map(|block| block.instructions.as_slice()),
    );
    selector.seed_function_value_use_counts(&lir);
    selector
        .lower_formal_arguments(&lir.signature, lir.entry_block)
        .expect("fixture ABI must lower");
    for id in lir.layout_order() {
        let block = &lir.blocks[&id];
        selector
            .select_block_with_provenance(
                id,
                &block.instructions,
                &block.source_locs,
                &lir.trust_ir_origins[&id],
            )
            .expect("fixture instructions must select");
    }
    let machine = selector
        .finalize_with_eh_info(&lir.eh_info)
        .expect("fixture has no unsupported EH")
        .to_ir_func();
    (lir, machine)
}

fn accept(module: &Module, ordinal: usize, lir: &LirFunction, machine: &MachFunction) {
    let checked = check_aarch64_trust_ir_affine_lowering(module, ordinal, lir, machine)
        .unwrap_or_else(|error| panic!("real adapter/selector pair rejected: {error}"));
    assert!(std::ptr::eq(checked.module(), module));
    assert!(std::ptr::eq(checked.source(), &module.functions[ordinal]));
    assert!(std::ptr::eq(checked.lir(), lir));
    assert!(std::ptr::eq(checked.machine(), machine));
    let statistics = checked.statistics();
    assert_eq!(
        statistics.trust_ir_instructions,
        module.functions[ordinal].blocks[0].body.len()
    );
    assert_eq!(
        statistics.lowering.source_instructions,
        lir.blocks[&lir.entry_block].instructions.len()
    );
    assert_eq!(
        statistics.lowering.parameter_count,
        lir.signature.params.len()
    );
    assert_eq!(
        statistics.lowering.machine_instructions,
        machine.block(machine.entry).insts.len()
    );
}

fn reject(
    module: &Module,
    ordinal: usize,
    lir: &LirFunction,
    machine: &MachFunction,
) -> TrustIrAffineLoweringError {
    match check_aarch64_trust_ir_affine_lowering(module, ordinal, lir, machine) {
        Err(error) => error,
        Ok(_) => panic!("changed or unsupported endpoint acquired a canonical receipt"),
    }
}

fn add_fixture() -> Module {
    module(
        &Ty::I32,
        &[0, 1],
        vec![binary(&Ty::I32, BinOp::Add, 0, 1, 10)],
        Some(10),
    )
}

#[test]
fn explicit_abi_slots_cannot_reuse_ordinary_affine_machine_or_byte_bindings() {
    use trust_cg_verify::aarch64_affine_lowering::{
        AffineByteError, check_aarch64_trust_ir_affine_bytes,
    };
    use trust_ir::{ArgExt, PassMode};

    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        let narrow = matches!(ty, Ty::I32 | Ty::U32);
        let mut source = module(
            &ty,
            &[0, 1],
            vec![binary(&ty, BinOp::Add, 0, 1, 10)],
            Some(10),
        );
        source.functions[0].attrs.params = vec![ParamAttrs::default(); 2];
        assert!(trust_ir_build::validate_module(&source).is_empty());
        let (lir, machine) = lower(&source, 0);
        let add: u32 = if narrow { 0x0b01_0000 } else { 0x8b01_0000 };
        let bytes: Vec<u8> = [add, 0xd65f_03c0]
            .into_iter()
            .flat_map(u32::to_le_bytes)
            .collect();
        accept(&source, 0, &lir, &machine);
        check_aarch64_trust_ir_affine_bytes(&source, 0, &lir, &bytes).unwrap();
        let mut annotations = vec![
            ParamAttrs {
                pass: Some(PassMode::Direct),
                ..Default::default()
            },
            ParamAttrs {
                pass: Some(PassMode::Cast {
                    pieces: vec![Ty::U32; if narrow { 1 } else { 2 }],
                }),
                ..Default::default()
            },
        ];
        if narrow {
            annotations.extend([
                ParamAttrs {
                    ext: ArgExt::ZeroExt,
                    ..Default::default()
                },
                ParamAttrs {
                    ext: ArgExt::SignExt,
                    ..Default::default()
                },
            ]);
        }
        for annotation in annotations {
            for slot in 0..3 {
                let mut changed = source.clone();
                let attrs = &mut changed.functions[0].attrs;
                if slot < 2 {
                    attrs.params[slot] = annotation.clone();
                } else {
                    attrs.ret = annotation.clone();
                }
                let errors = trust_ir_build::validate_module(&changed);
                assert!(
                    errors.is_empty(),
                    "{ty:?}, slot {slot}, {annotation:?}: {errors:?}"
                );
                assert!(
                    trust_cg_lower::translate_function_with_license(
                        &changed.functions[0],
                        &changed,
                        &permit_unlicensed()
                    )
                    .is_err()
                );
                assert!(
                    matches!(
                        check_aarch64_trust_ir_affine_lowering(&changed, 0, &lir, &machine),
                        Err(TrustIrAffineLoweringError::UnsupportedTrustIr(_))
                    ),
                    "raw machine: {ty:?}, slot {slot}, {annotation:?}"
                );
                assert!(
                    matches!(
                        check_aarch64_trust_ir_affine_bytes(&changed, 0, &lir, &bytes),
                        Err(AffineByteError::Source(
                            TrustIrAffineLoweringError::UnsupportedTrustIr(_)
                        ))
                    ),
                    "final bytes: {ty:?}, slot {slot}, {annotation:?}"
                );
            }
        }
    }
}

#[test]
fn real_adapter_and_selector_cover_four_types_and_zero_through_eight_parameters() {
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        for count in 0..=8 {
            let params: Vec<u32> = (0..count).map(|i| 3_000_000_000 + i * 101).collect();
            let mut instructions = vec![constant(&ty, 17, 4_000_000_000)];
            let mut value = 4_000_000_000;
            for &parameter in &params {
                instructions.push(binary(&ty, BinOp::Add, value, parameter, value + 1));
                value += 1;
            }
            instructions.push(copy(&ty, value, value + 1));
            let source = module(&ty, &params, instructions, Some(value + 1));
            let (lir, machine) = lower(&source, 0);
            accept(&source, 0, &lir, &machine);
        }
    }
}

#[test]
fn real_void_functions_bind_all_declared_unused_parameters() {
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        for count in 0..=8 {
            let params: Vec<u32> = (0..count).map(|i| 700 + i * 17).collect();
            let source = module(&ty, &params, vec![], None);
            let (lir, machine) = lower(&source, 0);
            accept(&source, 0, &lir, &machine);
        }
    }
}

#[test]
fn signed_unsigned_boundaries_and_u64_fade_are_numeric_constants() {
    for (ty, values) in [
        (
            Ty::I32,
            vec![i128::from(i32::MIN), -1, 0, 1, i128::from(i32::MAX)],
        ),
        (Ty::U32, vec![0, 1, 0x8000_0000, i128::from(u32::MAX)]),
        (
            Ty::I64,
            vec![i128::from(i64::MIN), -1, 0, 1, i128::from(i64::MAX)],
        ),
        (
            Ty::U64,
            vec![
                0,
                1,
                0x8000_0000_0000_0000,
                0xFADE_0000_0000_0001,
                0xFADF_0000_0000_0000,
                i128::from(u64::MAX),
            ],
        ),
    ] {
        for value in values {
            let source = module(&ty, &[], vec![constant(&ty, value, 991)], Some(991));
            let (lir, machine) = lower(&source, 0);
            accept(&source, 0, &lir, &machine);
        }
    }
}

#[test]
fn module_vector_ordinal_not_sparse_func_id_or_shared_name_selects_source() {
    let mut source = add_fixture();
    source.functions[0].id = FuncId::new(4_000_000_000);
    let mut decoy = source.functions[0].clone();
    decoy.id = FuncId::new(97);
    decoy.name = "uniquely_named_decoy".into();
    decoy.blocks[0].body[0] = binary(&Ty::I32, BinOp::Sub, 0, 1, 10);
    source.functions.insert(0, decoy);
    // The actual adapter correctly requires unique module symbol names.
    let (lir, machine) = lower(&source, 1);
    accept(&source, 1, &lir, &machine);
    // Only the negative diagnostic mutates the decoy to share the selected
    // body's name. No positive lowering/receipt is claimed for that module.
    source.functions[0].name = source.functions[1].name.clone();
    assert!(matches!(
        reject(&source, 0, &lir, &machine),
        TrustIrAffineLoweringError::TrustIrLirMismatch
    ));
    assert!(matches!(
        reject(&source, 4_000_000_000, &lir, &machine),
        TrustIrAffineLoweringError::InvalidTrustIr(_)
    ));
}

#[test]
fn wrong_in_range_ordinal_cannot_downgrade_a_mispaired_declaration_to_unsupported() {
    let mut source = add_fixture();
    let mut declaration = source.functions[0].clone();
    declaration.id = FuncId::new(12);
    declaration.name = "declaration_before_the_selected_body".into();
    declaration.blocks.clear();
    source.functions.insert(0, declaration);
    let (lir, machine) = lower(&source, 1);
    accept(&source, 1, &lir, &machine);
    assert!(matches!(
        reject(&source, 0, &lir, &machine),
        TrustIrAffineLoweringError::TrustIrLirMismatch
    ));
}

#[test]
fn same_name_bodyless_selected_source_is_invalid_not_uncredited_coverage() {
    let source = add_fixture();
    let (lir, machine) = lower(&source, 0);
    let mut declaration = source.clone();
    declaration.functions[0].blocks.clear();
    assert!(matches!(
        reject(&declaration, 0, &lir, &machine),
        TrustIrAffineLoweringError::InvalidTrustIr(_)
    ));
}

#[test]
fn name_mismatch_is_hard_even_when_the_selected_source_operation_is_unsupported() {
    let source = add_fixture();
    let (lir, machine) = lower(&source, 0);
    let mut unrelated = source.clone();
    unrelated.functions[0].name = "unrelated_multiply".into();
    body(&mut unrelated)[0] = binary(&Ty::I32, BinOp::Mul, 0, 1, 10);
    assert!(matches!(
        reject(&unrelated, 0, &lir, &machine),
        TrustIrAffineLoweringError::TrustIrLirMismatch
    ));
}

#[test]
fn alpha_renaming_sparse_ssa_ids_preserves_the_same_independent_pair() {
    let source = module(
        &Ty::U64,
        &[2, 19],
        vec![binary(&Ty::U64, BinOp::Sub, 2, 19, 100)],
        Some(100),
    );
    let (lir, machine) = lower(&source, 0);
    let renamed = module(
        &Ty::U64,
        &[u32::MAX - 3, 1_000_000_001],
        vec![binary(
            &Ty::U64,
            BinOp::Sub,
            u32::MAX - 3,
            1_000_000_001,
            u32::MAX - 1,
        )],
        Some(u32::MAX - 1),
    );
    accept(&renamed, 0, &lir, &machine);
    let (renamed_lir, renamed_machine) = lower(&renamed, 0);
    accept(&renamed, 0, &renamed_lir, &renamed_machine);
}

#[test]
fn commutation_and_reassociation_are_semantic_not_adapter_shape_equality() {
    let source = module(
        &Ty::I64,
        &[0, 1, 2],
        vec![
            binary(&Ty::I64, BinOp::Add, 0, 1, 10),
            binary(&Ty::I64, BinOp::Add, 10, 2, 11),
        ],
        Some(11),
    );
    let (lir, machine) = lower(&source, 0);
    let mut commuted = source.clone();
    body(&mut commuted)[0] = binary(&Ty::I64, BinOp::Add, 1, 0, 10);
    accept(&commuted, 0, &lir, &machine);
    let mut reassociated = source.clone();
    body(&mut reassociated)[0] = binary(&Ty::I64, BinOp::Add, 1, 2, 10);
    body(&mut reassociated)[1] = binary(&Ty::I64, BinOp::Add, 0, 10, 11);
    accept(&reassociated, 0, &lir, &machine);
}

#[test]
fn shared_deep_dag_checks_without_expanding_source_expressions() {
    let mut instructions = vec![copy(&Ty::I64, 0, 10)];
    let mut previous = 10;
    for _ in 0..4096 {
        instructions.push(binary(
            &Ty::I64,
            BinOp::Add,
            previous,
            previous,
            previous + 1,
        ));
        previous += 1;
    }
    instructions.push(binary(&Ty::I64, BinOp::Add, previous, 1, previous + 1));
    let source = module(&Ty::I64, &[0, 1], instructions, Some(previous + 1));
    let (lir, machine) = lower(&source, 0);
    accept(&source, 0, &lir, &machine);
}

#[test]
fn ordinary_wrapping_arithmetic_needs_no_annotation_and_annotations_cannot_authorize_changes() {
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        let source = module(
            &ty,
            &[0, 1],
            vec![binary(&ty, BinOp::Add, 0, 1, 10)],
            Some(10),
        );
        let (lir, machine) = lower(&source, 0);
        accept(&source, 0, &lir, &machine);
        for annotation in [
            ProofAnnotation::Wrapping,
            ProofAnnotation::NoOverflow,
            ProofAnnotation::NoWrap,
        ] {
            let mut annotated = source.clone();
            annotated.functions[0].proofs.push(annotation.clone());
            body(&mut annotated)[0].proofs.push(annotation.clone());
            accept(&annotated, 0, &lir, &machine);
            // Keep the same claim and target, but change the actual operation.
            body(&mut annotated)[0].inst = Inst::BinOp {
                op: BinOp::Sub,
                ty: ty.clone(),
                lhs: v(0),
                rhs: v(1),
            };
            assert!(matches!(
                reject(&annotated, 0, &lir, &machine),
                TrustIrAffineLoweringError::TrustIrLirMismatch
            ));
        }
    }
}

#[test]
fn changed_source_return_operand_add_sub_and_constant_do_not_reuse_a_receipt() {
    let source = module(
        &Ty::I32,
        &[0, 1],
        vec![
            constant(&Ty::I32, 7, 9),
            binary(&Ty::I32, BinOp::Sub, 0, 1, 10),
            binary(&Ty::I32, BinOp::Add, 10, 9, 11),
        ],
        Some(11),
    );
    let (lir, machine) = lower(&source, 0);
    for case in 0..4 {
        let mut changed = source.clone();
        match case {
            0 => body(&mut changed)[3] = returned(Some(0)),
            1 => body(&mut changed)[1] = binary(&Ty::I32, BinOp::Sub, 1, 0, 10),
            2 => body(&mut changed)[1] = binary(&Ty::I32, BinOp::Add, 0, 1, 10),
            3 => body(&mut changed)[0] = constant(&Ty::I32, 8, 9),
            _ => unreachable!(),
        }
        assert!(
            matches!(
                reject(&changed, 0, &lir, &machine),
                TrustIrAffineLoweringError::TrustIrLirMismatch
            ),
            "source mutation {case}"
        );
    }
}

#[test]
fn valid_source_with_unsupported_lir_is_a_hard_lowering_error_not_coverage_downgrade() {
    let source = add_fixture();
    let (mut lir, machine) = lower(&source, 0);
    lir.blocks.get_mut(&lir.entry_block).unwrap().instructions[0].opcode = Opcode::Imul;
    assert!(matches!(
        reject(&source, 0, &lir, &machine),
        TrustIrAffineLoweringError::Lowering(AffineLoweringError::UnsupportedSource(_))
    ));
}

#[test]
fn correlated_lir_and_machine_corruption_still_fails_the_independent_trust_ir_binding() {
    let source = add_fixture();
    let mut wrong = source.clone();
    body(&mut wrong)[0] = binary(&Ty::I32, BinOp::Sub, 0, 1, 10);
    let (wrong_lir, wrong_machine) = lower(&wrong, 0);
    // The wrong pair is internally consistent and has the same source name.
    accept(&wrong, 0, &wrong_lir, &wrong_machine);
    assert!(matches!(
        reject(&source, 0, &wrong_lir, &wrong_machine),
        TrustIrAffineLoweringError::TrustIrLirMismatch
    ));
}

#[test]
fn independent_machine_mutation_is_not_hidden_by_an_exact_source_lir_pair() {
    let source = add_fixture();
    let (lir, mut machine) = lower(&source, 0);
    let instruction = machine
        .block(machine.entry)
        .insts
        .iter()
        .copied()
        .find(|&id| machine.inst(id).opcode == AArch64Opcode::AddRR)
        .expect("two-register add fixture");
    machine.inst_mut(instruction).opcode = AArch64Opcode::SubRR;
    assert!(matches!(
        reject(&source, 0, &lir, &machine),
        TrustIrAffineLoweringError::Lowering(AffineLoweringError::ReturnMismatch)
    ));
}

#[test]
fn unused_parameters_remain_part_of_the_exact_signature_binding() {
    let source = module(&Ty::I32, &[0, 1], vec![], Some(0));
    let (lir, machine) = lower(&source, 0);
    let mut missing = source.clone();
    missing.func_types[0].params.pop();
    missing.functions[0].blocks[0].params.pop();
    assert!(matches!(
        reject(&missing, 0, &lir, &machine),
        TrustIrAffineLoweringError::TrustIrLirMismatch
    ));
    let mut extra = source.clone();
    extra.func_types[0].params.push(Ty::I32);
    extra.functions[0].blocks[0].params.push((v(500), Ty::I32));
    assert!(matches!(
        reject(&extra, 0, &lir, &machine),
        TrustIrAffineLoweringError::TrustIrLirMismatch
    ));
}

/// The LIR may give an unread parameter another width than the body's (the
/// source-bound frame owner admits that shape), but both TrustIR binders hold
/// it to TrustIR's own signature, whose parameters share one width.
#[test]
fn an_unread_lir_parameter_keeps_the_trust_ir_width_in_both_binders() {
    use trust_cg_verify::aarch64_affine_lowering::{
        AffineByteError, check_aarch64_trust_ir_affine_bytes,
    };

    let source = module(&Ty::I64, &[0, 1], vec![], Some(1));
    let (lir, machine) = lower(&source, 0);
    accept(&source, 0, &lir, &machine);
    // `mov x0, x1; ret`
    let bytes: Vec<u8> = [0xaa01_03e0_u32, 0xd65f_03c0]
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect();
    check_aarch64_trust_ir_affine_bytes(&source, 0, &lir, &bytes).unwrap();
    let mut narrowed = lir.clone();
    narrowed.signature.params[0] = trust_cg_lower::Type::I32;
    narrowed
        .blocks
        .get_mut(&narrowed.entry_block)
        .unwrap()
        .params[0]
        .1 = trust_cg_lower::Type::I32;
    narrowed.value_types.insert(
        trust_cg_lower::instructions::Value(0),
        trust_cg_lower::Type::I32,
    );
    assert!(matches!(
        reject(&source, 0, &narrowed, &machine),
        TrustIrAffineLoweringError::TrustIrLirMismatch
    ));
    assert!(matches!(
        check_aarch64_trust_ir_affine_bytes(&source, 0, &narrowed, &bytes),
        Err(AffineByteError::Source(
            TrustIrAffineLoweringError::TrustIrLirMismatch
        ))
    ));
}

#[test]
fn parameter_order_is_independent_of_sparse_id_order_or_producer_mapping() {
    let source = module(
        &Ty::I32,
        &[91, 3],
        vec![binary(&Ty::I32, BinOp::Sub, 91, 3, 501)],
        Some(501),
    );
    let (lir, machine) = lower(&source, 0);
    let mut reversed = source.clone();
    reversed.functions[0].blocks[0].params.swap(0, 1);
    assert!(matches!(
        reject(&reversed, 0, &lir, &machine),
        TrustIrAffineLoweringError::TrustIrLirMismatch
    ));
}

#[test]
fn invalid_function_and_signature_indices_refuse_without_indexing_or_panicking() {
    let source = add_fixture();
    let (lir, machine) = lower(&source, 0);
    assert!(matches!(
        reject(&source, usize::MAX, &lir, &machine),
        TrustIrAffineLoweringError::InvalidTrustIr(_)
    ));
    let mut invalid = source.clone();
    invalid.functions[0].ty = FuncTyId::new(u32::MAX);
    assert!(matches!(
        reject(&invalid, 0, &lir, &machine),
        TrustIrAffineLoweringError::InvalidTrustIr(_)
    ));
    invalid = source.clone();
    invalid.func_types.clear();
    assert!(matches!(
        reject(&invalid, 0, &lir, &machine),
        TrustIrAffineLoweringError::InvalidTrustIr(_)
    ));
}

#[test]
fn a_missing_selected_function_is_invalid_even_with_a_valid_frozen_pair() {
    let source = add_fixture();
    let (lir, machine) = lower(&source, 0);
    let mut missing = source.clone();
    missing.functions.clear();
    assert!(matches!(
        reject(&missing, 0, &lir, &machine),
        TrustIrAffineLoweringError::InvalidTrustIr(_)
    ));
}

#[test]
fn invalid_actual_entry_block_id_is_not_a_coverage_downgrade() {
    let source = add_fixture();
    let (lir, machine) = lower(&source, 0);
    let mut invalid = source.clone();
    invalid.functions[0].entry = BlockId::new(u32::MAX);
    assert!(matches!(
        reject(&invalid, 0, &lir, &machine),
        TrustIrAffineLoweringError::InvalidTrustIr(_)
    ));
}

#[test]
fn empty_actual_entry_body_is_invalid_not_a_void_or_uncredited_function() {
    let source = add_fixture();
    let (lir, machine) = lower(&source, 0);
    let mut empty = source.clone();
    body(&mut empty).clear();
    assert!(matches!(
        reject(&empty, 0, &lir, &machine),
        TrustIrAffineLoweringError::InvalidTrustIr(_)
    ));
}

#[test]
fn changed_valid_signature_width_cannot_reuse_equal_zero_affine_terms() {
    for params in [vec![], vec![700]] {
        let source = module(
            &Ty::I32,
            &params,
            vec![constant(&Ty::I32, 0, 900)],
            Some(900),
        );
        let (lir, machine) = lower(&source, 0);
        accept(&source, 0, &lir, &machine);
        let wider = module(
            &Ty::I64,
            &params,
            vec![constant(&Ty::I64, 0, 900)],
            Some(900),
        );
        // Both independent sources are valid and return the same affine zero.
        // The frozen pair still belongs to the narrower ABI, including any
        // unused parameter, so coefficient equality alone must not authorize it.
        let (wider_lir, wider_machine) = lower(&wider, 0);
        accept(&wider, 0, &wider_lir, &wider_machine);
        assert!(matches!(
            reject(&wider, 0, &lir, &machine),
            TrustIrAffineLoweringError::TrustIrLirMismatch
        ));
    }
}

#[test]
fn ninth_unused_parameter_is_outside_the_register_only_source_contract() {
    let params: Vec<u32> = (0..8).map(|index| 700 + index * 19).collect();
    let source = module(
        &Ty::U64,
        &params,
        vec![constant(&Ty::U64, 0, 1000)],
        Some(1000),
    );
    let (lir, machine) = lower(&source, 0);
    accept(&source, 0, &lir, &machine);
    let mut ninth = source.clone();
    ninth.func_types[0].params.push(Ty::U64);
    ninth.functions[0].blocks[0].params.push((v(900), Ty::U64));
    assert!(matches!(
        reject(&ninth, 0, &lir, &machine),
        TrustIrAffineLoweringError::UnsupportedTrustIr(_)
    ));
}

#[test]
fn even_empty_call_proof_context_is_invalid_on_every_admitted_noncall_kind() {
    let source = module(
        &Ty::I32,
        &[0, 1],
        vec![
            constant(&Ty::I32, 0, 9),
            binary(&Ty::I32, BinOp::Add, 0, 1, 10),
            copy(&Ty::I32, 10, 11),
        ],
        Some(11),
    );
    let (lir, machine) = lower(&source, 0);
    for index in 0..source.functions[0].blocks[0].body.len() {
        let mut invalid = source.clone();
        body(&mut invalid)[index].proof_context = Some(ProofContext {
            assumes: vec![],
            establishes: vec![],
        });
        assert!(
            matches!(
                reject(&invalid, 0, &lir, &machine),
                TrustIrAffineLoweringError::InvalidTrustIr(_)
            ),
            "non-call proof-context mutation at instruction {index}"
        );
    }
}

#[test]
fn zero_like_empty_or_noncanonical_carriers_do_not_stand_in_for_integer_zero() {
    let source = module(&Ty::U64, &[], vec![constant(&Ty::U64, 0, 100)], Some(100));
    let (lir, machine) = lower(&source, 0);
    accept(&source, 0, &lir, &machine);
    for carrier in [
        Constant::U128(0),
        Constant::Float(0.0),
        Constant::Bool(false),
        Constant::Aggregate(vec![]),
        Constant::Bytes {
            data: vec![],
            utf8: false,
        },
        Constant::PhantomData,
    ] {
        let mut invalid = source.clone();
        body(&mut invalid)[0].inst = Inst::Const {
            ty: Ty::U64,
            value: carrier,
        };
        assert!(matches!(
            reject(&invalid, 0, &lir, &machine),
            TrustIrAffineLoweringError::InvalidTrustIr(_)
        ));
    }
}

#[test]
fn duplicate_undefined_forward_or_wrong_arity_ssa_is_invalid_even_with_good_targets() {
    let source = module(
        &Ty::I32,
        &[0, 1],
        vec![
            binary(&Ty::I32, BinOp::Add, 0, 1, 10),
            copy(&Ty::I32, 10, 11),
        ],
        Some(11),
    );
    let (lir, machine) = lower(&source, 0);
    for case in 0..7 {
        let mut invalid = source.clone();
        match case {
            0 => invalid.functions[0].blocks[0].params[1].0 = v(0),
            1 => body(&mut invalid)[0].results = vec![v(0)],
            2 => body(&mut invalid)[0] = binary(&Ty::I32, BinOp::Add, 0, 999, 10),
            3 => body(&mut invalid)[0] = binary(&Ty::I32, BinOp::Add, 0, 11, 10),
            4 => body(&mut invalid)[0].results.clear(),
            5 => body(&mut invalid)[0].results.push(v(99)),
            6 => body(&mut invalid)[1].results = vec![v(10)],
            _ => unreachable!(),
        }
        assert!(
            matches!(
                reject(&invalid, 0, &lir, &machine),
                TrustIrAffineLoweringError::InvalidTrustIr(_)
            ),
            "SSA mutation {case}"
        );
    }
}

#[test]
fn entry_signature_and_operand_declared_types_are_independently_checked() {
    let source = add_fixture();
    let (lir, machine) = lower(&source, 0);
    for case in 0..4 {
        let mut invalid = source.clone();
        match case {
            0 => {
                invalid.functions[0].blocks[0].params.pop();
            }
            1 => invalid.functions[0].blocks[0].params[1].1 = Ty::I64,
            2 => body(&mut invalid)[0] = binary(&Ty::I64, BinOp::Add, 0, 1, 10),
            3 => body(&mut invalid)[0] = binary(&Ty::U32, BinOp::Add, 0, 1, 10),
            _ => unreachable!(),
        }
        assert!(
            matches!(
                reject(&invalid, 0, &lir, &machine),
                TrustIrAffineLoweringError::InvalidTrustIr(_)
            ),
            "type mutation {case}"
        );
    }
}

#[test]
fn absent_nonfinal_duplicate_ill_formed_or_undefined_returns_are_invalid() {
    let source = add_fixture();
    let (lir, machine) = lower(&source, 0);
    for case in 0..7 {
        let mut invalid = source.clone();
        match case {
            0 => {
                body(&mut invalid).pop();
            }
            1 => body(&mut invalid).push(constant(&Ty::I32, 1, 100)),
            2 => body(&mut invalid).push(returned(Some(10))),
            3 => body(&mut invalid)[1] = returned(None),
            4 => {
                body(&mut invalid)[1] = InstrNode::new(Inst::Return {
                    values: vec![v(0), v(1)],
                })
            }
            5 => body(&mut invalid)[1].results.push(v(101)),
            6 => body(&mut invalid)[1] = returned(Some(999)),
            _ => unreachable!(),
        }
        assert!(
            matches!(
                reject(&invalid, 0, &lir, &machine),
                TrustIrAffineLoweringError::InvalidTrustIr(_)
            ),
            "return mutation {case}"
        );
    }
}

#[test]
fn literal_ranges_are_checked_before_accepting_equal_truncated_bits() {
    for (ty, valid, invalid) in [
        (Ty::I32, i128::from(i32::MIN), i128::from(i32::MAX) + 1),
        (Ty::I32, i128::from(i32::MAX), i128::from(i32::MIN) - 1),
        (Ty::U32, i128::from(u32::MAX), -1),
        (Ty::U32, 0, i128::from(u32::MAX) + 1),
        (Ty::I64, i128::from(i64::MIN), i128::from(i64::MAX) + 1),
        (Ty::I64, i128::from(i64::MAX), i128::from(i64::MIN) - 1),
        (Ty::U64, i128::from(u64::MAX), -1),
        (Ty::U64, 0, i128::from(u64::MAX) + 1),
    ] {
        let source = module(&ty, &[], vec![constant(&ty, valid, 100)], Some(100));
        let (lir, machine) = lower(&source, 0);
        accept(&source, 0, &lir, &machine);
        let mut changed = source.clone();
        body(&mut changed)[0] = constant(&ty, invalid, 100);
        assert!(
            matches!(
                reject(&changed, 0, &lir, &machine),
                TrustIrAffineLoweringError::InvalidTrustIr(_)
            ),
            "{ty:?} literal {invalid}"
        );
    }
}

#[test]
fn malformed_constants_and_copies_cannot_hide_in_dead_code() {
    let source = add_fixture();
    let (lir, machine) = lower(&source, 0);
    for node in [
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        }),
        constant(&Ty::I32, 0, 100).with_result(v(101)),
        copy(&Ty::I32, 999, 100),
        copy(&Ty::I64, 0, 100),
    ] {
        let mut invalid = source.clone();
        body(&mut invalid).insert(1, node);
        assert!(matches!(
            reject(&invalid, 0, &lir, &machine),
            TrustIrAffineLoweringError::InvalidTrustIr(_)
        ));
    }
}

#[test]
fn dead_calls_and_explicit_overflow_remain_unsupported_despite_claims() {
    let source = add_fixture();
    let (lir, machine) = lower(&source, 0);
    let dead_call = InstrNode::new(Inst::Call {
        callee: source.functions[0].id,
        args: vec![v(0), v(1)],
    })
    .with_result(v(100))
    .with_proof(ProofAnnotation::Pure);
    let overflow = InstrNode::new(Inst::Overflow {
        op: OverflowOp::AddOverflow,
        ty: Ty::I32,
        lhs: v(0),
        rhs: v(1),
    })
    .with_results([v(100), v(101)])
    .with_proof(ProofAnnotation::NoOverflow);
    let multiplication = binary(&Ty::I32, BinOp::Mul, 0, 1, 100);
    for node in [dead_call, overflow, multiplication] {
        let mut unsupported = source.clone();
        body(&mut unsupported).insert(1, node);
        assert!(matches!(
            reject(&unsupported, 0, &lir, &machine),
            TrustIrAffineLoweringError::UnsupportedTrustIr(_)
        ));
    }
}

#[test]
fn source_validity_precedes_an_unsupported_lowering_coverage_decision() {
    let mut source = add_fixture();
    let (mut lir, machine) = lower(&source, 0);
    body(&mut source)[0] = binary(&Ty::I32, BinOp::Add, 0, 999, 10);
    lir.blocks.get_mut(&lir.entry_block).unwrap().instructions[0].opcode = Opcode::Imul;
    assert!(matches!(
        reject(&source, 0, &lir, &machine),
        TrustIrAffineLoweringError::InvalidTrustIr(_)
    ));
}

#[test]
fn unsupported_abi_and_domains_never_gain_canonical_coverage() {
    let source = add_fixture();
    let (lir, machine) = lower(&source, 0);
    for case in 0..6 {
        let mut unsupported = source.clone();
        match case {
            0 => unsupported.func_types[0].is_vararg = true,
            1 => unsupported.functions[0].calling_conv = CallingConv::Fast,
            2 => {
                unsupported.functions[0].attrs.params = vec![ParamAttrs {
                    byval: true,
                    ..Default::default()
                }]
            }
            3 => {
                unsupported.functions[0].attrs.params = vec![ParamAttrs {
                    sret: true,
                    ..Default::default()
                }]
            }
            4 => {
                unsupported.func_types[0].params[1] = Ty::I64;
                unsupported.functions[0].blocks[0].params[1].1 = Ty::I64;
                // Both types are valid but outside the homogeneous domain;
                // keep the second parameter unused so no ill-typed op is needed.
                body(&mut unsupported)[0] = copy(&Ty::I32, 0, 10);
            }
            5 => {
                unsupported.func_types[0].params[1] = Ty::U32;
                unsupported.functions[0].blocks[0].params[1].1 = Ty::U32;
                body(&mut unsupported)[0] = copy(&Ty::I32, 0, 10);
            }
            _ => unreachable!(),
        }
        assert!(
            matches!(
                reject(&unsupported, 0, &lir, &machine),
                TrustIrAffineLoweringError::UnsupportedTrustIr(_)
            ),
            "unsupported ABI/domain {case}"
        );
    }
}

#[test]
fn unit_and_never_return_erasure_are_not_claimed_as_scalar_void_refinement() {
    let source = module(&Ty::I64, &[], vec![], None);
    let (lir, machine) = lower(&source, 0);
    for ty in [Ty::Unit, Ty::Never] {
        let mut erased = source.clone();
        erased.func_types[0].returns = vec![ty];
        assert!(matches!(
            reject(&erased, 0, &lir, &machine),
            TrustIrAffineLoweringError::UnsupportedTrustIr(_)
        ));
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
