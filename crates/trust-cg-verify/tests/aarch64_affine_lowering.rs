// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Exact source-to-raw-machine checks, using the real AArch64 selector.
//!
//! These are pre-optimization binding checks, not claims that the downstream
//! optimizer, encoder, Trust toolchain, or machine proof policy has been proved.

use trust_cg_ir::aarch64_regs::{LR, W0, X0, X1};
use trust_cg_ir::regs::{SpecialReg, VReg};
use trust_cg_ir::{
    AArch64Opcode, BlockId, InstFlags, InstId, LoweringProvenance, MachFunction, MachInst,
    MachOperand, RegClass, SyntheticReason, TrustIrInstId,
};
use trust_cg_lower::Type;
use trust_cg_lower::abi::AArch64AbiVariant;
use trust_cg_lower::function::{AbiSretParam, BasicBlock, Function, Signature, StackSlotInfo};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::isel::InstructionSelector;
use trust_cg_verify::aarch64_affine_lowering::{
    AffineLoweringError, check_aarch64_affine_lowering,
};
use trust_cg_verify::source_bound_frame::source_admits_frame_owner;

fn operation(opcode: Opcode, args: &[u32], result: u32) -> Instruction {
    Instruction {
        opcode,
        args: args.iter().copied().map(Value).collect(),
        results: vec![Value(result)],
    }
}

fn iconst(ty: Type, imm: i64, result: u32) -> Instruction {
    operation(Opcode::Iconst { ty, imm }, &[], result)
}

fn source(
    ty: Type,
    parameter_count: usize,
    mut instructions: Vec<Instruction>,
    returned: Option<u32>,
) -> Function {
    let signature = Signature {
        params: vec![ty.clone(); parameter_count],
        returns: returned.map(|_| ty.clone()).into_iter().collect(),
    };
    let mut function = Function::new("affine_fixture", signature);
    let params: Vec<_> = (0..parameter_count)
        .map(|index| (Value(index as u32), ty.clone()))
        .collect();
    function.value_types.extend(params.iter().cloned());
    for instruction in &instructions {
        for &result in &instruction.results {
            function.value_types.insert(result, ty.clone());
        }
    }
    instructions.push(Instruction {
        opcode: Opcode::Return,
        args: returned.map(Value).into_iter().collect(),
        results: vec![],
    });
    function.trust_ir_origins.insert(
        Block(0),
        (0..instructions.len())
            .map(|index| Some(TrustIrInstId(40 + index as u32)))
            .collect(),
    );
    function.blocks.insert(
        Block(0),
        BasicBlock {
            params,
            source_locs: vec![None; instructions.len()],
            instructions,
        },
    );
    function.block_order.push(Block(0));
    function
}

/// Mirror the production raw-selection setup, including the seeders that make
/// immediate and constant-left folding differ from isolated instruction tests.
fn select(function: &Function) -> MachFunction {
    let mut selector = InstructionSelector::new(function.name.clone(), function.signature.clone());
    selector.set_abi_variant(AArch64AbiVariant::Darwin);
    selector.set_stack_slots(function.stack_slots.clone());
    selector.seed_value_types(&function.value_types);
    selector.seed_iconst_origins(
        function
            .blocks
            .values()
            .map(|block| block.instructions.as_slice()),
    );
    selector.seed_function_value_use_counts(function);
    selector
        .lower_formal_arguments(&function.signature, function.entry_block)
        .expect("fixture formal arguments must lower");
    for id in function.layout_order() {
        let block = &function.blocks[&id];
        selector
            .select_block_with_provenance(
                id,
                &block.instructions,
                &block.source_locs,
                &function.trust_ir_origins[&id],
            )
            .expect("fixture body must lower");
    }
    selector
        .finalize_with_eh_info(&function.eh_info)
        .expect("fixture EH metadata must match")
        .to_ir_func()
}

fn binary(ty: Type, opcode: Opcode) -> (Function, MachFunction) {
    // Deliberately sparse result ids: only formal ids have an ABI convention.
    let function = source(ty, 2, vec![operation(opcode, &[0, 1], 100)], Some(100));
    let machine = select(&function);
    (function, machine)
}

fn instruction(machine: &MachFunction, opcode: AArch64Opcode) -> InstId {
    machine
        .block(machine.entry)
        .insts
        .iter()
        .copied()
        .find(|&id| machine.inst(id).opcode == opcode)
        .expect("real selector must emit the expected fixture shape")
}

fn rejected(source: &Function, machine: &MachFunction) -> AffineLoweringError {
    match check_aarch64_affine_lowering(source, machine) {
        Err(error) => error,
        Ok(_) => panic!("corrupt or unsupported lowering acquired a checked receipt"),
    }
}

fn insert_before_return(machine: &mut MachFunction, instruction: MachInst) {
    let id = machine.push_inst(instruction);
    let block = machine.block_mut(machine.entry);
    block.insts.insert(block.insts.len() - 1, id);
}

#[test]
fn seeded_shared_affine_programs_match_real_isel_and_reject_source_plus_one() {
    const SEED: u64 = 0x7463_675f_6166_6631;
    const CASES: usize = 256;

    fn next_random(state: &mut u64) -> u64 {
        *state ^= *state >> 12;
        *state ^= *state << 25;
        *state ^= *state >> 27;
        state.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn constant(state: &mut u64) -> i64 {
        // Mix arbitrary bit patterns with boundaries that select immediate,
        // shifted-immediate, MOVN and multi-halfword MOVK materializations.
        const EDGES: [i64; 14] = [
            0,
            1,
            -1,
            4095,
            4096,
            0xfff000,
            i64::MIN,
            i64::MAX,
            i32::MIN as i64,
            i32::MAX as i64,
            0xffff_ffff,
            0x1_0000_0000,
            0x1234_5678_9abc_def0,
            0xffff_1234_ffff_ffff_u64 as i64,
        ];
        let random = next_random(state);
        if random & 1 == 0 {
            EDGES[(random >> 1) as usize % EDGES.len()]
        } else {
            next_random(state) as i64
        }
    }

    let mut random = SEED;
    let mut checked_widths = [0; 2];
    let mut parameter_counts_seen = 0_u16;
    for case in 0..CASES {
        let width = case % 2;
        let ty = if width == 0 { Type::I32 } else { Type::I64 };
        let parameter_count = case % 9;
        parameter_counts_seen |= 1 << parameter_count;
        let mut available: Vec<u32> = (0..parameter_count as u32).collect();
        let mut next_value = 32_u32;
        let mut body = vec![iconst(ty.clone(), constant(&mut random), next_value)];
        let first_constant = next_value;
        available.push(next_value);
        next_value += 1;

        // Every case contains all four source operations and a shared value,
        // even when it has no parameters or the later random choices repeat.
        let copied = available[next_random(&mut random) as usize % available.len()];
        body.push(operation(Opcode::Copy, &[copied], next_value));
        let shared = next_value;
        available.push(next_value);
        next_value += 1;
        body.push(operation(
            Opcode::Iadd,
            &[shared, first_constant],
            next_value,
        ));
        available.push(next_value);
        next_value += 1;
        body.push(operation(
            Opcode::Isub,
            &[next_value - 1, shared],
            next_value,
        ));
        available.push(next_value);
        next_value += 1;

        let extra_operations = 8 + next_random(&mut random) as usize % 33;
        for _ in 0..extra_operations {
            let lhs = available[next_random(&mut random) as usize % available.len()];
            let rhs = available[next_random(&mut random) as usize % available.len()];
            let instruction = match next_random(&mut random) % 4 {
                0 => iconst(ty.clone(), constant(&mut random), next_value),
                1 => operation(Opcode::Copy, &[lhs], next_value),
                2 => operation(Opcode::Iadd, &[lhs, rhs], next_value),
                _ => operation(Opcode::Isub, &[lhs, rhs], next_value),
            };
            body.push(instruction);
            available.push(next_value);
            next_value += 1;
        }
        // Join the newest result with a previous shared value so the returned
        // expression exercises the DAG rather than just a fresh literal.
        let rhs = available[next_random(&mut random) as usize % available.len()];
        body.push(operation(Opcode::Iadd, &[next_value - 1, rhs], next_value));
        let returned = next_value;
        next_value += 1;

        let function = source(ty.clone(), parameter_count, body.clone(), Some(returned));
        // The real selector runs once, with all its normal seeders/transforms.
        // This machine is immutable and reused unchanged for both checks.
        let machine = select(&function);
        let checked = check_aarch64_affine_lowering(&function, &machine).unwrap_or_else(|error| {
            panic!("seed={SEED:#x} case={case} type={ty:?}: real ISel rejected: {error}")
        });
        assert_eq!(checked.statistics().source_instructions, body.len() + 1);
        assert_eq!(checked.statistics().parameter_count, parameter_count);
        checked_widths[width] += 1;

        // Add one to the source's final result before Return, retaining every
        // prior instruction and the original machine. +1 is inequivalent for
        // every input modulo both 2^32 and 2^64, including overflow boundaries.
        body.push(iconst(ty.clone(), 1, next_value));
        body.push(operation(
            Opcode::Iadd,
            &[returned, next_value],
            next_value + 1,
        ));
        let changed = source(ty.clone(), parameter_count, body, Some(next_value + 1));
        assert!(
            matches!(
                check_aarch64_affine_lowering(&changed, &machine),
                Err(AffineLoweringError::ReturnMismatch)
            ),
            "seed={SEED:#x} case={case} type={ty:?}: source +1 must refute the unchanged machine"
        );
    }
    assert_eq!(checked_widths, [128, 128]);
    assert_eq!(parameter_counts_seen, (1 << 9) - 1);
}

#[test]
fn real_identity_receipt_borrows_exact_inputs_and_counts_abi_glue() {
    for ty in [Type::I32, Type::I64] {
        let function = source(ty, 1, vec![], Some(0));
        let machine = select(&function);
        let checked = check_aarch64_affine_lowering(&function, &machine).unwrap();
        assert!(std::ptr::eq(checked.source(), &function));
        assert!(std::ptr::eq(checked.machine(), &machine));
        let statistics = checked.statistics();
        assert_eq!(statistics.parameter_count, 1);
        assert_eq!(statistics.source_instructions, 1);
        assert_eq!(statistics.machine_instructions, machine.insts.len());
        assert_eq!(machine.insts.len(), 3);
        let ids = &machine.block(machine.entry).insts;
        assert_eq!(
            machine.inst_lowering_provenance(ids[0]),
            LoweringProvenance::Synthetic {
                reason: SyntheticReason::FormalArguments
            }
        );
        for &id in &ids[1..] {
            assert!(matches!(
                machine.inst_lowering_provenance(id),
                LoweringProvenance::SourceInst {
                    trust_ir_inst: Some(TrustIrInstId(40)),
                    ..
                }
            ));
        }
        assert_eq!(machine.inst(ids[2]).operands, vec![MachOperand::PReg(LR)]);
    }
}

#[test]
fn immediate_arithmetic_register_31_is_sp_not_a_zero_operand() {
    for (ty, zero) in [(Type::I32, SpecialReg::WZR), (Type::I64, SpecialReg::XZR)] {
        for (opcode, result) in [
            (AArch64Opcode::AddRI, 1),
            (AArch64Opcode::AddRIShift12, 4096),
            (AArch64Opcode::SubRI, -1),
        ] {
            let function = source(ty.clone(), 0, vec![iconst(ty.clone(), result, 0)], Some(0));
            let mut machine = select(&function);
            let first = machine.blocks[0].insts[0];
            let dst = machine.inst(first).operands[0].clone();
            machine.insts[first.0 as usize] = MachInst::new(
                opcode,
                vec![dst, MachOperand::Special(zero), MachOperand::Imm(1)],
            );
            assert!(matches!(
                rejected(&function, &machine),
                AffineLoweringError::InvalidMachine(_)
            ));
        }
    }
}

#[test]
fn deep_shared_arithmetic_is_normalized_without_expression_expansion() {
    // Repeatedly reuse both previous results. Expanding an expression tree
    // would grow exponentially; fixed modular coefficients remain constant
    // size per value and all traversals/drop operations remain iterative.
    let depth = 4096_u32;
    for ty in [Type::I32, Type::I64] {
        let mut instructions = Vec::new();
        for i in 0..depth {
            let lhs = if i == 0 { 0 } else { i + 1 };
            instructions.push(operation(Opcode::Iadd, &[lhs, 1], i + 2));
            // Both arguments alias the same value, so each source node is
            // shared inside the next expression, not copied into a tree.
            if i > 0 {
                instructions.last_mut().unwrap().args[1] = Value(lhs);
            }
        }
        let function = source(ty, 2, instructions, Some(depth + 1));
        let machine = select(&function);
        let checked = check_aarch64_affine_lowering(&function, &machine).unwrap();
        assert_eq!(checked.statistics().source_instructions, depth as usize + 1);
        assert_eq!(
            checked.statistics().machine_instructions,
            depth as usize + 4
        );
    }
}

#[test]
fn real_i32_argument_and_return_register_spellings_are_not_conflated() {
    let (function, machine) = binary(Type::I32, Opcode::Iadd);
    check_aarch64_affine_lowering(&function, &machine).unwrap();
    let ids = &machine.block(machine.entry).insts;
    assert_eq!(machine.inst(ids[0]).operands[1], MachOperand::PReg(X0));
    assert_eq!(machine.inst(ids[1]).operands[1], MachOperand::PReg(X1));
    assert_eq!(machine.inst(ids[0]).implicit_uses, &[X1]);
    let returned = machine.inst(ids[ids.len() - 2]);
    assert_eq!(returned.operands[0], MachOperand::PReg(W0));
    assert_eq!(machine.inst(*ids.last().unwrap()).implicit_uses, &[W0]);
}

#[test]
fn real_copy_add_subtract_and_repeated_coefficients_are_accepted() {
    for ty in [Type::I32, Type::I64] {
        let function = source(
            ty,
            2,
            vec![
                operation(Opcode::Copy, &[1], 50),
                operation(Opcode::Iadd, &[0, 0], 100),
                operation(Opcode::Iadd, &[100, 50], 200),
                operation(Opcode::Isub, &[200, 0], 300),
            ],
            Some(300),
        );
        check_aarch64_affine_lowering(&function, &select(&function)).unwrap();
    }
}

#[test]
fn all_eight_register_parameters_are_bound() {
    for ty in [Type::I32, Type::I64] {
        let mut body = Vec::new();
        let mut previous = 0;
        for input in 1..8 {
            let result = 100 + input;
            body.push(operation(Opcode::Isub, &[previous, input], result));
            previous = result;
        }
        let function = source(ty, 8, body, Some(previous));
        let machine = select(&function);
        let checked = check_aarch64_affine_lowering(&function, &machine).unwrap();
        assert_eq!(checked.statistics().parameter_count, 8);
    }
}

#[test]
fn zero_argument_constants_cover_movz_movn_and_destructive_movk() {
    for ty in [Type::I32, Type::I64] {
        for constant in [0, 42, -1, -65_536, 0x0001_0002, 0x0001_0002_0003_0004] {
            let function = source(
                ty.clone(),
                0,
                vec![iconst(ty.clone(), constant, 100)],
                Some(100),
            );
            check_aarch64_affine_lowering(&function, &select(&function)).unwrap();
        }
    }
}

#[test]
fn movn_seed_with_high_halfword_repairs_is_accepted() {
    for (ty, constant) in [(Type::I32, 0x1234_ffff), (Type::I64, -0x1_0001_0001)] {
        let function = source(ty.clone(), 0, vec![iconst(ty, constant, 100)], Some(100));
        let machine = select(&function);
        instruction(&machine, AArch64Opcode::Movn);
        instruction(&machine, AArch64Opcode::Movk);
        check_aarch64_affine_lowering(&function, &machine).unwrap();
    }
}

#[test]
fn immediate_folds_include_constant_left_negative_add_and_shifted_add() {
    for ty in [Type::I32, Type::I64] {
        for (constant, opcode, constant_left, expected) in [
            (42, Opcode::Iadd, false, AArch64Opcode::AddRI),
            (42, Opcode::Iadd, true, AArch64Opcode::AddRI),
            (-42, Opcode::Iadd, false, AArch64Opcode::SubRI),
            (4096, Opcode::Iadd, false, AArch64Opcode::AddRIShift12),
            (42, Opcode::Isub, false, AArch64Opcode::SubRI),
        ] {
            let args = if constant_left { [100, 0] } else { [0, 100] };
            let function = source(
                ty.clone(),
                1,
                vec![
                    iconst(ty.clone(), constant, 100),
                    operation(opcode, &args, 200),
                ],
                Some(200),
            );
            let machine = select(&function);
            instruction(&machine, expected);
            check_aarch64_affine_lowering(&function, &machine).unwrap();
        }
    }
}

#[test]
fn wrapping_constant_arithmetic_is_compared_modulo_the_declared_width() {
    for (ty, maximum) in [(Type::I32, i32::MAX as i64), (Type::I64, i64::MAX)] {
        let function = source(
            ty.clone(),
            0,
            vec![
                iconst(ty.clone(), maximum, 100),
                iconst(ty, 1, 200),
                operation(Opcode::Iadd, &[100, 200], 300),
            ],
            Some(300),
        );
        check_aarch64_affine_lowering(&function, &select(&function)).unwrap();
    }
}

#[test]
fn no_result_function_still_checks_real_return_glue() {
    for parameter_count in [0, 1] {
        let function = source(Type::I64, parameter_count, vec![], None);
        let machine = select(&function);
        check_aarch64_affine_lowering(&function, &machine).unwrap();
        let ret = instruction(&machine, AArch64Opcode::Ret);
        assert!(machine.inst(ret).implicit_uses.is_empty());
    }
}

#[test]
fn commutative_machine_reordering_does_not_require_selector_witness() {
    let (function, mut machine) = binary(Type::I64, Opcode::Iadd);
    let add = instruction(&machine, AArch64Opcode::AddRR);
    machine.inst_mut(add).operands.swap(1, 2);
    check_aarch64_affine_lowering(&function, &machine).unwrap();
}

#[test]
fn machine_move_spelling_can_change_without_changing_semantics() {
    let function = source(Type::I64, 1, vec![], Some(0));
    let mut machine = select(&function);
    let ids = &machine.block(machine.entry).insts;
    let returned = ids[ids.len() - 2];
    machine.inst_mut(returned).opcode = AArch64Opcode::MovR;
    machine.inst_mut(returned).flags = AArch64Opcode::MovR.default_flags();
    check_aarch64_affine_lowering(&function, &machine).unwrap();
}

#[test]
fn missing_or_forged_provenance_neither_supplies_nor_blocks_exact_binding() {
    let (function, mut machine) = binary(Type::I64, Opcode::Iadd);
    let ids = machine.block(machine.entry).insts.clone();
    for &id in &ids {
        machine.set_inst_lowering_provenance(id, LoweringProvenance::UNATTRIBUTED);
    }
    check_aarch64_affine_lowering(&function, &machine).unwrap();
    for id in ids {
        machine.set_inst_lowering_provenance(
            id,
            LoweringProvenance::Synthetic {
                reason: SyntheticReason::FormalArguments,
            },
        );
    }
    let add = instruction(&machine, AArch64Opcode::AddRR);
    machine.inst_mut(add).opcode = AArch64Opcode::SubRR;
    assert!(matches!(
        rejected(&function, &machine),
        AffineLoweringError::ReturnMismatch
    ));
}

#[test]
fn changed_machine_opcode_is_rejected_with_original_provenance_intact() {
    let (function, mut machine) = binary(Type::I64, Opcode::Iadd);
    let add = instruction(&machine, AArch64Opcode::AddRR);
    let provenance = machine.inst_lowering_provenance(add);
    machine.inst_mut(add).opcode = AArch64Opcode::SubRR;
    assert_eq!(machine.inst_lowering_provenance(add), provenance);
    assert!(matches!(
        rejected(&function, &machine),
        AffineLoweringError::ReturnMismatch
    ));
}

#[test]
fn swapped_subtraction_operands_are_rejected() {
    let (function, mut machine) = binary(Type::I64, Opcode::Isub);
    let sub = instruction(&machine, AArch64Opcode::SubRR);
    machine.inst_mut(sub).operands.swap(1, 2);
    assert!(matches!(
        rejected(&function, &machine),
        AffineLoweringError::ReturnMismatch
    ));
}

#[test]
fn repeated_wrong_operand_is_not_authenticated_by_opcode_or_arity() {
    let (function, mut machine) = binary(Type::I64, Opcode::Iadd);
    let add = instruction(&machine, AArch64Opcode::AddRR);
    let wrong = machine.inst(add).operands[1].clone();
    machine.inst_mut(add).operands[2] = wrong;
    assert!(matches!(
        rejected(&function, &machine),
        AffineLoweringError::ReturnMismatch
    ));
}

#[test]
fn wrong_formal_argument_copy_is_rejected() {
    let (function, mut machine) = binary(Type::I64, Opcode::Isub);
    let first = machine.block(machine.entry).insts[0];
    machine.inst_mut(first).operands[1] = MachOperand::PReg(X1);
    rejected(&function, &machine);
}

#[test]
fn changed_source_operands_with_identical_old_digest_are_rejected() {
    let (mut function, machine) = binary(Type::I64, Opcode::Isub);
    let body = &mut function.blocks.get_mut(&Block(0)).unwrap().instructions;
    let old_digest = body[0].lowering_digest();
    body[0].args.swap(0, 1);
    assert_eq!(old_digest, body[0].lowering_digest());
    assert!(matches!(
        rejected(&function, &machine),
        AffineLoweringError::ReturnMismatch
    ));
}

#[test]
fn changed_constant_repair_is_rejected() {
    let function = source(
        Type::I64,
        0,
        vec![iconst(Type::I64, 0x0001_0002_0003_0004, 100)],
        Some(100),
    );
    let mut machine = select(&function);
    let repair = instruction(&machine, AArch64Opcode::Movk);
    machine.inst_mut(repair).operands[1] = MachOperand::Imm(0x1234);
    assert!(matches!(
        rejected(&function, &machine),
        AffineLoweringError::ReturnMismatch
    ));
}

#[test]
fn illegal_constant_halfwords_and_shifts_are_rejected() {
    let function = source(
        Type::I32,
        0,
        vec![iconst(Type::I32, 0x0001_0002, 100)],
        Some(100),
    );
    let machine = select(&function);
    let repair = instruction(&machine, AArch64Opcode::Movk);
    for (operand, invalid) in [(1, -1), (1, 65_536), (2, 8), (2, 32)] {
        let mut corrupt = machine.clone();
        corrupt.inst_mut(repair).operands[operand] = MachOperand::Imm(invalid);
        rejected(&function, &corrupt);
    }
}

#[test]
fn movk_cannot_read_an_uninitialized_destination() {
    let function = source(Type::I64, 0, vec![iconst(Type::I64, 42, 100)], Some(100));
    let mut machine = select(&function);
    let seed = instruction(&machine, AArch64Opcode::Movz);
    machine.inst_mut(seed).opcode = AArch64Opcode::Movk;
    machine.inst_mut(seed).operands.push(MachOperand::Imm(0));
    rejected(&function, &machine);
}

#[test]
fn changed_vreg_width_is_rejected_even_when_numeric_id_is_unchanged() {
    let (function, mut machine) = binary(Type::I64, Opcode::Iadd);
    let add = instruction(&machine, AArch64Opcode::AddRR);
    let MachOperand::VReg(register) = &mut machine.inst_mut(add).operands[0] else {
        panic!("raw add must define a virtual register");
    };
    register.class = RegClass::Gpr32;
    rejected(&function, &machine);
}

#[test]
fn changed_source_value_type_is_rejected() {
    let (mut function, machine) = binary(Type::I64, Opcode::Iadd);
    function.value_types.insert(Value(100), Type::I32);
    rejected(&function, &machine);
}

#[test]
fn rogue_synthetic_store_cannot_hide_behind_matching_return() {
    let (function, mut machine) = binary(Type::I64, Opcode::Iadd);
    insert_before_return(
        &mut machine,
        MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(0),
            ],
        ),
    );
    rejected(&function, &machine);
}

#[test]
fn undeclared_implicit_clobber_is_rejected() {
    let (function, mut machine) = binary(Type::I64, Opcode::Iadd);
    let add = instruction(&machine, AArch64Opcode::AddRR);
    machine.inst_mut(add).implicit_defs = &[X1];
    rejected(&function, &machine);
}

#[test]
fn forged_effect_flags_on_an_affine_opcode_are_rejected() {
    let (function, machine) = binary(Type::I64, Opcode::Iadd);
    let add = instruction(&machine, AArch64Opcode::AddRR);
    for flag in [
        InstFlags::IS_CALL,
        InstFlags::WRITES_MEMORY,
        InstFlags::HAS_SIDE_EFFECTS,
    ] {
        let mut corrupt = machine.clone();
        corrupt.inst_mut(add).flags.insert(flag);
        rejected(&function, &corrupt);
    }
}

#[test]
fn missing_return_and_wrong_return_register_are_rejected() {
    let (function, machine) = binary(Type::I64, Opcode::Iadd);
    let mut missing = machine.clone();
    missing.block_mut(missing.entry).insts.pop();
    rejected(&function, &missing);
    let mut wrong = machine;
    let ret = instruction(&wrong, AArch64Opcode::Ret);
    wrong.inst_mut(ret).operands[0] = MachOperand::PReg(X0);
    rejected(&function, &wrong);
}

#[test]
fn instruction_after_return_is_rejected() {
    let (function, mut machine) = binary(Type::I64, Opcode::Iadd);
    let ret = instruction(&machine, AArch64Opcode::Ret);
    let duplicate = machine.push_inst(machine.inst(ret).clone());
    machine.append_inst(machine.entry, duplicate);
    rejected(&function, &machine);
}

#[test]
fn malformed_machine_graph_and_instruction_ownership_are_rejected() {
    let (function, machine) = binary(Type::I64, Opcode::Iadd);
    let mut duplicate_layout = machine.clone();
    duplicate_layout.block_order.push(duplicate_layout.entry);
    rejected(&function, &duplicate_layout);
    let mut edge = machine.clone();
    edge.block_mut(edge.entry).succs.push(BlockId(99));
    rejected(&function, &edge);
    let mut duplicate_instruction = machine;
    let first = duplicate_instruction
        .block(duplicate_instruction.entry)
        .insts[0];
    duplicate_instruction
        .block_mut(duplicate_instruction.entry)
        .insts
        .insert(1, first);
    rejected(&function, &duplicate_instruction);
}

#[test]
fn dangling_and_unaccounted_machine_arena_entries_are_rejected() {
    let (function, machine) = binary(Type::I64, Opcode::Iadd);
    let mut dangling = machine.clone();
    dangling.block_mut(dangling.entry).insts[0] = InstId(u32::MAX);
    rejected(&function, &dangling);
    let mut orphan = machine.clone();
    let add = instruction(&orphan, AArch64Opcode::AddRR);
    orphan.push_inst(orphan.inst(add).clone());
    rejected(&function, &orphan);
    let mut sparse_vreg = machine;
    let MachOperand::VReg(register) = &mut sparse_vreg.inst_mut(add).operands[0] else {
        panic!("raw add must define a virtual register");
    };
    register.id = u32::MAX;
    rejected(&function, &sparse_vreg);
}

#[test]
fn source_and_machine_signatures_must_match_in_count_and_width() {
    let (function, machine) = binary(Type::I64, Opcode::Iadd);
    let mut width = machine.clone();
    width.signature.params[0] = trust_cg_ir::Type::I32;
    rejected(&function, &width);
    let mut arity = machine;
    arity.signature.returns.clear();
    rejected(&function, &arity);
    let mut mixed_source = function;
    mixed_source.signature.params[0] = Type::I32;
    rejected(&mixed_source, &width);
}

#[test]
fn malformed_source_arity_undefined_use_and_duplicate_definition_are_rejected() {
    let (function, machine) = binary(Type::I64, Opcode::Iadd);
    let mut arity = function.clone();
    arity.blocks.get_mut(&Block(0)).unwrap().instructions[0]
        .args
        .pop();
    rejected(&arity, &machine);
    let mut undefined = function.clone();
    undefined.blocks.get_mut(&Block(0)).unwrap().instructions[0].args[0] = Value(999);
    rejected(&undefined, &machine);
    let mut duplicate = function;
    duplicate.blocks.get_mut(&Block(0)).unwrap().instructions[0].results[0] = Value(0);
    rejected(&duplicate, &machine);
}

#[test]
fn malformed_source_entry_parameter_convention_is_rejected() {
    let (mut function, machine) = binary(Type::I64, Opcode::Iadd);
    function
        .blocks
        .get_mut(&Block(0))
        .unwrap()
        .params
        .swap(0, 1);
    rejected(&function, &machine);
}

#[test]
fn extra_source_block_and_source_after_return_are_rejected() {
    let (function, machine) = binary(Type::I64, Opcode::Iadd);
    let mut extra_block = function.clone();
    extra_block.blocks.insert(Block(99), BasicBlock::default());
    rejected(&extra_block, &machine);
    let mut after_return = function;
    after_return
        .blocks
        .get_mut(&Block(0))
        .unwrap()
        .instructions
        .push(operation(Opcode::Copy, &[0], 200));
    after_return.value_types.insert(Value(200), Type::I64);
    rejected(&after_return, &machine);
}

#[test]
fn unsupported_source_multiply_is_not_silently_ignored() {
    let (function, machine) = binary(Type::I64, Opcode::Imul);
    assert!(matches!(
        rejected(&function, &machine),
        AffineLoweringError::UnsupportedSource(_)
    ));
}

#[test]
fn ninth_parameter_and_stack_metadata_fail_closed() {
    let function = source(Type::I64, 9, vec![], Some(8));
    let machine = select(&function);
    rejected(&function, &machine);
    let (mut function, machine) = binary(Type::I64, Opcode::Iadd);
    function.stack_slots.push(StackSlotInfo::new(8, 8));
    rejected(&function, &machine);
}

#[test]
fn hidden_return_buffer_metadata_is_outside_the_affine_domain() {
    // Keep the original ordinary-ABI machine untouched. Even metadata that
    // cannot affect this call-free body is outside the checker's stated domain;
    // it must not acquire an ordinary X0-based ABI receipt by being ignored.
    let (function, machine) = binary(Type::I64, Opcode::Iadd);
    check_aarch64_affine_lowering(&function, &machine).unwrap();
    let mut hidden_formal = function.clone();
    hidden_formal.abi_sret_param = Some(AbiSretParam { param_index: 0 });
    assert!(matches!(
        rejected(&hidden_formal, &machine),
        AffineLoweringError::UnsupportedSource(_)
    ));
    let mut hidden_call = function;
    hidden_call.sret_arg_callees.insert("buffer_return".into());
    assert!(matches!(
        rejected(&hidden_call, &machine),
        AffineLoweringError::UnsupportedSource(_)
    ));
}

/// [`source`] with each parameter at its own width.
fn mixed_source(
    params: &[Type],
    returned: Type,
    instructions: Vec<Instruction>,
    result: u32,
) -> Function {
    let mut function = source(returned, params.len(), instructions, Some(result));
    function.signature.params = params.to_vec();
    for (index, ty) in params.iter().enumerate() {
        function.blocks.get_mut(&Block(0)).unwrap().params[index].1 = ty.clone();
        function.value_types.insert(Value(index as u32), ty.clone());
    }
    function
}

/// `fn(<64-bit>) -> i32 { 7 }` and `fn(i32) -> i64 { 7 }`, both selected.
fn unread_parameter_cases() -> Vec<(Function, MachFunction)> {
    [(Type::I64, Type::I32), (Type::I32, Type::I64)]
        .into_iter()
        .map(|(param, returned)| {
            let constant = iconst(returned.clone(), 7, 100);
            let function = mixed_source(&[param], returned, vec![constant], 100);
            let machine = select(&function);
            (function, machine)
        })
        .collect()
}

/// Rejected as `InvalidMachine` for exactly `reason`: a variant-only check
/// would also pass on an unrelated refusal (an orphaned arena entry, say).
fn invalid_machine(source: &Function, machine: &MachFunction, reason: &str) {
    let error = rejected(source, machine);
    assert!(
        matches!(&error, AffineLoweringError::InvalidMachine(message) if message.contains(reason)),
        "expected InvalidMachine({reason:?}), got {error:?}"
    );
}

#[test]
fn a_parameter_the_body_never_reads_may_have_another_width() {
    // The unread formal is ABI glue: `fn(*const T) -> i32 { 7 }` lowers its
    // pointer to an I64 parameter beside an I32 return. Raw ISel still copies
    // the formal at its own width (an X-named copy into a W register for the
    // I32 formal), and the constant materializes at the return's width.
    for (function, machine) in unread_parameter_cases() {
        check_aarch64_affine_lowering(&function, &machine)
            .unwrap_or_else(|error| panic!("{:?}: {error:?}", function.signature));
    }
}

#[test]
fn an_unread_parameter_cannot_be_returned_or_read_at_another_width() {
    for (function, machine) in unread_parameter_cases() {
        let entry = machine.entry;
        let insts = machine.block(entry).insts.clone();
        let [formal, constant, glue, ret] = insts.as_slice() else {
            panic!("real selector must emit formal copy, MOVZ, return copy, RET");
        };
        assert_eq!(machine.inst(*constant).opcode, AArch64Opcode::Movz);
        let formal_vreg = machine.inst(*formal).operands[0].clone();
        // Returning the parameter instead of the constant: its register
        // keeps the parameter's width, which is not the return's.
        let mut returns_parameter = machine.clone();
        returns_parameter.inst_mut(*glue).operands[1] = formal_vreg.clone();
        invalid_machine(&function, &returns_parameter, "wrong-width register write");
        // Returning the untouched argument register. The RET's own width
        // check must refuse it; the orphaned MOVZ and return copy would only
        // be noticed after the walk, under another reason.
        let mut untouched = machine.clone();
        untouched.block_mut(entry).insts = vec![*formal, *ret];
        invalid_machine(&function, &untouched, "return register has wrong type");
        // Changing the formal's width: a 64-bit parameter read through its
        // W view is narrowed, and a 32-bit one copied into an X register
        // would expose its unknown upper bits.
        let mut resized = machine.clone();
        let MachOperand::VReg(formal_vreg) = formal_vreg else {
            panic!("raw formal copy defines a virtual register");
        };
        if formal_vreg.class == RegClass::Gpr64 {
            resized.inst_mut(*formal).operands[1] = MachOperand::PReg(W0);
        } else {
            resized.inst_mut(*formal).operands[0] = MachOperand::VReg(VReg {
                id: formal_vreg.id,
                class: RegClass::Gpr64,
            });
        }
        invalid_machine(&function, &resized, "wrong-width read");
    }
}

/// A void body has no return to fix the domain's width, so the values it
/// observes do: a dead `i32` constant beside an `i64` parameter, or a dead read
/// of the `i32` parameter beside an unread `i64` one, binds and admits the
/// frame owner. Observing both widths, or nothing at all, stays outside.
#[test]
fn a_void_body_takes_the_width_of_what_it_observes() {
    let void = |params: &[Type], instructions: Vec<Instruction>| {
        let mut function = source(Type::I32, params.len(), instructions, None);
        function.signature.params = params.to_vec();
        for (index, ty) in params.iter().enumerate() {
            function.blocks.get_mut(&Block(0)).unwrap().params[index].1 = ty.clone();
            function.value_types.insert(Value(index as u32), ty.clone());
        }
        function
    };
    for admitted in [
        void(&[Type::I64], vec![iconst(Type::I32, 5, 10)]),
        void(
            &[Type::I64, Type::I32],
            vec![operation(Opcode::Iadd, &[1, 1], 10)],
        ),
    ] {
        check_aarch64_affine_lowering(&admitted, &select(&admitted)).unwrap();
        assert!(
            source_admits_frame_owner(&admitted),
            "{:?}",
            admitted.signature
        );
    }
    let mut both = void(
        &[Type::I64, Type::I32],
        vec![
            operation(Opcode::Iadd, &[0, 0], 10),
            operation(Opcode::Iadd, &[1, 1], 11),
        ],
    );
    both.value_types.insert(Value(10), Type::I64);
    let empty = void(&[Type::I64, Type::I32], vec![]);
    for refused in [both, empty] {
        assert!(
            !source_admits_frame_owner(&refused),
            "{:?}",
            refused.signature
        );
        let error = rejected(&refused, &select(&refused));
        assert!(
            matches!(error, AffineLoweringError::UnsupportedSource(_)),
            "{error:?}"
        );
    }
}

#[test]
fn a_read_parameter_of_another_width_stays_outside_the_domain() {
    let unsupported = |source: &Function, machine: &MachFunction| {
        let error = rejected(source, machine);
        assert!(
            matches!(error, AffineLoweringError::UnsupportedSource(_)),
            "{error:?}"
        );
    };
    // Only the I32 parameter is read: admitted, the pointer is glue.
    let sum = operation(Opcode::Iadd, &[1, 1], 100);
    let glue = mixed_source(&[Type::I64, Type::I32], Type::I32, vec![sum], 100);
    let machine = select(&glue);
    check_aarch64_affine_lowering(&glue, &machine).unwrap();
    // Reading the I64 parameter too joins its width to the domain.
    let mut read_both = glue.clone();
    read_both.blocks.get_mut(&Block(0)).unwrap().instructions[0].args[0] = Value(0);
    unsupported(&read_both, &machine);
    // Returning it directly is the same refusal.
    let returned = mixed_source(&[Type::I64], Type::I32, vec![], 0);
    unsupported(&returned, &machine);
    // With nothing observed to fix a width, the parameters must still agree.
    let mut void = source(Type::I64, 2, vec![], None);
    void.signature.params[1] = Type::I32;
    void.blocks.get_mut(&Block(0)).unwrap().params[1].1 = Type::I32;
    void.value_types.insert(Value(1), Type::I32);
    unsupported(&void, &machine);
}
