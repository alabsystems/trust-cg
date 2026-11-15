// trust-cg-opt - Multiply-by-small-constant strength-reduction tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use crate::fast_hash::FxHashMap as HashMap;

use super::*;
use trust_cg_ir::{
    BlockId, PassId, ProvenanceMap, RegClass, Signature, TransformKind, TrustIrInstId,
};

fn assert_instruction_unchanged(actual: &MachInst, expected: &MachInst) {
    assert_eq!(actual.opcode, expected.opcode);
    assert_eq!(actual.operands, expected.operands);
    assert_eq!(actual.flags, expected.flags);
    assert_eq!(actual.implicit_defs, expected.implicit_defs);
    assert_eq!(actual.implicit_uses, expected.implicit_uses);
    assert_eq!(actual.proof, expected.proof);
    assert_eq!(actual.source_loc, expected.source_loc);
}

fn assert_function_unchanged(actual: &MachFunction, expected: &MachFunction) {
    assert_eq!(actual.block_order, expected.block_order);
    assert_eq!(actual.blocks.len(), expected.blocks.len());
    for (actual, expected) in actual.blocks.iter().zip(&expected.blocks) {
        assert_eq!(actual.insts, expected.insts);
        assert_eq!(actual.preds, expected.preds);
        assert_eq!(actual.succs, expected.succs);
        assert_eq!(actual.loop_depth, expected.loop_depth);
    }
    assert_eq!(actual.insts.len(), expected.insts.len());
    for (actual, expected) in actual.insts.iter().zip(&expected.insts) {
        assert_instruction_unchanged(actual, expected);
    }
    assert_eq!(actual.next_vreg, expected.next_vreg);
    assert_eq!(actual.lowering_provenance, expected.lowering_provenance);
    assert_eq!(actual.source_fusion_targets, expected.source_fusion_targets);
    assert_eq!(actual.call_abi_facts, expected.call_abi_facts);
}

fn provenance_for_instructions(func: &MachFunction) -> ProvenanceMap {
    let mut provenance = ProvenanceMap::new();
    for index in 0..func.insts.len() {
        provenance.record_lowering(
            TrustIrInstId(index as u32),
            &[InstId(index as u32)],
            PassId::new("isel"),
        );
    }
    provenance
}

fn assert_public_pass_refuses_unchanged(mut func: MachFunction) {
    let before = func.clone();
    let mut pass = MulShiftReduce;
    assert!(!pass.run(&mut func));
    assert_function_unchanged(&func, &before);

    let mut func = before.clone();
    let mut provenance = provenance_for_instructions(&func);
    let original_provenance = provenance.clone();
    assert!(!pass.run_with_provenance(&mut func, &mut provenance));
    assert_function_unchanged(&func, &before);
    for index in 0..before.insts.len() {
        let id = InstId(index as u32);
        let origin = TrustIrInstId(index as u32);
        let actual = provenance.get_entry(id).unwrap();
        let expected = original_provenance.get_entry(id).unwrap();
        assert_eq!(actual.trust_ir_origins, expected.trust_ir_origins);
        assert_eq!(actual.transforms, expected.transforms);
        assert_eq!(actual.status, expected.status);
        assert_eq!(
            provenance.get_mach_insts(origin),
            original_provenance.get_mach_insts(origin)
        );
    }
}

fn assert_consumed_retired(func: &MachFunction, id: InstId) {
    let expected = MachInst::new(AArch64Opcode::Nop, vec![]);
    assert_instruction_unchanged(func.inst(id), &expected);
    assert!(func.blocks.iter().all(|block| !block.insts.contains(&id)));
}

fn constant_multiply(
    func: &mut MachFunction,
    block: BlockId,
    opcode: AArch64Opcode,
    class: RegClass,
    first: u32,
) -> InstId {
    emit_const(func, block, v(first + 1, class), 3);
    let mut operands = vec![v(first + 3, class), v(first, class), v(first + 1, class)];
    if opcode == AArch64Opcode::Madd {
        operands.push(v(first + 2, class));
    }
    let id = func.push_inst(MachInst::new(opcode, operands));
    func.append_inst(block, id);
    // These fixtures name their existing registers directly, rather than
    // calling alloc_vreg. Synchronize the real arena boundary with those IDs.
    func.next_vreg = func.next_vreg.max(first + 4);
    id
}

#[test]
fn constant_multiply_retires_only_actual_consumed_keys_after_all_block_splices() {
    let (mut func, entry) = new_func();
    let next = func.create_block();
    func.add_edge(entry, next);
    let multiply = constant_multiply(&mut func, entry, AArch64Opcode::MulRR, RegClass::Gpr64, 0);
    let madd = constant_multiply(&mut func, next, AArch64Opcode::Madd, RegClass::Gpr32, 10);
    let orphan = func.push_inst(
        MachInst::new(
            AArch64Opcode::MulRR,
            vec![
                v(30, RegClass::Gpr64),
                v(31, RegClass::Gpr64),
                v(32, RegClass::Gpr64),
            ],
        )
        .with_proof(trust_cg_ir::ProofAnnotation::NoUnsignedOverflow)
        .with_source_loc(SourceLoc {
            file: 2,
            line: 45,
            col: 6,
        }),
    );
    let unrelated = func.push_inst(MachInst::new(
        AArch64Opcode::MulRR,
        vec![
            v(40, RegClass::Gpr64),
            v(41, RegClass::Gpr64),
            v(42, RegClass::Gpr64),
        ],
    ));
    func.append_inst(next, unrelated);
    func.next_vreg = 1000;
    let before = func.clone();
    assert!(run_mul_shift_reduce(&mut func, None));
    assert_consumed_retired(&func, multiply);
    assert_consumed_retired(&func, madd);
    assert_instruction_unchanged(func.inst(orphan), before.inst(orphan));
    assert_instruction_unchanged(func.inst(unrelated), before.inst(unrelated));
    for &id in &before.block(entry).insts {
        if id != multiply {
            assert_instruction_unchanged(func.inst(id), before.inst(id));
        }
    }
    assert!(func.block(next).insts.contains(&unrelated));
    assert!(func.block(entry).insts.iter().all(|&id| id != multiply));
    assert!(func.block(next).insts.iter().all(|&id| id != madd));
}

#[test]
fn multiply_retirement_checks_links_outside_block_order() {
    let (mut func, entry) = new_func();
    let multiply = constant_multiply(&mut func, entry, AArch64Opcode::MulRR, RegClass::Gpr64, 0);
    let outside = func.create_block();
    func.block_order.retain(|&block| block != outside);
    func.append_inst(outside, multiply);
    func.block_mut(entry).insts.retain(|&id| id != multiply);
    let original = func.inst(multiply).clone();
    assert_eq!(
        crate::retirement::retire_unlinked(&mut func, &[multiply]),
        0
    );
    assert_instruction_unchanged(func.inst(multiply), &original);
    func.block_mut(outside).insts.clear();
    assert_eq!(
        crate::retirement::retire_unlinked(&mut func, &[multiply]),
        1
    );
    assert_consumed_retired(&func, multiply);
}

#[test]
fn multiply_shared_ownership_refuses_before_materialization_or_provenance_changes() {
    use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest, SourceInstId};

    for opcode in [AArch64Opcode::MulRR, AArch64Opcode::Madd] {
        for class in [RegClass::Gpr32, RegClass::Gpr64] {
            for shape in 0..4 {
                let (mut func, entry) = new_func();
                let old = constant_multiply(&mut func, entry, opcode, class, 0);
                func.inst_mut(old).source_loc = Some(SourceLoc {
                    file: 5,
                    line: 124,
                    col: 8,
                });
                let source = SourceInstId {
                    block: 3,
                    index: 124,
                };
                func.set_inst_lowering_provenance(
                    old,
                    LoweringProvenance::SourceInst {
                        id: source,
                        digest: SourceInstDigest::compute("Imul", 2, 1),
                        trust_ir_inst: Some(TrustIrInstId(124)),
                    },
                );
                func.source_fusion_targets.insert(
                    SourceInstId {
                        block: 3,
                        index: 125,
                    },
                    source,
                );
                func.next_vreg = 1000;
                let mut provenance = ProvenanceMap::new();
                for index in 0..func.insts.len() {
                    provenance.record_lowering(
                        TrustIrInstId(124 + index as u32),
                        &[InstId(index as u32)],
                        PassId::new("isel"),
                    );
                }
                let mut unique = func.clone();
                let mut unique_provenance = provenance.clone();

                match shape {
                    0 | 1 => {
                        let other = func.create_block();
                        if shape == 0 {
                            // A block omitted from layout is still an owner.
                            func.block_order.retain(|&block| block != other);
                        } else {
                            func.add_edge(entry, other);
                        }
                        func.append_inst(other, old);
                    }
                    2 => func.append_inst(entry, old),
                    _ => func.block_order.push(entry),
                }

                // The refusal must be ownership-driven, not an unrelated
                // failure to recognize the constant multiply.
                let ctx = std::cell::OnceCell::new();
                let census = MoveWideCensus::build(&func);
                assert!(analyze(&func, &ctx, &census, old).is_some());
                let before = func.clone();
                let old_provenance: Vec<_> = (0..func.insts.len())
                    .map(|index| {
                        let id = InstId(index as u32);
                        let origin = TrustIrInstId(124 + index as u32);
                        (
                            id,
                            origin,
                            provenance.get_entry(id).unwrap().clone(),
                            provenance.get_mach_insts(origin).unwrap().to_vec(),
                        )
                    })
                    .collect();

                let mut pass = MulShiftReduce;
                assert!(!pass.run_with_provenance(&mut func, &mut provenance));
                assert_eq!(func.block_order, before.block_order);
                assert_eq!(func.blocks.len(), before.blocks.len());
                for (actual, expected) in func.blocks.iter().zip(&before.blocks) {
                    assert_eq!(actual.insts, expected.insts);
                    assert_eq!(actual.preds, expected.preds);
                    assert_eq!(actual.succs, expected.succs);
                    assert_eq!(actual.loop_depth, expected.loop_depth);
                }
                assert_eq!(func.insts.len(), before.insts.len());
                assert_eq!(func.next_vreg, before.next_vreg);
                assert_eq!(func.lowering_provenance, before.lowering_provenance);
                assert_eq!(func.source_fusion_targets, before.source_fusion_targets);
                assert_eq!(func.call_abi_facts, before.call_abi_facts);
                for (actual, expected) in func.insts.iter().zip(&before.insts) {
                    assert_instruction_unchanged(actual, expected);
                }
                for (id, origin, expected, mach_insts) in old_provenance {
                    let actual = provenance.get_entry(id).unwrap();
                    assert_eq!(actual.trust_ir_origins, expected.trust_ir_origins);
                    assert_eq!(actual.transforms, expected.transforms);
                    assert_eq!(actual.status, expected.status);
                    assert_eq!(provenance.get_mach_insts(origin), Some(&mach_insts[..]));
                }

                // Exercise the same public entrypoint with the ownership
                // hazard absent, so a disabled pass cannot satisfy the test.
                assert!(pass.run_with_provenance(&mut unique, &mut unique_provenance));
                assert_consumed_retired(&unique, old);
                assert!(unique_provenance.get_entry(old).is_none());
            }
        }
    }
}

#[test]
fn multiply_replacement_preserves_location_provenance_and_lowering_sidecars() {
    use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest, SourceInstId};
    for opcode in [AArch64Opcode::MulRR, AArch64Opcode::Madd] {
        let (mut func, entry) = new_func();
        let old = constant_multiply(&mut func, entry, opcode, RegClass::Gpr64, 0);
        let location = SourceLoc {
            file: 4,
            line: 124,
            col: 7,
        };
        func.inst_mut(old).source_loc = Some(location);
        let source = SourceInstId {
            block: 2,
            index: 124,
        };
        func.set_inst_lowering_provenance(
            old,
            LoweringProvenance::SourceInst {
                id: source,
                digest: SourceInstDigest::compute("Imul", 2, 1),
                trust_ir_inst: Some(TrustIrInstId(124)),
            },
        );
        func.source_fusion_targets.insert(
            SourceInstId {
                block: 2,
                index: 125,
            },
            source,
        );
        let lowering = func.lowering_provenance.clone();
        let fusion = func.source_fusion_targets.clone();
        let call_facts = func.call_abi_facts.clone();
        func.next_vreg = 1000;
        let first_created = func.insts.len();
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(124), &[old], PassId::new("isel"));
        assert!(run_mul_shift_reduce(&mut func, Some(&mut provenance)));
        assert_consumed_retired(&func, old);
        assert_eq!(func.lowering_provenance, lowering);
        assert_eq!(func.source_fusion_targets, fusion);
        assert_eq!(func.call_abi_facts, call_facts);
        let replacements: Vec<_> = func
            .block(entry)
            .insts
            .iter()
            .copied()
            .filter(|id| id.0 as usize >= first_created)
            .collect();
        assert!(!replacements.is_empty());
        assert!(
            replacements
                .iter()
                .all(|&id| func.inst(id).source_loc == Some(location))
        );
        let last = *replacements.last().unwrap();
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(124)),
            Some(&[last][..])
        );
        assert!(provenance.get_entry(old).is_none());
        let record = provenance
            .get_entry(last)
            .unwrap()
            .transforms
            .last()
            .unwrap();
        assert_eq!(record.pass, pass_id());
        assert_eq!(record.kind, TransformKind::Replaced { old });
    }
}

#[test]
fn multiply_and_madd_refuse_hidden_effects_flags_and_opcode_bound_proofs() {
    use trust_cg_ir::regs::{NZCV, X9};
    use trust_cg_ir::{InstFlags, ProofAnnotation};
    for opcode in [AArch64Opcode::MulRR, AArch64Opcode::Madd] {
        for class in [RegClass::Gpr32, RegClass::Gpr64] {
            for mutation in 0..5 {
                let (mut func, entry) = new_func();
                let candidate = constant_multiply(&mut func, entry, opcode, class, 0);
                let instruction = func.inst_mut(candidate);
                match mutation {
                    0 => instruction.flags |= InstFlags::HAS_SIDE_EFFECTS,
                    1 => instruction.flags |= InstFlags::PROOF_REORDERABLE,
                    2 => instruction.implicit_defs = &[X9],
                    3 => instruction.implicit_uses = &[NZCV],
                    _ => instruction.proof = Some(ProofAnnotation::NoOverflow),
                }
                func.next_vreg = 1000;
                let before = func.clone();
                assert!(!run_mul_shift_reduce(&mut func, None));
                assert_eq!(func.block(entry).insts, before.block(entry).insts);
                assert_eq!(func.insts.len(), before.insts.len());
                assert_eq!(func.next_vreg, before.next_vreg);
                for (actual, expected) in func.insts.iter().zip(&before.insts) {
                    assert_instruction_unchanged(actual, expected);
                }
            }
        }
    }
}

#[test]
fn masked_umull_does_not_delete_or_transfer_unhandled_proof_metadata() {
    for candidate in 0..3 {
        let (mut func, entry, ids) = masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
        func.inst_mut(ids[candidate]).proof =
            Some(trust_cg_ir::ProofAnnotation::NoUnsignedOverflow);
        let before = func.clone();
        assert!(!run_mul_shift_reduce(&mut func, None));
        assert_eq!(func.block(entry).insts, before.block(entry).insts);
        assert_eq!(func.insts.len(), before.insts.len());
        for (actual, expected) in func.insts.iter().zip(&before.insts) {
            assert_instruction_unchanged(actual, expected);
        }
    }
}

#[test]
fn multiply_and_madd_refuse_inexact_operand_arities_without_mutation() {
    for opcode in [AArch64Opcode::MulRR, AArch64Opcode::Madd] {
        for extra in [false, true] {
            let (mut func, entry) = new_func();
            let candidate = constant_multiply(&mut func, entry, opcode, RegClass::Gpr64, 0);
            if extra {
                func.inst_mut(candidate).operands.push(MachOperand::Imm(0));
            } else {
                func.inst_mut(candidate).operands.pop();
            }
            let before = func.clone();
            assert!(!run_mul_shift_reduce(&mut func, None));
            assert_eq!(func.insts.len(), before.insts.len());
            assert_eq!(func.block(entry).insts, before.block(entry).insts);
            for (actual, expected) in func.insts.iter().zip(&before.insts) {
                assert_instruction_unchanged(actual, expected);
            }
        }
    }
}

#[test]
fn multiply_operand_arena_bounds_refuse_before_queries_and_preserve_provenance() {
    for opcode in [AArch64Opcode::MulRR, AArch64Opcode::Madd] {
        for class in [RegClass::Gpr32, RegClass::Gpr64] {
            let arity = if opcode == AArch64Opcode::Madd { 4 } else { 3 };
            for operand in 0..arity {
                for out_of_arena in [16, 65] {
                    let (mut func, entry) = new_func();
                    let old = constant_multiply(&mut func, entry, opcode, class, 0);
                    func.inst_mut(old).operands[operand] = v(out_of_arena, class);
                    if operand == 2 {
                        // Keep the malformed constant operand recognizable.
                        // Without the arena check its matching move-wide def
                        // would reach the multiply and authorize a rewrite.
                        let constant = func.block(entry).insts[0];
                        func.inst_mut(constant).operands[0] = v(out_of_arena, class);
                    }

                    let mut repaired = func.clone();
                    repaired.next_vreg = out_of_arena + 1;
                    let ctx = std::cell::OnceCell::new();
                    let census = MoveWideCensus::build(&repaired);
                    assert!(analyze(&repaired, &ctx, &census, old).is_some());

                    // Test both the exact boundary and a strictly larger ID.
                    for arena_end in [out_of_arena, out_of_arena - 1] {
                        let mut malformed = func.clone();
                        malformed.next_vreg = arena_end;
                        let ctx = std::cell::OnceCell::new();
                        let census = MoveWideCensus::build(&malformed);
                        assert!(analyze(&malformed, &ctx, &census, old).is_none());
                        assert!(ctx.get().is_none(), "arena refusal must precede queries");
                        assert_public_pass_refuses_unchanged(malformed);
                    }

                    let mut plain = repaired.clone();
                    let mut pass = MulShiftReduce;
                    assert!(pass.run(&mut plain));
                    assert_consumed_retired(&plain, old);
                    let mut provenance = provenance_for_instructions(&repaired);
                    assert!(pass.run_with_provenance(&mut repaired, &mut provenance));
                    assert_consumed_retired(&repaired, old);
                    assert!(provenance.get_entry(old).is_none());
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// `decompose` — the arithmetic core
// ---------------------------------------------------------------------------

fn terms(pos_shift: &[(bool, u32)]) -> Vec<Term> {
    pos_shift
        .iter()
        .map(|&(positive, shift)| Term { positive, shift })
        .collect()
}

/// The integer value a term list evaluates to (independent re-derivation of the
/// decomposition, used to cross-check every `decompose` result).
fn value_of(ts: &[Term]) -> i128 {
    ts.iter()
        .map(|t| {
            let m = 1i128 << t.shift;
            if t.positive { m } else { -m }
        })
        .sum()
}

#[test]
fn decompose_powers_and_pm_one() {
    assert_eq!(decompose(2, 64), Some(terms(&[(true, 1)])));
    assert_eq!(decompose(4, 64), Some(terms(&[(true, 2)])));
    assert_eq!(decompose(8, 64), Some(terms(&[(true, 3)])));
    assert_eq!(decompose(16, 64), Some(terms(&[(true, 4)])));
    // 3 = 2 + 1
    assert_eq!(decompose(3, 64), Some(terms(&[(true, 1), (true, 0)])));
    // 5 = 4 + 1, 9 = 8 + 1, 17 = 16 + 1
    assert_eq!(decompose(5, 64), Some(terms(&[(true, 2), (true, 0)])));
    assert_eq!(decompose(9, 64), Some(terms(&[(true, 3), (true, 0)])));
    assert_eq!(decompose(17, 64), Some(terms(&[(true, 4), (true, 0)])));
    // 7 = 8 - 1, 15 = 16 - 1
    assert_eq!(decompose(7, 64), Some(terms(&[(true, 3), (false, 0)])));
    assert_eq!(decompose(15, 64), Some(terms(&[(true, 4), (false, 0)])));
}

#[test]
fn decompose_bails_on_two_shift_forms() {
    // Two-shift forms (both powers >= 2) are throughput-risky and BAIL:
    // 6=4+2, 10=8+2, 12=8+4, 24=16+8, 96=64+32, 20=16+4, 18=16+2.
    for c in [6i128, 10, 12, 14, 18, 20, 24, 96] {
        assert_eq!(decompose(c, 64), None, "two-shift {c} must bail");
    }
}

#[test]
fn decompose_negative_via_minus_form() {
    // -3 = 1 - 4  (leading positive: x - (x<<2))
    let ts = decompose(-3, 64).expect("-3 must decompose");
    assert_eq!(value_of(&ts), -3);
    assert!(
        ts.iter().any(|t| t.positive),
        "must keep a leading positive"
    );
    // -7 = 1 - 8
    let ts = decompose(-7, 64).expect("-7 must decompose");
    assert_eq!(value_of(&ts), -7);
    assert!(ts.iter().any(|t| t.positive));
}

#[test]
fn decompose_bails_on_three_term_and_degenerate() {
    // 11 = 8+2+1, 13 = 8+4+1 — three nonzero terms, cannot be ≤2 signed powers.
    assert_eq!(decompose(11, 64), None);
    assert_eq!(decompose(13, 64), None);
    assert_eq!(decompose(19, 64), None);
    assert_eq!(decompose(23, 64), None);
    // Degenerate multipliers are left to const-fold, not this pass.
    assert_eq!(decompose(0, 64), None);
    assert_eq!(decompose(1, 64), None);
    assert_eq!(decompose(-1, 64), None);
    // `-6 = 2 - 8` and `-10 = -(8+2)` are two-shift / (-,-) — both bail.
    assert_eq!(decompose(-6, 64), None);
    assert_eq!(decompose(-10, 64), None);
    // `-11 = -(8+2+1)` is a three-term negative — bails.
    assert_eq!(decompose(-11, 64), None);
}

#[test]
fn decompose_respects_width_shift_range() {
    // For a 32-bit op every shift must be < 32.
    for c in [3i128, 5, 6, 7, 9, 10, 15, 17, -3] {
        if let Some(ts) = decompose(c, 32) {
            assert!(ts.iter().all(|t| t.shift < 32));
            assert_eq!(value_of(&ts), c);
        }
    }
}

// ---------------------------------------------------------------------------
// End-to-end rewrite: build a MulRR/Madd, evaluate before and after the pass,
// assert bit-exact equality (a differential correctness oracle) and that the
// hardware multiply is gone.
// ---------------------------------------------------------------------------

fn v(id: u32, class: RegClass) -> MachOperand {
    MachOperand::VReg(VReg::new(id, class))
}

fn mask(x: u64, width: u32) -> u64 {
    if width == 32 { x & 0xFFFF_FFFF } else { x }
}

/// Emit a constant materialization into `dst` (id) — `Movz` for a small
/// non-negative value, `Movn` for a small negative — mirroring isel.
fn emit_const(func: &mut MachFunction, block: BlockId, dst: MachOperand, value: i64) {
    let inst = if (0..=0xFFFF).contains(&value) {
        MachInst::new(AArch64Opcode::Movz, vec![dst, MachOperand::Imm(value)])
    } else {
        let n = (!value) & 0xFFFF;
        assert!(
            (0..=0xFFFF).contains(&n),
            "test only materializes constants whose Movn imm fits"
        );
        MachInst::new(AArch64Opcode::Movn, vec![dst, MachOperand::Imm(n)])
    };
    push(func, block, inst);
}

fn push(func: &mut MachFunction, block: BlockId, inst: MachInst) {
    // Synthetic fixtures name vregs directly. Keep the arena counter honest
    // so negative controls exercise their intended guard, not stale bounds.
    for operand in &inst.operands {
        if let Some(reg) = operand.as_vreg() {
            func.next_vreg = func.next_vreg.max(reg.id.checked_add(1).unwrap());
        }
    }
    let id = func.push_inst(inst);
    func.append_inst(block, id);
}

/// Evaluate a straight-line block for the subset of opcodes this pass produces
/// or consumes. `inputs` seeds registers with no in-block definition (the
/// multiplicand `x`).
fn eval(
    func: &MachFunction,
    block: BlockId,
    inputs: &HashMap<u32, u64>,
    width: u32,
) -> HashMap<u32, u64> {
    let mut vals = inputs.clone();
    let rd = |o: &MachOperand, vals: &HashMap<u32, u64>| -> u64 {
        match o {
            MachOperand::VReg(reg) => *vals
                .get(&reg.id)
                .unwrap_or_else(|| panic!("read of undefined v{}", reg.id)),
            _ => panic!("expected register operand"),
        }
    };
    let imm = |o: &MachOperand| -> i64 {
        match o {
            MachOperand::Imm(k) => *k,
            _ => panic!("expected imm operand"),
        }
    };
    for &iid in &func.block(block).insts {
        let inst = func.inst(iid);
        let ops = &inst.operands;
        let (dst_id, val) = match inst.opcode {
            AArch64Opcode::Movz => {
                let shift = ops.get(2).map(imm).unwrap_or(0);
                let val = (imm(&ops[1]) as u64) << shift;
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::Movn => {
                let shift = ops.get(2).map(imm).unwrap_or(0);
                let val = !((imm(&ops[1]) as u64) << shift);
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::Movk => {
                // Insert the 16-bit field at `shift`; the rest of the register
                // is the value the same ID already holds.
                let shift = ops.get(2).map(imm).unwrap_or(0);
                let field = 0xFFFFu64 << shift;
                let val = (rd(&ops[0], &vals) & !field) | ((imm(&ops[1]) as u64) << shift);
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::LslRI => {
                let val = rd(&ops[1], &vals) << (imm(&ops[2]) as u32);
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::AddRR => {
                let val = rd(&ops[1], &vals).wrapping_add(rd(&ops[2], &vals));
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::SubRR => {
                let val = rd(&ops[1], &vals).wrapping_sub(rd(&ops[2], &vals));
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::MulRR => {
                let val = rd(&ops[1], &vals).wrapping_mul(rd(&ops[2], &vals));
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::AndRI => {
                let val = rd(&ops[1], &vals) & imm(&ops[2]) as u64;
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::Umull => {
                let lhs = rd(&ops[1], &vals) as u32 as u64;
                let rhs = rd(&ops[2], &vals) as u32 as u64;
                (vreg_id(&ops[0]), lhs * rhs)
            }
            AArch64Opcode::Madd => {
                let prod = rd(&ops[1], &vals).wrapping_mul(rd(&ops[2], &vals));
                let val = rd(&ops[3], &vals).wrapping_add(prod);
                (vreg_id(&ops[0]), mask(val, width))
            }
            _ => continue,
        };
        vals.insert(dst_id, val);
    }
    vals
}

fn vreg_id(o: &MachOperand) -> u32 {
    match o {
        MachOperand::VReg(r) => r.id,
        _ => panic!("expected vreg dst"),
    }
}

fn new_func() -> (MachFunction, BlockId) {
    let func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    (func, entry)
}

/// Fixed multiplicand test vectors exercising sign, small, and high bits.
const X_VECS: [u64; 6] = [
    0,
    1,
    7,
    0x0000_0000_DEAD_BEEF,
    0xFFFF_FFFF_FFFF_FFFD,
    0x8000_0000_0000_0001,
];

fn opcodes(func: &MachFunction, block: BlockId) -> Vec<AArch64Opcode> {
    func.block(block)
        .insts
        .iter()
        .map(|&i| func.inst(i).opcode)
        .collect()
}

/// Build `dst = x * c (+ y)` and assert the rewrite is bit-exact for every
/// multiplicand, and that the hardware multiply disappeared.
fn check_fires(class: RegClass, c: i64, addend: Option<i64>) {
    let width = class.size_bits();
    // ids: x=0, cReg=1, yReg=2, dst=3.
    let x = v(0, class);
    let creg = v(1, class);
    let yreg = v(2, class);
    let dst = v(3, class);

    let (mut func, entry) = new_func();
    emit_const(&mut func, entry, creg.clone(), c);
    if let Some(y) = addend {
        emit_const(&mut func, entry, yreg.clone(), y);
    }
    let mul = match addend {
        None => MachInst::new(
            AArch64Opcode::MulRR,
            vec![dst.clone(), x.clone(), creg.clone()],
        ),
        Some(_) => MachInst::new(
            AArch64Opcode::Madd,
            vec![dst.clone(), x.clone(), creg.clone(), yreg.clone()],
        ),
    };
    push(&mut func, entry, mul);
    // Fresh vregs must not alias the test ids.
    func.next_vreg = 1000;

    for &xv in &X_VECS {
        let mut inputs = HashMap::default();
        inputs.insert(0u32, mask(xv, width));

        // Snapshot the reference value from the ORIGINAL mul/madd.
        let before = eval(&func, entry, &inputs, width);
        let expected = before[&3];

        // Sanity: the reference equals x*c (+y) mod 2^W (independent formula).
        let indep = {
            let xw = mask(xv, width);
            let prod = xw.wrapping_mul(c as u64);
            let base = addend.map(|y| mask(y as u64, width)).unwrap_or(0);
            mask(base.wrapping_add(prod), width)
        };
        assert_eq!(expected, indep, "reference formula mismatch for c={c}");

        // Run the pass on a fresh clone so opcode assertions see one rewrite.
        let mut f2 = func.clone();
        let mut pass = MulShiftReduce;
        assert!(
            pass.run(&mut f2),
            "pass must fire for c={c} addend={addend:?}"
        );
        let after = eval(&f2, entry, &inputs, width);
        assert_eq!(
            after[&3], expected,
            "rewrite changed the value for c={c} addend={addend:?} x={xv:#x}"
        );

        let ops = opcodes(&f2, entry);
        assert!(
            !ops.contains(&AArch64Opcode::MulRR) && !ops.contains(&AArch64Opcode::Madd),
            "hardware multiply must be gone for c={c} addend={addend:?}: {ops:?}"
        );
        assert!(
            ops.iter().all(|o| matches!(
                o,
                AArch64Opcode::Movz
                    | AArch64Opcode::Movn
                    | AArch64Opcode::LslRI
                    | AArch64Opcode::AddRR
                    | AArch64Opcode::SubRR
            )),
            "only shift/add/sub + const-materialize may remain: {ops:?}"
        );
    }
}

#[test]
fn mulrr_fires_all_small_constants_64() {
    for c in [2i64, 3, 4, 5, 7, 8, 9, 15, 16, 17, -3] {
        check_fires(RegClass::Gpr64, c, None);
    }
}

#[test]
fn mulrr_fires_all_small_constants_32() {
    for c in [2i64, 3, 4, 5, 7, 8, 9, 15, 16, 17, -3] {
        check_fires(RegClass::Gpr32, c, None);
    }
}

#[test]
fn madd_fires_all_small_constants_64() {
    // Madd(x, c, y) = y + x*c — the p2_collatz `c*3 + 1` shape included.
    for c in [2i64, 3, 4, 5, 7, 8, 9, 15, 16, 17, -3] {
        check_fires(RegClass::Gpr64, c, Some(1));
    }
}

#[test]
fn madd_fires_all_small_constants_32() {
    for c in [2i64, 3, 5, 7, 9, 15, 17, -3] {
        check_fires(RegClass::Gpr32, c, Some(1));
    }
}

#[test]
fn collatz_madd_by_3_lowers_to_shift_add() {
    // MADD dst, x, #3, #1  (dst = x*3 + 1) -> LslRI + AddRR + AddRR, NO madd.
    let class = RegClass::Gpr64;
    let x = v(0, class);
    let creg = v(1, class);
    let yreg = v(2, class);
    let dst = v(3, class);
    let (mut func, entry) = new_func();
    emit_const(&mut func, entry, creg.clone(), 3);
    emit_const(&mut func, entry, yreg.clone(), 1);
    push(
        &mut func,
        entry,
        MachInst::new(AArch64Opcode::Madd, vec![dst, x, creg, yreg]),
    );
    func.next_vreg = 1000;

    let mut pass = MulShiftReduce;
    assert!(pass.run(&mut func));
    let ops = opcodes(&func, entry);
    assert!(!ops.contains(&AArch64Opcode::Madd), "madd gone: {ops:?}");
    assert_eq!(
        ops.iter().filter(|o| **o == AArch64Opcode::LslRI).count(),
        1,
        "one shift (x<<1): {ops:?}"
    );
    assert_eq!(
        ops.iter().filter(|o| **o == AArch64Opcode::AddRR).count(),
        2,
        "two adds ((x+1) + (x<<1)): {ops:?}"
    );
    // The single shift is by 1 (x*3 = x + x<<1).
    let shift_amt = func
        .block(entry)
        .insts
        .iter()
        .map(|&i| func.inst(i))
        .find(|i| i.opcode == AArch64Opcode::LslRI)
        .and_then(|i| i.operands[2].as_imm())
        .unwrap();
    assert_eq!(shift_amt, 1);
}

// ---------------------------------------------------------------------------
// Masked low-word multiply -> UMULL
// ---------------------------------------------------------------------------

fn masked_mul_func(
    lhs_mask: i64,
    rhs_mask: i64,
) -> (MachFunction, BlockId, [trust_cg_ir::InstId; 3]) {
    let class = RegClass::Gpr64;
    let (mut func, entry) = new_func();
    let lhs_and = func.push_inst(MachInst::new(
        AArch64Opcode::AndRI,
        vec![v(2, class), v(0, class), MachOperand::Imm(lhs_mask)],
    ));
    func.append_inst(entry, lhs_and);
    let rhs_and = func.push_inst(MachInst::new(
        AArch64Opcode::AndRI,
        vec![v(3, class), v(1, class), MachOperand::Imm(rhs_mask)],
    ));
    func.append_inst(entry, rhs_and);
    let mul = func.push_inst(MachInst::new(
        AArch64Opcode::MulRR,
        vec![v(4, class), v(2, class), v(3, class)],
    ));
    func.append_inst(entry, mul);
    func.next_vreg = 1000;
    (func, entry, [lhs_and, rhs_and, mul])
}

fn assert_public_masked_fuses(mut func: MachFunction, ids: [InstId; 3]) {
    let [lhs_and, rhs_and, mul] = ids;
    let mut plain = func.clone();
    let mut pass = MulShiftReduce;
    assert!(pass.run(&mut plain));
    assert_eq!(plain.inst(mul).opcode, AArch64Opcode::Umull);
    assert_eq!(plain.inst(lhs_and).opcode, AArch64Opcode::Nop);
    assert_eq!(plain.inst(rhs_and).opcode, AArch64Opcode::Nop);

    let mut provenance = provenance_for_instructions(&func);
    assert!(pass.run_with_provenance(&mut func, &mut provenance));
    assert_eq!(func.inst(mul).opcode, AArch64Opcode::Umull);
    assert_eq!(func.inst(lhs_and).opcode, AArch64Opcode::Nop);
    assert_eq!(func.inst(rhs_and).opcode, AArch64Opcode::Nop);
    assert!(provenance.get_entry(lhs_and).is_none());
    assert!(provenance.get_entry(rhs_and).is_none());
    for id in ids {
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(id.0)),
            Some(&[mul][..])
        );
    }
}

#[test]
fn masked_umull_operand_arena_bounds_refuse_without_ir_or_provenance_changes() {
    for operand in 0..5 {
        for out_of_arena in [16, 65] {
            let (mut func, _, ids @ [lhs_and, rhs_and, mul]) =
                masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
            match operand {
                0 => func.inst_mut(mul).operands[0] = v(out_of_arena, RegClass::Gpr64),
                1 => {
                    func.inst_mut(lhs_and).operands[0] = v(out_of_arena, RegClass::Gpr64);
                    func.inst_mut(mul).operands[1] = v(out_of_arena, RegClass::Gpr64);
                }
                2 => {
                    func.inst_mut(rhs_and).operands[0] = v(out_of_arena, RegClass::Gpr64);
                    func.inst_mut(mul).operands[2] = v(out_of_arena, RegClass::Gpr64);
                }
                3 => func.inst_mut(lhs_and).operands[1] = v(out_of_arena, RegClass::Gpr64),
                _ => func.inst_mut(rhs_and).operands[1] = v(out_of_arena, RegClass::Gpr64),
            }
            for arena_end in [out_of_arena, out_of_arena - 1] {
                let mut malformed = func.clone();
                malformed.next_vreg = arena_end;
                assert_public_pass_refuses_unchanged(malformed);
            }
            // Every operand shape and its mask remain valid when the exact
            // same register ID is inside the arena; no disabled-pass vacuity.
            func.next_vreg = out_of_arena + 1;
            assert_public_masked_fuses(func, ids);
        }
    }
}

#[test]
fn masked_umull_shared_ownership_refuses_before_overwrite_or_provenance_merge() {
    for candidate in 0..3 {
        for shape in 0..4 {
            let (mut func, entry, ids) = masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
            let unique = func.clone();
            match shape {
                0 | 1 => {
                    let other = func.create_block();
                    if shape == 0 {
                        func.block_order.retain(|&block| block != other);
                    } else {
                        func.add_edge(entry, other);
                    }
                    func.append_inst(other, ids[candidate]);
                }
                2 => func.append_inst(entry, ids[candidate]),
                _ => func.block_order.push(entry),
            }
            assert_public_pass_refuses_unchanged(func);
            assert_public_masked_fuses(unique, ids);
        }
    }
}

#[test]
fn masked_umull_preserves_hidden_readers_with_distinct_instruction_ids() {
    for masked in [2, 3] {
        for consumer in 0..4 {
            let (mut func, entry, ids) = masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
            let unique = func.clone();
            let outside = func.create_block();
            func.block_order.retain(|&block| block != outside);
            let class = RegClass::Gpr64;
            let reader = match consumer {
                0 => MachInst::new(
                    AArch64Opcode::AddRR,
                    vec![v(5, class), v(masked, class), v(6, class)],
                ),
                1 => MachInst::new(
                    AArch64Opcode::Movk,
                    vec![v(masked, class), MachOperand::Imm(1), MachOperand::Imm(0)],
                ),
                2 => MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![v(masked, class), v(6, class), MachOperand::Imm(0)],
                ),
                _ => MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![v(6, class), v(masked, class), MachOperand::Imm(0)],
                ),
            };
            let reader_id = func.push_inst(reader);
            func.append_inst(outside, reader_id);
            assert!(!ids.contains(&reader_id));
            assert!(func.block(entry).insts.iter().all(|&id| id != reader_id));
            // The previous layout-only use census cannot see this reader.
            // This confirms that the fixture targets the new all-block seam.
            let layout_reads = crate::effects::build_vreg_read_counts(&func);
            assert_eq!(layout_reads.get(&VReg::new(masked, class)), Some(&1));
            let mut reads_masked = false;
            crate::effects::for_each_inst_use(func.inst(reader_id), |used| {
                reads_masked |= used == VReg::new(masked, class);
            });
            assert!(reads_masked);
            assert_public_pass_refuses_unchanged(func);
            assert_public_masked_fuses(unique, ids);
        }
    }
}

#[test]
fn masked_umull_preserves_hidden_w_view_reads_of_x_view_producers() {
    for masked in [2, 3] {
        for consumer in 0..3 {
            let (mut func, _, ids) = masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
            let unique = func.clone();
            let outside = func.create_block();
            func.block_order.retain(|&block| block != outside);
            let narrow = RegClass::Gpr32;
            let reader = match consumer {
                0 => MachInst::new(
                    AArch64Opcode::AddRR,
                    vec![v(5, narrow), v(masked, narrow), v(6, narrow)],
                ),
                1 => MachInst::new(
                    AArch64Opcode::Movk,
                    vec![v(masked, narrow), MachOperand::Imm(1), MachOperand::Imm(0)],
                ),
                _ => MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        v(masked, narrow),
                        v(6, RegClass::Gpr64),
                        MachOperand::Imm(0),
                    ],
                ),
            };
            let reader_id = func.push_inst(reader);
            func.append_inst(outside, reader_id);
            assert!(!ids.contains(&reader_id));
            let mut reads_narrow = false;
            crate::effects::for_each_inst_use(func.inst(reader_id), |used| {
                reads_narrow |= used == VReg::new(masked, narrow);
            });
            assert!(reads_narrow);
            assert_ne!(
                VReg::new(masked, narrow),
                VReg::new(masked, RegClass::Gpr64),
                "class-sensitive map keys would miss the aliased low-word read"
            );
            assert_public_pass_refuses_unchanged(func);
            assert_public_masked_fuses(unique, ids);
        }
    }
}

#[test]
fn masked_umull_refuses_w_view_redefinitions_of_raw_or_masked_x_view_ids() {
    for redefined in 0..4 {
        let (mut func, entry, ids @ [lhs_and, rhs_and, mul]) =
            masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
        let unique = func.clone();
        let narrow = RegClass::Gpr32;
        // A nonconstant W definition preserves Phase A's no-constant verdict.
        // A move-wide of masked id2/3 would instead legitimately authorize the
        // independent ordinary constant-multiply rewrite before masked fusion.
        let redef = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![v(redefined, narrow), v(6, narrow), v(7, narrow)],
        ));
        func.block_mut(entry).insts.insert(2, redef);
        assert_eq!(func.block(entry).insts, vec![lhs_and, rhs_and, redef, mul]);
        assert_eq!(
            func.inst(redef).operands[0].as_vreg(),
            Some(VReg::new(redefined, narrow))
        );
        let ctx = std::cell::OnceCell::new();
        let census = MoveWideCensus::build(&func);
        assert!(analyze(&func, &ctx, &census, mul).is_none());
        assert!(ctx.get().is_none());
        assert_public_pass_refuses_unchanged(func);
        assert_public_masked_fuses(unique, ids);
    }
}

#[test]
fn masked_low_words_fold_to_one_umull_and_are_bit_exact() {
    let (func, entry, [lhs_and, rhs_and, mul]) = masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
    let vectors = [
        0,
        1,
        0xffff_ffff,
        0x1_0000_0000,
        0xdead_beef_cafe_babe,
        u64::MAX,
    ];

    let mut rewritten = func.clone();
    let mut pass = MulShiftReduce;
    assert!(pass.run(&mut rewritten));
    assert_eq!(
        opcodes(&rewritten, entry),
        vec![AArch64Opcode::Nop, AArch64Opcode::Nop, AArch64Opcode::Umull]
    );
    let fused = rewritten.inst(mul);
    assert_eq!(
        fused.operands,
        vec![
            v(4, RegClass::Gpr64),
            v(0, RegClass::Gpr64),
            v(1, RegClass::Gpr64)
        ],
        "UMULL must read the original low words directly"
    );
    assert_eq!(rewritten.inst(lhs_and).opcode, AArch64Opcode::Nop);
    assert_eq!(rewritten.inst(rhs_and).opcode, AArch64Opcode::Nop);

    for &lhs in &vectors {
        for &rhs in &vectors {
            let inputs = HashMap::from_iter([(0, lhs), (1, rhs)]);
            let before = eval(&func, entry, &inputs, 64)[&4];
            let after = eval(&rewritten, entry, &inputs, 64)[&4];
            let independent = (lhs as u32 as u64) * (rhs as u32 as u64);
            assert_eq!(before, independent, "reference mismatch: {lhs:#x} {rhs:#x}");
            assert_eq!(after, before, "UMULL mismatch: {lhs:#x} {rhs:#x}");
        }
    }
}

#[test]
fn masked_umull_records_three_to_one_provenance_merge() {
    let (mut func, _entry, [lhs_and, rhs_and, mul]) = masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
    let mut provenance = ProvenanceMap::new();
    provenance.record_lowering(TrustIrInstId(10), &[lhs_and], PassId::new("isel"));
    provenance.record_lowering(TrustIrInstId(11), &[rhs_and], PassId::new("isel"));
    provenance.record_lowering(TrustIrInstId(12), &[mul], PassId::new("isel"));

    let mut pass = MulShiftReduce;
    assert!(pass.run_with_provenance(&mut func, &mut provenance));
    let entry = provenance
        .get_entry(mul)
        .expect("surviving UMULL must retain merged provenance");
    for origin in [TrustIrInstId(10), TrustIrInstId(11), TrustIrInstId(12)] {
        assert!(entry.trust_ir_origins.contains(&origin));
        assert_eq!(provenance.get_mach_insts(origin), Some(&[mul][..]));
    }
    let transform = entry.transforms.last().expect("merge transform");
    assert_eq!(transform.pass, PassId::new("masked-umull-fuse"));
    assert_eq!(
        transform.kind,
        TransformKind::Merged {
            sources: vec![lhs_and, rhs_and, mul]
        }
    );
    assert!(provenance.get_entry(lhs_and).is_none());
    assert!(provenance.get_entry(rhs_and).is_none());
}

fn assert_masked_umull_bails(mut func: MachFunction, entry: BlockId) {
    let before = opcodes(&func, entry);
    assert!(!run_masked_umull_fuse(&mut func, None));
    assert_eq!(opcodes(&func, entry), before);
}

#[test]
fn masked_umull_bails_on_inexact_mask() {
    for masks in [(0xffff, LOW_WORD_MASK), (LOW_WORD_MASK, 0x7fff_ffff)] {
        let (func, entry, _) = masked_mul_func(masks.0, masks.1);
        assert_masked_umull_bails(func, entry);
    }
}

#[test]
fn masked_umull_bails_when_a_masked_value_has_an_extra_use() {
    let (mut func, entry, _) = masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
    push(
        &mut func,
        entry,
        MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                v(5, RegClass::Gpr64),
                v(2, RegClass::Gpr64),
                v(0, RegClass::Gpr64),
            ],
        ),
    );
    assert_masked_umull_bails(func, entry);
}

#[test]
fn masked_umull_bails_on_source_or_masked_temp_redefinition() {
    for redefine_masked_temp in [false, true] {
        let class = RegClass::Gpr64;
        let (mut func, entry) = new_func();
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![v(2, class), v(0, class), MachOperand::Imm(LOW_WORD_MASK)],
            ),
        );
        let redefined = if redefine_masked_temp { 2 } else { 0 };
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddRR,
                vec![v(redefined, class), v(6, class), v(7, class)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![v(3, class), v(1, class), MachOperand::Imm(LOW_WORD_MASK)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::MulRR,
                vec![v(4, class), v(2, class), v(3, class)],
            ),
        );
        assert_masked_umull_bails(func, entry);
    }
}

#[test]
fn masked_umull_bails_on_cross_block_producers() {
    let class = RegClass::Gpr64;
    let (mut func, entry) = new_func();
    let body = func.create_block();
    func.block_order.push(body);
    func.add_edge(entry, body);
    for (dst, src) in [(2, 0), (3, 1)] {
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![
                    v(dst, class),
                    v(src, class),
                    MachOperand::Imm(LOW_WORD_MASK),
                ],
            ),
        );
    }
    push(
        &mut func,
        body,
        MachInst::new(
            AArch64Opcode::MulRR,
            vec![v(4, class), v(2, class), v(3, class)],
        ),
    );
    let before_entry = opcodes(&func, entry);
    let before_body = opcodes(&func, body);
    assert!(!run_masked_umull_fuse(&mut func, None));
    assert_eq!(opcodes(&func, entry), before_entry);
    assert_eq!(opcodes(&func, body), before_body);
}

#[test]
fn masked_umull_bails_on_wrong_width_and_same_masked_operand() {
    let class = RegClass::Gpr32;
    let (mut func, entry) = new_func();
    for (dst, src) in [(2, 0), (3, 1)] {
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![
                    v(dst, class),
                    v(src, class),
                    MachOperand::Imm(LOW_WORD_MASK),
                ],
            ),
        );
    }
    push(
        &mut func,
        entry,
        MachInst::new(
            AArch64Opcode::MulRR,
            vec![v(4, class), v(2, class), v(3, class)],
        ),
    );
    assert_masked_umull_bails(func, entry);

    let (mut func, entry, [_, rhs_and, mul]) = masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
    func.inst_mut(mul).operands[2] = v(2, RegClass::Gpr64);
    // Remove the now-dead second producer from the live list so the rejection
    // specifically exercises the same-masked-operand admission guard.
    func.block_mut(entry).insts.retain(|&id| id != rhs_and);
    assert_masked_umull_bails(func, entry);
}

#[test]
fn masked_umull_bails_on_tied_and_source() {
    let (mut func, entry, [lhs_and, _, _]) = masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
    func.inst_mut(lhs_and).operands[1] = v(2, RegClass::Gpr64);
    assert_masked_umull_bails(func, entry);
}

#[test]
fn masked_umull_has_a_narrow_kill_switch() {
    let (mut func, entry, _) = masked_mul_func(LOW_WORD_MASK, LOW_WORD_MASK);
    crate::env_lock::with_env_overrides(&[("TCG_NO_MASKED_UMULL_FUSE", "1")], || {
        let mut pass = MulShiftReduce;
        assert!(!pass.run(&mut func));
    });
    assert_eq!(
        opcodes(&func, entry),
        vec![
            AArch64Opcode::AndRI,
            AArch64Opcode::AndRI,
            AArch64Opcode::MulRR
        ]
    );
}

// ---------------------------------------------------------------------------
// BAIL controls — the multiply MUST survive unchanged.
// ---------------------------------------------------------------------------

fn assert_bails(build: impl FnOnce(&mut MachFunction, BlockId)) {
    let (mut func, entry) = new_func();
    build(&mut func, entry);
    func.next_vreg = 1000;
    let before = opcodes(&func, entry);
    let mut pass = MulShiftReduce;
    let changed = pass.run(&mut func);
    assert!(!changed, "pass must not fire");
    assert_eq!(opcodes(&func, entry), before, "block must be unchanged");
}

#[test]
fn bails_on_three_term_constant_11() {
    let class = RegClass::Gpr64;
    assert_bails(|func, e| {
        emit_const(func, e, v(1, class), 11);
        push(
            func,
            e,
            MachInst::new(
                AArch64Opcode::MulRR,
                vec![v(3, class), v(0, class), v(1, class)],
            ),
        );
    });
}

#[test]
fn bails_on_three_term_constant_13() {
    let class = RegClass::Gpr64;
    assert_bails(|func, e| {
        emit_const(func, e, v(1, class), 13);
        push(
            func,
            e,
            MachInst::new(
                AArch64Opcode::MulRR,
                vec![v(3, class), v(0, class), v(1, class)],
            ),
        );
    });
}

#[test]
fn bails_when_multiplier_is_runtime_value() {
    // The multiplier v1 is produced by an ADD, not a constant materialization.
    let class = RegClass::Gpr64;
    assert_bails(|func, e| {
        push(
            func,
            e,
            MachInst::new(
                AArch64Opcode::AddRR,
                vec![v(1, class), v(4, class), v(5, class)],
            ),
        );
        push(
            func,
            e,
            MachInst::new(
                AArch64Opcode::MulRR,
                vec![v(3, class), v(0, class), v(1, class)],
            ),
        );
    });
}

#[test]
fn bails_when_neither_operand_is_constant() {
    // Both multiply operands are plain (undefined) registers.
    let class = RegClass::Gpr64;
    assert_bails(|func, e| {
        push(
            func,
            e,
            MachInst::new(
                AArch64Opcode::MulRR,
                vec![v(3, class), v(0, class), v(1, class)],
            ),
        );
    });
}

#[test]
fn bails_on_ambiguous_two_reaching_defs() {
    // Two different Movz values reach the multiply on merging paths → the sound
    // reaching-const query returns None → BAIL (no miscompile of the wrong K).
    let class = RegClass::Gpr64;
    let (mut func, entry) = new_func();
    let (b1, b2, b3) = (
        func.create_block(),
        func.create_block(),
        func.create_block(),
    );
    func.block_order = vec![entry, b1, b2, b3];
    func.add_edge(entry, b1);
    func.add_edge(entry, b2);
    func.add_edge(b1, b3);
    func.add_edge(b2, b3);
    emit_const(&mut func, b1, v(1, class), 3);
    push(
        &mut func,
        b1,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(b3)]),
    );
    emit_const(&mut func, b2, v(1, class), 5);
    push(
        &mut func,
        b2,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(b3)]),
    );
    push(
        &mut func,
        b3,
        MachInst::new(
            AArch64Opcode::MulRR,
            vec![v(3, class), v(0, class), v(1, class)],
        ),
    );
    func.next_vreg = 1000;
    let before = opcodes(&func, b3);
    let mut pass = MulShiftReduce;
    assert!(!pass.run(&mut func), "ambiguous constant must bail");
    assert_eq!(opcodes(&func, b3), before);
}

/// Materialize `value` (at `class`'s width) into `dst` as isel does: one
/// `Movz`/`Movn` when it fits, else `Movz` of the low half then a `Movk` for
/// each nonzero higher half.
fn emit_wide_const(func: &mut MachFunction, block: BlockId, dst: MachOperand, value: i64) {
    let class = dst.as_vreg().expect("register destination").class;
    let bits = mask(value as u64, class.size_bits());
    let fits_movn = class.size_bits() == 64 && (!value) as u64 <= 0xFFFF;
    if bits <= 0xFFFF || fits_movn {
        emit_const(func, block, dst, value);
        return;
    }
    push(
        func,
        block,
        MachInst::new(
            AArch64Opcode::Movz,
            vec![dst.clone(), MachOperand::Imm((bits & 0xFFFF) as i64)],
        ),
    );
    for shift in (16..class.size_bits()).step_by(16) {
        let half = (bits >> shift) & 0xFFFF;
        if half != 0 {
            push(
                func,
                block,
                MachInst::new(
                    AArch64Opcode::Movk,
                    vec![
                        dst.clone(),
                        MachOperand::Imm(half as i64),
                        MachOperand::Imm(i64::from(shift)),
                    ],
                ),
            );
        }
    }
}

/// `y = p - q` computed in the block, then `dst = x*c + y` (`Madd`) at
/// `class`'s width: the p5_struct_acc shape `a = a*31 + (c ^ i)`, whose addend
/// is the late value. The rewrite must agree with the original on every
/// [`X_VECS`] input (the independent evaluator [`eval`]). Returns the
/// function, its block and the rewritten block's last instruction.
fn late_addend_madd_at(c: i64, class: RegClass) -> (MachFunction, BlockId, MachInst) {
    let (x, creg, y, dst, p, q) = (
        v(0, class),
        v(1, class),
        v(2, class),
        v(3, class),
        v(4, class),
        v(5, class),
    );
    let (mut func, entry) = new_func();
    emit_wide_const(&mut func, entry, creg.clone(), c);
    push(
        &mut func,
        entry,
        MachInst::new(AArch64Opcode::SubRR, vec![y.clone(), p, q]),
    );
    push(
        &mut func,
        entry,
        MachInst::new(AArch64Opcode::Madd, vec![dst, x, creg, y]),
    );
    func.next_vreg = 1000;
    let orig = func.clone();
    let width = class.size_bits();
    let inputs_for = |xv: u64| {
        let mut inputs = HashMap::default();
        inputs.insert(0u32, xv);
        inputs.insert(4u32, xv.rotate_left(13) ^ 0x5555);
        inputs.insert(5u32, xv.rotate_right(7));
        inputs
    };
    // The evaluator reads the materialized multiplier back as `c`.
    let probe = eval(&orig, entry, &inputs_for(1), width);
    assert_eq!(probe[&1], mask(c as u64, width), "c={c}: materialization");
    let mut pass = MulShiftReduce;
    assert!(pass.run(&mut func), "c={c} {class:?}");
    for &xv in &X_VECS {
        let inputs = inputs_for(xv);
        assert_eq!(
            eval(&func, entry, &inputs, width)[&3],
            eval(&orig, entry, &inputs, width)[&3],
            "c={c} {class:?} x={xv:#x}"
        );
    }
    let last = func.inst(*func.block(entry).insts.last().unwrap()).clone();
    (func, entry, last)
}

fn late_addend_madd(c: i64) -> (MachFunction, BlockId, MachInst) {
    late_addend_madd_at(c, RegClass::Gpr64)
}

/// Every multiplier `decompose` splits with a subtracted term at `width`.
/// Its two-term output is `±2^a ± 2^0` (the one-shift rule: the smaller
/// power is always `2^0`) with `a < width` and `|c| <= MAX_ABS_CONST`, so
/// enumerating `2^a - 1` and `1 - 2^a` and keeping those it decomposes with a
/// negative term is the whole set.
fn subtracting_constants(width: u32) -> Vec<i64> {
    let mut out = Vec::new();
    for a in 1..width {
        for c in [(1i128 << a) - 1, 1 - (1i128 << a)] {
            if decompose(c, width).is_some_and(|ts| ts.iter().any(|t| !t.positive)) {
                out.push(c as i64);
            }
        }
    }
    out
}

#[test]
fn late_addend_is_added_last_when_the_decomposition_subtracts() {
    // 31 = 2^5 - 1 and -3 = 1 - 2^2: `((x<<k) - x) + y`, one add after `y`.
    // 3 decomposes as 2 + 1 (no subtracted term), so `2^a - 1` starts at 7.
    let mut expected: Vec<i64> = (3..=20).map(|a| (1i64 << a) - 1).collect();
    expected.extend((2..=20).map(|a| 1 - (1i64 << a)));
    expected.sort_unstable();
    for (class, width) in [(RegClass::Gpr64, 64), (RegClass::Gpr32, 32)] {
        let mut constants = subtracting_constants(width);
        constants.sort_unstable();
        assert_eq!(constants, expected, "width {width}");
        for &c in &constants {
            let (_, _, last) = late_addend_madd_at(c, class);
            assert_eq!(last.opcode, AArch64Opcode::AddRR, "c={c} {class:?}");
            assert_eq!(last.operands[2], v(2, class), "c={c} {class:?}: y last");
        }
    }
}

#[test]
fn late_addend_keeps_the_two_power_plus_one_order() {
    // 17 = 2^4 + 1: no subtracted term, so the measured `m1_call_chain` order
    // (addend folded early, shift temp last) is kept.
    let (_, _, last) = late_addend_madd(17);
    assert_ne!(last.operands[2], v(2, RegClass::Gpr64));
}

#[test]
fn constant_addend_keeps_the_subtracting_order() {
    // A constant addend is ready early: `(y + (x<<5)) - x` as before.
    let class = RegClass::Gpr64;
    let (mut func, entry) = new_func();
    emit_const(&mut func, entry, v(1, class), 31);
    emit_const(&mut func, entry, v(2, class), 9);
    push(
        &mut func,
        entry,
        MachInst::new(
            AArch64Opcode::Madd,
            vec![v(3, class), v(0, class), v(1, class), v(2, class)],
        ),
    );
    func.next_vreg = 1000;
    assert!(MulShiftReduce.run(&mut func));
    let last = func.inst(*func.block(entry).insts.last().unwrap());
    assert_eq!(last.opcode, AArch64Opcode::SubRR);
}
