// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Regression checks over ordinary TrustIR comparison compiler output. These
//! checks exercise the existing final-byte and provenance boundaries; they do
//! not confer solver, replay, or certificate authority.

use super::*;
use crate::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest, SourceInstId};
use trust_cg_ir::{AArch64Opcode, InstId, MachFunction};
use trust_cg_lower::Function;
use trust_cg_verify::provenance_xcheck::{
    LirSourceIndex, ProvenanceMismatchKind, cross_check_inst,
};
use trust_ir::{ICmpOp, Inst, Module, Ty};
use trust_ir_build::ModuleBuilder;

const TARGETS: [&str; 2] = ["aarch64-unknown-linux-gnu", "aarch64-apple-darwin"];
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const CONDITIONS: [ICmpOp; 10] = [
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
];

fn source(ty: Ty, op: ICmpOp, immediate: Option<i128>) -> (Module, Function) {
    let mut builder = ModuleBuilder::new("final_core_predicate_bytes");
    let signature = builder.add_func_type(
        vec![ty.clone(); if immediate.is_some() { 1 } else { 2 }],
        vec![Ty::Bool],
    );
    let mut function = builder.function("compare", signature);
    let entry = function.create_block();
    let lhs = function.add_block_param(entry, ty.clone());
    let rhs = immediate
        .is_none()
        .then(|| function.add_block_param(entry, ty.clone()));
    function.switch_to_block(entry);
    let rhs = rhs.unwrap_or_else(|| function.iconst(ty.clone(), immediate.unwrap()));
    let result = function.icmp(op, ty, lhs, rhs);
    function.ret(vec![result]);
    function.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    (module, lir)
}

fn prepare(triple: &str, module: &Module, lir: &Function, level: OptLevel) -> MachFunction {
    Pipeline::new(PipelineConfig {
        opt_level: level,
        verify: false,
        target_triple: triple.into(),
        ..Default::default()
    })
    .prepare_function_with_metrics_for_sealed_core(lir, None, module, 0)
    .unwrap()
    .0
}

fn only_word(code: &[u8], mask: u32, value: u32) -> (usize, u32) {
    let (words, remainder) = code.as_chunks::<4>();
    assert!(remainder.is_empty());
    let found: Vec<_> = words
        .iter()
        .enumerate()
        .map(|(index, word)| (index * 4, u32::from_le_bytes(*word)))
        .filter(|(_, word)| word & mask == value)
        .collect();
    assert_eq!(found.len(), 1, "one actual instruction: {found:?}");
    found[0]
}

fn rejected_word(module: &Module, lir: &Function, code: &[u8], offset: usize, word: u32) {
    let mut changed = code.to_vec();
    changed[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
    assert_ne!(changed, code, "the mutation must change actual bytes");
    assert!(
        matches!(
            check_core_bytes(module, 0, lir, &changed, &FixupList::new()),
            Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
        ),
        "changed word {word:#010x} at byte {offset} must be rejected"
    );
}

#[test]
fn actual_core_predicate_bytes_bind_operands_width_condition_and_destination() {
    let mut cases = 0;
    for ty in [Ty::I32, Ty::I64] {
        for condition in CONDITIONS {
            let (module, lir) = source(ty.clone(), condition, None);
            for target in TARGETS {
                for level in LEVELS {
                    let machine = prepare(target, &module, &lir, level);
                    let (code, fixups, sites) =
                        encode_core_function(&module, 0, &lir, &machine).unwrap();
                    assert!(fixups.is_empty() && sites.is_empty());
                    // CMP register is SUBS with Rd = ZR and no shift. CSET is
                    // CSINC with both inputs ZR and the inverted condition.
                    let (cmp_offset, cmp) = only_word(&code, 0x7fe0fc1f, 0x6b00001f);
                    let (cset_offset, cset) = only_word(&code, 0x7fff0fe0, 0x1a9f07e0);
                    let lhs = (cmp >> 5) & 31;
                    let rhs = (cmp >> 16) & 31;
                    assert_ne!(lhs, rhs, "distinct ABI arguments must remain distinct");
                    rejected_word(
                        &module,
                        &lir,
                        &code,
                        cmp_offset,
                        (cmp & !(31 << 16)) | (lhs << 16),
                    );
                    rejected_word(&module, &lir, &code, cmp_offset, cmp ^ (1 << 31));
                    // Removing the producer must not retain initialized flags.
                    rejected_word(&module, &lir, &code, cmp_offset, 0xd503201f);
                    rejected_word(&module, &lir, &code, cset_offset, cset ^ (1 << 12));
                    rejected_word(&module, &lir, &code, cset_offset, cset ^ 1);
                    // A non-ZR CSINC input is not the source's canonical CSET.
                    rejected_word(&module, &lir, &code, cset_offset, cset ^ (1 << 5));
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 160);
}

#[test]
fn actual_core_predicate_bytes_bind_compare_immediates() {
    let mut cases = 0;
    for ty in [Ty::I32, Ty::I64] {
        for condition in [ICmpOp::Eq, ICmpOp::Slt, ICmpOp::Uge] {
            let (module, lir) = source(ty.clone(), condition, Some(13));
            for target in TARGETS {
                for level in LEVELS {
                    let machine = prepare(target, &module, &lir, level);
                    let (code, fixups, sites) =
                        encode_core_function(&module, 0, &lir, &machine).unwrap();
                    assert!(fixups.is_empty() && sites.is_empty());
                    let (offset, cmp) = only_word(&code, 0x7fc0001f, 0x7100001f);
                    assert_eq!((cmp >> 10) & 4095, 13);
                    rejected_word(&module, &lir, &code, offset, cmp ^ (1 << 10));
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 48);
}

#[test]
fn final_core_predicate_bytes_recheck_source_identity_and_condition() {
    let (module, lir) = source(Ty::I64, ICmpOp::Slt, None);
    let machine = prepare(TARGETS[0], &module, &lir, OptLevel::O2);
    let (code, _, _) = encode_core_function(&module, 0, &lir, &machine).unwrap();
    assert!(matches!(
        check_core_bytes(&module, 1, &lir, &code, &FixupList::new()),
        Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
    ));

    let mut changed_lir = lir.clone();
    let comparison = changed_lir
        .blocks
        .get_mut(&changed_lir.entry_block)
        .unwrap()
        .instructions
        .iter_mut()
        .find(|inst| {
            matches!(
                inst.opcode,
                trust_cg_lower::instructions::Opcode::Icmp { .. }
            )
        })
        .unwrap();
    comparison.opcode = trust_cg_lower::instructions::Opcode::Icmp {
        cond: trust_cg_lower::instructions::IntCC::SignedGreaterThan,
    };
    assert!(matches!(
        check_core_bytes(&module, 0, &changed_lir, &code, &FixupList::new()),
        Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
    ));

    let mut changed_module = module.clone();
    let Inst::ICmp { op, .. } = &mut changed_module.functions[0].blocks[0].body[0].inst else {
        panic!("comparison source fixture");
    };
    *op = ICmpOp::Sgt;
    assert!(matches!(
        check_core_bytes(&changed_module, 0, &lir, &code, &FixupList::new()),
        Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
    ));
    let mut renamed_module = module;
    renamed_module.functions[0].name = "different_source".into();
    assert!(matches!(
        check_core_bytes(&renamed_module, 0, &lir, &code, &FixupList::new()),
        Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
    ));
}

#[test]
fn actual_cmp_cset_source_stamps_are_checked_separately_from_bytes() {
    for ty in [Ty::I32, Ty::I64] {
        let (module, lir) = source(ty, ICmpOp::Slt, None);
        let index = LirSourceIndex::build(&lir);
        for target in TARGETS {
            for level in LEVELS {
                let machine = prepare(target, &module, &lir, level);
                let (code, _, _) = encode_core_function(&module, 0, &lir, &machine).unwrap();
                for opcode in [AArch64Opcode::CmpRR, AArch64Opcode::CSet] {
                    let ordinal = machine
                        .insts
                        .iter()
                        .position(|i| i.opcode == opcode)
                        .unwrap();
                    let instruction = InstId(ordinal as u32);
                    let stamp = machine.inst_lowering_provenance(instruction);
                    let LoweringProvenance::SourceInst {
                        id,
                        digest,
                        trust_ir_inst,
                    } = stamp
                    else {
                        panic!("actual {opcode:?} must retain its source stamp");
                    };
                    assert!(cross_check_inst(&stamp, None, "comparison", &index).is_none());
                    for (stale, expected) in [
                        (
                            LoweringProvenance::SourceInst {
                                id,
                                digest: SourceInstDigest(digest.0 ^ 1),
                                trust_ir_inst,
                            },
                            ProvenanceMismatchKind::DigestMismatch,
                        ),
                        (
                            LoweringProvenance::SourceInst {
                                id: SourceInstId {
                                    block: u32::MAX,
                                    index: u32::MAX,
                                },
                                digest,
                                trust_ir_inst,
                            },
                            ProvenanceMismatchKind::DanglingSourceId,
                        ),
                    ] {
                        let mut changed = machine.clone();
                        changed.set_inst_lowering_provenance(instruction, stale);
                        let (unchanged_bytes, _, _) =
                            encode_function_with_fixups_and_sites(&changed).unwrap();
                        assert_eq!(unchanged_bytes, code, "stamps cannot change emission");
                        let mismatch = cross_check_inst(
                            &changed.inst_lowering_provenance(instruction),
                            None,
                            "comparison",
                            &index,
                        )
                        .expect("TV-2 must reject stale source attribution even without OpClass");
                        assert_eq!(mismatch.kind, expected);
                    }
                }
            }
        }
    }
}
