// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Actual ordinary Core comparison-driven selects through allocation/emission.
//! These source/byte and provenance controls confer no solver or proof credit.

use super::*;
use crate::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest, SourceInstId};
use trust_cg_ir::{AArch64Opcode as M, MachFunction};
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

fn source(ty: Ty, condition: ICmpOp) -> (Module, Function) {
    let mut builder = ModuleBuilder::new("allocated_core_select_bytes");
    let signature = builder.add_func_type(vec![ty.clone(); 4], vec![ty.clone()]);
    let mut function = builder.function("choose_four_arguments", signature);
    let entry = function.create_block();
    let args: Vec<_> = (0..4)
        .map(|_| function.add_block_param(entry, ty.clone()))
        .collect();
    function.switch_to_block(entry);
    let condition = function.icmp(condition, ty.clone(), args[0], args[1]);
    let result = function.select(ty, condition, args[2], args[3]);
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

fn prepare(target: &str, module: &Module, lir: &Function, level: OptLevel) -> MachFunction {
    Pipeline::new(PipelineConfig {
        opt_level: level,
        verify: false,
        target_triple: target.into(),
        ..Default::default()
    })
    .prepare_function_with_metrics_for_sealed_core(lir, None, module, 0)
    .unwrap()
    .0
}

fn words(code: &[u8]) -> Vec<(usize, u32)> {
    let (words, remainder) = code.as_chunks::<4>();
    assert!(remainder.is_empty());
    words
        .iter()
        .enumerate()
        .map(|(index, word)| (index * 4, u32::from_le_bytes(*word)))
        .collect()
}

fn cmp_register(word: u32) -> bool {
    word & 0x7fe0fc1f == 0x6b00001f
}

fn cmp_immediate(word: u32) -> bool {
    word & 0x7fc0001f == 0x7100001f
}

fn rejected(module: &Module, lir: &Function, code: &[u8], changed: &[u8]) {
    assert_ne!(changed, code, "control must change actual bytes");
    assert!(
        matches!(
            check_core_bytes(module, 0, lir, changed, &FixupList::new()),
            Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
        ),
        "changed actual select bytes must be rejected"
    );
}

fn rejected_word(module: &Module, lir: &Function, code: &[u8], offset: usize, word: u32) {
    let mut changed = code.to_vec();
    changed[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
    rejected(module, lir, code, &changed);
}

#[test]
fn actual_core_select_bytes_bind_comparison_arms_width_destination_and_latest_flags() {
    let mut cases = 0;
    for ty in [Ty::I32, Ty::I64] {
        for condition in CONDITIONS {
            let (module, lir) = source(ty.clone(), condition);
            for target in TARGETS {
                for level in LEVELS {
                    let machine = prepare(target, &module, &lir, level);
                    let (code, fixups, sites) =
                        encode_core_function(&module, 0, &lir, &machine).unwrap();
                    assert!(fixups.is_empty() && sites.is_empty());
                    let words = words(&code);
                    // A plain select with independent variable arms must emit
                    // CSEL. Do not confuse CSET's CSINC alias with this site.
                    let selects: Vec<_> = words
                        .iter()
                        .copied()
                        .filter(|(_, word)| word & 0x7fe00c00 == 0x1a800000)
                        .collect();
                    let [(select_offset, select)] = selects.as_slice() else {
                        panic!(
                            "one actual variable-arm CSEL: {ty:?}/{condition:?}/{target}/{level:?}: {words:?}"
                        );
                    };
                    let (select_offset, select) = (*select_offset, *select);
                    let comparisons: Vec<_> = words
                        .iter()
                        .copied()
                        .filter(|(offset, word)| *offset < select_offset && cmp_register(*word))
                        .collect();
                    let [(cmp_offset, cmp)] = comparisons.as_slice() else {
                        panic!("one actual source comparison: {words:?}");
                    };
                    let (cmp_offset, cmp) = (*cmp_offset, *cmp);
                    let lhs = (cmp >> 5) & 31;
                    let rhs = (cmp >> 16) & 31;
                    assert_ne!(lhs, rhs);
                    let then_arm = (select >> 5) & 31;
                    let else_arm = (select >> 16) & 31;
                    assert_ne!(then_arm, else_arm);
                    assert_eq!(select >> 31, u32::from(ty == Ty::I64));
                    assert_eq!(cmp >> 31, select >> 31);
                    // A materialized predicate has CSET, then CMP selector,#0;
                    // a folded predicate reaches CSEL directly from CMP a,b.
                    let latest = words
                        .iter()
                        .rev()
                        .find(|(offset, word)| {
                            *offset < select_offset && (cmp_register(*word) || cmp_immediate(*word))
                        })
                        .unwrap();
                    let csets: Vec<_> = words
                        .iter()
                        .copied()
                        .filter(|(_, word)| word & 0x7fff0fe0 == 0x1a9f07e0)
                        .collect();
                    if csets.is_empty() {
                        assert_eq!(*latest, (cmp_offset, cmp));
                    } else {
                        let [(offset, cset)] = csets.as_slice() else {
                            panic!("one materialized canonical predicate: {words:?}");
                        };
                        assert!(cmp_offset < *offset && *offset < latest.0);
                        assert!(cmp_immediate(latest.1));
                        assert_eq!((latest.1 >> 10) & 4095, 0);
                        rejected_word(&module, &lir, &code, *offset, *cset ^ (1 << 12));
                        rejected_word(&module, &lir, &code, *offset, *cset ^ 1);
                    }
                    rejected_word(
                        &module,
                        &lir,
                        &code,
                        cmp_offset,
                        (cmp & !(31 << 16)) | (lhs << 16),
                    );
                    rejected_word(&module, &lir, &code, cmp_offset, cmp ^ (1 << 31));
                    rejected_word(&module, &lir, &code, cmp_offset, 0xd503201f);
                    for wrong in [
                        (select & !(31 << 5)) | (else_arm << 5),
                        (select & !(31 << 16)) | (then_arm << 16),
                        select ^ (1 << 12),
                        select ^ (1 << 31),
                        select ^ 1,
                        select | (1 << 10),             // CSINC false arm +1
                        select | (1 << 30),             // CSINV false arm NOT
                        select | (1 << 30) | (1 << 10), // CSNEG false arm -value
                    ] {
                        rejected_word(&module, &lir, &code, select_offset, wrong);
                    }
                    // Insert a genuine new flag producer immediately before
                    // CSEL: CMP arm,arm replaces NZCV with a constant outcome.
                    // Reusing the earlier source comparison must not pass.
                    let clobber = (if select >> 31 == 0 {
                        0x6b00001f
                    } else {
                        0xeb00001f
                    }) | (then_arm << 5)
                        | (then_arm << 16);
                    let mut changed = code.clone();
                    drop(changed.splice(select_offset..select_offset, clobber.to_le_bytes()));
                    rejected(&module, &lir, &code, &changed);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 160);
}

#[test]
fn actual_core_select_bytes_recheck_exact_core_lir_identity_and_source_operands() {
    use trust_cg_lower::instructions::{IntCC, Opcode as L};
    for ty in [Ty::I32, Ty::I64] {
        let (module, lir) = source(ty, ICmpOp::Slt);
        for target in TARGETS {
            for level in LEVELS {
                let machine = prepare(target, &module, &lir, level);
                let (code, _, _) = encode_core_function(&module, 0, &lir, &machine).unwrap();
                let refuses = |module: &Module, ordinal: usize, lir: &Function| {
                    assert!(matches!(
                        check_core_bytes(module, ordinal, lir, &code, &FixupList::new()),
                        Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
                    ));
                };
                refuses(&module, 1, &lir);
                let mut renamed = module.clone();
                renamed.functions[0].name = "another_select_source".into();
                refuses(&renamed, 0, &lir);
                for comparison in [true, false] {
                    let mut changed = module.clone();
                    for node in &mut changed.functions[0].blocks[0].body {
                        match &mut node.inst {
                            Inst::ICmp { op, .. } if comparison => *op = ICmpOp::Sgt,
                            Inst::Select {
                                then_val, else_val, ..
                            } if !comparison => {
                                std::mem::swap(then_val, else_val);
                            }
                            _ => {}
                        }
                    }
                    refuses(&changed, 0, &lir);
                    let mut changed = lir.clone();
                    for inst in &mut changed
                        .blocks
                        .get_mut(&changed.entry_block)
                        .unwrap()
                        .instructions
                    {
                        match &mut inst.opcode {
                            L::Icmp { cond } if comparison => *cond = IntCC::SignedGreaterThan,
                            L::Select { cond } if !comparison => *cond = IntCC::Equal,
                            _ => {}
                        }
                    }
                    refuses(&module, 0, &changed);
                }
            }
        }
    }
}

#[test]
fn actual_cmp_select_source_stamps_cannot_be_forged_without_changing_bytes() {
    for ty in [Ty::I32, Ty::I64] {
        let (module, lir) = source(ty, ICmpOp::Uge);
        let index = LirSourceIndex::build(&lir);
        for target in TARGETS {
            for level in LEVELS {
                let machine = prepare(target, &module, &lir, level);
                let (code, _, _) = encode_core_function(&module, 0, &lir, &machine).unwrap();
                let mut select_seen = false;
                let mut comparison_seen = false;
                for id in machine
                    .blocks
                    .iter()
                    .flat_map(|block| block.insts.iter())
                    .copied()
                {
                    let opcode = machine.insts[id.0 as usize].opcode;
                    if !matches!(opcode, M::CmpRR | M::CmpRI | M::CSet | M::Csel) {
                        continue;
                    }
                    select_seen |= opcode == M::Csel;
                    comparison_seen |= opcode == M::CmpRR;
                    let stamp = machine.inst_lowering_provenance(id);
                    let LoweringProvenance::SourceInst {
                        id: source,
                        digest,
                        trust_ir_inst,
                    } = stamp
                    else {
                        panic!("actual {opcode:?} must keep its source stamp");
                    };
                    assert!(cross_check_inst(&stamp, None, "select", &index).is_none());
                    for (stale, expected) in [
                        (
                            LoweringProvenance::SourceInst {
                                id: source,
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
                        changed.set_inst_lowering_provenance(id, stale);
                        let (unchanged, _, _) =
                            encode_function_with_fixups_and_sites(&changed).unwrap();
                        assert_eq!(unchanged, code);
                        let mismatch = cross_check_inst(
                            &changed.inst_lowering_provenance(id),
                            None,
                            "select",
                            &index,
                        )
                        .expect("stale source stamp must refuse without OpClass");
                        assert_eq!(mismatch.kind, expected);
                    }
                }
                assert!(select_seen && comparison_seen);
            }
        }
    }
}
