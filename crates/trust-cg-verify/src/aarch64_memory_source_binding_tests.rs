// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Source-bound memory rows: the frame-record contract is the frame theorem's
//! record, every binding refuses a wrong slot, operand, width or direction,
//! receipts are bound to the exact query they judged, and the walk never
//! credits a bound row without a Clean-checked certificate of every part.

use super::*;
use crate::function_verifier::InstructionVerificationResult;
use crate::provenance_xcheck::ProvenanceXCheckMode;
use crate::source_bound_frame::memory_leaf::tests::{chase, copy64, imm, load64, swap64, w, x};
use crate::source_bound_frame::{source_bound_frame, source_bound_memory_leaf};
use crate::{FunctionVerifier, VerificationConfig};
use trust_cg_ir::regs::X1;
use trust_cg_ir::{AArch64Opcode as M, MachOperand as O, SpecialReg};

fn sp() -> O {
    O::Special(SpecialReg::SP)
}

fn access(opcode: M, operands: Vec<O>) -> MemoryAccess {
    memory_access(&MachInst::new(opcode, operands)).expect("an admitted access")
}

#[test]
fn the_frame_record_contract_is_the_frame_theorem_record() {
    let save = ContractAccess::frame_record(FrameEnvelopeRole::Save).unwrap();
    let restore = ContractAccess::frame_record(FrameEnvelopeRole::Restore).unwrap();
    assert!(ContractAccess::frame_record(FrameEnvelopeRole::Establish).is_none());
    assert_eq!(
        save,
        ContractAccess {
            load: false,
            pair: Some(PairMode::PreIndex),
            simd: false,
            bytes: 8,
            offset: -16,
            transfer: [29, 30],
            zero: [false, false],
            base: 31,
        }
    );
    assert_eq!(
        restore,
        ContractAccess {
            load: true,
            pair: Some(PairMode::PostIndex),
            offset: 16,
            ..save
        }
    );
    // The envelope the frame owner admits names exactly these accesses.
    save.check(&access(M::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)]))
        .unwrap();
    restore
        .check(&access(M::LdpPostIndex, vec![x(29), x(30), sp(), imm(16)]))
        .unwrap();
    // The theorem's constants: the record is sixteen bytes below the entry
    // SP, LR one eight-byte lane above FP.
    assert_eq!((FRAME_RECORD_BYTES, FRAME_RECORD_LANE_BYTES), (16, 8));
}

/// A frame pair bound to the wrong slot, without writeback, with its
/// registers swapped, through another base or in the other direction: each
/// is refused by the field it gets wrong.
#[test]
fn a_frame_pair_bound_to_the_wrong_slot_or_shape_is_refused() {
    use MemoryBindingRefusal as R;
    let save = ContractAccess::frame_record(FrameEnvelopeRole::Save).unwrap();
    let restore = ContractAccess::frame_record(FrameEnvelopeRole::Restore).unwrap();
    let cases: [(ContractAccess, M, Vec<O>, R); 7] = [
        (
            save,
            M::StpPreIndex,
            vec![x(29), x(30), sp(), imm(-32)],
            R::Slot {
                contract: -16,
                machine: -32,
            },
        ),
        (
            restore,
            M::LdpPostIndex,
            vec![x(29), x(30), sp(), imm(32)],
            R::Slot {
                contract: 16,
                machine: 32,
            },
        ),
        (
            save,
            M::StpRI,
            vec![x(29), x(30), sp(), imm(-16)],
            R::Form {
                contract: "Some(PreIndex)".into(),
                machine: "Pair(Offset)".into(),
            },
        ),
        (
            save,
            M::StpPreIndex,
            vec![x(30), x(29), sp(), imm(-16)],
            R::Data {
                lane: 0,
                contract: 29,
                machine: 30,
            },
        ),
        (
            save,
            M::StpPreIndex,
            vec![x(29), x(30), x(1), imm(-16)],
            R::Base {
                contract: 31,
                machine: 1,
            },
        ),
        (
            save,
            M::LdpPostIndex,
            vec![x(29), x(30), sp(), imm(16)],
            R::Direction {
                contract_load: false,
            },
        ),
        (
            restore,
            M::LdpPostIndex,
            vec![x(19), x(20), sp(), imm(16)],
            R::Data {
                lane: 0,
                contract: 29,
                machine: 19,
            },
        ),
    ];
    for (contract, opcode, operands, expected) in cases {
        let inst = MachInst::new(opcode, operands);
        assert_eq!(
            contract.check(&memory_access(&inst).unwrap()),
            Err(expected.clone()),
            "{inst:?}"
        );
        let refused = SourceBoundMemoryRow::bind(
            &inst,
            InstId(0),
            contract,
            MemoryRowBinding::FrameRecord {
                role: FrameEnvelopeRole::Save,
            },
        )
        .expect_err("a wrong record never binds");
        assert_eq!(refused, expected);
    }
}

#[test]
fn the_frame_owner_binds_exactly_its_two_records() {
    let (source, machine) = crate::source_bound_alu::tests::fixture(64, M::AddRR, O::PReg(X1));
    let frame = source_bound_frame(&source, &machine).expect("a checked leaf frame");
    for (id, role, word) in [
        (0, FrameEnvelopeRole::Save, 0xa9bf_7bfd),
        (3, FrameEnvelopeRole::Restore, 0xa8c1_7bfd),
    ] {
        let row = SourceBoundMemoryRow::bind_frame_record(&frame, InstId(id)).unwrap();
        assert_eq!(row.binding(), MemoryRowBinding::FrameRecord { role });
        assert_eq!(row.word(), word, "{role}: clang's word");
        assert_eq!(
            row.parts().len(),
            6,
            "fields, two addresses, writeback, two lanes"
        );
        assert_eq!(row.contract(), &ContractAccess::frame_record(role).unwrap());
        let decided = row.decide(&VerificationConfig::default()).unwrap();
        assert_eq!((decided.exact, decided.undecided), (6, None));
    }
    // The parts a formal sidecar exports beside the frame theorem are
    // exactly the parts the walk replays for these two records.
    let walked: Vec<ProofObligation> = [0, 3]
        .into_iter()
        .flat_map(|id| {
            SourceBoundMemoryRow::bind_frame_record(&frame, InstId(id))
                .unwrap()
                .parts()
                .iter()
                .map(|part| part.obligation().clone())
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(frame_record_part_obligations(), walked);
    // The establishing ADD, the body, the return and no instruction at all
    // are not frame records.
    for id in [1, 2, 4, 99] {
        assert_eq!(
            SourceBoundMemoryRow::bind_frame_record(&frame, InstId(id)).unwrap_err(),
            MemoryBindingRefusal::NotOwned,
            "instruction {id}"
        );
    }
}

#[test]
fn leaf_accesses_bind_to_their_source_access() {
    let (source, machine) = swap64();
    let leaf = source_bound_memory_leaf(&source, &machine).unwrap();
    for (position, access) in leaf.accesses().iter().enumerate() {
        let row = SourceBoundMemoryRow::bind_leaf_access(&leaf, access.instruction).unwrap();
        assert_eq!(
            row.binding(),
            MemoryRowBinding::LeafAccess {
                block: 0,
                source_index: position,
                position,
            }
        );
        assert_eq!(row.parts().len(), 3, "fields, address, one lane");
        assert!(
            row.proof_name().ends_with(&format!(
                "bound to source access {position}, LIR instruction lir0.{position}"
            )),
            "{}",
            row.proof_name()
        );
        assert_eq!(
            row.decide(&VerificationConfig::default())
                .unwrap()
                .undecided,
            None
        );
    }
    assert_eq!(
        SourceBoundMemoryRow::bind_leaf_access(&leaf, InstId(4)).unwrap_err(),
        MemoryBindingRefusal::NotOwned,
        "the return is no access"
    );
}

/// A load bound to another source access's operands (its base, its data
/// register, its width, its slot or its direction) is refused.
#[test]
fn a_load_bound_to_the_wrong_source_operand_or_width_is_refused() {
    use MemoryBindingRefusal as R;
    let (source, machine) = swap64();
    let leaf = source_bound_memory_leaf(&source, &machine).unwrap();
    let first = &machine.insts[0]; // ldr x2, [x0]: the source's load of `a`
    let second = leaf.accesses()[1].contract; // the load of `b`: base x1, data x3
    let bind = |contract| {
        SourceBoundMemoryRow::bind(
            first,
            InstId(0),
            contract,
            MemoryRowBinding::LeafAccess {
                block: 0,
                source_index: 0,
                position: 0,
            },
        )
        .map(|_| ())
    };
    let own = leaf.accesses()[0].contract;
    assert_eq!(bind(own), Ok(()));
    assert_eq!(
        bind(second),
        Err(R::Base {
            contract: 1,
            machine: 0
        })
    );
    assert_eq!(
        bind(ContractAccess {
            transfer: [3, 3],
            ..own
        }),
        Err(R::Data {
            lane: 0,
            contract: 3,
            machine: 2
        })
    );
    assert_eq!(
        bind(ContractAccess { bytes: 4, ..own }),
        Err(R::Width {
            contract: 4,
            machine: 8
        })
    );
    assert_eq!(
        bind(ContractAccess { offset: 8, ..own }),
        Err(R::Slot {
            contract: 8,
            machine: 0
        })
    );
    assert_eq!(
        bind(ContractAccess { load: false, ..own }),
        Err(R::Direction {
            contract_load: false
        })
    );
    // A sign-extending load names no access this route binds.
    let ldrsh = MachInst::new(M::LdrshRI, vec![w(1), x(0), imm(0)]);
    assert_eq!(
        SourceBoundMemoryRow::bind(
            &ldrsh,
            InstId(0),
            ContractAccess::scalar(true, 2, 0, 0, 1, false),
            MemoryRowBinding::LeafAccess {
                block: 0,
                source_index: 0,
                position: 0
            },
        )
        .unwrap_err(),
        R::NotAdmitted
    );
}

fn valid(row: &SourceBoundMemoryRow<'_>) -> Vec<PartReceipt> {
    row.parts()
        .iter()
        .map(|part| PartReceipt::of(part, Some(VerificationResult::Valid), None))
        .collect()
}

/// A receipt is bound to the exact query it judged: receipts minted for one
/// word (here `ldr x0, [x1, #8]`) never credit another (`ldr x1, [x0]`),
/// nor do receipts in another order or for fewer parts.
#[test]
fn a_stale_or_foreign_certificate_receipt_is_refused() {
    let (source_a, machine_a) = chase();
    let leaf_a = source_bound_memory_leaf(&source_a, &machine_a).unwrap();
    let first = SourceBoundMemoryRow::bind_leaf_access(&leaf_a, InstId(0)).unwrap();
    let second = SourceBoundMemoryRow::bind_leaf_access(&leaf_a, InstId(1)).unwrap();
    assert_eq!(first.credit(&valid(&first)), MemoryCredit::Checked);
    assert_eq!(second.credit(&valid(&second)), MemoryCredit::Checked);
    assert_eq!(
        first.credit(&valid(&second)),
        MemoryCredit::Foreign {
            index: 0,
            why: "a receipt judged another query (a stale or foreign certificate)"
        }
    );
    // The same access shape in another function: the same word, so the same
    // queries. A receipt is about the query, and the query is the word's;
    // the binding, not the receipt, ties the row to its source.
    let (source_b, machine_b) = load64();
    let leaf_b = source_bound_memory_leaf(&source_b, &machine_b).unwrap();
    let other = SourceBoundMemoryRow::bind_leaf_access(&leaf_b, InstId(0)).unwrap();
    assert_eq!(other.word(), first.word());
    assert_eq!(other.credit(&valid(&first)), MemoryCredit::Checked);
    // Fewer receipts than parts, and receipts in another order.
    let mut receipts = valid(&first);
    receipts.pop();
    assert_eq!(
        first.credit(&receipts),
        MemoryCredit::Foreign {
            index: 2,
            why: "the receipts do not cover exactly this row's parts"
        }
    );
    let mut receipts = valid(&first);
    receipts.swap(0, 1);
    assert_eq!(
        first.credit(&receipts),
        MemoryCredit::Foreign {
            index: 0,
            why: "a receipt judged another part"
        }
    );
}

#[test]
fn a_counterexample_fails_and_a_missing_certificate_is_named() {
    let (source, machine) = copy64();
    let leaf = source_bound_memory_leaf(&source, &machine).unwrap();
    let row = SourceBoundMemoryRow::bind_leaf_access(&leaf, InstId(1)).unwrap();
    let parts = row.parts();
    let refuted = vec![
        PartReceipt::of(&parts[0], Some(VerificationResult::Valid), None),
        PartReceipt::of(
            &parts[1],
            Some(VerificationResult::Invalid {
                counterexample: "base = 0x10".into(),
            }),
            None,
        ),
        PartReceipt::of(&parts[2], None, Some("not replayed".into())),
    ];
    assert_eq!(
        row.credit(&refuted),
        MemoryCredit::Refuted {
            part: parts[1].obligation().name.clone(),
            counterexample: "base = 0x10".into()
        }
    );
    let missing = vec![
        PartReceipt::of(&parts[0], Some(VerificationResult::Valid), None),
        PartReceipt::of(
            &parts[1],
            None,
            Some("AY Unknown(incomplete self-check-rejected) /private/tmp/q.smt2".into()),
        ),
        PartReceipt::of(&parts[2], None, Some("not replayed".into())),
    ];
    let credit = row.credit(&missing);
    assert_eq!(
        credit,
        MemoryCredit::Partial {
            checked: 1,
            first: MemoryEffectPart::Address { lane: 0 },
            why: "AY Unknown(incomplete self-check-rejected)".into()
        }
    );
    assert_eq!(
        credit.uncredited_clause(3).unwrap(),
        "1 of 3 parts have a Clean-checked certificate; the first without one is `address lane \
         0` (AY Unknown(incomplete self-check-rejected))"
    );
}

/// Through the walk, with no live replay, a bound leaf access is never
/// credited: it keeps its lane's reason and names the source binding and the
/// first part without a certificate. The Formal-only rule's certificates are
/// disabled here so the row reaches this route on every host.
#[test]
fn the_walk_never_credits_a_bound_access_without_checked_parts() {
    crate::env_lock::with_env_overrides(
        &[("TCG_REFINE_SOLVER", "0"), ("TCG_CANARY_NO_CACHE", "1")],
        || {
            let (source, machine) = copy64();
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let captured = verifier.verify_with_request(&machine, Some(&source), &request);
            let report = captured.report();
            assert!(report.precondition_failure.is_none());
            for (index, position) in [(0, 0), (1, 1)] {
                let InstructionVerificationResult::Unverified { reason } =
                    &report.instructions[index].result
                else {
                    panic!("{:?}", report.instructions[index].result);
                };
                assert!(
                    reason.contains(&format!(
                        "; {SOURCE_BOUND_MEMORY_NOT_CREDITED}: `A64 memory effect"
                    )) && reason.contains(&format!(
                        "bound to source access {position}, LIR instruction lir0.{position}; \
                         holds in process: all 3 parts exactly; 0 of 3 parts have a \
                         Clean-checked certificate; the first without one is `fields` (replay \
                         refused: TCG_REFINE_SOLVER=0)"
                    )),
                    "{reason}"
                );
            }
            assert!(!report.emitted_opcode_inventory().is_promotable());
            // Under an evaluation-only policy nothing is bound or replayed:
            // the rows keep the ordinary memory-effect clause.
            let evaluation = FunctionVerifier::with_config(VerificationConfig::default())
                .verify_with_lir_source_and_mode(
                    &machine,
                    Some(&source),
                    ProvenanceXCheckMode::Enforce,
                );
            for row in &evaluation.instructions[..2] {
                let InstructionVerificationResult::Unverified { reason } = &row.result else {
                    panic!("{:?}", row.result);
                };
                assert!(
                    !reason.contains(SOURCE_BOUND_MEMORY_NOT_CREDITED),
                    "{reason}"
                );
            }
        },
    );
}

/// The frame records of a checked leaf keep the frame theorem's verdict when
/// it was not replayed: no part replay can stand in for the theorem.
#[test]
fn the_frame_records_keep_an_unreplayed_frame_theorem_verdict() {
    crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
        let (source, machine) = crate::source_bound_alu::tests::fixture(64, M::AddRR, O::PReg(X1));
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let captured = verifier.verify_with_request(&machine, Some(&source), &request);
        for index in [0, 3] {
            assert!(
                matches!(
                    &captured.report().instructions[index].result,
                    InstructionVerificationResult::Unverified { reason }
                        if reason == "source-bound frame needs independently replayed proof"
                ),
                "{:?}",
                captured.report().instructions[index].result
            );
        }
    });
}

/// A frame record is no longer credited by the frame theorem alone: with the
/// theorem replayed and checked but its parts unreplayed, the record stays
/// unverified and names how far its parts got. A theorem that failed keeps
/// its own verdict.
#[test]
fn a_frame_record_needs_its_parts_as_well_as_the_frame_theorem() {
    use crate::proof_database::ProofCategory;
    use crate::source_bound_frame::FRAME_OBLIGATION_NAME;
    crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
        let (source, machine) = crate::source_bound_alu::tests::fixture(64, M::AddRR, O::PReg(X1));
        let frame = source_bound_frame(&source, &machine).unwrap();
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
        let theorem = InstructionVerificationResult::Verified {
            proof_name: FRAME_OBLIGATION_NAME.into(),
            category: ProofCategory::FrameLayout,
            strength: VerificationStrength::Formal,
            degenerate: false,
        };
        let owned = std::cell::OnceCell::new();
        for (id, role, word) in [
            (0, "save", "StpPreIndex 0xa9bf7bfd"),
            (3, "restore", "LdpPostIndex 0xa8c17bfd"),
        ] {
            let row = verifier.frame_record_row(
                &frame,
                "arithmetic",
                id,
                InstId(id as u32),
                theorem.clone(),
                ProvenanceXCheckMode::Enforce,
                None,
                &owned,
            );
            let InstructionVerificationResult::Unverified { reason } = row else {
                panic!("{role}: {row:?}");
            };
            assert_eq!(
                reason,
                format!(
                    "{SOURCE_BOUND_MEMORY_NOT_CREDITED}: the frame theorem has a checked proof; \
                     `A64 memory effect {word}` bound to the source-bound frame's {role} record; \
                     holds in process: all 6 parts exactly; 0 of 6 parts have a Clean-checked \
                     certificate; the first without one is `fields` (replay refused: \
                     TCG_REFINE_SOLVER=0)"
                )
            );
            let failed = InstructionVerificationResult::Failed {
                proof_name: FRAME_OBLIGATION_NAME.into(),
                detail: "Unknown: incomplete".into(),
            };
            assert!(matches!(
                verifier.frame_record_row(
                    &frame,
                    "arithmetic",
                    id,
                    InstId(id as u32),
                    failed,
                    ProvenanceXCheckMode::Enforce,
                    None,
                    &owned,
                ),
                InstructionVerificationResult::Failed { detail, .. }
                    if detail == "Unknown: incomplete"
            ));
        }
    });
}

// ---------------------------------------------------------------------------
// With a capable AY and Clean (TRUST_CG_RUN_FORMAL_PROOF_TESTS=1)
// ---------------------------------------------------------------------------

/// The development AY and Clean the 2026-09-29 memory-effect record and the
/// source-bound JIT qualification name (an overlay pair; see
/// `reports/2026-10-01-darwin-memory-source-binding`).
const DEV_AY: (&str, &str) = (
    "$HOME/ay-worktrees/bin/ay-2657db47c-darwin-dev",
    "b37fa549fa0712cc6283f0675d029f2a802641d1c61c0a6a329ed69faae3a9a8",
);
const DEV_CLEAN: (&str, &str) = (
    "$HOME/clean-worktrees/bin/clean-ed21fee39-darwin-dev",
    "ad10bed671a8bf8110b3abefd4f72d6b13380ddba308aa1c58181867a03fac96",
);

fn dev_tools() -> Option<(std::path::PathBuf, std::path::PathBuf)> {
    if trust_cg_process_env::var("TRUST_CG_RUN_FORMAL_PROOF_TESTS").as_deref() != Ok("1") {
        eprintln!(
            "source-bound memory formal test not run: TRUST_CG_RUN_FORMAL_PROOF_TESTS is not 1"
        );
        return None;
    }
    let mut paths = Vec::new();
    for (path, digest) in [DEV_AY, DEV_CLEAN] {
        let path = std::path::PathBuf::from(path);
        if !path.is_file() || crate::ay_identity::test_fixtures::sha256_of(&path) != digest {
            eprintln!(
                "source-bound memory formal test not run: {} is not the recorded binary",
                path.display()
            );
            return None;
        }
        paths.push(path);
    }
    let clean = paths.pop()?;
    Some((paths.pop()?, clean))
}

/// With the development AY and Clean `ed21fee39` (admitted for this test by
/// digest, as the overlay admits them for a build), every bound access of the
/// leaves is credited at `Formal` under the source-bound memory proof name,
/// and a leaf whose only rows are those accesses and its return is
/// promotable; the frame records of a checked leaf frame are credited by the
/// frame theorem and their parts. The Formal-only rule's certificates are
/// disabled, so no row is credited by the form route here; a corrupted leaf
/// binds nothing and stays refused.
#[cfg(unix)]
#[test]
fn with_a_capable_ay_and_clean_bound_rows_are_credited_end_to_end() {
    let Some((ay, clean)) = dev_tools() else {
        return;
    };
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let cache = tempfile::tempdir().expect("scratch cache");
    trust_cg_process_env::with_env_edits(|env| {
        env.set("AY_SOLVER_PATH", &ay);
        env.set(
            crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV,
            crate::ay_identity::test_fixtures::declare(&[&ay]),
        );
        env.set("TCG_EXTERNAL_CLEAN_CHECKER", &clean);
        env.set("TCG_NO_SOLVER_SERVER", "1");
        env.set("TCG_NO_CERT_STORE", "1");
        env.set("TCG_NO_VERDICT_DB", "1");
        env.set("TCG_CANARY_NO_CACHE", "1");
        env.set("TCG_REFINE_SOLVER", "1");
        env.set("XDG_CACHE_HOME", cache.path());
        env.remove("TCG_NO_PROOF_CACHE");
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
        type Fixture = fn() -> (trust_cg_lower::Function, trust_cg_ir::MachFunction);
        let leaves: [(&str, Fixture, bool); 4] = [
            ("copy64", copy64, true),
            ("chase", chase, true),
            ("swap64", swap64, true),
            // `mov x0, x1` is an uncredited register copy (E0.2).
            ("load64", load64, false),
        ];
        for (name, fixture, promotable) in leaves {
            let (source, machine) = fixture();
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let captured = verifier.verify_with_request(&machine, Some(&source), &request);
            let report = captured.report();
            let mut credited = 0;
            for row in &report.instructions {
                let inst = &machine.insts[row.inst_index];
                if memory_access(inst).is_none() {
                    continue;
                }
                match &row.result {
                    InstructionVerificationResult::Verified {
                        proof_name,
                        strength: VerificationStrength::Formal,
                        degenerate: false,
                        ..
                    } if proof_name.starts_with(SOURCE_BOUND_MEMORY_PROOF_PREFIX) => credited += 1,
                    other => panic!("{name}: {inst:?}: {other:?}"),
                }
            }
            assert_eq!(
                credited,
                source_bound_memory_leaf(&source, &machine)
                    .unwrap()
                    .accesses()
                    .len(),
                "{name}"
            );
            assert_eq!(
                report.emitted_opcode_inventory().is_promotable(),
                promotable,
                "{name}: {report:?}"
            );
        }
        // A corrupted chase (the second load reads +16) binds nothing: its
        // memory rows keep their lanes and the function is refused.
        let (source, mut machine) = chase();
        machine.insts[1].operands[2] = imm(16);
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let report = verifier.verify_with_request(&machine, Some(&source), &request);
        assert!(!report.report().emitted_opcode_inventory().is_promotable());
        assert!(
            report.report().instructions[..2]
                .iter()
                .all(|row| !matches!(
                    &row.result,
                    InstructionVerificationResult::Verified { proof_name, .. }
                        if proof_name.starts_with(SOURCE_BOUND_MEMORY_PROOF_PREFIX)
                ))
        );
        // The frame records: the frame theorem and every part.
        let (source, machine) = crate::source_bound_alu::tests::fixture(64, M::AddRR, O::PReg(X1));
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let captured = verifier.verify_with_request(&machine, Some(&source), &request);
        for index in [0, 3] {
            assert!(
                matches!(
                    &captured.report().instructions[index].result,
                    InstructionVerificationResult::Verified {
                        proof_name,
                        strength: VerificationStrength::Formal,
                        ..
                    } if proof_name == crate::source_bound_frame::FRAME_OBLIGATION_NAME
                ),
                "{:?}",
                captured.report().instructions[index].result
            );
        }
        assert!(captured.report().emitted_opcode_inventory().is_promotable());
    });
}
