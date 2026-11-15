// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::aarch64_pair_memory::check_pair_encoding;
use crate::ay_bridge::{
    AYConfig, AYResult, DEFAULT_AY_TIMEOUT_MS, generate_smt2_query_raw,
    verify_with_cli_raw_attributed,
};
use sha2::{Digest, Sha256};
use trust_cg_ir::regs::{PReg, X0, X1};
use trust_cg_ir::{AArch64Opcode as Op, InstFlags, MachOperand as O, SpecialReg};

#[derive(Clone)]
struct PairFixture {
    save: MachInst,
    restore: MachInst,
    save_word: u32,
    restore_word: u32,
}

fn pair_word(prefix: u32, fields: [u8; 2], offset: i64, base: u8) -> u32 {
    assert_eq!(offset % 8, 0);
    assert!((-64..=63).contains(&(offset / 8)));
    prefix
        | (((offset / 8) as u32 & 127) << 15)
        | (u32::from(fields[1]) << 10)
        | (u32::from(base) << 5)
        | u32::from(fields[0])
}

fn pair_inst(opcode: Op, fields: [u8; 2], offset: i64) -> MachInst {
    let transfer = |field| {
        if field == 31 {
            O::Special(SpecialReg::XZR)
        } else {
            O::PReg(PReg::new(u16::from(field)))
        }
    };
    MachInst::new(
        opcode,
        vec![
            transfer(fields[0]),
            transfer(fields[1]),
            O::Special(SpecialReg::SP),
            O::Imm(offset),
        ],
    )
}

impl PairFixture {
    fn new(saved: [u8; 2], allocation: i64, restored: [u8; 2], increment: i64) -> Self {
        Self {
            save: pair_inst(Op::StpPreIndex, saved, -allocation),
            restore: pair_inst(Op::LdpPostIndex, restored, increment),
            // Independent A64 instruction diagrams, not backend encoding or
            // the descriptor's own decoded view. Literal cases below pin them.
            save_word: pair_word(0xa980_0000, saved, -allocation, 31),
            restore_word: pair_word(0xa8c0_0000, restored, increment, 31),
        }
    }

    fn query(&self) -> Result<ConditionalSavedPair<'_>, SavedPairRefusal> {
        conditional_saved_pair(
            check_pair_encoding(&self.save, &self.save_word.to_le_bytes()).unwrap(),
            check_pair_encoding(&self.restore, &self.restore_word.to_le_bytes()).unwrap(),
        )
    }
}

#[test]
fn saved_pair_retains_exact_descriptors_and_arbitrary_body_premises() {
    for (registers, allocation, words) in [
        ([29, 30], 16, [0xa9bf_7bfd, 0xa8c1_7bfd]),
        ([19, 20], 32, [0xa9be_53f3, 0xa8c2_53f3]),
        // The captured TY first-function outer pair. This models only these
        // two words conditionally, not its intervening calls or four other pairs.
        ([26, 25], 80, [0xa9bb_67fa, 0xa8c5_67fa]),
    ] {
        let fixture = PairFixture::new(registers, allocation, registers, allocation);
        assert_eq!([fixture.save_word, fixture.restore_word], words);
        assert_eq!(
            fixture.save.flags,
            InstFlags::WRITES_MEMORY | InstFlags::HAS_SIDE_EFFECTS
        );
        assert_eq!(fixture.restore.flags, InstFlags::READS_MEMORY);
        let owner = fixture.query().unwrap();
        assert!(std::ptr::eq(owner.save().instruction(), &fixture.save));
        assert!(std::ptr::eq(
            owner.restore().instruction(),
            &fixture.restore
        ));
        assert_eq!([owner.save().word(), owner.restore().word()], words);
        let obligation = owner.obligation();
        assert_eq!(obligation.inputs.len(), 4);
        assert_eq!(obligation.preconditions.len(), 5);
        assert!(!obligation.is_reconstructed());
        assert!(obligation.is_genuinely_proven()); // Structural, not discharge.
        let query = generate_smt2_query_raw(obligation, &AYConfig::default());
        for memory in ["pair_entry_memory", "pair_resume_memory"] {
            assert!(query.contains(&format!(
                "(declare-fun {memory} () (Array (_ BitVec 64) (_ BitVec 8)))"
            )));
        }
        for operation in ["(store ", "(select ", "pair_resume_sp", "(check-sat)"] {
            assert!(query.contains(operation), "missing {operation}");
        }
        assert!(!query.contains("as const"));
        assert!(!query.contains("(forall"));
        assert!(!query.contains("(assert false)"));
    }
}

#[test]
fn saved_pair_refuses_hidden_flags_uses_and_clobbers_on_either_instruction() {
    for save in [true, false] {
        for effect in 0..3 {
            let mut fixture = PairFixture::new([19, 20], 32, [19, 20], 32);
            let instruction = if save {
                &mut fixture.save
            } else {
                &mut fixture.restore
            };
            match effect {
                0 => instruction.flags |= InstFlags::IS_PSEUDO,
                1 => instruction.implicit_uses = &[X0],
                _ => instruction.implicit_defs = &[X1],
            }
            assert_eq!(
                fixture.query().unwrap_err(),
                SavedPairRefusal::HiddenEffects(if save { "save" } else { "restore" })
            );
        }
    }
}

#[test]
fn saved_pair_refuses_unrepresented_frames_and_register_domains() {
    for allocation in [8, 0, -16] {
        let fixture = PairFixture::new([19, 20], allocation, [19, 20], 16);
        assert_eq!(fixture.query().unwrap_err(), SavedPairRefusal::FrameSize);
    }
    for (saved, loaded) in [
        ([19, 19], [19, 20]),
        ([19, 31], [19, 31]),
        ([19, 20], [19, 21]),
    ] {
        let fixture = PairFixture::new(saved, 32, loaded, 32);
        assert_eq!(fixture.query().unwrap_err(), SavedPairRefusal::Registers);
    }
    let mut offset_save = PairFixture::new([19, 20], 32, [19, 20], 32);
    offset_save.save = pair_inst(Op::StpRI, [19, 20], -32);
    offset_save.save_word = pair_word(0xa900_0000, [19, 20], -32, 31);
    assert_eq!(
        offset_save.query().unwrap_err(),
        SavedPairRefusal::SaveShape
    );

    let mut offset_restore = PairFixture::new([19, 20], 32, [19, 20], 32);
    offset_restore.restore = pair_inst(Op::LdpRI, [19, 20], 32);
    offset_restore.restore_word = pair_word(0xa940_0000, [19, 20], 32, 31);
    assert_eq!(
        offset_restore.query().unwrap_err(),
        SavedPairRefusal::RestoreShape
    );

    let mut other_base = PairFixture::new([19, 20], 32, [19, 20], 32);
    other_base.save.operands[2] = O::PReg(X0);
    other_base.save_word = pair_word(0xa980_0000, [19, 20], -32, 0);
    assert_eq!(other_base.query().unwrap_err(), SavedPairRefusal::SaveShape);

    for (bank, word) in [(32, 0x29bc_53f3), (96, 0x6dbe_53f3), (64, 0xadbf_53f3)] {
        let mut non_x64 = PairFixture::new([19, 20], 32, [19, 20], 32);
        non_x64.save.operands[0] = O::PReg(PReg::new(bank + 19));
        non_x64.save.operands[1] = O::PReg(PReg::new(bank + 20));
        non_x64.save_word = word;
        // Each is a valid W/D/Q descriptor, but not this GPR64 theorem.
        assert_eq!(non_x64.query().unwrap_err(), SavedPairRefusal::SaveShape);
    }
}

#[test]
fn saved_pair_semantic_mutants_remain_queries_not_shape_refusals() {
    let correct = PairFixture::new([26, 25], 80, [26, 25], 80);
    let correct = correct.query().unwrap();
    for fixture in [
        PairFixture::new([26, 25], 80, [25, 26], 80),
        PairFixture::new([26, 25], 80, [26, 25], 64),
    ] {
        let mutant = fixture.query().unwrap();
        assert_eq!(correct.obligation().inputs, mutant.obligation().inputs);
        assert_eq!(
            correct.obligation().preconditions,
            mutant.obligation().preconditions
        );
        assert_ne!(
            correct.obligation().aarch64_expr,
            mutant.obligation().aarch64_expr
        );
    }
    let without_second_slot = without_second_slot_premise(correct.obligation());
    assert_eq!(without_second_slot.preconditions.len(), 4);
    assert_eq!(correct.obligation().preconditions.len(), 5);
}

fn without_second_slot_premise(original: &ProofObligation) -> ProofObligation {
    let mut mutant = original.clone();
    assert_eq!(mutant.preconditions.len(), 5);
    mutant.preconditions.pop().unwrap();
    mutant
        .name
        .push_str("; MUTANT missing second saved-slot premise");
    mutant
}

#[test]
fn saved_pair_arbitrary_memory_is_not_discharged_by_sampling() {
    use crate::lowering_proof::{VerificationConfig, verify_by_evaluation_with_config};
    use crate::verify::VerificationResult;
    let fixture = PairFixture::new([19, 20], 32, [19, 20], 32);
    let owner = fixture.query().unwrap();
    let result = verify_by_evaluation_with_config(
        owner.obligation(),
        &VerificationConfig::with_sample_count(8),
    );
    assert!(
        matches!(&result, VerificationResult::Unknown { .. }),
        "{result:?}"
    );
}

fn replay(
    case: &str,
    owner: &ConditionalSavedPair<'_>,
    obligation: &ProofObligation,
    config: &AYConfig,
    positive: bool,
) {
    let query = generate_smt2_query_raw(obligation, config);
    // Bound retained diagnostic output independently of solver deadlines. The
    // root runner captures these exact query bytes; hashes alone are not proofs.
    assert!(
        query.len() <= 64 * 1024,
        "unexpected saved-pair query growth"
    );
    let query_sha256 = format!("{:x}", Sha256::digest(query.as_bytes()));
    println!(
        "SAVED_PAIR_QUERY={}",
        serde_json::json!({
            "case": case,
            "save_word": format!("{:08x}", owner.save().word()),
            "restore_word": format!("{:08x}", owner.restore().word()),
            "query_sha256": query_sha256,
            "query_bytes": query.len(),
            "query": query,
            "expected": if positive { "Verified" } else { "CounterExample" },
        })
    );
    let verdict = verify_with_cli_raw_attributed(obligation, config);
    println!(
        "SAVED_PAIR_VERDICT={}",
        serde_json::json!({
            "case": case,
            "query_sha256": query_sha256,
            "result": format!("{:?}", verdict.result),
            "provenance": verdict.provenance(),
        })
    );
    if positive {
        assert_eq!(
            verdict.result,
            AYResult::Verified,
            "{case}: {}",
            verdict.provenance()
        );
    } else {
        assert!(
            matches!(&verdict.result, AYResult::CounterExample(_)),
            "{case}: {verdict:?}"
        );
    }
}

/// Explicit opt-in qualification, NOT a silently passing environment probe.
/// The runner selects each ignored case separately and retains zero ignored
/// tests in that execution. Existing certificate-store policy may retain exact
/// positive proofs; no test changes global environment or cache policy.
fn live_config() -> AYConfig {
    let solver = crate::ay_identity::resolve_for_process()
        .expect("saved-pair qualification requires an authenticated AY; absence is not a pass");
    AYConfig {
        solver: Some(solver),
        timeout_ms: DEFAULT_AY_TIMEOUT_MS,
        produce_models: true,
    }
}

fn replay_fixture(case: &str, fixture: PairFixture, positive: bool) {
    let config = live_config();
    let owner = fixture.query().unwrap();
    replay(case, &owner, owner.obligation(), &config, positive);
}

#[test]
#[ignore = "requires authenticated AY plus independent proof checker"]
fn saved_pair_raw_positive_fp_lr_16() {
    replay_fixture(
        "positive-fp-lr-16",
        PairFixture::new([29, 30], 16, [29, 30], 16),
        true,
    );
}

#[test]
#[ignore = "requires authenticated AY plus independent proof checker"]
fn saved_pair_raw_positive_ordinary_callee_save_32() {
    replay_fixture(
        "positive-ordinary-callee-save-32",
        PairFixture::new([19, 20], 32, [19, 20], 32),
        true,
    );
}

#[test]
#[ignore = "requires authenticated AY plus independent proof checker"]
fn saved_pair_raw_positive_captured_ty_outer_pair_80() {
    replay_fixture(
        "positive-captured-ty-outer-pair-80",
        PairFixture::new([26, 25], 80, [26, 25], 80),
        true,
    );
}

#[test]
#[ignore = "requires authenticated AY plus independent proof checker"]
fn saved_pair_raw_negative_reversed_restore_order() {
    replay_fixture(
        "negative-reversed-restore-order",
        PairFixture::new([26, 25], 80, [25, 26], 80),
        false,
    );
}

#[test]
#[ignore = "requires authenticated AY plus independent proof checker"]
fn saved_pair_raw_negative_wrong_restore_writeback() {
    replay_fixture(
        "negative-wrong-restore-writeback",
        PairFixture::new([26, 25], 80, [26, 25], 64),
        false,
    );
}

#[test]
#[ignore = "requires authenticated AY plus independent proof checker"]
fn saved_pair_raw_negative_missing_second_slot_preservation() {
    let config = live_config();
    let fixture = PairFixture::new([26, 25], 80, [26, 25], 80);
    let owner = fixture.query().unwrap();
    replay(
        "negative-missing-second-slot-preservation",
        &owner,
        &without_second_slot_premise(owner.obligation()),
        &config,
        false,
    );
}
