// Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::aarch64_static_frame::{
    FrameImagePatch, StaticFrameEnvelopeCandidates, StaticFrameLayoutClaim,
    check_static_frame_envelopes,
};
use crate::ay_bridge::{
    AYConfig, AYResult, DEFAULT_AY_TIMEOUT_MS, generate_smt2_query_raw,
    verify_with_cli_raw_attributed,
};
use sha2::{Digest, Sha256};
use std::sync::Arc;
use trust_cg_ir::MachFunction;
use trust_cg_ir::function::{Signature, StackSlot, Type};
use trust_cg_ir::regs::PReg;
use trust_cg_lower::Function;

// Envelope projection of the retained original E1 capture: exact selected
// operands, original arena IDs, laid-out row coordinates and full 184-byte
// image. Body rows are placeholders and LIR is empty: this fixture establishes
// NO source/body or body-word binding. A separate same-attempt ordinary E1
// diagnostic qualifies these exact queries with the real borrowed endpoints.
struct Fixture {
    source: Function,
    machine: MachFunction,
    image: Vec<u8>,
    claim: StaticFrameLayoutClaim,
    candidates: StaticFrameEnvelopeCandidates,
    patches: Vec<FrameImagePatch>,
}

fn pair(op: Op, fields: [u8; 2], offset: i64) -> MachInst {
    MachInst::new(
        op,
        vec![
            O::PReg(PReg::new(u16::from(fields[0]))),
            O::PReg(PReg::new(u16::from(fields[1]))),
            O::Special(SpecialReg::SP),
            O::Imm(offset),
        ],
    )
}

impl Fixture {
    fn fp_addressed_record_variant() -> Self {
        let mut fixture = Self::captured_envelope_projection();
        let at = fixture.geometry().byte_offset(InstId(57)).unwrap();
        let inst = &mut fixture.machine.insts[57];
        inst.operands[2] = O::PReg(PReg::new(29));
        inst.operands[3] = O::Imm(0);
        // Explicit VARIANT, not the original E1: LDP X29,X30,[X29].
        assert_eq!(
            crate::aarch64_memory_effect::memory_effect_word(inst),
            Some(0xa9407bbd)
        );
        fixture.image[at..at + 4].copy_from_slice(&0xa9407bbdu32.to_le_bytes());
        fixture
    }
    fn captured_envelope_projection() -> Self {
        let signature = Signature::new(vec![Type::I64; 3], vec![Type::I64; 5]);
        let source = Function::new(
            "tla_def_0",
            trust_cg_lower::function::Signature {
                params: vec![trust_cg_lower::Type::I64; 3],
                returns: vec![trust_cg_lower::Type::I64; 5],
            },
        );
        let mut machine = MachFunction::new("tla_def_0".into(), signature);
        machine.create_block();
        machine.create_block();
        let mut placeholder = MachInst::new(Op::Nop, vec![]);
        // Preserve real row coordinates without claiming that these body
        // placeholders decode the captured image's unchecked body words.
        placeholder.flags = trust_cg_ir::InstFlags::EMPTY;
        machine.insts = vec![placeholder; 67];
        machine.blocks[0].insts = [51, 52, 53, 54, 55, 56, 0, 1, 3, 4, 9, 13, 14, 15]
            .map(InstId)
            .to_vec();
        machine.blocks[1].insts = [
            16, 17, 18, 19, 20, 21, 23, 25, 26, 35, 36, 37, 38, 39, 40, 41, 57, 58, 59, 60, 61, 42,
        ]
        .map(InstId)
        .to_vec();
        machine.blocks[2].insts = [43, 44, 45, 48, 62, 63, 64, 65, 66, 50]
            .map(InstId)
            .to_vec();
        for (id, fields, offset) in [
            (51, [26, 25], -80),
            (52, [24, 23], 16),
            (53, [22, 21], 32),
            (54, [20, 19], 48),
            (55, [29, 30], 64),
        ] {
            machine.insts[id] = pair(
                if id == 51 { Op::StpPreIndex } else { Op::StpRI },
                fields,
                offset,
            );
        }
        machine.insts[56] = MachInst::new(
            Op::AddRI,
            vec![
                O::PReg(PReg::new(29)),
                O::Special(SpecialReg::SP),
                O::Imm(64),
            ],
        );
        for start in [57, 62] {
            for (position, fields, offset) in [
                (0, [29, 30], 64),
                (1, [20, 19], 48),
                (2, [22, 21], 32),
                (3, [24, 23], 16),
                (4, [26, 25], 80),
            ] {
                machine.insts[start + position] = pair(
                    if position == 4 {
                        Op::LdpPostIndex
                    } else {
                        Op::LdpRI
                    },
                    fields,
                    offset,
                );
            }
        }
        for id in [42, 50] {
            machine.insts[id] = MachInst::new(Op::Ret, vec![O::PReg(PReg::new(30))]);
        }
        machine.stack_slots = vec![StackSlot::new(0, 1); 2];
        let claim = StaticFrameLayoutClaim {
            saved_pairs: [[29, 30], [19, 20], [21, 22], [23, 24], [25, 26]]
                .map(|pair| pair.map(SavedFrameRegister::X))
                .to_vec(),
            callee_saved_bytes: 80,
            stack_slot_bytes: 0,
            outgoing_argument_bytes: 0,
            total_bytes: 80,
            uses_frame_pointer: true,
            dynamic_allocation: false,
            red_zone: false,
            slot_fp_offsets: vec![Some(-64); 2],
        };
        let candidates = StaticFrameEnvelopeCandidates {
            prologue: [51, 52, 53, 54, 55, 56].map(InstId).to_vec(),
            epilogues: vec![
                [57, 58, 59, 60, 61, 42].map(InstId).to_vec(),
                [62, 63, 64, 65, 66, 50].map(InstId).to_vec(),
            ],
        };
        Self {
            source,
            machine,
            image: include_bytes!("../tests/fixtures/original_e1_static_frame.bin").to_vec(),
            claim,
            candidates,
            patches: vec![
                FrameImagePatch {
                    offset: 36,
                    bytes: 4,
                },
                FrameImagePatch {
                    offset: 88,
                    bytes: 4,
                },
            ],
        }
    }
    fn geometry(&self) -> crate::aarch64_static_frame::CheckedStaticFrameEnvelopes<'_> {
        check_static_frame_envelopes(
            &self.source,
            &self.machine,
            &self.image,
            &self.claim,
            &self.candidates,
            &self.patches,
        )
        .unwrap()
    }
}

#[test]
fn conditional_frame_keeps_actual_store_chain_and_independent_exit_premises() {
    let fixture = Fixture::captured_envelope_projection();
    let geometry = fixture.geometry();
    let owner = conditional_static_frame_envelopes(&geometry).unwrap();
    assert!(std::ptr::eq(owner.geometry(), &geometry));
    assert_eq!(owner.exits().len(), 2);
    assert_eq!(geometry.byte_offset(InstId(56)), Some(20));
    assert_eq!(
        format!("{:x}", Sha256::digest(&fixture.image)),
        "d486fd98e20a18030a4c3738cdcc4cb4d9e9e674471104567d37e16c6b68d6da"
    );
    let stored = owner.post_save_memory().to_string();
    assert_eq!(stored.matches("(store ").count(), 80);
    assert!(stored.contains("frame_entry_memory"));
    for (index, exit) in owner.exits().iter().enumerate() {
        assert_eq!(exit.return_instruction(), InstId([42, 50][index]));
        assert_eq!(exit.premises().len(), 14);
        assert_eq!(exit.obligation().preconditions.len(), 14);
        assert_eq!(
            exit.premises()[2],
            ConditionalFramePremise::ResumeSp {
                relative_offset: -80
            }
        );
        assert_eq!(
            exit.premises()[3],
            ConditionalFramePremise::ResumeFp {
                relative_offset: -16
            }
        );
        assert_eq!(
            exit.premises()
                .iter()
                .filter(|p| matches!(p, ConditionalFramePremise::SavedLane(_)))
                .count(),
            10
        );
        let query = generate_smt2_query_raw(exit.obligation(), &AYConfig::default());
        assert!(query.contains(&format!("frame_exit_{index}_resume_memory")));
        assert!(!query.contains(&format!("frame_exit_{}_resume_memory", 1 - index)));
        assert!(!query.contains("as const") && !query.contains("(assert false)"));
        assert!(!exit.obligation().is_reconstructed());
    }
}

#[test]
fn frame_body_original_e1_source_keeps_missing_provider_witness_refusal() {
    let raw = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reports/2026-11-12-original-e1-machine/fixture/core.tmbc"
    ));
    let module = trust_cg_codegen::pipeline::decode_tmbc(raw).unwrap();
    let (lowered, _) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::MachOTlv,
            &crate::license_test_support::permit_unlicensed(),
        )
        .unwrap();
    assert_eq!(lowered.len(), 6);
    let (ordinal, original) = module
        .functions
        .iter()
        .enumerate()
        .find(|(_, f)| f.name == "tla_def_0")
        .unwrap();
    let mut fixture = Fixture::captured_envelope_projection();
    fixture.source = lowered
        .into_iter()
        .find(|(f, _)| f.name == original.name)
        .unwrap()
        .0;
    assert_eq!(fixture.source.signature.params.len(), 3);
    assert_eq!(fixture.source.signature.returns.len(), 5);
    assert_eq!(
        fixture
            .source
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|n| matches!(n.opcode, trust_cg_lower::instructions::Opcode::Call { .. }))
            .count(),
        2
    );
    let geometry = fixture.geometry();
    assert_eq!(geometry.layout_claim().total_bytes, 80);
    // This intentionally retains the historical envelope-only projection. No
    // body row is credited: actual provider effects refuse before body/patch
    // selection, even with all six original source functions retained.
    let error = check_frame_body(&geometry, &module, ordinal, &fixture.image, 0, &[]).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("original provider source/LIR/native footprint witness is missing")
    );
    assert_eq!(
        conditional_static_frame_envelopes(&geometry)
            .unwrap()
            .exits()[0]
            .premises()
            .len(),
        14
    );
}

#[test]
fn conditional_frame_arbitrary_memory_queries_have_an_array_free_image() {
    let fixture = Fixture::captured_envelope_projection();
    let geometry = fixture.geometry();
    let owner = conditional_static_frame_envelopes(&geometry).unwrap();
    for exit in owner.exits() {
        // This is the original conditional expression, including EVERY body
        // premise. It is not a claim that those premises hold during E1.
        let formula = exit.obligation().negated_equivalence();
        let image = crate::array_row_lowering::eliminate_arrays(&formula)
            .expect("the actual arbitrary entry/resume memory shape must lower exactly");
        assert!(!crate::array_row_lowering::mentions_arrays(&image));
        assert_eq!(exit.obligation().preconditions.len(), 14);
        assert_eq!(exit.premises().len(), 14);
    }
}

#[test]
fn conditional_frame_wrong_physical_fp_and_sp_restore_are_refused() {
    for (id, operand, delta) in [(56, 2, 8), (61, 3, 16)] {
        let mut fixture = Fixture::captured_envelope_projection();
        let at = fixture.geometry().byte_offset(InstId(id)).unwrap();
        let inst = &mut fixture.machine.insts[id as usize];
        let O::Imm(value) = &mut inst.operands[operand] else {
            panic!("immediate")
        };
        *value += delta;
        let word = crate::aarch64_memory_effect::memory_effect_word(inst)
            .or_else(|| {
                crate::aarch64_instruction_word_proofs::instruction_word(inst).map(|w| w.word)
            })
            .unwrap();
        fixture.image[at..at + 4].copy_from_slice(&word.to_le_bytes());
        assert!(
            check_static_frame_envelopes(
                &fixture.source,
                &fixture.machine,
                &fixture.image,
                &fixture.claim,
                &fixture.candidates,
                &fixture.patches
            )
            .is_err()
        );
    }
}

#[test]
fn conditional_frame_adjust_uses_bound_word_and_actual_state_without_widening_profile() {
    let fixture = Fixture::captured_envelope_projection();
    let mut state = State {
        sp: E::var("actual_sp", 64),
        registers: BTreeMap::from([(29, E::var("old_fp", 64)), (19, E::var("saved_x19", 64))]),
        memory: E::uf("unchanged_memory", Vec::new(), memory_sort()),
    };
    let inst = &fixture.machine.insts[56];
    let before = state.registers.clone();
    let memory = state.memory.clone();
    state.adjust(inst, &fixture.image[20..24]).unwrap();
    assert_eq!(state.sp, E::var("actual_sp", 64));
    assert_eq!(state.memory, memory);
    assert_eq!(state.registers[&19], before[&19]);
    assert_eq!(
        state.registers[&29],
        E::var("actual_sp", 64).bvadd(E::bv_const(64, 12).zero_ext(52))
    );
    for word in [0x9100_03fd_u32, 0x9141_03fd, 0x1101_03fd, 0xb101_03fd] {
        assert!(state.adjust(inst, &word.to_le_bytes()).is_err());
    }
    let mut shifted = inst.clone();
    shifted.opcode = Op::AddRIShift12;
    assert!(
        state
            .adjust(&shifted, &0x9141_03fdu32.to_le_bytes())
            .is_err()
    );
    assert!(state.adjust(inst, &[0; 3]).is_err());
}

#[test]
fn conditional_frame_sampling_cannot_discharge_arbitrary_resume_memories() {
    use crate::lowering_proof::{VerificationConfig, verify_by_evaluation_with_config};
    let fixture = Fixture::captured_envelope_projection();
    let geometry = fixture.geometry();
    let owner = conditional_static_frame_envelopes(&geometry).unwrap();
    for exit in owner.exits() {
        assert!(matches!(
            verify_by_evaluation_with_config(
                exit.obligation(),
                &VerificationConfig::with_sample_count(8)
            ),
            crate::verify::VerificationResult::Unknown { .. }
        ));
    }
}

fn live_config() -> AYConfig {
    AYConfig {
        solver: Some(
            crate::ay_identity::resolve_for_process()
                .expect("authenticated AY required; absence is not a pass"),
        ),
        timeout_ms: DEFAULT_AY_TIMEOUT_MS,
        produce_models: true,
    }
}

fn replay(
    case: &str,
    exit: &ConditionalStaticFrameExit,
    obligation: &ProofObligation,
    positive: bool,
) {
    if positive {
        // Query the EXACT premises for a model, independently of the restore
        // conclusion. UNSAT validity alone must never hide contradictory
        // assumptions. With true != false, the raw refutation query is just
        // this unchanged precondition set and must be SAT.
        let mut satisfiable = obligation.clone();
        satisfiable.aarch64_expr = E::bool_const(false);
        satisfiable.name.push_str("; premise satisfiability");
        replay(
            &format!("{case}-premises-satisfiable"),
            exit,
            &satisfiable,
            false,
        );
    }
    let config = live_config();
    let checker = crate::obligation_cert_store::resolve_proof_checker()
        .expect("independent proof checker required");
    let query = generate_smt2_query_raw(obligation, &config);
    assert!(
        query.len() <= 4 * 1024 * 1024,
        "bounded conditional-frame raw query"
    );
    let hash = format!("{:x}", Sha256::digest(query.as_bytes()));
    println!(
        "CONDITIONAL_FRAME_QUERY={}",
        serde_json::json!({"case":case,"return_instruction":exit.return_instruction().0,"query_sha256":hash,"query_bytes":query.len(),"query":query,"checker":checker,"expected":if positive {"Verified"} else {"CounterExample"}})
    );
    let verdict = verify_with_cli_raw_attributed(obligation, &config);
    println!(
        "CONDITIONAL_FRAME_VERDICT={}",
        serde_json::json!({"case":case,"query_sha256":hash,"result":format!("{:?}",verdict.result),"provenance":verdict.provenance()})
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
            matches!(verdict.result, AYResult::CounterExample(_)),
            "{case}: {verdict:?}"
        );
    }
}

fn raw_positive(index: usize) {
    let fixture = Fixture::captured_envelope_projection();
    let geometry = fixture.geometry();
    let owner = conditional_static_frame_envelopes(&geometry).unwrap();
    let exit = &owner.exits()[index];
    replay(
        &format!("positive-original-e1-exit-{index}"),
        exit,
        exit.obligation(),
        true,
    );
}
fn raw_missing(index: usize, register: u8) {
    let fixture = Fixture::captured_envelope_projection();
    let geometry = fixture.geometry();
    let owner = conditional_static_frame_envelopes(&geometry).unwrap();
    let exit = &owner.exits()[index];
    let position=exit.premises().iter().position(|p| matches!(p,ConditionalFramePremise::SavedLane(slot) if slot.register==SavedFrameRegister::X(register))).unwrap();
    let mut mutant = exit.obligation().clone();
    mutant.preconditions.remove(position);
    mutant
        .name
        .push_str(&format!("; MUTANT missing X{register} preservation"));
    replay(
        &format!("negative-exit-{index}-missing-x{register}"),
        exit,
        &mutant,
        false,
    );
}

#[test]
#[ignore = "requires authenticated AY and independent checker"]
fn conditional_frame_raw_positive_e1_exit_0() {
    raw_positive(0)
}
#[test]
#[ignore = "requires authenticated AY and independent checker"]
fn conditional_frame_raw_positive_e1_exit_1() {
    raw_positive(1)
}
#[test]
#[ignore = "requires authenticated AY and independent checker"]
fn conditional_frame_raw_negative_exit_0_missing_inner_x19() {
    raw_missing(0, 19)
}
#[test]
#[ignore = "requires authenticated AY and independent checker"]
fn conditional_frame_raw_negative_exit_1_missing_lr() {
    raw_missing(1, 30)
}
#[test]
#[ignore = "requires authenticated AY and independent checker"]
fn conditional_frame_raw_negative_wrong_resume_sp() {
    let fixture = Fixture::captured_envelope_projection();
    let geometry = fixture.geometry();
    let owner = conditional_static_frame_envelopes(&geometry).unwrap();
    let exit = &owner.exits()[0];
    let mut mutant = exit.obligation().clone();
    mutant.preconditions[2] =
        E::var("frame_exit_0_resume_sp", 64).eq_expr(relative(&E::var("frame_entry_sp", 64), -64));
    mutant.name.push_str("; MUTANT wrong resume SP");
    replay("negative-exit-0-wrong-resume-sp", exit, &mutant, false);
}

#[test]
#[ignore = "requires authenticated AY and independent checker"]
fn conditional_frame_raw_positive_fp_addressed_record_variant() {
    let fixture = Fixture::fp_addressed_record_variant();
    let geometry = fixture.geometry();
    let owner = conditional_static_frame_envelopes(&geometry).unwrap();
    let exit = &owner.exits()[0];
    replay(
        "positive-fp-addressed-record-VARIANT",
        exit,
        exit.obligation(),
        true,
    );
}

#[test]
#[ignore = "requires authenticated AY and independent checker"]
fn conditional_frame_raw_negative_wrong_resume_fp_in_variant() {
    let fixture = Fixture::fp_addressed_record_variant();
    let geometry = fixture.geometry();
    let owner = conditional_static_frame_envelopes(&geometry).unwrap();
    let exit = &owner.exits()[0];
    let mut mutant = exit.obligation().clone();
    mutant.preconditions[3] =
        E::var("frame_exit_0_resume_fp", 64).eq_expr(relative(&E::var("frame_entry_sp", 64), -32));
    mutant.name.push_str("; VARIANT wrong resume FP");
    replay(
        "negative-fp-addressed-record-VARIANT-wrong-fp",
        exit,
        &mutant,
        false,
    );
}

// These are the existing owner's conditional mathematical statements. A
// checked reduced query establishes NONE of its original body premises.
fn replay_array_free_image(obligation: &ProofObligation, positive: bool) -> bool {
    let config = live_config();
    let queries = crate::ay_bridge::generate_lowered_queries(obligation, &config);
    assert_eq!(queries.len(), 1, "one exact array-free encoding");
    let (query, lowered) = &queries[0];
    assert!(!query.contains("(Array "));
    assert_eq!(lowered.preconditions, obligation.preconditions);
    assert_eq!(lowered.inputs, obligation.inputs);
    let raw = generate_smt2_query_raw(obligation, &config);
    let checker = crate::obligation_cert_store::resolve_proof_checker()
        .expect("independent checker required; absence is not a pass");
    let verdict = crate::ay_bridge::verify_respelled_query(lowered, &config, query);
    println!(
        "ARRAY_READ_IMAGE={}",
        serde_json::json!({
            "name": obligation.name, "raw_sha256":format!("{:x}",Sha256::digest(raw.as_bytes())),
            "raw_bytes":raw.len(), "image_sha256":format!("{:x}",Sha256::digest(query.as_bytes())),
            "image_bytes":query.len(), "premises":obligation.preconditions.len(),
            "raw_query":raw, "image_query":query, "checker_probe":checker,
            "result":format!("{:?}",verdict.result), "provenance":verdict.provenance()
        })
    );
    if positive {
        verdict.result == AYResult::Verified
    } else {
        assert!(
            matches!(verdict.result, AYResult::CounterExample(_)),
            "{verdict:?}"
        );
        // Independently retain the ORIGINAL array-theory counterexample route.
        assert!(matches!(
            verify_with_cli_raw_attributed(obligation, &config).result,
            AYResult::CounterExample(_)
        ));
        true
    }
}

#[test]
#[ignore = "requires authenticated AY and independent checker; conditional mathematics only"]
fn conditional_frame_array_free_images_keep_premises_and_counterexamples() {
    let fixture = Fixture::captured_envelope_projection();
    let geometry = fixture.geometry();
    let owner = conditional_static_frame_envelopes(&geometry).unwrap();
    let mut checked = Vec::new();
    for (index, exit) in owner.exits().iter().enumerate() {
        assert_eq!(exit.obligation().preconditions.len(), 14);
        let mut premises = exit.obligation().clone();
        premises.aarch64_expr = E::bool_const(false);
        premises.name.push_str("; premises satisfiable");
        replay_array_free_image(&premises, false);
        checked.push(replay_array_free_image(exit.obligation(), true));
        let register = if index == 0 { 19 } else { 30 };
        let position = exit.premises().iter().position(|p| matches!(p,
            ConditionalFramePremise::SavedLane(slot) if slot.register == SavedFrameRegister::X(register))).unwrap();
        let mut missing = exit.obligation().clone();
        missing.preconditions.remove(position);
        missing.name.push_str("; missing actual saved lane");
        replay_array_free_image(&missing, false);
    }
    let mut wrong_sp = owner.exits()[0].obligation().clone();
    wrong_sp.preconditions[2] =
        E::var("frame_exit_0_resume_sp", 64).eq_expr(relative(&E::var("frame_entry_sp", 64), -64));
    wrong_sp.name.push_str("; wrong actual resume SP");
    replay_array_free_image(&wrong_sp, false);
    assert_eq!(
        checked,
        vec![true, true],
        "both conditional images must independently replay; image construction is not proof completion"
    );
}

fn ordinary_memory_fixture() -> (ProofObligation, E, E, E) {
    use crate::lowering_proof::{MachineSideProvenance, TransvalCheckKind};
    use crate::smt::SmtSort;
    let memory = E::uf("ordinary_memory", vec![], SmtSort::bv_array(2, 2));
    let p = E::var("p", 2);
    let q = E::var("q", 2);
    let load = |array: E, at: E| E::Select {
        array: Arc::new(array),
        index: Arc::new(at),
    };
    let obligation = ProofObligation {
        name: "ordinary arbitrary memory alias congruence".into(),
        trust_ir_expr: load(memory.clone(), p.clone()),
        aarch64_expr: load(memory.clone(), q.clone()),
        inputs: vec![("p".into(), 2), ("q".into(), 2)],
        preconditions: vec![p.clone().eq_expr(q.clone())],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    (obligation, memory, p, q)
}

#[test]
#[ignore = "requires authenticated AY and independent checker"]
fn ordinary_arbitrary_memory_alias_and_distinct_memory_images() {
    use crate::smt::SmtSort;
    let (mut obligation, _, p, q) = ordinary_memory_fixture();
    let checked = replay_array_free_image(&obligation, true);
    // Exercise the actual public consumer, not only the encoding diagnostic.
    // Only an independently checked UNSAT may be reused from the image.
    let consumed = crate::ay_bridge::verify_with_ay_attributed(&obligation, &live_config());
    assert_eq!(consumed.result, AYResult::Verified);
    println!("ORDINARY_ARRAY_OWNER={}", consumed.provenance());
    obligation.preconditions.clear();
    obligation.name.push_str("; no alias premise");
    replay_array_free_image(&obligation, false);
    obligation.preconditions.push(p.clone().eq_expr(q.clone()));
    obligation.aarch64_expr = E::Select {
        array: Arc::new(E::uf("distinct_memory", vec![], SmtSort::bv_array(2, 2))),
        index: Arc::new(q.clone()),
    };
    obligation.name = "ordinary independent memory contents".into();
    replay_array_free_image(&obligation, false);
    assert!(
        checked,
        "the alias-congruence theorem must independently replay"
    );
}

#[test]
#[ignore = "requires authenticated AY and independent checker; store/load proof remains a strict challenge"]
fn ordinary_arbitrary_memory_store_images() {
    let (mut obligation, memory, p, q) = ordinary_memory_fixture();
    let load = |array: E, at: E| E::Select {
        array: Arc::new(array),
        index: Arc::new(at),
    };
    obligation.trust_ir_expr = load(
        E::Store {
            array: Arc::new(memory.clone()),
            index: Arc::new(p.clone()),
            value: Arc::new(E::bv_const(1, 2)),
        },
        q.clone(),
    );
    obligation.aarch64_expr = E::bv_const(1, 2);
    obligation.name = "ordinary aliased store/load".into();
    let checked = replay_array_free_image(&obligation, true);
    obligation.trust_ir_expr = load(
        E::Store {
            array: Arc::new(memory),
            index: Arc::new(p),
            value: Arc::new(E::bv_const(2, 2)),
        },
        q,
    );
    obligation.name = "ordinary wrong stored value".into();
    replay_array_free_image(&obligation, false);
    assert!(checked, "the store/load theorem must independently replay");
}

#[test]
fn conditional_frame_lowered_print_views_preserve_exact_images() {
    let fixture = Fixture::captured_envelope_projection();
    let geometry = fixture.geometry();
    let owner = conditional_static_frame_envelopes(&geometry).unwrap();
    let config = AYConfig::default();
    for (exit_index, exit) in owner.exits().iter().enumerate() {
        let originals = crate::ay_bridge::generate_lowered_queries(exit.obligation(), &config);
        let candidates =
            crate::ay_bridge::source_bound_lowered_query_scripts(exit.obligation(), &config);
        assert_eq!(originals.len(), candidates.len());
        assert!(!candidates.is_empty());
        for (index, ((expected, _), (original, producer, _))) in
            originals.iter().zip(&candidates).enumerate()
        {
            assert_eq!(
                original, expected,
                "original checker/cache problem must stay exact"
            );
            if let Some(producer) = producer.as_ref() {
                assert!(producer.contains("(let "));
                assert!(producer.len() <= original.len() * 3 / 4);
            }
            assert_eq!(exit.premises().len(), 14);
            if let Some(directory) = std::env::var_os("QUERY_SHARING_TEST_OUTPUT_DIR") {
                let directory = std::path::PathBuf::from(directory);
                std::fs::create_dir_all(&directory).unwrap();
                std::fs::write(
                    directory.join(format!("exit{exit_index}-{index}.image.smt2")),
                    original,
                )
                .unwrap();
                if let Some(producer) = producer.as_ref() {
                    std::fs::write(
                        directory.join(format!("exit{exit_index}-{index}.producer.smt2")),
                        producer,
                    )
                    .unwrap();
                }
                std::fs::write(
                    directory.join(format!("exit{exit_index}-{index}.mode.json")),
                    serde_json::to_vec(&serde_json::json!({
                        "producer_view": producer.is_some(),
                        "original_bytes": original.len(),
                        "conditional_premises": exit.premises().len(),
                        "native_authority": false,
                    }))
                    .unwrap(),
                )
                .unwrap();
            }
        }
    }
}
