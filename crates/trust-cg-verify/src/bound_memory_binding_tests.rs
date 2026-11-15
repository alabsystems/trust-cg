// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Refutation-precondition and wrong-binding controls for the Formal-only
//! bound-memory rule (owner ruling 2026-09-29, [`super`]).
//!
//! * Clause 2: a row credits only when its own in-process refutation check
//!   RAN and HELD. Rows no lane judges stay unverified with
//!   [`BOUND_MEMORY_REFUTATION_NOT_RUN`], although their form certificate
//!   replays.
//! * Clause 3: an instruction ATTRIBUTED to the wrong form (W for X, pre for
//!   post, unsigned-offset for unscaled, a mis-scaled `imm7`, a wrong
//!   register-offset mode) is refused with [`BOUND_MEMORY_BINDING_MISMATCH`];
//!   under the [`binding_check_seam`] mutant the same attribution IS credited
//!   through the wrong form's replaying certificate, so each refusal is the
//!   binding check's doing.
//! * The certificate bodies: a corrupted, truncated, substituted or missing
//!   `*.lratcert.zst` credits nothing, while a faithful copy in the same
//!   directory replays.

use super::*;
use crate::aarch64_pair_memory_forms::{
    PAIR_MEMORY_FORMS, PairAddressing, PairRegisterBank, PairTransfer,
};
use crate::aarch64_scalar_memory_proofs::{
    SCALAR_MEMORY_FORMS, ScalarAddressing, ScalarBank, ScalarExtension, ScalarTransfer,
};
use crate::function_verifier::{FunctionVerifier, InstructionVerificationResult};
use crate::lowering_proof::VerificationConfig;
use crate::verify::VerificationStrength;
use trust_cg_ir::aarch64_regs::{D0, D1, H0, S0, S1, V0, V1, W0, W19, W20, X0, X1, X2, X19, X20};
use trust_cg_ir::{AArch64Opcode as O, InstId, MachFunction, MachOperand, Signature, SpecialReg};

fn p(reg: trust_cg_ir::PReg) -> MachOperand {
    MachOperand::PReg(reg)
}

fn sp() -> MachOperand {
    MachOperand::Special(SpecialReg::SP)
}

fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}

fn function(insts: Vec<MachInst>) -> MachFunction {
    let mut func = MachFunction::new(
        "bound_memory_binding".to_string(),
        Signature::new(vec![], vec![]),
    );
    for (index, inst) in insts.into_iter().enumerate() {
        func.insts.push(inst);
        func.blocks[0].insts.push(InstId(index as u32));
    }
    func
}

fn promotion_config() -> VerificationConfig {
    let mut config = VerificationConfig::for_proof_promotion();
    config.sample_count = 64;
    config
}

fn promotion() -> FunctionVerifier {
    FunctionVerifier::with_config(promotion_config())
}

fn bound(inst: &MachInst) -> BoundMemoryBinding {
    match bind_bound_memory_row(inst) {
        Some(Ok(binding)) => binding,
        other => panic!("{inst:?} must bind a form: {other:?}"),
    }
}

/// The row's own held instruction-derived check.
fn instruction_word_check(inst: &MachInst) -> BoundMemoryRefutation {
    let verdict =
        crate::aarch64_instruction_word_proofs::instruction_word_verdict(inst, &promotion_config())
            .unwrap_or_else(|| panic!("{inst:?}: the instruction-derived lane admits it"));
    BoundMemoryRefutation::instruction_word(&verdict)
        .unwrap_or_else(|| panic!("{inst:?}: its instruction-derived check holds"))
}

/// The row's own held pair concrete-word check.
fn pair_check(inst: &MachInst) -> BoundMemoryRefutation {
    let (obligation, word) =
        crate::aarch64_pair_memory_proofs::pair_memory_obligation_and_word(inst)
            .unwrap_or_else(|| panic!("{inst:?}: the pair lane admits it"));
    let (verdict, _) = crate::lowering_proof::discharge_reconstructed_obligation(
        &obligation,
        &obligation,
        &promotion_config(),
    );
    BoundMemoryRefutation::pair_concrete_word(word, &verdict)
        .unwrap_or_else(|| panic!("{inst:?}: its concrete-word check holds: {verdict:?}"))
}

/// What the rule credits `inst` ATTRIBUTED to `claimed`, under the
/// proof-promotion policy (certificates replayed).
fn credit(
    inst: &MachInst,
    claimed: &BoundMemoryBinding,
    check: Option<&BoundMemoryRefutation>,
) -> BoundMemoryCredit {
    credit_bound_form(inst, claimed, check, true, None)
}

/// A credit the replaying certificate of `form` grants: `Certified` citing
/// it on a qualified host, a checker-identity miss elsewhere.
fn assert_certificate_credit(credit: &BoundMemoryCredit, form: &str, what: &str) {
    match (bound_memory_checker_qualification(), credit) {
        (Ok(()), BoundMemoryCredit::Certified { proof_name }) => {
            assert!(proof_name.starts_with(form), "{what}: {proof_name}");
        }
        (Err(_), BoundMemoryCredit::Uncertified { proof_name, reason }) => assert!(
            proof_name.starts_with(form) && reason.contains(CHECKER_IDENTITY_MISS),
            "{what}: {proof_name}: {reason}"
        ),
        (qualification, other) => {
            panic!("{what}: {other:?} under checker qualification {qualification:?}")
        }
    }
}

fn assert_misbound(credit: &BoundMemoryCredit, what: &str) -> String {
    match credit {
        BoundMemoryCredit::Misbound { reason, .. } => {
            assert!(
                reason.starts_with(BOUND_MEMORY_BINDING_MISMATCH),
                "{what}: {reason}"
            );
            reason.clone()
        }
        other => panic!("{what}: a wrong attribution must be refused, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Clause 2: the refutation check must have run and held
// ---------------------------------------------------------------------------

/// Scalar rows that bind a form theorem whose certificate replays are never
/// credited by the rule without a held in-process check: with no check the
/// rule returns [`BoundMemoryCredit::Unrefuted`] and grants nothing.
/// Non-vacuous: each form's certificate replays on a qualified host, and
/// before this clause the walk credited every one of these rows `Formal` from
/// the certificate alone (measured on 3cdb57101). Through the promotion walk
/// these SIMD&FP rows are now judged by their exact word-bound memory-effect
/// decomposition (L04-P1, [`RefutationCheck::MemoryEffect`]), so the walk
/// credits them on a qualified host; see
/// [`only_forms_with_an_in_walk_refutation_check_are_credited`].
#[test]
fn a_bound_row_whose_refutation_check_never_ran_is_not_credited() {
    let rows = [
        // ldr d0, [x1, #8]
        MachInst::new(O::LdrRI, vec![p(D0), p(X1), imm(8)]),
        // stur s0, [x1, #-4]
        MachInst::new(O::StrRI, vec![p(S0), p(X1), imm(-4)]),
        // ldr h0, [sp, #2]
        MachInst::new(O::LdrRI, vec![p(H0), sp(), imm(2)]),
        // ldr d0, [x1, x2, lsl #3]
        MachInst::new(O::LdrRO, vec![p(D0), p(X1), p(X2), imm(7)]),
    ];
    let qualified = bound_memory_checker_qualification().is_ok();
    for inst in &rows {
        let binding = bound(inst);
        if qualified {
            assert_eq!(
                form_certificate_status(&binding.obligation()),
                Ok(()),
                "{inst:?}: the form certificate must replay (non-vacuity)"
            );
        }
        assert_eq!(
            bound_memory_credit(inst, None, true),
            Some(BoundMemoryCredit::Unrefuted {
                proof_name: binding.obligation().name
            }),
            "{inst:?}"
        );
    }
    // The walk now runs a check on them: the memory-effect decomposition.
    let report = promotion().verify(&function(rows.to_vec()));
    for (row, inst) in report.instructions.iter().zip(&rows) {
        let form = bound(inst).obligation().name;
        let tag = form
            .split(':')
            .next()
            .expect("form theorem names start with their tag");
        crate::bound_memory_authority::assert_form_credit_or_checker_miss(
            &row.result,
            tag,
            "an H/S/D/Q row judged by its memory-effect decomposition",
        );
    }
}

/// An undecided instruction-derived check, and a pair check that did not
/// hold, are not evidence: neither builds a [`BoundMemoryRefutation`].
#[test]
fn only_a_holding_check_is_refutation_evidence() {
    use crate::aarch64_instruction_word_proofs::{InstructionWordVerdict, Outcome};
    use crate::verify::VerificationResult;
    let inst = MachInst::new(O::StrRI, vec![p(X1), p(X0), imm(8)]);
    let verdict = crate::aarch64_instruction_word_proofs::instruction_word_verdict(
        &inst,
        &promotion_config(),
    )
    .expect("admitted");
    assert!(BoundMemoryRefutation::instruction_word(&verdict).is_some());
    for outcome in [
        Outcome::Undecided("sampled".into()),
        Outcome::Refuted("counterexample".into()),
    ] {
        let not_held = InstructionWordVerdict {
            outcome,
            ..verdict.clone()
        };
        assert_eq!(BoundMemoryRefutation::instruction_word(&not_held), None);
    }
    let mut holed = verdict.clone();
    holed.word.hole_mask = 0x3ff << 10;
    assert_eq!(BoundMemoryRefutation::instruction_word(&holed), None);
    for verdict in [
        VerificationResult::Invalid {
            counterexample: "x".into(),
        },
        VerificationResult::Unknown { reason: "x".into() },
    ] {
        assert_eq!(
            BoundMemoryRefutation::pair_concrete_word(0xa9bf_7bfd, &verdict),
            None
        );
    }
}

/// One representative instruction per attributable form, self-checked: it
/// must bind exactly that form.
fn representative_rows() -> Vec<(String, MachInst)> {
    let mut rows = Vec::new();
    for (form, query) in PAIR_MEMORY_FORMS {
        let (t, t2) = match (form.bank, form.element_bytes) {
            (PairRegisterBank::Gpr, 4) => (W19, W20),
            (PairRegisterBank::Gpr, _) => (X19, X20),
            (PairRegisterBank::Fpr, 4) => (S0, S1),
            (PairRegisterBank::Fpr, 8) => (D0, D1),
            (PairRegisterBank::Fpr, _) => (V0, V1),
        };
        let opcode = match (form.transfer, form.addressing) {
            (PairTransfer::Store, PairAddressing::SignedOffset) => O::StpRI,
            (PairTransfer::Store, PairAddressing::PreIndex) => O::StpPreIndex,
            (PairTransfer::Store, PairAddressing::PostIndex) => O::NeonStpQPost,
            (PairTransfer::Load, PairAddressing::SignedOffset) => O::LdpRI,
            (PairTransfer::Load, _) => O::LdpPostIndex,
        };
        rows.push((
            query.to_string(),
            MachInst::new(opcode, vec![p(t), p(t2), sp(), imm(16)]),
        ));
    }
    for (form, query) in SCALAR_MEMORY_FORMS {
        let load = form.transfer == ScalarTransfer::Load;
        let t = match (form.bank, form.access_bytes, form.extension) {
            (ScalarBank::Fpr, 2, _) => H0,
            (ScalarBank::Fpr, 4, _) => S0,
            (ScalarBank::Fpr, 8, _) => D0,
            (ScalarBank::Fpr, _, _) => V0,
            (ScalarBank::Gpr, 8, _) | (ScalarBank::Gpr, _, ScalarExtension::SignTo64) => X0,
            (ScalarBank::Gpr, _, _) => W0,
        };
        let narrow = |byte, half, word| match form.access_bytes {
            1 => byte,
            2 => half,
            _ => word,
        };
        let inst = match form.addressing {
            ScalarAddressing::Literal => continue,
            ScalarAddressing::UnsignedOffset | ScalarAddressing::Unscaled => {
                let opcode = match (load, form.bank, form.extension) {
                    (_, ScalarBank::Fpr, _) => {
                        if load {
                            O::LdrRI
                        } else {
                            O::StrRI
                        }
                    }
                    (true, _, ScalarExtension::Zero) => narrow(O::LdrbRI, O::LdrhRI, O::LdrRI),
                    (true, _, _) => narrow(O::LdrsbRI, O::LdrshRI, O::LdrRI),
                    (false, _, _) => narrow(O::StrbRI, O::StrhRI, O::StrRI),
                };
                let offset = if form.addressing == ScalarAddressing::Unscaled {
                    -8
                } else {
                    i64::from(form.access_bytes)
                };
                MachInst::new(opcode, vec![p(t), p(X1), imm(offset)])
            }
            ScalarAddressing::PreIndex | ScalarAddressing::PostIndex => {
                let pre = form.addressing == ScalarAddressing::PreIndex;
                let opcode = match (load, pre) {
                    (true, true) => O::LdrPreIndex,
                    (true, false) => O::LdrPostIndex,
                    (false, true) => O::StrPreIndex,
                    (false, false) => O::StrPostIndex,
                };
                MachInst::new(opcode, vec![p(t), p(X1), imm(-16)])
            }
            ScalarAddressing::RegisterOffset => {
                let opcode = match (load, form.bank) {
                    (true, ScalarBank::Fpr) => O::LdrRO,
                    (false, ScalarBank::Fpr) => O::StrRO,
                    (true, _) => narrow(O::LdrbRO, O::LdrhRO, O::LdrRO),
                    (false, _) => narrow(O::StrbRO, O::StrhRO, O::StrRO),
                };
                MachInst::new(opcode, vec![p(t), p(X1), p(X2), imm(6)])
            }
        };
        rows.push((query.to_string(), inst));
    }
    for (query, inst) in &rows {
        assert_eq!(bound(inst).query(), query, "{inst:?}");
    }
    rows
}

/// Which bound-memory rows the clause-2 precondition leaves uncredited: one
/// representative row per attributable form, through the promotion walk.
///
/// Credited (on a qualified host): all 21 pair forms (the pair lane judges
/// every admitted pair row), the 40 general-purpose scalar forms the
/// instruction-derived lane judges (`LDR`/`STR{,B,H}` and the sign-extending
/// `LDRSB`/`LDRSH` immediates, W/X pre/post-index and every GPR register
/// offset) and, since L04-P1, the 24 SIMD&FP scalar forms (immediates 16,
/// register offset 8), which the exact word-bound memory-effect decomposition
/// judges. None is uncredited any more. Before the clause each FP form was
/// credited from its certificate alone (3cdb57101), with nothing in the walk
/// judging that the instruction is an instance of the certified form; until
/// L04-P1 they were uncredited here (40 scalar checked, 24 unrefuted, 61
/// credited). No row is Misbound: the independent word decoders agree with
/// the binder, and with the lanes' re-derived words, on every faithful row.
#[test]
fn only_forms_with_an_in_walk_refutation_check_are_credited() {
    let rows = representative_rows();
    assert_eq!(rows.len(), 21 + 64);
    let insts: Vec<MachInst> = rows.iter().map(|(_, inst)| inst.clone()).collect();
    let report = promotion().verify(&function(insts));
    let qualified = bound_memory_checker_qualification().is_ok();
    let (mut checked, mut unrefuted) = (Vec::new(), Vec::new());
    for ((query, inst), row) in rows.iter().zip(&report.instructions) {
        match &row.result {
            InstructionVerificationResult::Verified {
                proof_name,
                strength: VerificationStrength::Formal,
                degenerate: false,
                ..
            } if qualified => {
                assert!(
                    proof_name.to_lowercase().contains(query.as_str()),
                    "{proof_name}"
                );
                checked.push(query.clone());
            }
            InstructionVerificationResult::Unverified { reason }
                if !qualified && reason.contains(CHECKER_IDENTITY_MISS) =>
            {
                checked.push(query.clone());
            }
            InstructionVerificationResult::Unverified { reason }
                if reason.contains(BOUND_MEMORY_REFUTATION_NOT_RUN) =>
            {
                unrefuted.push(query.clone());
            }
            other => panic!("{query} {inst:?}: {other:?}"),
        }
    }
    eprintln!(
        "BOUND_MEMORY_REFUTATION_PRECONDITION checked={} unrefuted={}\n  unrefuted: {}",
        checked.len(),
        unrefuted.len(),
        unrefuted.join(" ")
    );
    let scalar_checked: Vec<&String> = checked
        .iter()
        .filter(|query| query.starts_with("scalarmem["))
        .collect();
    assert_eq!(checked.len() - scalar_checked.len(), 21, "{checked:?}");
    assert_eq!(scalar_checked.len(), 64, "{scalar_checked:?}");
    assert!(unrefuted.is_empty(), "{unrefuted:?}");
    assert_eq!(
        report.formally_credited_count(),
        if qualified { 85 } else { 0 }
    );
}

// ---------------------------------------------------------------------------
// Clause 3: wrong-form attribution
// ---------------------------------------------------------------------------

/// Each case attributes an instruction to the WRONG form while its own
/// refutation check holds. The rule refuses every one before consulting a
/// certificate. Under the [`binding_check_seam`] mutant (the binding check
/// skipped) the same attribution IS credited through the wrong form's
/// replaying certificate: the refusal is the binding check's, not an absent
/// certificate's.
#[test]
fn an_instruction_attributed_to_the_wrong_form_is_refused() {
    let ldr_w = MachInst::new(O::LdrRI, vec![p(W0), p(X1), imm(8)]);
    let ldr_x = MachInst::new(O::LdrRI, vec![p(X0), p(X1), imm(8)]);
    let stp_w = MachInst::new(O::StpRI, vec![p(W19), p(W20), sp(), imm(16)]);
    let stp_x = MachInst::new(O::StpRI, vec![p(X19), p(X20), sp(), imm(16)]);
    let stp_q_pre = MachInst::new(O::StpPreIndex, vec![p(V0), p(V1), sp(), imm(-32)]);
    let stp_q_post = MachInst::new(O::NeonStpQPost, vec![p(V0), p(V1), sp(), imm(-32)]);
    let str_pre = MachInst::new(O::StrPreIndex, vec![p(X0), sp(), imm(-16)]);
    let str_post = MachInst::new(O::StrPostIndex, vec![p(X0), sp(), imm(-16)]);
    let ldr_ro_lsl3 = MachInst::new(O::LdrRO, vec![p(X0), p(X1), p(X2), imm(7)]);

    // ldr x0, [x1, #8] attributed to the UNSCALED form (same operands).
    let ldr_x_unscaled = match bound(&ldr_x) {
        BoundMemoryBinding::Scalar(mut binding) => {
            binding.form.addressing = ScalarAddressing::Unscaled;
            BoundMemoryBinding::Scalar(binding)
        }
        pair => panic!("{pair:?}"),
    };
    // stp x19, x20, [sp, #16] with its imm7 (2) scaled by the W width: 8.
    let stp_x_misscaled = match bound(&stp_x) {
        BoundMemoryBinding::Pair(mut binding) => {
            binding.offset = 2 * 4;
            BoundMemoryBinding::Pair(binding)
        }
        scalar => panic!("{scalar:?}"),
    };
    // ldr x0, [x1, x2, lsl #3] attributed to mode 6 (LSL #0).
    let ldr_ro_lsl0 = match bound(&ldr_ro_lsl3) {
        BoundMemoryBinding::Scalar(mut binding) => {
            binding.operand = 6;
            BoundMemoryBinding::Scalar(binding)
        }
        pair => panic!("{pair:?}"),
    };
    // The real words of the two forms no production lane judges (clang).
    let str_pre_word = BoundMemoryRefutation::assumed_for_test(
        RefutationCheck::InstructionWord,
        0xf81f_0fe0, // str x0, [sp, #-16]!
    );
    let ldr_ro_word = BoundMemoryRefutation::assumed_for_test(
        RefutationCheck::InstructionWord,
        0xf862_7820, // ldr x0, [x1, x2, lsl #3]
    );

    let cases: Vec<(&str, &MachInst, BoundMemoryBinding, BoundMemoryRefutation)> = vec![
        (
            "W as X: ldr w0 attributed to ldr.ui.gpr.w8",
            &ldr_w,
            bound(&ldr_x),
            instruction_word_check(&ldr_w),
        ),
        (
            "X as W: ldr x0 attributed to ldr.ui.gpr.w4",
            &ldr_x,
            bound(&ldr_w),
            instruction_word_check(&ldr_x),
        ),
        (
            "W as X: stp w19, w20 attributed to stp.offset.gpr.w8",
            &stp_w,
            bound(&stp_x),
            pair_check(&stp_w),
        ),
        (
            "pre as post: stp q0, q1, [sp, #-32]! attributed to stp.post.fpr.w16",
            &stp_q_pre,
            bound(&stp_q_post),
            pair_check(&stp_q_pre),
        ),
        (
            "post as pre: stp q0, q1, [sp], #-32 attributed to stp.pre.fpr.w16",
            &stp_q_post,
            bound(&stp_q_pre),
            pair_check(&stp_q_post),
        ),
        (
            "pre as post: str x0, [sp, #-16]! attributed to str.post.gpr.w8",
            &str_pre,
            bound(&str_post),
            str_pre_word,
        ),
        (
            "unsigned offset as unscaled: ldr x0, [x1, #8] attributed to ldr.unscaled",
            &ldr_x,
            ldr_x_unscaled,
            instruction_word_check(&ldr_x),
        ),
        (
            "mis-scaled imm7: stp x19, x20, [sp, #16] bound at offset 8",
            &stp_x,
            stp_x_misscaled,
            pair_check(&stp_x),
        ),
        (
            "wrong register-offset mode: lsl #3 attributed to lsl #0",
            &ldr_ro_lsl3,
            ldr_ro_lsl0,
            ldr_ro_word,
        ),
        (
            "wrong check kind: a pair check offered for a scalar row",
            &ldr_x,
            bound(&ldr_x),
            pair_check(&stp_x),
        ),
    ];
    for (what, inst, claimed, check) in &cases {
        let refused = credit(inst, claimed, Some(check));
        let reason = assert_misbound(&refused, what);
        eprintln!("WRONG_BINDING {what}: {reason}");
        // Non-vacuity: skip the binding check and the wrong form credits.
        let mutant = {
            let _mutant = binding_check_seam::skip();
            credit(inst, claimed, Some(check))
        };
        assert_certificate_credit(&mutant, &claimed.obligation().name, what);
    }
    // The faithful attributions of the same rows are not refused.
    for (inst, check) in [
        (&ldr_w, instruction_word_check(&ldr_w)),
        (&ldr_x, instruction_word_check(&ldr_x)),
        (&stp_w, pair_check(&stp_w)),
        (&stp_x, pair_check(&stp_x)),
        (&stp_q_pre, pair_check(&stp_q_pre)),
        (&stp_q_post, pair_check(&stp_q_post)),
        (&str_pre, str_pre_word),
        (&ldr_ro_lsl3, ldr_ro_word),
    ] {
        let binding = bound(inst);
        assert_certificate_credit(
            &credit(inst, &binding, Some(&check)),
            &binding.obligation().name,
            &format!("faithful {inst:?}"),
        );
    }
}

/// Clause 3 on the WORD alone: the binder's own attribution, but the held
/// check judged a word of another form (or with another field). Refused.
#[test]
fn a_word_of_another_form_does_not_carry_the_bound_form() {
    let ldr_x = MachInst::new(O::LdrRI, vec![p(X0), p(X1), imm(8)]);
    let ldr_ro_lsl3 = MachInst::new(O::LdrRO, vec![p(X0), p(X1), p(X2), imm(7)]);
    let stp_x = MachInst::new(O::StpRI, vec![p(X19), p(X20), sp(), imm(16)]);
    let own_stp = pair_check(&stp_x).word();
    assert_eq!(own_stp, 0xa901_53f3, "clang: stp x19, x20, [sp, #16]");
    let cases = [
        (
            "ldr x0, [x1, #8] judged as ldur x0, [x1, #8]",
            &ldr_x,
            BoundMemoryRefutation::assumed_for_test(RefutationCheck::InstructionWord, 0xf840_8020),
        ),
        (
            "ldr x0, [x1, #8] judged as ldr w0, [x1, #8]",
            &ldr_x,
            BoundMemoryRefutation::assumed_for_test(RefutationCheck::InstructionWord, 0xb940_0820),
        ),
        (
            "ldr x0, [x1, x2, lsl #3] judged as ldr x0, [x1, x2]",
            &ldr_ro_lsl3,
            BoundMemoryRefutation::assumed_for_test(RefutationCheck::InstructionWord, 0xf862_6820),
        ),
        (
            "stp x19, x20, [sp, #16] judged with imm7 = 16 (unscaled)",
            &stp_x,
            BoundMemoryRefutation::assumed_for_test(
                RefutationCheck::PairConcreteWord,
                (own_stp & !(0x7f << 15)) | (16 << 15),
            ),
        ),
        (
            "stp x19, x20, [sp, #16] judged as a word with bit 25 set",
            &stp_x,
            BoundMemoryRefutation::assumed_for_test(
                RefutationCheck::PairConcreteWord,
                own_stp | (1 << 25),
            ),
        ),
        (
            "stp x19, x20, [sp, #16] judged as stp w19, w20, [sp, #8]",
            &stp_x,
            BoundMemoryRefutation::assumed_for_test(RefutationCheck::PairConcreteWord, 0x2901_53f3),
        ),
    ];
    for (what, inst, check) in &cases {
        let binding = bound(inst);
        let reason = assert_misbound(&credit(inst, &binding, Some(check)), what);
        assert!(
            reason.contains(&format!("{:#010x}", check.word())),
            "{what}: the refusal names the word: {reason}"
        );
        let mutant = {
            let _mutant = binding_check_seam::skip();
            credit(inst, &binding, Some(check))
        };
        assert_certificate_credit(&mutant, &binding.obligation().name, what);
    }
}

/// Clause 3 is field for field, not form for form: a judged word of the SAME
/// form family that differs from the row in one register field, its
/// direction, its extension, its bank, its immediate or its transfer order is
/// refused, and the refusal names the word. The cases above change the
/// addressing, width or scaling; these change what they leave alone. Each
/// is credited under the [`binding_check_seam`] mutant (the refusal is the
/// binding check's), and the row's own word is credited (so the row itself
/// is creditable).
#[test]
fn a_word_differing_in_one_field_does_not_carry_the_bound_form() {
    let ldr_x = MachInst::new(O::LdrRI, vec![p(X0), p(X1), imm(8)]);
    let ldrb = MachInst::new(O::LdrbRI, vec![p(W0), p(X1), imm(1)]);
    let ldr_ro_lsl3 = MachInst::new(O::LdrRO, vec![p(X0), p(X1), p(X2), imm(7)]);
    let stp_x = MachInst::new(O::StpRI, vec![p(X19), p(X20), sp(), imm(16)]);

    let own_ldr = instruction_word_check(&ldr_x).word();
    assert_eq!(own_ldr, 0xf940_0420, "clang: ldr x0, [x1, #8]");
    let own_ldrb = instruction_word_check(&ldrb).word();
    assert_eq!(own_ldrb, 0x3940_0420, "clang: ldrb w0, [x1, #1]");
    let own_ro = 0xf862_7820; // clang: ldr x0, [x1, x2, lsl #3]
    let own_stp = pair_check(&stp_x).word();
    assert_eq!(own_stp, 0xa901_53f3, "clang: stp x19, x20, [sp, #16]");
    let (stp_rt, stp_rt2) = (own_stp & 0x1f, (own_stp >> 10) & 0x1f);
    let stp_swapped = (own_stp & !(0x1f | (0x1f << 10))) | stp_rt2 | (stp_rt << 10);
    assert_eq!(stp_swapped, 0xa901_4ff4, "clang: stp x20, x19, [sp, #16]");

    let scalar = RefutationCheck::InstructionWord;
    let pair = RefutationCheck::PairConcreteWord;
    let cases: [(&str, &MachInst, RefutationCheck, u32); 12] = [
        (
            "ldr x0, [x1, #8] judged as ldr x1, [x1, #8] (Rt)",
            &ldr_x,
            scalar,
            own_ldr ^ 1,
        ),
        (
            "ldr x0, [x1, #8] judged as ldr x0, [x0, #8] (Rn)",
            &ldr_x,
            scalar,
            own_ldr ^ (1 << 5),
        ),
        (
            "ldr x0, [x1, #8] judged as str x0, [x1, #8] (direction)",
            &ldr_x,
            scalar,
            own_ldr & !(1 << 22),
        ),
        (
            "ldr x0, [x1, #8] judged as ldr x0, [x1] (imm12)",
            &ldr_x,
            scalar,
            own_ldr ^ (1 << 10),
        ),
        (
            "ldrb w0, [x1, #1] judged as ldrsb w0, [x1, #1] (extension)",
            &ldrb,
            scalar,
            own_ldrb | (1 << 23),
        ),
        (
            "ldrb w0, [x1, #1] judged as ldrsb x0, [x1, #1] (extension)",
            &ldrb,
            scalar,
            own_ldrb ^ (0b11 << 22),
        ),
        (
            "ldr x0, [x1, x2, lsl #3] judged as ldr x0, [x1, x3, lsl #3] (Rm)",
            &ldr_ro_lsl3,
            scalar,
            own_ro ^ (1 << 16),
        ),
        (
            "ldr x0, [x1, x2, lsl #3] judged as ldr x0, [x1, w2, uxtw #3] (option)",
            &ldr_ro_lsl3,
            scalar,
            own_ro & !(1 << 13),
        ),
        (
            "stp x19, x20, [sp, #16] judged as stp x20, x19, [sp, #16] (order)",
            &stp_x,
            pair,
            stp_swapped,
        ),
        (
            "stp x19, x20, [sp, #16] judged as ldp x19, x20, [sp, #16] (direction)",
            &stp_x,
            pair,
            own_stp | (1 << 22),
        ),
        (
            "stp x19, x20, [sp, #16] judged as stp x19, x20, [x30, #16] (Rn)",
            &stp_x,
            pair,
            own_stp ^ (1 << 5),
        ),
        (
            "stp x19, x20, [sp, #16] judged as stp q19, q20, [sp, #32] (bank)",
            &stp_x,
            pair,
            own_stp | (1 << 26),
        ),
    ];
    for (what, inst, kind, word) in cases {
        let binding = bound(inst);
        let check = BoundMemoryRefutation::assumed_for_test(kind, word);
        let reason = assert_misbound(&credit(inst, &binding, Some(&check)), what);
        assert!(
            reason.contains(&format!("{word:#010x}")),
            "{what}: the refusal names the word: {reason}"
        );
        let mutant = {
            let _mutant = binding_check_seam::skip();
            credit(inst, &binding, Some(&check))
        };
        assert_certificate_credit(&mutant, &binding.obligation().name, what);
    }
    for (inst, kind, word) in [
        (&ldr_x, scalar, own_ldr),
        (&ldrb, scalar, own_ldrb),
        (&ldr_ro_lsl3, scalar, own_ro),
        (&stp_x, pair, own_stp),
    ] {
        let binding = bound(inst);
        assert_certificate_credit(
            &credit(
                inst,
                &binding,
                Some(&BoundMemoryRefutation::assumed_for_test(kind, word)),
            ),
            &binding.obligation().name,
            &format!("own word {word:#010x} of {inst:?}"),
        );
    }
}

/// Through the promotion walk: `LDR X0, [X1, #8]` binds the unsigned-offset
/// form. Judged against the UNSCALED word `LDUR X0, [X1, #8]` (the same
/// access, so the instruction-derived check HOLDS), the row is refused by the
/// binding check, not credited through the unsigned-offset certificate; with
/// the binding check skipped (mutant) the same walk credits it. This failed
/// on 3cdb57101, which credited the row `Formal`.
#[test]
fn an_unscaled_word_is_not_credited_through_the_unsigned_offset_form() {
    let inst = MachInst::new(O::LdrRI, vec![p(X0), p(X1), imm(8)]);
    let own = crate::aarch64_instruction_word_proofs::instruction_word(&inst)
        .expect("admitted")
        .word;
    assert_eq!(own, 0xf940_0420, "clang: ldr x0, [x1, #8]");
    let ldur = 0xf840_8020; // clang: ldur x0, [x1, #8]
    let walk = || {
        let _seam = crate::function_verifier::instruction_word_seam::judge_against(ldur);
        promotion().verify(&function(vec![inst.clone()]))
    };
    let report = walk();
    match &report.instructions[0].result {
        InstructionVerificationResult::Unverified { reason } => assert!(
            reason.starts_with(crate::function_verifier::INSTRUCTION_DERIVED_IS_NOT_CREDIT)
                && reason.contains(" holds ")
                && reason.contains(BOUND_MEMORY_BINDING_MISMATCH)
                && reason.contains("scalarmem[ldr.unscaled.gpr.w8.zx]"),
            "{reason}"
        ),
        other => panic!("the unscaled word must hold its check yet stay uncredited: {other:?}"),
    }
    let mutant = {
        let _mutant = binding_check_seam::skip();
        walk()
    };
    crate::bound_memory_authority::assert_form_credit_or_checker_miss(
        &mutant.instructions[0].result,
        "ScalarMem[ldr.ui.gpr.w8.zx]",
        "binding check skipped",
    );
}

/// Through the promotion walk: `STP X19, X20, [SP, #16]` judged against a
/// word whose `imm7` is the unscaled byte offset (16, i.e. `[SP, #128]`) is
/// never credited: the concrete-word check refutes the displaced access.
#[test]
fn a_misscaled_pair_word_fails_the_promotion_walk() {
    let inst = MachInst::new(O::StpRI, vec![p(X19), p(X20), sp(), imm(16)]);
    let own = pair_check(&inst).word();
    let misscaled = (own & !(0x7f << 15)) | (16 << 15);
    let report = {
        let _seam = crate::function_verifier::pair_word_seam::judge_against(misscaled);
        promotion().verify(&function(vec![inst.clone()]))
    };
    match &report.instructions[0].result {
        InstructionVerificationResult::Failed { proof_name, .. } => {
            assert!(proof_name.contains("PairMemory_STP"), "{proof_name}");
        }
        other => panic!("a mis-scaled pair word must fail its check: {other:?}"),
    }
    assert_eq!(report.formally_credited_count(), 0);
    let faithful = {
        let _seam = crate::function_verifier::pair_word_seam::judge_against(own);
        promotion().verify(&function(vec![inst.clone()]))
    };
    crate::bound_memory_authority::assert_form_credit_or_checker_miss(
        &faithful.instructions[0].result,
        "PairMem[stp.offset.gpr.w8]",
        "own word",
    );
}

/// The independent word decoders agree with the binder on every
/// representative row the lanes judge, and on the hand-encoded words above.
#[test]
fn word_decoders_agree_with_the_binder_on_faithful_rows() {
    for (query, inst) in representative_rows() {
        let binding = bound(&inst);
        let word = match binding {
            BoundMemoryBinding::Pair(_) => Some(pair_check(&inst).word()),
            BoundMemoryBinding::Scalar(_) => {
                crate::aarch64_instruction_word_proofs::instruction_word(&inst).map(|w| w.word)
            }
            BoundMemoryBinding::Atomic(_) => {
                crate::aarch64_atomic_effect::atomic_effect_word(&inst)
            }
            BoundMemoryBinding::Neon(_) => crate::aarch64_memory_effect::memory_effect_word(&inst),
        };
        let Some(word) = word else { continue };
        let decoded = match binding {
            BoundMemoryBinding::Pair(_) => {
                crate::aarch64_pair_memory_forms::decode_pair_memory_binding(word)
                    .map(BoundMemoryBinding::Pair)
            }
            BoundMemoryBinding::Scalar(_) => {
                crate::aarch64_scalar_memory_proofs::decode_scalar_memory_word(word)
                    .map(BoundMemoryBinding::Scalar)
            }
            BoundMemoryBinding::Atomic(_) => crate::aarch64_atomic_forms::decode_atomic_word(word)
                .map(BoundMemoryBinding::Atomic),
            BoundMemoryBinding::Neon(_) => {
                crate::aarch64_neon_structure_forms::decode_neon_structure_word(word)
                    .map(BoundMemoryBinding::Neon)
            }
        };
        assert_eq!(decoded, Some(binding), "{query}: {word:#010x}");
    }
    for (word, inst) in [
        (
            0xf81f_0fe0,
            MachInst::new(O::StrPreIndex, vec![p(X0), sp(), imm(-16)]),
        ),
        (
            0xf81f_07e0,
            MachInst::new(O::StrPostIndex, vec![p(X0), sp(), imm(-16)]),
        ),
        (
            0xf862_7820,
            MachInst::new(O::LdrRO, vec![p(X0), p(X1), p(X2), imm(7)]),
        ),
    ] {
        match bound(&inst) {
            BoundMemoryBinding::Scalar(binding) => assert_eq!(
                crate::aarch64_scalar_memory_proofs::decode_scalar_memory_word(word),
                Some(binding),
                "{word:#010x}"
            ),
            pair => panic!("{pair:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Certificate bodies on disk
// ---------------------------------------------------------------------------

/// A corrupted, truncated, substituted, garbage or missing body under the
/// committed file name credits nothing; a faithful copy in the same
/// directory replays (on a qualified host), so each refusal is the body's.
#[test]
fn a_corrupted_or_substituted_certificate_body_on_disk_credits_nothing() {
    use crate::canary_cert::bound_memory::{
        BOUND_MEMORY_CERT_DIR, bound_memory_cert_replays_from_dir,
    };
    let queries = certifiable_bound_memory_queries();
    let pick = |file: &str| {
        queries
            .iter()
            .find(|query| query.file == file)
            .unwrap_or_else(|| panic!("{file} is a committed query"))
            .clone()
    };
    let target = pick("scalarmem_str_ui_gpr_w1.lratcert");
    let other = pick("scalarmem_str_ui_gpr_w2.lratcert");
    let smt2 = crate::verdict_db::db_obligation_smt2(&target.obligation);
    let committed = std::path::Path::new(BOUND_MEMORY_CERT_DIR);
    let body = |file: &str| {
        std::fs::read(committed.join(format!("{file}.zst"))).expect("committed body is readable")
    };
    let compress = |text: &[u8]| zstd::stream::encode_all(text, 3).expect("zstd");
    let faithful = body(&target.file);
    let text = zstd::stream::decode_all(&faithful[..]).expect("committed body decompresses");
    // One byte of the DRAT proof, far from the header, flipped.
    let mut flipped = text.clone();
    let at = flipped.len() - 16;
    flipped[at] ^= 0x01;

    let cases: Vec<(&str, Option<Vec<u8>>, &str)> = vec![
        (
            "one flipped byte",
            Some(compress(&flipped)),
            "digest mismatch",
        ),
        (
            "another query's body",
            Some(body(&other.file)),
            "digest mismatch",
        ),
        (
            "truncated stream",
            Some(faithful[..faithful.len() / 2].to_vec()),
            "cannot decompress",
        ),
        (
            "garbage text",
            Some(compress(b"not a certificate\n")),
            "digest mismatch",
        ),
        ("missing", None, "cannot read"),
    ];
    for (what, bytes, expected) in cases {
        let dir = tempfile::tempdir().expect("tempdir");
        if let Some(bytes) = bytes {
            std::fs::write(dir.path().join(format!("{}.zst", target.file)), bytes).unwrap();
        }
        match bound_memory_cert_replays_from_dir(&smt2, dir.path()) {
            Ok(()) => panic!("{what}: a bad body was credited"),
            Err(reason) => assert!(reason.contains(expected), "{what}: {reason}"),
        }
    }
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(dir.path().join(format!("{}.zst", target.file)), &faithful).unwrap();
    let copied = bound_memory_cert_replays_from_dir(&smt2, dir.path());
    match bound_memory_checker_qualification() {
        Ok(()) => assert_eq!(copied, Ok(()), "the faithful copy must replay"),
        Err(_) => assert!(copied.is_err()),
    }
}
