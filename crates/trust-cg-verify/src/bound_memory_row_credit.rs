// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Opcode-level coverage-gate credit for the bound-memory rows (ledger
//! `L04-P1`, `X-OPCODES-P1`, `X-OPCODES-P2`).
//!
//! # The problem the opcode row has
//!
//! A memory or atomic row is authenticated PER EMITTED INSTRUCTION by the
//! Formal-only rule ([`crate::bound_memory_authority`]): the instruction
//! binds one FORM theorem (operation x addressing x bank x width x
//! extension), its own word is judged in process and decodes to that form,
//! and the form theorem's committed certificate replays. The opcode alone
//! names none of that: `LDR` (immediate) is twelve forms, `LDADDAL` four. So,
//! exactly as for `MOVK`/`MOVN` (`coverage_gate::aarch64_form_polymorphic_proofs`),
//! an opcode row may be credited only when EVERY legal form of the opcode
//! carries that per-instruction authority; crediting one form for all would
//! be the unfaithful inheritance #62 retracted.
//!
//! # What a credited row means
//!
//! For each legal form of the opcode ([`crate::aarch64_atomic_forms::atomic_opcode_forms`],
//! [`crate::aarch64_scalar_memory_proofs::scalar_opcode_forms`]):
//!
//! 1. **Formal:** the form theorem's committed certificate replays in this
//!    process with the vendored independent checker (`drat-trim`), through
//!    the same lookup the walk uses
//!    ([`crate::bound_memory_authority::form_certificate_status`]);
//! 2. **binding (testing grade):** representative instructions of the
//!    opcode in that form go through the rule's clauses 2-4
//!    ([`crate::bound_memory_authority::credit_bound_form`]): the in-process
//!    word judgement held (the atomic decomposition, decided exactly; the
//!    instruction-derived obligation for a scalar row), the judged word decodes
//!    to the form, and the certificate replays — so the walk would credit
//!    those instructions;
//! 3. **controls (testing grade):** every applicable machine-side defect of
//!    the form theorem is refuted by the in-process structured-grid search
//!    (atomic: wrong operation, swapped operands, signedness, max/min, short
//!    or extra access, big-endian, displaced address, sign-extended or new
//!    returned value, missing write, CAS writing on failure or comparing the
//!    whole register; scalar: the twelve defects of
//!    [`crate::aarch64_scalar_memory_proofs::ScalarMachineMutation`]); for an
//!    atomic row also every single-bit flip of the representative word, a
//!    word of the neighbouring operation and a word of another width refute
//!    its decomposition, and the word's ordering bits are the opcode's own as
//!    the `L03-P3` memory-order decoder classifies them
//!    ([`crate::aarch64_memory_order::decode_ordering_word`]).
//!
//! The credit is the certificate's (clause 1); everything else is the
//! in-process evidence that ties instructions of this opcode to it. The
//! H/S/D/Q forms of `LDR`/`STR`, which the instruction-derived lane does not
//! model, are judged by their exact word-bound memory-effect decomposition
//! ([`crate::aarch64_memory_effect`]).
//! The ordering of an atomic access against other threads is the `L03-P3`
//! table's claim, not this credit's.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use crate::aarch64_atomic_effect as atomic_effect;
use crate::aarch64_atomic_forms as atomic_forms;
use crate::aarch64_neon_structure_forms as neon_forms;
use crate::aarch64_pair_memory_forms as pair_forms;
use crate::aarch64_scalar_memory_proofs as scalar_forms;
use crate::bound_memory_authority::{
    BoundMemoryBinding, BoundMemoryCredit, BoundMemoryRefutation, credit_bound_form,
    form_certificate_status,
};
use trust_cg_ir::AArch64Opcode as O;

/// What one credited bound-memory opcode row rests on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundMemoryRowCredit {
    /// The form queries of the opcode, each with a replayed certificate.
    pub forms: Vec<&'static str>,
    /// Representative instructions credited through clauses 2-4.
    pub instructions: usize,
    /// Machine-side defects of the form theorems refuted in process.
    pub defects_refuted: usize,
    /// Word controls refuted (single-bit flips, neighbouring operation and
    /// width) — atomic rows only.
    pub word_controls_refuted: usize,
}

/// One form's opcode-independent evidence: its defects refuted and its
/// certificate replayed. Memoized per form query for the process (both are
/// deterministic, and only a SUCCESSFUL replay is memoized below it too).
fn form_evidence(
    query: &'static str,
    compute: impl FnOnce() -> Result<usize, String>,
) -> Result<usize, String> {
    static MEMO: OnceLock<Mutex<HashMap<&'static str, Result<usize, String>>>> = OnceLock::new();
    let memo = MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(done) = memo.lock().unwrap_or_else(|p| p.into_inner()).get(query) {
        return done.clone();
    }
    let result = compute();
    memo.lock()
        .unwrap_or_else(|p| p.into_inner())
        .insert(query, result.clone());
    result
}

fn certified(
    inst: &trust_cg_ir::MachInst,
    binding: &BoundMemoryBinding,
    check: &BoundMemoryRefutation,
) -> Result<(), String> {
    match credit_bound_form(inst, binding, Some(check), true, None) {
        BoundMemoryCredit::Certified { .. } => Ok(()),
        other => Err(format!(
            "{inst:?} is not credited through clauses 2-4: {}",
            other
                .uncredited_note()
                .unwrap_or_else(|| format!("{other:?}"))
        )),
    }
}

// ===========================================================================
// Atomic rows
// ===========================================================================

/// The opcode-level credit of an atomic row, or `None` for a non-atomic
/// opcode. `Err` names the first form or control that failed.
pub fn atomic_row_credit(opcode: O) -> Option<Result<BoundMemoryRowCredit, String>> {
    let forms = atomic_forms::atomic_opcode_forms(opcode)?;
    let shape = atomic_forms::atomic_opcode_shape(opcode)?;
    Some((|| {
        let mut credit = BoundMemoryRowCredit {
            forms: Vec::new(),
            instructions: 0,
            defects_refuted: 0,
            word_controls_refuted: 0,
        };
        for form in &forms {
            let query = form.query().ok_or("an atomic opcode form has no query")?;
            credit.defects_refuted += form_evidence(query, || atomic_form_evidence(form))
                .map_err(|why| format!("{query}: {why}"))?;
            credit.forms.push(query);
            // Two register assignments: distinct registers, and an SP base
            // with Rs == Rt where the operation allows it.
            for (rs, rt, rn) in [(1, 2, 3), (9, 9, 31)] {
                let inst = atomic_forms::representative_instruction(opcode, form.bytes, rs, rt, rn)
                    .ok_or_else(|| format!("{query}: no representative instruction"))?;
                let decomposition = atomic_effect::atomic_effect(&inst)
                    .ok_or_else(|| format!("{inst:?}: the atomic lane does not admit it"))?;
                let verdict = atomic_effect::judge(&decomposition);
                let check = BoundMemoryRefutation::atomic_effect(&decomposition, &verdict)
                    .ok_or_else(|| {
                        format!("{inst:?}: its decomposition did not hold: {verdict:?}")
                    })?;
                certified(
                    &inst,
                    &BoundMemoryBinding::Atomic(decomposition.binding),
                    &check,
                )?;
                ordering_matches(opcode, &shape, form, decomposition.word)?;
                credit.word_controls_refuted += word_controls(&inst, &decomposition, form)?;
                credit.instructions += 1;
            }
        }
        Ok(credit)
    })())
}

/// The form theorem's defects refuted on the grid, and its certificate.
fn atomic_form_evidence(form: &atomic_forms::AtomicForm) -> Result<usize, String> {
    let faithful = atomic_forms::proof_atomic_form(form).ok_or("illegal form")?;
    if faithful.is_degenerate() {
        return Err("the form theorem is X == X".into());
    }
    let mut refuted = 0;
    for mutation in atomic_forms::AtomicMachineMutation::DEFECTS {
        let Some(wrong) = atomic_forms::proof_atomic_form_with_mutation(form, mutation) else {
            continue;
        };
        if atomic_forms::grid_counterexample(form, &wrong).is_none() {
            return Err(format!("the {mutation:?} defect is not refuted in process"));
        }
        refuted += 1;
    }
    form_certificate_status(&faithful)?;
    Ok(refuted)
}

/// The word's ordering class (`L03-P3`'s decoder) is the opcode's own.
fn ordering_matches(
    opcode: O,
    shape: &atomic_forms::AtomicOpcodeShape,
    form: &atomic_forms::AtomicForm,
    word: u32,
) -> Result<(), String> {
    use crate::aarch64_memory_order::{AcquireKind, LseOp, OrderingWord, decode_ordering_word};
    use atomic_forms::AtomicOp;
    let bytes = form.bytes;
    let decoded = decode_ordering_word(word);
    let expected = match shape.op {
        AtomicOp::LoadAcquire => OrderingWord::LoadAcquire {
            bytes,
            kind: AcquireKind::Rcsc,
            rt_zero: false,
        },
        AtomicOp::StoreRelease => OrderingWord::StoreRelease { bytes },
        AtomicOp::Cas => OrderingWord::Cas {
            bytes,
            pair: false,
            acquire_bit: shape.acquire,
            release: shape.release,
            rs_zero: false,
        },
        op => OrderingWord::LseRmw {
            bytes,
            op: match op {
                AtomicOp::Add => LseOp::Add,
                AtomicOp::Clr => LseOp::Clr,
                AtomicOp::Eor => LseOp::Eor,
                AtomicOp::Set => LseOp::Set,
                AtomicOp::Smax => LseOp::Smax,
                AtomicOp::Smin => LseOp::Smin,
                AtomicOp::Umax => LseOp::Umax,
                AtomicOp::Umin => LseOp::Umin,
                _ => LseOp::Swp,
            },
            acquire_bit: shape.acquire,
            release: shape.release,
            rt_zero: false,
        },
    };
    if decoded == expected {
        Ok(())
    } else {
        Err(format!(
            "{opcode:?} word {word:#010x}: the memory-order decoder reads {decoded:?}, the opcode \
             names {expected:?}"
        ))
    }
}

/// Every single-bit flip of the word refutes the decomposition, and a word
/// of the neighbouring operation and one of another width refute a VALUE or
/// MEMORY part on its own.
fn word_controls(
    inst: &trust_cg_ir::MachInst,
    decomposition: &atomic_effect::AtomicEffectDecomposition,
    form: &atomic_forms::AtomicForm,
) -> Result<usize, String> {
    use atomic_effect::{AtomicEffectPart, AtomicEffectVerdict, atomic_effect_for_word, judge};
    use atomic_forms::AtomicOp;
    let word = decomposition.word;
    let mut refuted = 0;
    for bit in 0..32 {
        let flipped = atomic_effect_for_word(inst, word ^ (1 << bit))
            .ok_or("the atomic lane stopped admitting the instruction")?;
        if !matches!(judge(&flipped), AtomicEffectVerdict::Refuted { .. }) {
            return Err(format!("{inst:?}: the flip of bit {bit} is not refuted"));
        }
        refuted += 1;
    }
    let operation_bit = match form.op {
        AtomicOp::Swp => 15,
        AtomicOp::Cas => 21,
        AtomicOp::LoadAcquire | AtomicOp::StoreRelease => 22,
        _ => 12,
    };
    for bit in [operation_bit, 30] {
        let neighbour = atomic_effect_for_word(inst, word ^ (1 << bit))
            .ok_or("the atomic lane stopped admitting the instruction")?;
        let semantic = neighbour.parts.iter().any(|part| {
            part.part != AtomicEffectPart::Fields
                && matches!(
                    atomic_effect::decide_exactly(&part.obligation),
                    Some(Err(_))
                )
        });
        if !semantic {
            return Err(format!(
                "{inst:?}: the neighbouring word (bit {bit}) is refuted by its fields alone"
            ));
        }
        refuted += 1;
    }
    Ok(refuted)
}

// ===========================================================================
// Scalar rows
// ===========================================================================

/// The opcode-level credit of a scalar memory row, or `None` for an opcode
/// the scalar binder never attributes. `Err` names the first form that has
/// no replayed certificate, a defect that survived, or a form no in-process
/// lane judges.
pub fn scalar_row_credit(opcode: O) -> Option<Result<BoundMemoryRowCredit, String>> {
    let forms = scalar_forms::scalar_opcode_forms(opcode)?;
    Some((|| {
        let mut credit = BoundMemoryRowCredit {
            forms: Vec::new(),
            instructions: 0,
            defects_refuted: 0,
            word_controls_refuted: 0,
        };
        for form in &forms {
            let query = form.query().ok_or("a scalar opcode form has no query")?;
            credit.defects_refuted += form_evidence(query, || scalar_form_evidence(form))
                .map_err(|why| format!("{query}: {why}"))?;
            credit.forms.push(query);
            let inst = scalar_forms::representative_scalar_instruction(opcode, form)
                .ok_or_else(|| format!("{query}: no representative instruction of {opcode:?}"))?;
            let config = crate::lowering_proof::VerificationConfig::for_proof_promotion();
            // Clause 2: the instruction-derived obligation for a general-
            // purpose form, the exact memory-effect decomposition for H/S/D/Q.
            let check = if form.bank == scalar_forms::ScalarBank::Fpr {
                let decomposition = crate::aarch64_memory_effect::memory_effect(&inst)
                    .ok_or_else(|| format!("{inst:?}: the memory-effect lane does not admit it"))?;
                BoundMemoryRefutation::memory_effect(&decomposition, &config).ok_or_else(|| {
                    format!("{inst:?}: its memory-effect decomposition did not hold exactly")
                })?
            } else {
                let verdict = crate::aarch64_instruction_word_proofs::instruction_word_verdict(
                    &inst, &config,
                )
                .ok_or_else(|| {
                    format!("{inst:?}: the instruction-derived lane does not admit it")
                })?;
                BoundMemoryRefutation::instruction_word(&verdict).ok_or_else(|| {
                    format!("{inst:?}: its instruction-derived obligation did not hold")
                })?
            };
            let binding = scalar_forms::bind_scalar_memory_instruction(&inst)
                .map_err(|why| format!("{inst:?}: {why}"))?;
            certified(&inst, &BoundMemoryBinding::Scalar(binding), &check)?;
            credit.instructions += 1;
        }
        Ok(credit)
    })())
}

// ===========================================================================
// Pair rows
// ===========================================================================

/// The pair forms an opcode can be emitted in: W/X and S/D/Q transfers for
/// `STP`/`LDP` in their addressing mode, Q only for the NEON post-index
/// pairs.
pub fn pair_opcode_forms(opcode: O) -> Option<Vec<pair_forms::PairMemoryForm>> {
    use pair_forms::PairRegisterBank::{Fpr, Gpr};
    if !pair_forms::is_pair_memory_opcode(opcode) {
        return None;
    }
    Some(
        [(Gpr, 4), (Gpr, 8), (Fpr, 4), (Fpr, 8), (Fpr, 16)]
            .into_iter()
            .filter_map(|(bank, bytes)| pair_forms::pair_form_for(opcode, bank, bytes))
            .collect(),
    )
}

/// A representative pair instruction of `opcode` in `form`:
/// `[Rt, Rt2, SP, #16]` with W19/W20, X19/X20, S0/S1, D0/D1 or Q0/Q1.
fn representative_pair_instruction(
    opcode: O,
    form: &pair_forms::PairMemoryForm,
) -> Option<trust_cg_ir::MachInst> {
    use pair_forms::PairRegisterBank::{Fpr, Gpr};
    use trust_cg_ir::aarch64_regs::{D0, D1, S0, S1, V0, V1, W19, W20, X19, X20};
    use trust_cg_ir::{MachOperand, SpecialReg};
    let (t, t2) = match (form.bank, form.element_bytes) {
        (Gpr, 4) => (W19, W20),
        (Gpr, _) => (X19, X20),
        (Fpr, 4) => (S0, S1),
        (Fpr, 8) => (D0, D1),
        (Fpr, _) => (V0, V1),
    };
    let inst = trust_cg_ir::MachInst::new(
        opcode,
        vec![
            MachOperand::PReg(t),
            MachOperand::PReg(t2),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(16),
        ],
    );
    (pair_forms::bind_admitted_pair_instruction(&inst).ok()?.form == *form).then_some(inst)
}

/// The opcode-level credit of a pair row, or `None` for a non-pair opcode.
/// Clause 2 for a pair row is the pair lane's concrete-word obligation
/// (`aarch64_pair_memory_proofs`), decided by the evaluation lane: a held
/// verdict means "not refuted", which is what the walk requires too.
pub fn pair_row_credit(opcode: O) -> Option<Result<BoundMemoryRowCredit, String>> {
    let forms = pair_opcode_forms(opcode)?;
    Some((|| {
        if forms.is_empty() {
            return Err(format!("{opcode:?} has no legal pair form"));
        }
        let mut credit = BoundMemoryRowCredit {
            forms: Vec::new(),
            instructions: 0,
            defects_refuted: 0,
            word_controls_refuted: 0,
        };
        let config = crate::lowering_proof::VerificationConfig::default();
        for form in &forms {
            let query = form.query().ok_or("a pair opcode form has no query")?;
            credit.defects_refuted += form_evidence(query, || pair_form_evidence(form))
                .map_err(|why| format!("{query}: {why}"))?;
            credit.forms.push(query);
            let inst = representative_pair_instruction(opcode, form)
                .ok_or_else(|| format!("{query}: no representative instruction of {opcode:?}"))?;
            let (obligation, word) =
                crate::aarch64_pair_memory_proofs::pair_memory_obligation_and_word(&inst)
                    .ok_or_else(|| format!("{inst:?}: the pair lane does not admit it"))?;
            let (verdict, _) = crate::lowering_proof::discharge_reconstructed_obligation(
                &obligation,
                &obligation,
                &config,
            );
            let check =
                BoundMemoryRefutation::pair_concrete_word(word, &verdict).ok_or_else(|| {
                    format!("{inst:?}: its concrete-word obligation did not hold: {verdict:?}")
                })?;
            let binding = pair_forms::bind_admitted_pair_instruction(&inst)
                .map_err(|why| format!("{inst:?}: {why}"))?;
            certified(&inst, &BoundMemoryBinding::Pair(binding), &check)?;
            credit.instructions += 1;
        }
        Ok(credit)
    })())
}

// ===========================================================================
// NEON structure rows
// ===========================================================================

/// The opcode-level credit of a NEON `LD1`/`ST1` post-index row, or `None`
/// for another opcode. Every one of the seven arrangements of the opcode
/// needs its replayed form certificate, its machine defects refuted on the
/// grid, and representative instructions (an X base and SP) credited through
/// clauses 2-4, clause 2 being the exact word-bound memory-effect
/// decomposition (`L04-P6`).
pub fn neon_row_credit(opcode: O) -> Option<Result<BoundMemoryRowCredit, String>> {
    let forms = neon_forms::neon_opcode_forms(opcode)?;
    Some((|| {
        let mut credit = BoundMemoryRowCredit {
            forms: Vec::new(),
            instructions: 0,
            defects_refuted: 0,
            word_controls_refuted: 0,
        };
        let config = crate::lowering_proof::VerificationConfig::for_proof_promotion();
        for form in &forms {
            let query = form.query().ok_or("a NEON opcode form has no query")?;
            credit.defects_refuted += form_evidence(query, || neon_form_evidence(form))
                .map_err(|why| format!("{query}: {why}"))?;
            credit.forms.push(query);
            for base_sp in [false, true] {
                let inst = neon_forms::representative_neon_instruction(form, base_sp);
                let decomposition = crate::aarch64_memory_effect::memory_effect(&inst)
                    .ok_or_else(|| format!("{inst:?}: the memory-effect lane does not admit it"))?;
                let check = BoundMemoryRefutation::memory_effect(&decomposition, &config)
                    .ok_or_else(|| {
                        format!("{inst:?}: its memory-effect decomposition did not hold exactly")
                    })?;
                let binding = neon_forms::bind_neon_structure_instruction(&inst)
                    .map_err(|why| format!("{inst:?}: {why}"))?;
                certified(&inst, &BoundMemoryBinding::Neon(binding), &check)?;
                credit.instructions += 1;
            }
        }
        Ok(credit)
    })())
}

fn neon_form_evidence(form: &neon_forms::NeonStructureForm) -> Result<usize, String> {
    let faithful = neon_forms::proof_neon_structure_form(form).ok_or("illegal form")?;
    if faithful.is_degenerate() {
        return Err("the form theorem is X == X".into());
    }
    let mut refuted = 0;
    for mutation in neon_forms::NeonStructureMutation::DEFECTS {
        let Some(wrong) = neon_forms::proof_neon_structure_form_with_mutation(form, mutation)
        else {
            continue;
        };
        if neon_forms::grid_counterexample(&wrong, form).is_none() {
            return Err(format!("the {mutation:?} defect is not refuted in process"));
        }
        refuted += 1;
    }
    form_certificate_status(&faithful)?;
    Ok(refuted)
}

fn pair_form_evidence(form: &pair_forms::PairMemoryForm) -> Result<usize, String> {
    let faithful = pair_forms::proof_pair_memory_form(form).ok_or("illegal form")?;
    if faithful.is_degenerate() {
        return Err("the form theorem is X == X".into());
    }
    let mut refuted = 0;
    for mutation in pair_forms::PairMachineMutation::DEFECTS {
        let Some(wrong) = pair_forms::proof_pair_memory_form_with_mutation(form, mutation) else {
            continue;
        };
        if pair_forms::grid_counterexample(&wrong, form).is_none() {
            return Err(format!("the {mutation:?} defect is not refuted in process"));
        }
        refuted += 1;
    }
    form_certificate_status(&faithful)?;
    Ok(refuted)
}

fn scalar_form_evidence(form: &scalar_forms::ScalarMemoryForm) -> Result<usize, String> {
    let faithful = scalar_forms::proof_scalar_memory(form).ok_or("illegal form")?;
    if faithful.is_degenerate() {
        return Err("the form theorem is X == X".into());
    }
    let mut refuted = 0;
    for mutation in scalar_forms::ScalarMachineMutation::DEFECTS {
        let Some(wrong) = scalar_forms::proof_scalar_memory_with_mutation(form, mutation) else {
            continue;
        };
        if scalar_forms::grid_counterexample(&wrong, form).is_none() {
            return Err(format!("the {mutation:?} defect is not refuted in process"));
        }
        refuted += 1;
    }
    form_certificate_status(&faithful)?;
    Ok(refuted)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_pair_opcode_row_is_credited_on_a_qualified_host() {
        let qualified = crate::bound_memory_authority::bound_memory_checker_qualification();
        let expected = [
            (O::StpRI, 5),
            (O::LdpRI, 5),
            (O::StpPreIndex, 5),
            (O::LdpPostIndex, 5),
            (O::NeonStpQPost, 1),
            (O::NeonLdpQPost, 1),
        ];
        for (opcode, forms) in expected {
            assert_eq!(
                pair_opcode_forms(opcode).unwrap().len(),
                forms,
                "{opcode:?}"
            );
            match (&qualified, pair_row_credit(opcode).expect("pair opcode")) {
                (Ok(()), Ok(credit)) => {
                    assert_eq!(credit.forms.len(), forms, "{opcode:?}");
                    assert_eq!(credit.instructions, forms, "{opcode:?}");
                    assert!(credit.defects_refuted >= 6 * forms, "{opcode:?}");
                }
                (Err(_), Err(_)) => {}
                (qualification, other) => {
                    panic!("{opcode:?}: {other:?} under qualification {qualification:?}")
                }
            }
        }
        assert!(pair_row_credit(O::LdrRI).is_none());
    }

    #[test]
    fn every_neon_structure_row_is_credited_on_a_qualified_host() {
        let qualified = crate::bound_memory_authority::neon_memory_checker_qualification();
        for opcode in [O::NeonLd1Post, O::NeonSt1Post] {
            let forms = neon_forms::neon_opcode_forms(opcode).unwrap();
            assert_eq!(forms.len(), 7, "{opcode:?}");
            match (&qualified, neon_row_credit(opcode).expect("NEON opcode")) {
                (Ok(()), Ok(credit)) => {
                    assert_eq!(credit.forms.len(), 7, "{opcode:?}");
                    assert_eq!(credit.instructions, 14, "{opcode:?}");
                    assert!(credit.defects_refuted >= 5 * 7, "{opcode:?}");
                }
                (Err(_), Err(_)) => {}
                (qualification, other) => {
                    panic!("{opcode:?}: {other:?} under qualification {qualification:?}")
                }
            }
        }
        assert!(neon_row_credit(O::LdrRI).is_none());
    }

    #[test]
    fn every_atomic_opcode_row_is_credited_on_a_qualified_host() {
        let qualified = crate::bound_memory_authority::atomic_memory_checker_qualification();
        for opcode in atomic_forms::ATOMIC_MEMORY_OPCODES {
            let credit = atomic_row_credit(opcode).expect("atomic opcode");
            match (&qualified, credit) {
                (Ok(()), Ok(credit)) => {
                    let forms = atomic_forms::atomic_opcode_forms(opcode).unwrap();
                    assert_eq!(credit.forms.len(), forms.len(), "{opcode:?}");
                    assert_eq!(credit.instructions, 2 * forms.len(), "{opcode:?}");
                    assert!(credit.defects_refuted >= 2 * forms.len(), "{opcode:?}");
                    assert_eq!(
                        credit.word_controls_refuted,
                        2 * forms.len() * 34,
                        "{opcode:?}"
                    );
                }
                (Err(_), Err(why)) => assert!(
                    why.contains(crate::bound_memory_authority::CHECKER_IDENTITY_MISS),
                    "{opcode:?}: {why}"
                ),
                (qualification, other) => {
                    panic!("{opcode:?}: {other:?} under qualification {qualification:?}")
                }
            }
        }
        assert!(atomic_row_credit(O::Ldxr).is_none());
    }

    #[test]
    fn scalar_rows_need_every_form_judged_and_certified() {
        let qualified = crate::bound_memory_authority::bound_memory_checker_qualification();
        for opcode in [
            O::LdrbRI,
            O::LdrhRI,
            O::LdrsbRI,
            O::LdrshRI,
            O::StrbRI,
            O::StrhRI,
            O::LdrPreIndex,
            O::LdrPostIndex,
            O::StrPreIndex,
            O::StrPostIndex,
            O::LdrbRO,
            O::LdrhRO,
            O::StrbRO,
            O::StrhRO,
        ] {
            match (
                &qualified,
                scalar_row_credit(opcode).expect("scalar opcode"),
            ) {
                (Ok(()), Ok(credit)) => {
                    assert_eq!(
                        credit.forms.len(),
                        scalar_forms::scalar_opcode_forms(opcode).unwrap().len(),
                        "{opcode:?}"
                    );
                }
                (Err(_), Err(_)) => {}
                (qualification, other) => {
                    panic!("{opcode:?}: {other:?} under qualification {qualification:?}")
                }
            }
        }
        // The register-class opcodes' H/S/D/Q forms are judged by the exact
        // memory-effect decomposition.
        for opcode in [O::LdrRI, O::StrRI, O::LdrRO, O::StrRO] {
            match (
                &qualified,
                scalar_row_credit(opcode).expect("scalar opcode"),
            ) {
                (Ok(()), Ok(credit)) => assert_eq!(
                    credit.forms.len(),
                    scalar_forms::scalar_opcode_forms(opcode).unwrap().len(),
                    "{opcode:?}"
                ),
                (Err(_), Err(_)) => {}
                (qualification, other) => {
                    panic!("{opcode:?}: {other:?} under qualification {qualification:?}")
                }
            }
        }
        // Volatile aliases and the literal load bind no form at the opcode.
        for opcode in [O::VolatileLdrRI, O::LdrLiteral, O::AddRR] {
            assert!(scalar_row_credit(opcode).is_none(), "{opcode:?}");
        }
    }

    #[test]
    fn the_scalar_opcode_form_table_matches_the_binder() {
        let mut total = 0;
        for opcode in [
            O::LdrRI,
            O::StrRI,
            O::LdrbRI,
            O::LdrhRI,
            O::LdrsbRI,
            O::LdrshRI,
            O::StrbRI,
            O::StrhRI,
            O::LdrPreIndex,
            O::LdrPostIndex,
            O::StrPreIndex,
            O::StrPostIndex,
            O::LdrRO,
            O::StrRO,
            O::LdrbRO,
            O::LdrhRO,
            O::StrbRO,
            O::StrhRO,
        ] {
            let forms = scalar_forms::scalar_opcode_forms(opcode).unwrap();
            for form in &forms {
                let inst = scalar_forms::representative_scalar_instruction(opcode, form)
                    .unwrap_or_else(|| panic!("{opcode:?} {form:?}: no representative"));
                assert_eq!(
                    scalar_forms::bind_scalar_memory_instruction(&inst)
                        .unwrap()
                        .form,
                    *form
                );
            }
            total += forms.len();
        }
        // LDR/STR imm: 2 x 6 each; LDRB/LDRH/STRB/STRH imm: 2 each;
        // LDRSB/LDRSH: 4 each; writeback: 2 each; LDR/STR RO: 6 each; the
        // byte/halfword RO forms: 1 each.
        assert_eq!(total, 24 + 8 + 8 + 8 + 12 + 4);
    }
}
