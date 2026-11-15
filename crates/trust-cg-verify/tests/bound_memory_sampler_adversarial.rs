// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Does the DEFAULT evaluation sampler (`VerificationConfig::default()`, 100k
//! random samples plus the edge battery) accept deliberately WRONG
//! bound-memory theorems? This is the measurement behind the owner's
//! Formal-only ruling (2026-09-29, `bound_memory_authority`): no bound-memory
//! row is credited by sampling. The report is
//! `reports/2026-09-29-bound-memory-sampler-false-pass/`.
//!
//! Three theorem families are judged, each as (faithful theorem, machine-side
//! defect) pairs, with every sampler `Valid` on a defect re-judged by AY and
//! every AY counterexample re-evaluated in process (so a "false pass" is a
//! solver counterexample the evaluator itself confirms, never an assumption
//! that a mutation must be wrong):
//!
//! 1. the FORM theorems (`PairMem[...]`, 21 forms; `ScalarMem[...]`, 65
//!    forms; `aarch64_pair_memory_forms`, `aarch64_scalar_memory_proofs`), the
//!    hand port of trust-cg 7af30f92d that the Formal-only rule credits by
//!    certificate. That commit measured 93/143 and 395/478 of their defects
//!    accepted. They observe memory through a free query byte or a
//!    single-point memory `ite(x == p, c, d)`, which uniform sampling almost
//!    never places on an accessed byte. The default sampler's
//!    precondition-directed trials (41e850748) reach some of those points,
//!    and it still accepts 43/143 and 153/478 (2026-10-22).
//! 2. MAIN's pair theorem (`aarch64_pair_memory_proofs`, the one
//!    `FunctionVerifier::try_pair_memory` discharges for every admitted
//!    `STP`/`LDP`), with every single-bit mutation of the encoded word plus
//!    transposed, duplicated and off-by-one-immediate words.
//! 3. MAIN's scalar `LDR`/`STR`(`B`/`H`) immediate theorem
//!    (`aarch64_instruction_word_proofs`, the one
//!    `FunctionVerifier::try_instruction_word` reports), with every single-bit
//!    mutation of the encoded word.
//!
//! The numbers are PINNED: when the sampler, a theorem or a corpus changes,
//! the test fails and the report must be re-measured, not the pin nudged.
//!
//! Run: `scripts/trust_cargo.sh test -p trust-cg-verify --test
//! bound_memory_sampler_adversarial -- --nocapture --test-threads 1`

use trust_cg_verify::aarch64_pair_memory_forms as form_pair;
use trust_cg_verify::aarch64_scalar_memory_proofs as form_scalar;

use std::collections::HashSet;

use rayon::prelude::*;
use trust_cg_ir::aarch64_regs::PReg;
use trust_cg_ir::{AArch64Opcode as O, MachInst, MachOperand, SpecialReg};
use trust_cg_verify::aarch64_instruction_word_proofs::{
    Decision, Outcome, instruction_word, instruction_word_verdict_for,
};
use trust_cg_verify::aarch64_pair_memory_proofs::{
    pair_memory_intent, pair_memory_obligation, pair_memory_obligation_from_word, pair_memory_word,
};
use trust_cg_verify::ay_bridge::{AYConfig, AYResult, ay_available, verify_with_ay};
use trust_cg_verify::lowering_proof::{
    ProofObligation, VerificationConfig, verify_by_evaluation_with_config,
};
use trust_cg_verify::smt::{EvalEnv, EvalResult};
use trust_cg_verify::verify::{VerificationResult, VerificationStrength};

// ---------------------------------------------------------------------------
// Ground truth
// ---------------------------------------------------------------------------

/// What an independent judge says about a theorem the sampler accepted.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Truth {
    /// AY produced a model under which the preconditions hold and the two
    /// sides evaluate differently: the theorem is WRONG, the sampler's Valid
    /// is a false pass.
    Wrong,
    /// AY reported UNSAT (certified or not): the mutation did not change the
    /// meaning, so the sampler's Valid is correct.
    Holds,
    /// AY absent, timed out, erred, or gave a model the evaluator does not
    /// confirm. Counted, never folded into either side.
    Undecided(String),
}

fn truth(obligation: &ProofObligation) -> Truth {
    if !ay_available() {
        return Truth::Undecided("AY unavailable".into());
    }
    match verify_with_ay(obligation, &AYConfig::default()) {
        AYResult::Verified | AYResult::SolverUnsat => Truth::Holds,
        AYResult::CounterExample(model) => {
            if model_refutes(obligation, &model) {
                Truth::Wrong
            } else {
                Truth::Undecided(format!("AY model not confirmed by evaluation: {model:?}"))
            }
        }
        other => Truth::Undecided(format!("{other:?}")),
    }
}

/// Evaluate `obligation` under the AY model (unassigned inputs are zero).
fn model_refutes(obligation: &ProofObligation, model: &[(String, u64)]) -> bool {
    let mut env = EvalEnv::default();
    for (name, width) in &obligation.inputs {
        let value = model
            .iter()
            .find(|(var, _)| var == name)
            .map_or(0, |(_, value)| *value);
        let mask = if *width >= 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        env.insert(name.clone(), value & mask);
    }
    let holds = |expr: &trust_cg_verify::smt::SmtExpr| {
        matches!(expr.try_eval(&env), Ok(EvalResult::Bool(true)))
    };
    if !obligation.preconditions.iter().all(holds) {
        return false;
    }
    match (
        obligation.trust_ir_expr.try_eval(&env),
        obligation.aarch64_expr.try_eval(&env),
    ) {
        (Ok(intent), Ok(machine)) => !intent.semantically_equal(&machine),
        _ => false,
    }
}

fn sampler_valid(obligation: &ProofObligation) -> bool {
    matches!(
        verify_by_evaluation_with_config(obligation, &VerificationConfig::default()),
        VerificationResult::Valid
    )
}

/// The census of one family of (faithful, defect) obligations.
#[derive(Debug, Default)]
struct Census {
    /// Defect obligations judged.
    total: usize,
    /// Defects the default sampler REFUTED.
    sampler_refuted: usize,
    /// Defects the default sampler accepted as Valid.
    sampler_valid: usize,
    /// ... of which AY + evaluation confirm the theorem is wrong.
    false_pass: usize,
    /// ... of which AY says the defect does not change the meaning.
    equivalent: usize,
    /// ... of which no independent verdict was reached.
    undecided: usize,
    /// Sampler verdicts that were neither Valid nor Invalid.
    sampler_unknown: usize,
    /// First few false passes, for the report.
    examples: Vec<String>,
}

impl Census {
    fn judge(obligations: Vec<(String, ProofObligation)>) -> Self {
        let verdicts: Vec<(String, VerificationResult, Option<Truth>)> = obligations
            .into_par_iter()
            .map(|(label, obligation)| {
                let verdict =
                    verify_by_evaluation_with_config(&obligation, &VerificationConfig::default());
                let truth =
                    matches!(verdict, VerificationResult::Valid).then(|| truth(&obligation));
                (label, verdict, truth)
            })
            .collect();
        let mut census = Census::default();
        for (label, verdict, truth) in verdicts {
            census.total += 1;
            match verdict {
                VerificationResult::Invalid { .. } => census.sampler_refuted += 1,
                VerificationResult::Unknown { .. } => census.sampler_unknown += 1,
                VerificationResult::Valid => {
                    census.sampler_valid += 1;
                    match truth.expect("a Valid verdict is always re-judged") {
                        Truth::Wrong => {
                            census.false_pass += 1;
                            if census.examples.len() < 8 {
                                census.examples.push(label);
                            }
                        }
                        Truth::Holds => census.equivalent += 1,
                        Truth::Undecided(why) => {
                            census.undecided += 1;
                            eprintln!("UNDECIDED {label}: {why}");
                        }
                    }
                }
            }
        }
        census
    }

    fn print(&self, tag: &str) {
        eprintln!(
            "{tag} total={} sampler_refuted={} sampler_valid={} false_pass={} \
             equivalent={} undecided={} sampler_unknown={} live_ay={}",
            self.total,
            self.sampler_refuted,
            self.sampler_valid,
            self.false_pass,
            self.equivalent,
            self.undecided,
            self.sampler_unknown,
            ay_available()
        );
        for example in &self.examples {
            eprintln!("{tag} false pass: {example}");
        }
    }
}

// ---------------------------------------------------------------------------
// 1. The form theorems (the 7af30f92d port), judged by main's sampler
// ---------------------------------------------------------------------------

#[test]
fn pair_form_theorems_default_sampler_false_passes() {
    use form_pair::{
        PAIR_MEMORY_FORMS, PairMachineMutation, proof_pair_memory_form as proof_pair_memory,
        proof_pair_memory_form_with_mutation as proof_pair_memory_with_mutation,
    };
    let mut defects = Vec::new();
    for (form, query) in PAIR_MEMORY_FORMS {
        let faithful = proof_pair_memory(&form).expect("table form");
        assert!(
            sampler_valid(&faithful),
            "faithful {query} must pass the sampler"
        );
        for mutation in PairMachineMutation::DEFECTS {
            if let Some(defect) = proof_pair_memory_with_mutation(&form, mutation) {
                defects.push((format!("{query} {mutation:?}"), defect));
            }
        }
    }
    let census = Census::judge(defects);
    census.print("FORM_PAIR");
    assert_eq!(
        census.total, 143,
        "7af30f92d judged 143 applicable pair defects"
    );
    // 7af30f92d measured 93/143 accepted, and so did main's sampler until its
    // precondition-directed trials (41e850748, on main's first-parent line
    // since e1e2619d4, 2026-10-14) reached accessed bytes uniform sampling
    // missed: it refutes 50 more and still accepts 43 (re-measured 2026-10-22
    // at cd1bffb0b; with those trials off, 93/50 again). Pinned: a change
    // means re-measure.
    assert_eq!(census.sampler_valid, 43, "{census:#?}");
    assert_eq!(census.sampler_refuted, 100, "{census:#?}");
    if ay_available() {
        assert_eq!(census.false_pass, census.sampler_valid, "{census:#?}");
    }
}

#[test]
fn scalar_form_theorems_default_sampler_false_passes() {
    use form_scalar::{
        SCALAR_MEMORY_FORMS, ScalarMachineMutation, proof_scalar_memory,
        proof_scalar_memory_with_mutation,
    };
    let mut defects = Vec::new();
    let mut faithful_rejected = Vec::new();
    for (form, query) in SCALAR_MEMORY_FORMS {
        let faithful = proof_scalar_memory(&form).expect("table form");
        let verdict = verify_by_evaluation_with_config(&faithful, &VerificationConfig::default());
        if !matches!(verdict, VerificationResult::Valid) {
            faithful_rejected.push(format!("{query}: {verdict:?}"));
        }
        for mutation in ScalarMachineMutation::DEFECTS {
            if let Some(defect) = proof_scalar_memory_with_mutation(&form, mutation) {
                defects.push((format!("{query} {mutation:?}"), defect));
            }
        }
    }
    let census = Census::judge(defects);
    census.print("FORM_SCALAR");
    eprintln!(
        "FORM_SCALAR faithful_not_valid={} (of 65)",
        faithful_rejected.len()
    );
    for rejected in &faithful_rejected {
        eprintln!("FORM_SCALAR faithful not Valid: {rejected}");
    }
    assert_eq!(
        census.total, 478,
        "7af30f92d judged 478 applicable scalar defects"
    );
    // 7af30f92d measured 395/478 accepted. Main's sampler then answered 34 of
    // those `Unknown` (a vacuous sample: no sampled input met the
    // preconditions) and accepted the other 361 as Valid. Its
    // precondition-directed trials (41e850748, on main since e1e2619d4) meet
    // every one's preconditions and refute 242 more: 153 are still accepted
    // (re-measured 2026-10-22 at cd1bffb0b; with those trials off,
    // 361/34/83 again). Pinned: a change means re-measure.
    assert_eq!(census.sampler_valid, 153, "{census:#?}");
    assert_eq!(census.sampler_unknown, 0, "{census:#?}");
    assert_eq!(census.sampler_refuted, 325, "{census:#?}");
    if ay_available() {
        assert_eq!(census.false_pass, census.sampler_valid, "{census:#?}");
    }
}

// ---------------------------------------------------------------------------
// 2. Main's pair theorem (`aarch64_pair_memory_proofs`)
// ---------------------------------------------------------------------------

const PAIR_OPCODES: [O; 6] = [
    O::StpRI,
    O::LdpRI,
    O::StpPreIndex,
    O::LdpPostIndex,
    O::NeonLdpQPost,
    O::NeonStpQPost,
];

fn p(encoding: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(encoding))
}

/// The 440-shape corpus of `aarch64_pair_memory_proofs`'s
/// `every_well_formed_pair_shape_discharges`: six opcodes, five transfer
/// banks, four bases, extreme and zero scaled offsets.
fn pair_corpus() -> Vec<MachInst> {
    let mut corpus = Vec::new();
    for opcode in PAIR_OPCODES {
        let q_only = matches!(opcode, O::NeonLdpQPost | O::NeonStpQPost);
        for (bank, element) in [(0u16, 8i64), (32, 4), (128, 4), (96, 8), (64, 16)] {
            if q_only && bank != 64 {
                continue;
            }
            for base in [p(3), p(29), MachOperand::Special(SpecialReg::SP), p(31)] {
                for scaled in [-64i64, -1, 0, 1, 63] {
                    corpus.push(MachInst::new(
                        opcode,
                        vec![
                            p(bank + 1),
                            p(bank + 2),
                            base.clone(),
                            MachOperand::Imm(scaled * element),
                        ],
                    ));
                }
            }
        }
    }
    corpus
}

/// Machine-side defects of one pair word: every single-bit flip, the
/// transfer fields transposed, `Rt2` naming `Rt`'s register, and `imm7` one
/// scaled unit up and down.
fn pair_word_mutations(word: u32) -> Vec<(String, u32)> {
    let mut out: Vec<(String, u32)> = (0..32)
        .map(|bit| (format!("bit{bit}"), word ^ (1 << bit)))
        .collect();
    let rt = word & 0x1f;
    let rt2 = (word >> 10) & 0x1f;
    out.push(("Rt<->Rt2".into(), (word & !0x7c1f) | (rt << 10) | rt2));
    out.push(("Rt2:=Rt".into(), (word & !0x7c00) | (rt << 10)));
    let imm7 = (word >> 15) & 0x7f;
    for (label, delta) in [("imm7+1", 1u32), ("imm7-1", 0x7f)] {
        out.push((
            label.into(),
            (word & !(0x7f << 15)) | (((imm7 + delta) & 0x7f) << 15),
        ));
    }
    out.retain(|(_, mutated)| *mutated != word);
    out
}

#[test]
fn main_pair_theorem_default_sampler_false_passes() {
    let corpus = pair_corpus();
    assert_eq!(corpus.len(), 440);
    let mut seen = HashSet::new();
    let mut faithful_set = HashSet::new();
    let mut defects = Vec::new();
    let (mut mutations, mut refused) = (0usize, 0usize);
    // A mutated word the decoder reads back to the SAME fields builds the
    // faithful obligation itself: no defect reached the theorem. Counted per
    // mutation label. Since 2026-09-30 `decode_pair_memory_word` refuses bit
    // 25 (the pair class's fixed zero) and `pair_memory_obligation_from_word`
    // refuses a same-width W/S bank flip, so those 440 + 160 words are now
    // refused; what remains is architecturally equivalent (a mode change of a
    // zero-offset shape: its writeback adds zero).
    let mut identical: std::collections::BTreeMap<String, usize> = Default::default();
    for inst in &corpus {
        let intent = pair_memory_intent(inst).expect("corpus shape is admitted");
        let word = pair_memory_word(&intent).expect("encodable");
        let faithful = pair_memory_obligation(inst).expect("admitted");
        // Every pair obligation carries a 64-bit base, so its evaluation
        // strength is Statistical: `InstructionVerificationResult::
        // from_discharge` reports it, never credits it (E0.2).
        assert!(
            matches!(
                VerificationStrength::for_obligation_with_config(
                    &faithful,
                    &VerificationConfig::default()
                ),
                VerificationStrength::Statistical { .. }
            ),
            "{inst:?}"
        );
        faithful_set.insert(faithful.clone());
        for (label, mutated) in pair_word_mutations(word) {
            mutations += 1;
            let Some(obligation) = pair_memory_obligation_from_word(inst, mutated) else {
                refused += 1;
                continue;
            };
            if obligation == faithful {
                *identical.entry(label).or_default() += 1;
                continue;
            }
            if seen.insert(obligation.clone()) {
                defects.push((
                    format!(
                        "{:?} {inst:?} {label} {word:#010x}->{mutated:#010x}",
                        inst.opcode
                    ),
                    obligation,
                ));
            }
        }
    }
    let census = Census::judge(defects);
    eprintln!(
        "MAIN_PAIR corpus={} mutations={mutations} refused_no_obligation={refused} \
         identical_to_faithful={} {identical:?}",
        corpus.len(),
        identical.values().sum::<usize>()
    );
    census.print("MAIN_PAIR");
    assert_eq!(census.total, 978, "{census:#?}");
    assert_eq!(census.sampler_refuted, 978, "{census:#?}");
    assert_eq!(identical.values().sum::<usize>(), 108, "{identical:?}");
    assert!(
        identical
            .keys()
            .all(|label| label == "bit23" || label == "bit24"),
        "only zero-offset mode flips may read back as the faithful word: {identical:?}"
    );
    // Would a Formal-only rule credit main's FAITHFUL pair theorems today?
    // Ask AY about every distinct one (the walk's own discharge never does).
    let faithful: Vec<ProofObligation> = faithful_set.into_iter().collect();
    let answers: Vec<String> = faithful
        .par_iter()
        .map(|ob| {
            if !ay_available() {
                return "AY unavailable".to_string();
            }
            match verify_with_ay(ob, &AYConfig::default()) {
                AYResult::Verified => "Verified".into(),
                AYResult::SolverUnsat => "SolverUnsat".into(),
                AYResult::CounterExample(_) => "CounterExample".into(),
                AYResult::Timeout => "Timeout".into(),
                AYResult::Unknown(reason) => format!("Unknown({reason})"),
                AYResult::Error(error) => format!("Error({})", error.lines().next().unwrap_or("")),
            }
        })
        .collect();
    let mut tally: std::collections::BTreeMap<&str, usize> = Default::default();
    for answer in &answers {
        *tally.entry(answer.as_str()).or_default() += 1;
    }
    eprintln!(
        "MAIN_PAIR faithful_distinct={} ay={tally:?}",
        faithful.len()
    );
    assert!(
        !answers.iter().any(|answer| answer == "CounterExample"),
        "AY refuted a faithful pair theorem: {answers:?}"
    );
    assert_eq!(census.false_pass, 0, "{census:#?}");
    assert_eq!(census.undecided, 0, "{census:#?}");
}

// ---------------------------------------------------------------------------
// 3. Main's scalar immediate load/store theorem
//    (`aarch64_instruction_word_proofs`)
// ---------------------------------------------------------------------------

fn scalar_corpus() -> Vec<MachInst> {
    let mut corpus = Vec::new();
    for (opcode, bytes) in [
        (O::LdrRI, 8i64),
        (O::StrRI, 8),
        (O::LdrbRI, 1),
        (O::StrbRI, 1),
        (O::LdrhRI, 2),
        (O::StrhRI, 2),
    ] {
        let store = matches!(opcode, O::StrRI | O::StrbRI | O::StrhRI);
        let mut data = vec![p(1), p(32 + 2)];
        if store {
            data.push(MachOperand::Special(SpecialReg::XZR));
        }
        for data in data {
            for base in [3u16, 29, 31] {
                for offset in [0i64, bytes, 2 * bytes, -8, -256, 255, 1, 4095 * bytes] {
                    let inst = MachInst::new(
                        opcode,
                        vec![
                            data.clone(),
                            MachOperand::MemOp {
                                base: PReg::new(base),
                                offset,
                            },
                        ],
                    );
                    if instruction_word(&inst).is_some() {
                        corpus.push(inst);
                    }
                }
            }
        }
    }
    corpus
}

#[test]
fn main_scalar_theorem_default_sampler_false_passes() {
    let corpus = scalar_corpus();
    let config = VerificationConfig::default();
    // (label, outcome, locations needing the evaluator)
    let judged: Vec<(String, Outcome, Vec<ProofObligation>)> = corpus
        .par_iter()
        .flat_map_iter(|inst| {
            let word = instruction_word(inst).expect("corpus shape is admitted");
            let faithful = instruction_word_verdict_for(inst, word.word, &config).expect("shape");
            assert!(
                matches!(faithful.outcome, Outcome::Holds(_)),
                "faithful {inst:?}: {:?}",
                faithful.outcome
            );
            (0..32)
                .filter(move |bit| word.hole_mask & (1 << bit) == 0)
                .map(move |bit| {
                    let mutated = word.word ^ (1 << bit);
                    let verdict =
                        instruction_word_verdict_for(inst, mutated, &VerificationConfig::default())
                            .expect("shape");
                    (
                        format!("{:?} {inst:?} bit{bit} {:#010x}", inst.opcode, mutated),
                        verdict.outcome,
                        verdict.locations.into_iter().map(|(_, ob)| ob).collect(),
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect();
    let (mut refuted, mut exact, mut evaluated, mut undecided) = (0usize, 0usize, 0usize, 0usize);
    let mut exact_labels: std::collections::BTreeMap<String, usize> = Default::default();
    let mut sampled_holds: Vec<(String, Vec<ProofObligation>)> = Vec::new();
    for (label, outcome, locations) in judged {
        match outcome {
            Outcome::Refuted(_) => refuted += 1,
            Outcome::Undecided(_) => undecided += 1,
            Outcome::Holds(Decision::Exact) => {
                exact += 1;
                let opcode = label.split(' ').next().unwrap_or("").to_string();
                let bit = label
                    .split(' ')
                    .find(|part| part.starts_with("bit"))
                    .unwrap_or("")
                    .to_string();
                *exact_labels.entry(format!("{opcode} {bit}")).or_default() += 1;
            }
            Outcome::Holds(Decision::Evaluated(_)) => {
                evaluated += 1;
                sampled_holds.push((label, locations));
            }
        }
    }
    // A Holds decided by the evaluator is re-judged per location by AY.
    let mut false_pass = Vec::new();
    for (label, locations) in &sampled_holds {
        if locations.iter().any(|ob| truth(ob) == Truth::Wrong) {
            false_pass.push(label.clone());
        }
    }
    eprintln!(
        "MAIN_SCALAR corpus={} mutations={} refuted={refuted} holds_exact={exact} \
         holds_evaluated={evaluated} undecided={undecided} false_pass={} live_ay={}",
        corpus.len(),
        refuted + exact + evaluated + undecided,
        false_pass.len(),
        ay_available()
    );
    eprintln!("MAIN_SCALAR holds_exact by (opcode, flipped bit): {exact_labels:?}");
    for example in false_pass.iter().take(8) {
        eprintln!("MAIN_SCALAR false pass: {example}");
    }
    assert_eq!(false_pass, Vec::<String>::new());
    // No scalar mutation reaches the sampler at all: every location is decided
    // by term identity, exact bit routing or the boundary search.
    assert_eq!(evaluated, 0);
    assert_eq!((corpus.len(), refuted, exact), (354, 11283, 45));
}
