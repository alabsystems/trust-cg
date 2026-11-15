// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Formal-only credit for AArch64 bound-memory rows.
//!
//! Owner ruling 2026-09-29: an AArch64 bound-memory obligation — a pair
//! `LDP`/`STP` row or a scalar `LDR`/`STR` memory row — earns instruction
//! credit ONLY from a formal proof, never from statistical sampling.
//!
//! # The rule
//!
//! A bound-memory row is `Verified` exactly when all of the following hold:
//!
//! 1. its instruction binds to exactly one FORM theorem —
//!    [`crate::aarch64_pair_memory_forms`] (pair; its binding must also agree
//!    field for field with the per-instruction lane's own admission) or
//!    [`crate::aarch64_scalar_memory_proofs`] (scalar);
//! 2. the row's in-process refutation check RAN on this instruction and HELD
//!    ([`BoundMemoryRefutation`]): the pair lane's concrete-word obligation
//!    ([`crate::aarch64_pair_memory_proofs`]) for a pair row, the
//!    instruction-derived obligation
//!    ([`crate::aarch64_instruction_word_proofs`]) for a general-purpose
//!    scalar row. That lane judges general-purpose scalar loads and stores:
//!    `LDR`/`STR{,B,H}` and the sign-extending `LDRSB`/`LDRSH` with an
//!    immediate offset, W/X `LDR`/`STR` with pre/post-index writeback, and
//!    register-offset forms. It models no SIMD/FP register; an `H`/`S`/`D`/`Q`
//!    scalar row is judged instead by its word-bound memory-effect
//!    decomposition ([`crate::aarch64_memory_effect`], `L04-P1`), every part
//!    of which must hold exactly in process ([`RefutationCheck::MemoryEffect`]);
//!    that decision, like every clause-2 check, is never credit by itself. A
//!    refutation fails the row as it always did; a row no such check judged
//!    (no lane admits it, or its check was undecided) is never credited
//!    ([`BOUND_MEMORY_REFUTATION_NOT_RUN`]);
//! 3. the bound form is the form of the WORD that check judged, field for
//!    field ([`crate::aarch64_pair_memory_forms::decode_pair_memory_binding`],
//!    [`crate::aarch64_scalar_memory_proofs::decode_scalar_memory_word`]),
//!    and the binder's own attribution of the instruction
//!    ([`BOUND_MEMORY_BINDING_MISMATCH`]);
//! 4. the exact SMT-LIB query of that form theorem has a certificate in the
//!    committed bound-memory set (`verdict_db/bound_memory_certs/`) that the
//!    vendored independent `drat-trim` replays in this process
//!    ([`crate::canary_cert`]'s bound-memory set).
//!
//! The credit is `Formal`. Everything else leaves the row `Unverified`, with
//! the reason it had before this rule plus [`BOUND_MEMORY_FORMAL_ONLY`] and
//! the form's status (unbound, unrefuted, misbound, or bound without a
//! replayable certificate).
//!
//! Clauses 2 and 3 are what tie the certificate to THIS row. The certificate
//! proves the form theorem for every operand value; it says nothing about
//! whether this instruction is an instance of that form. The operand binder
//! alone would attribute a form from the machine-IR operands; the refutation
//! check is the only in-walk judgement of the instruction's own word (the word
//! ENC-5 binds to the emitted one), and clause 3 requires the certificate to
//! be about that word's form. A semantically equal word of ANOTHER form (an
//! `LDUR` judged for an `LDR` whose binder chose the unsigned-offset form) holds
//! its check and is still refused.
//! A sampled `Valid` never contributes: not for the form theorem (the
//! evaluation sweep is never run on it) and not for the concrete-word
//! obligation, whose sampled verdict only means "not refuted". No verdict
//! strength other than a replayed certificate is consulted, so neither a
//! future `Exhaustive` evaluation nor a live solver `unsat` can credit a row.
//!
//! # The source-bound route
//!
//! A memory row a source-bound owner binds to its source
//! ([`crate::aarch64_memory_source_binding`], 2026-10-01) has a second
//! formal route: every part of its word's memory-effect decomposition with an
//! AY proof that the independent Clean checker fully verified, the evidence
//! class the source-bound frame and ALU owners already credit. It is not a
//! relaxation of this rule (both are formal proofs, neither is sampling) and
//! it applies only with the binding: a row this rule credits keeps that
//! credit, and an unbound row's Clean-checked parts are still recorded, never
//! credited.
//!
//! # Why sampling cannot be the evidence
//!
//! The form theorems observe memory through a free query byte `q` (stores) or
//! a single-point memory `ite(x == p, c, d)` (loads). Uniform 64-bit sampling
//! essentially never places that point on an accessed byte: with the default
//! 100k sampler, 93 of 143 deliberately wrong pair theorems and 361 of 478
//! deliberately wrong scalar theorems came back `Valid` (measured on
//! 2026-09-29, `tests/bound_memory_sampler_adversarial.rs`). The sampler's
//! precondition-directed trials (41e850748) since reach some of those points,
//! and it still accepts 43 of the 143 and 153 of the 478 (re-measured
//! 2026-10-22).
//!
//! # Atomic rows
//!
//! The 46 single-instruction atomic opcodes (`LDAR{,B,H}`, `STLR{,B,H}`,
//! `CAS*`, `SWP*`, `LD<op>*`; ledger `X-OPCODES-P2`) are memory rows of the
//! same kind and take the same rule: clause 1 binds the atomic form theorem
//! ([`crate::aarch64_atomic_forms`]); clause 2's check is the word-bound
//! atomic decomposition ([`crate::aarch64_atomic_effect`]), decided exactly
//! in process (every field, the returned value and the memory window); clause
//! 3 decodes that word with [`crate::aarch64_atomic_forms::decode_atomic_word`];
//! clause 4 replays a certificate of the committed atomic-memory set
//! (`verdict_db/atomic_memory_certs/`, its own manifest and host
//! qualifications). The atomic form theorem states the single-thread value
//! and memory effect; the ordering of the access is the memory-order table of
//! ledger `L03-P3` ([`crate::aarch64_memory_order`]), which this rule does not
//! replace.
//!
//! # NEON structure rows
//!
//! The NEON `LD1`/`ST1` one-register immediate post-index rows (ledger
//! `L04-P1`) take the same rule: clause 1 binds the form theorem of
//! [`crate::aarch64_neon_structure_forms`] (load/store x arrangement);
//! clause 2's check is the row's word-bound memory-effect decomposition
//! ([`crate::aarch64_memory_effect`], `L04-P6`), every part decided exactly in
//! process ([`RefutationCheck::MemoryEffect`]); clause 3 decodes that word with
//! [`crate::aarch64_neon_structure_forms::decode_neon_structure_word`]; clause 4
//! replays a certificate of the committed NEON set
//! (`verdict_db/neon_memory_certs/`, its own manifest and host
//! qualifications).
//!
//! # Claim boundary
//!
//! A credited row means: the architectural effect of this instruction form
//! (all transfers, the byte-level frame condition for stores, the extension
//! for loads, and the base writeback) equals the operand intent the MachIR
//! instruction names, for every operand value and every memory. It does not
//! bind the instruction to a SOURCE load or store, and it relies on ENC-5
//! (`trust-cg-codegen` `decode_check`) to bind the emitted word to those
//! operands. The certificate's residual trusted link is the regen-time
//! bit-blast by the manifest-recorded AY producer, exactly as for the
//! portable canaries.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use crate::aarch64_atomic_forms as atomic_forms;
use crate::aarch64_neon_structure_forms as neon_forms;
use crate::aarch64_pair_memory_forms as pair_forms;
use crate::aarch64_scalar_memory_proofs as scalar_forms;
use crate::lowering_proof::ProofObligation;
use trust_cg_ir::MachInst;

/// Reason clause appended to every uncredited bound-memory row.
pub const BOUND_MEMORY_FORMAL_ONLY: &str = "bound-memory rows are credited only by a \
     checker-accepted certificate of their form theorem (owner ruling 2026-09-29)";

/// Clause of an uncredited bound-memory row whose certificate exists but whose
/// host's `drat-trim` bytes the bound-memory manifest does not authorize.
pub const CHECKER_IDENTITY_MISS: &str = "a checker-identity miss, not a proof gap";

/// Clause of a bound-memory row that binds a form theorem but that no
/// in-process refutation check judged and found holding (rule clause 2).
pub const BOUND_MEMORY_REFUTATION_NOT_RUN: &str = "no in-process refutation check ran and \
     held on this row (the pair lane's concrete-word obligation, or the instruction-derived \
     obligation of a general-purpose scalar load or store), so nothing ties this instruction \
     to the certified form";

/// Clause of a bound-memory row whose bound form is not the form of the word
/// its refutation check judged, or not the binder's attribution of the
/// instruction (rule clause 3).
pub const BOUND_MEMORY_BINDING_MISMATCH: &str = "the certified form is not the form of the \
     word this row's refutation check judged";

/// Which in-process refutation check judged a bound-memory row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefutationCheck {
    /// The pair lane's concrete-word obligation
    /// ([`crate::aarch64_pair_memory_proofs::pair_memory_obligation`]).
    PairConcreteWord,
    /// The instruction-derived obligation
    /// ([`crate::aarch64_instruction_word_proofs::instruction_word_verdict`]).
    InstructionWord,
    /// The word-bound atomic decomposition, decided exactly
    /// ([`crate::aarch64_atomic_effect::judge`]).
    AtomicEffect,
    /// The word-bound memory-effect decomposition of a SIMD&FP (`H`/`S`/`D`/
    /// `Q`) scalar load or store, every part decided exactly
    /// ([`crate::aarch64_memory_effect::decide_in_process`]); the
    /// instruction-derived lane models no SIMD&FP register.
    MemoryEffect,
}

/// Evidence that a bound-memory row's in-process refutation check RAN on the
/// row and HELD, with the 32-bit word it judged (rule clause 2).
///
/// Built only by the two lanes, from their own verdicts: a refuted, unknown
/// or undecided check yields none. The word is what rule clause 3 decodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoundMemoryRefutation {
    check: RefutationCheck,
    word: u32,
}

impl BoundMemoryRefutation {
    /// The pair lane's concrete-word obligation over `word` came back
    /// `verdict`: evidence only when it held (`Valid`; its strength is never
    /// credit, and a sampled `Valid` only means "not refuted").
    pub(crate) fn pair_concrete_word(
        word: u32,
        verdict: &crate::verify::VerificationResult,
    ) -> Option<Self> {
        matches!(verdict, crate::verify::VerificationResult::Valid).then_some(Self {
            check: RefutationCheck::PairConcreteWord,
            word,
        })
    }

    /// The instruction-derived obligation: evidence only when it `Holds`,
    /// over a word with no fixup hole (a hole's bits are not the instruction's).
    pub(crate) fn instruction_word(
        verdict: &crate::aarch64_instruction_word_proofs::InstructionWordVerdict,
    ) -> Option<Self> {
        (matches!(
            verdict.outcome,
            crate::aarch64_instruction_word_proofs::Outcome::Holds(_)
        ) && verdict.word.hole_mask == 0)
            .then_some(Self {
                check: RefutationCheck::InstructionWord,
                word: verdict.word.word,
            })
    }

    /// The atomic decomposition of `decomposition.word`: evidence only when
    /// every part held exactly ([`crate::aarch64_atomic_effect::AtomicEffectVerdict::Holds`]).
    pub(crate) fn atomic_effect(
        decomposition: &crate::aarch64_atomic_effect::AtomicEffectDecomposition,
        verdict: &crate::aarch64_atomic_effect::AtomicEffectVerdict,
    ) -> Option<Self> {
        matches!(
            verdict,
            crate::aarch64_atomic_effect::AtomicEffectVerdict::Holds
        )
        .then_some(Self {
            check: RefutationCheck::AtomicEffect,
            word: decomposition.word,
        })
    }

    /// The memory-effect decomposition of a SIMD&FP scalar row: evidence only
    /// when EVERY part holds for every input in process (exactly, never by
    /// sampling).
    pub(crate) fn memory_effect(
        decomposition: &crate::aarch64_memory_effect::MemoryEffectDecomposition,
        config: &crate::lowering_proof::VerificationConfig,
    ) -> Option<Self> {
        use crate::aarch64_memory_effect::{InProcess, decide_in_process};
        decomposition
            .parts
            .iter()
            .all(|part| {
                matches!(
                    decide_in_process(part, config),
                    InProcess::Holds(crate::verify::VerificationStrength::Exhaustive)
                )
            })
            .then_some(Self {
                check: RefutationCheck::MemoryEffect,
                word: decomposition.word,
            })
    }

    /// A held check of kind `check` over `word`, for tests that ask what the
    /// binding check makes of a word no production lane judges.
    #[cfg(test)]
    pub(crate) fn assumed_for_test(check: RefutationCheck, word: u32) -> Self {
        Self { check, word }
    }

    /// Which check held.
    pub fn check(&self) -> RefutationCheck {
        self.check
    }

    /// The word it judged.
    pub fn word(&self) -> u32 {
        self.word
    }
}

/// Rule clause 3: `binding` is the binder's attribution of `inst`, and the
/// form (and every field) of the word `refutation` judged, decoded
/// independently of the binder. `Err` names the disagreement.
pub(crate) fn binding_check(
    inst: &MachInst,
    binding: &BoundMemoryBinding,
    refutation: &BoundMemoryRefutation,
) -> Result<(), String> {
    #[cfg(test)]
    if binding_check_seam::skipped() {
        return Ok(());
    }
    match bind_bound_memory_row(inst) {
        Some(Ok(attributed)) if attributed == *binding => {}
        Some(Ok(attributed)) => {
            return Err(format!(
                "{BOUND_MEMORY_BINDING_MISMATCH}: the instruction binds `{}` ({attributed:?}), \
                 not `{}` ({binding:?})",
                attributed.query(),
                binding.query()
            ));
        }
        other => {
            return Err(format!(
                "{BOUND_MEMORY_BINDING_MISMATCH}: the instruction does not bind `{}`: {other:?}",
                binding.query()
            ));
        }
    }
    let word = refutation.word;
    let decoded = match (binding, refutation.check) {
        (BoundMemoryBinding::Pair(_), RefutationCheck::PairConcreteWord) => {
            pair_forms::decode_pair_memory_binding(word).map(BoundMemoryBinding::Pair)
        }
        (BoundMemoryBinding::Scalar(_), RefutationCheck::InstructionWord) => {
            scalar_forms::decode_scalar_memory_word(word).map(BoundMemoryBinding::Scalar)
        }
        (BoundMemoryBinding::Atomic(_), RefutationCheck::AtomicEffect) => {
            atomic_forms::decode_atomic_word(word).map(BoundMemoryBinding::Atomic)
        }
        (BoundMemoryBinding::Scalar(scalar), RefutationCheck::MemoryEffect)
            if scalar.form.bank == scalar_forms::ScalarBank::Fpr =>
        {
            scalar_forms::decode_scalar_memory_word(word).map(BoundMemoryBinding::Scalar)
        }
        (BoundMemoryBinding::Neon(_), RefutationCheck::MemoryEffect) => {
            neon_forms::decode_neon_structure_word(word).map(BoundMemoryBinding::Neon)
        }
        (_, check) => {
            return Err(format!(
                "{BOUND_MEMORY_BINDING_MISMATCH}: a {check:?} check does not judge a {:?} row",
                binding.family()
            ));
        }
    };
    match decoded {
        Some(decoded) if decoded == *binding => Ok(()),
        Some(decoded) => Err(format!(
            "{BOUND_MEMORY_BINDING_MISMATCH}: word {word:#010x} is `{}` ({decoded:?}), the row \
             binds `{}` ({binding:?})",
            decoded.query(),
            binding.query()
        )),
        None => Err(format!(
            "{BOUND_MEMORY_BINDING_MISMATCH}: word {word:#010x} is no attributable {:?} form",
            binding.family()
        )),
    }
}

/// Mutant switch for the non-vacuity controls: while a guard lives, this
/// thread's [`binding_check`] accepts every binding.
#[cfg(test)]
pub(crate) mod binding_check_seam {
    use std::cell::Cell;

    thread_local! {
        static SKIP: Cell<bool> = const { Cell::new(false) };
    }

    pub(crate) fn skipped() -> bool {
        SKIP.with(Cell::get)
    }

    /// Skip the binding check on this thread until the guard drops.
    pub(crate) fn skip() -> Guard {
        SKIP.with(|cell| cell.set(true));
        Guard
    }

    pub(crate) struct Guard;

    impl Drop for Guard {
        fn drop(&mut self) {
            SKIP.with(|cell| cell.set(false));
        }
    }
}

/// Whether this build's vendored checker is one the committed bound-memory
/// manifest authorizes: `Ok(())`, or why not and how to qualify the host.
///
/// A test that observes bound-memory CREDIT asks this first: on a qualified
/// host every faithful row is credited `Formal`; on any other host every row
/// misses fail closed with [`CHECKER_IDENTITY_MISS`], and the one test
/// `bound_memory_set_binds_the_exact_runtime_checker_bytes` is red. It grants
/// nothing: credit still requires the per-query replay.
pub fn bound_memory_checker_qualification() -> Result<(), String> {
    crate::canary_cert::bound_memory::bound_memory_checker_qualification()
}

/// [`bound_memory_checker_qualification`] for the separate atomic-memory set
/// (`verdict_db/atomic_memory_certs/manifest.v1`).
pub fn atomic_memory_checker_qualification() -> Result<(), String> {
    crate::canary_cert::bound_memory::ATOMIC_MEMORY_SET.checker_qualification()
}

/// [`bound_memory_checker_qualification`] for the separate NEON
/// structure-memory set (`verdict_db/neon_memory_certs/manifest.v1`).
pub fn neon_memory_checker_qualification() -> Result<(), String> {
    crate::canary_cert::bound_memory::NEON_MEMORY_SET.checker_qualification()
}

/// The bound-memory families.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundMemoryFamily {
    /// `STP`/`LDP` pair forms.
    Pair,
    /// `LDR`/`STR` scalar forms.
    Scalar,
    /// Single-instruction atomic forms (`LDAR`, `STLR`, `CAS`, `SWP`,
    /// `LD<op>`).
    Atomic,
    /// NEON `LD1`/`ST1` one-register immediate post-index forms.
    NeonStructure,
}

/// A concrete instruction bound to exactly one form theorem.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundMemoryBinding {
    /// A pair instruction and its form.
    Pair(pair_forms::PairMemoryBinding),
    /// A scalar instruction and its form.
    Scalar(scalar_forms::ScalarMemoryBinding),
    /// A single-instruction atomic and its form.
    Atomic(atomic_forms::AtomicBinding),
    /// A NEON `LD1`/`ST1` post-index instruction and its form.
    Neon(neon_forms::NeonStructureBinding),
}

impl BoundMemoryBinding {
    /// The family of the bound form.
    pub fn family(&self) -> BoundMemoryFamily {
        match self {
            Self::Pair(_) => BoundMemoryFamily::Pair,
            Self::Scalar(_) => BoundMemoryFamily::Scalar,
            Self::Atomic(_) => BoundMemoryFamily::Atomic,
            Self::Neon(_) => BoundMemoryFamily::NeonStructure,
        }
    }

    /// The unique form query (`pairmem[...]` / `scalarmem[...]`).
    pub fn query(&self) -> &'static str {
        match self {
            Self::Pair(binding) => binding.query(),
            Self::Scalar(binding) => binding.query(),
            Self::Atomic(binding) => binding.query(),
            Self::Neon(binding) => binding.query(),
        }
    }

    /// The faithful form theorem this binding instantiates.
    pub fn obligation(&self) -> ProofObligation {
        form_obligation(self.query())
    }
}

/// Bind a row, or say why it binds no form theorem. `None` when the opcode is
/// not a bound-memory opcode at all.
pub fn bind_bound_memory_row(inst: &MachInst) -> Option<Result<BoundMemoryBinding, String>> {
    if pair_forms::is_pair_memory_opcode(inst.opcode) {
        return Some(
            pair_forms::bind_admitted_pair_instruction(inst).map(BoundMemoryBinding::Pair),
        );
    }
    if scalar_forms::is_scalar_memory_opcode(inst.opcode) {
        return Some(
            scalar_forms::bind_scalar_memory_instruction(inst).map(BoundMemoryBinding::Scalar),
        );
    }
    if atomic_forms::is_atomic_memory_opcode(inst.opcode) {
        return Some(atomic_forms::bind_atomic_instruction(inst).map(BoundMemoryBinding::Atomic));
    }
    if neon_forms::is_neon_structure_opcode(inst.opcode) {
        return Some(
            neon_forms::bind_neon_structure_instruction(inst).map(BoundMemoryBinding::Neon),
        );
    }
    None
}

/// The faithful form theorem named by `query`, memoized.
fn form_obligation(query: &str) -> ProofObligation {
    static MEMO: OnceLock<HashMap<&'static str, ProofObligation>> = OnceLock::new();
    MEMO.get_or_init(|| {
        let mut map = HashMap::new();
        for (form, q) in pair_forms::PAIR_MEMORY_FORMS {
            map.insert(
                q,
                pair_forms::proof_pair_memory_form(&form).expect("table forms are legal"),
            );
        }
        for (form, q) in scalar_forms::SCALAR_MEMORY_FORMS {
            map.insert(
                q,
                scalar_forms::proof_scalar_memory(&form).expect("table forms are legal"),
            );
        }
        for (form, q) in atomic_forms::ATOMIC_MEMORY_FORMS {
            map.insert(
                q,
                atomic_forms::proof_atomic_form(&form).expect("table forms are legal"),
            );
        }
        for (form, q) in neon_forms::NEON_STRUCTURE_FORMS {
            map.insert(
                q,
                neon_forms::proof_neon_structure_form(&form).expect("table forms are legal"),
            );
        }
        map
    })
    .get(query)
    .cloned()
    .unwrap_or_else(|| panic!("unknown bound-memory form query {query:?}"))
}

/// Whether the form theorem's exact query has a committed certificate the
/// independent checker replays now: `Ok(())`, or the reason it does not.
///
/// Only a SUCCESSFUL replay is memoized (by the canary replay memo); a miss is
/// recomputed so a transient checker failure is never cached as a refusal.
pub fn form_certificate_status(obligation: &ProofObligation) -> Result<(), String> {
    form_certificate_status_in(obligation, None)
}

/// [`form_certificate_status`] under a verification request's captured replay
/// authority (`None`: an authority captured now).
pub(crate) fn form_certificate_status_in(
    obligation: &ProofObligation,
    request: Option<&crate::function_request::FunctionVerificationRequest>,
) -> Result<(), String> {
    // Keyed by the COMPLETE obligation, never by its name: a wrong theorem
    // wearing a faithful form's name must not share (or poison) its query.
    static SMT2: OnceLock<Mutex<HashMap<ProofObligation, std::sync::Arc<String>>>> =
        OnceLock::new();
    let smt2 = {
        let memo = SMT2.get_or_init(|| Mutex::new(HashMap::new()));
        let mut memo = memo.lock().unwrap_or_else(|p| p.into_inner());
        std::sync::Arc::clone(memo.entry(obligation.clone()).or_insert_with(|| {
            std::sync::Arc::new(crate::verdict_db::db_obligation_smt2(obligation))
        }))
    };
    // An atomic form theorem's certificate lives in the separate atomic set,
    // a NEON structure form theorem's in the NEON set.
    #[derive(Clone, Copy)]
    enum Set {
        Bound,
        Atomic,
        Neon,
    }
    let which = if obligation.name.starts_with("AtomicMem[") {
        Set::Atomic
    } else if obligation.name.starts_with("NeonMem[") {
        Set::Neon
    } else {
        Set::Bound
    };
    let set = match which {
        Set::Atomic => &crate::canary_cert::bound_memory::ATOMIC_MEMORY_SET,
        Set::Neon => &crate::canary_cert::bound_memory::NEON_MEMORY_SET,
        Set::Bound => &crate::canary_cert::bound_memory::BOUND_MEMORY_SET,
    };
    let verified = match (request, which) {
        (Some(request), Set::Bound) => request.bound_memory_cert_verified(&smt2),
        (Some(request), Set::Atomic) => request.atomic_memory_cert_verified(&smt2),
        (Some(request), Set::Neon) => request.neon_memory_cert_verified(&smt2),
        (None, _) => set.cert_verified(&smt2),
    };
    if verified {
        Ok(())
    } else {
        Err(set.cert_miss_reason(&smt2))
    }
}

/// What the Formal-only rule grants one bound-memory row, given that no
/// in-process check refuted it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoundMemoryCredit {
    /// A committed certificate of the bound form theorem replayed: credit at
    /// `Formal`, citing the form theorem.
    Certified {
        /// The form theorem's name.
        proof_name: String,
    },
    /// The row binds a form theorem, but no in-process refutation check ran
    /// on it and held (rule clause 2). No certificate is consulted.
    Unrefuted {
        /// The form theorem's name.
        proof_name: String,
    },
    /// The bound form is not the form of the word the row's refutation check
    /// judged, or not the binder's attribution (rule clause 3). No
    /// certificate is consulted.
    Misbound {
        /// The form theorem's name.
        proof_name: String,
        /// The disagreement.
        reason: String,
    },
    /// The row binds a form theorem, but no committed certificate of it
    /// replays here.
    Uncertified {
        /// The form theorem's name.
        proof_name: String,
        /// Why no certificate credits it.
        reason: String,
    },
    /// The row binds no form theorem.
    Unbound {
        /// The binder's refusal.
        reason: String,
    },
}

impl BoundMemoryCredit {
    /// The clause an uncredited row's reason carries; `None` when certified.
    pub fn uncredited_note(&self) -> Option<String> {
        match self {
            Self::Certified { .. } => None,
            Self::Unrefuted { proof_name } => Some(format!(
                "{BOUND_MEMORY_FORMAL_ONLY}; form theorem `{proof_name}`: \
                 {BOUND_MEMORY_REFUTATION_NOT_RUN}"
            )),
            Self::Uncertified { proof_name, reason } | Self::Misbound { proof_name, reason } => {
                Some(format!(
                    "{BOUND_MEMORY_FORMAL_ONLY}; form theorem `{proof_name}`: {reason}"
                ))
            }
            Self::Unbound { reason } => Some(format!(
                "{BOUND_MEMORY_FORMAL_ONLY}; no form theorem binds this instruction: {reason}"
            )),
        }
    }
}

/// Reason an uncertified row carries when its walk does not replay
/// certificates (`ProofReplayPolicy::EvaluationOnly`).
pub const CERTIFICATE_REPLAY_OFF: &str = "certificates are replayed only under the \
     proof-promotion policy (SourceBoundReplay); this walk is evaluation-only";

/// The Formal-only verdict for a bound-memory row (`None` for any other
/// opcode). `refutation` is the row's held refutation check, `None` when no
/// check ran on the row or it did not hold (the caller has already failed a
/// refuted row). With `replay` false no certificate is consulted and a bound,
/// checked row is `Uncertified` with [`CERTIFICATE_REPLAY_OFF`].
pub fn bound_memory_credit(
    inst: &MachInst,
    refutation: Option<&BoundMemoryRefutation>,
    replay: bool,
) -> Option<BoundMemoryCredit> {
    bound_memory_credit_in(inst, refutation, replay, None)
}

/// [`bound_memory_credit`] under a verification request's captured replay
/// authority (`None`: an authority captured now).
pub(crate) fn bound_memory_credit_in(
    inst: &MachInst,
    refutation: Option<&BoundMemoryRefutation>,
    replay: bool,
    request: Option<&crate::function_request::FunctionVerificationRequest>,
) -> Option<BoundMemoryCredit> {
    Some(match bind_bound_memory_row(inst)? {
        Err(reason) => BoundMemoryCredit::Unbound { reason },
        Ok(binding) => credit_bound_form(inst, &binding, refutation, replay, request),
    })
}

/// The credit `inst` earns when ATTRIBUTED to `binding`: rule clauses 2-4.
///
/// Production passes the binder's own attribution
/// ([`bind_bound_memory_row`]); the wrong-binding controls pass another
/// form's binding and require a refusal. Clauses 2 and 3 are decided before
/// any certificate is consulted.
pub(crate) fn credit_bound_form(
    inst: &MachInst,
    binding: &BoundMemoryBinding,
    refutation: Option<&BoundMemoryRefutation>,
    replay: bool,
    request: Option<&crate::function_request::FunctionVerificationRequest>,
) -> BoundMemoryCredit {
    let obligation = binding.obligation();
    let Some(refutation) = refutation else {
        return BoundMemoryCredit::Unrefuted {
            proof_name: obligation.name,
        };
    };
    if let Err(reason) = binding_check(inst, binding, refutation) {
        return BoundMemoryCredit::Misbound {
            proof_name: obligation.name,
            reason,
        };
    }
    if !replay {
        return BoundMemoryCredit::Uncertified {
            proof_name: obligation.name,
            reason: CERTIFICATE_REPLAY_OFF.to_string(),
        };
    }
    match form_certificate_status_in(&obligation, request) {
        Ok(()) => BoundMemoryCredit::Certified {
            proof_name: obligation.name,
        },
        Err(reason) => BoundMemoryCredit::Uncertified {
            proof_name: obligation.name,
            reason,
        },
    }
}

/// One distinct exact form query and the form theorems that share it.
#[derive(Debug, Clone)]
pub struct CertifiableBoundMemoryQuery {
    /// Certificate filename in `verdict_db/bound_memory_certs/`.
    pub file: String,
    /// Names of every form theorem whose exact query this is.
    pub forms: Vec<String>,
    /// The first (primary) form theorem, whose query is certified.
    pub obligation: ProofObligation,
}

/// Every distinct exact query of a form theorem some row can bind, in table
/// order (pair forms first). Equal-width store forms of different register
/// banks are one formula and therefore one query and one file. The scalar
/// literal form is excluded: no row is ever attributed to it
/// ([`scalar_forms::bind_scalar_memory_instruction`]).
pub fn certifiable_bound_memory_queries() -> Vec<CertifiableBoundMemoryQuery> {
    let mut named: Vec<(String, ProofObligation)> = Vec::new();
    for (form, query) in pair_forms::PAIR_MEMORY_FORMS {
        let tag = query
            .trim_start_matches("pairmem[")
            .trim_end_matches(']')
            .replace('.', "_");
        named.push((
            format!("pairmem_{tag}.lratcert"),
            pair_forms::proof_pair_memory_form(&form).expect("table forms are legal"),
        ));
    }
    for (form, query) in scalar_forms::SCALAR_MEMORY_FORMS {
        if form.addressing == scalar_forms::ScalarAddressing::Literal {
            continue;
        }
        let tag = query
            .trim_start_matches("scalarmem[")
            .trim_end_matches(']')
            .replace('.', "_");
        named.push((
            format!("scalarmem_{tag}.lratcert"),
            scalar_forms::proof_scalar_memory(&form).expect("table forms are legal"),
        ));
    }
    let mut out: Vec<CertifiableBoundMemoryQuery> = Vec::new();
    let mut by_query: HashMap<String, usize> = HashMap::new();
    for (file, obligation) in named {
        let key = crate::canary_cert::portable_query_key(&crate::verdict_db::db_obligation_smt2(
            &obligation,
        ));
        match by_query.get(&key) {
            Some(&index) => out[index].forms.push(obligation.name),
            None => {
                by_query.insert(key, out.len());
                out.push(CertifiableBoundMemoryQuery {
                    file,
                    forms: vec![obligation.name.clone()],
                    obligation,
                });
            }
        }
    }
    out
}

/// A deliberately WRONG pair theorem wearing a faithful form's name (the
/// machine side transposes the two transfers). The certificate consumer must
/// refuse it: its exact query is not the faithful one.
pub fn representative_wrong_pair_theorem() -> ProofObligation {
    let (form, _) = pair_forms::PAIR_MEMORY_FORMS[6];
    let mut wrong = pair_forms::proof_pair_memory_form_with_mutation(
        &form,
        pair_forms::PairMachineMutation::SwapTransfers,
    )
    .expect("SwapTransfers applies to every pair form");
    wrong.name = pair_forms::proof_pair_memory_form(&form)
        .expect("table forms are legal")
        .name;
    wrong
}

/// The Formal-only credit a bound-memory row earns when not refuted: on a
/// host whose checker the bound-memory manifest qualifies, `Verified` at
/// `Formal` citing the form theorem `form`; elsewhere a fail-closed miss.
#[cfg(test)]
pub(crate) fn assert_form_credit_or_checker_miss(
    result: &crate::function_verifier::InstructionVerificationResult,
    form: &str,
    what: &str,
) {
    match (bound_memory_checker_qualification(), result) {
        (
            Ok(()),
            crate::function_verifier::InstructionVerificationResult::Verified {
                proof_name,
                category: crate::proof_database::ProofCategory::Memory,
                strength: crate::verify::VerificationStrength::Formal,
                degenerate: false,
            },
        ) => assert!(proof_name.starts_with(form), "{what}: {proof_name}"),
        (
            Err(_),
            crate::function_verifier::InstructionVerificationResult::Unverified { reason },
        ) => assert!(
            reason.contains(BOUND_MEMORY_FORMAL_ONLY) && reason.contains(CHECKER_IDENTITY_MISS),
            "{what}: {reason}"
        ),
        (qualification, other) => {
            panic!("{what}: {other:?} under checker qualification {qualification:?}")
        }
    }
}

#[cfg(test)]
#[path = "bound_memory_binding_tests.rs"]
mod binding_tests;

#[cfg(test)]
#[path = "bound_memory_atomic_tests.rs"]
mod atomic_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::VerificationResult;
    use trust_cg_ir::aarch64_regs::{SP, X0, X1, X19, X20, X29, X30};
    use trust_cg_ir::{AArch64Opcode as O, MachOperand, SpecialReg};

    fn p(reg: trust_cg_ir::PReg) -> MachOperand {
        MachOperand::PReg(reg)
    }

    #[test]
    fn every_bound_form_has_one_query_and_file_and_store_aliases_share_it() {
        let queries = certifiable_bound_memory_queries();
        let forms: usize = queries.iter().map(|query| query.forms.len()).sum();
        // 21 pair forms and 64 scalar forms (the literal form is never
        // attributed to a row, so it needs no certificate).
        assert_eq!(forms, 21 + 64);
        let mut files = std::collections::HashSet::new();
        for query in &queries {
            assert!(files.insert(query.file.clone()), "duplicate {}", query.file);
            for name in &query.forms[1..] {
                assert!(
                    name.contains("STP") || name.contains("STR"),
                    "only store forms may share a query: {name}"
                );
            }
        }
        let aliased: usize = queries.iter().map(|query| query.forms.len() - 1).sum();
        // Pair: stp.offset and stp.pre at W/S and X/D (4). Scalar: ui,
        // unscaled and ro stores at w2, w4 and w8 (9).
        assert_eq!(aliased, 4 + 9, "store alias groups changed");
        assert_eq!(queries.len(), 21 + 64 - aliased);
    }

    #[test]
    fn the_wrong_theorem_is_not_the_faithful_query() {
        let wrong = representative_wrong_pair_theorem();
        let (form, _) = pair_forms::PAIR_MEMORY_FORMS[6];
        let faithful = pair_forms::proof_pair_memory_form(&form).unwrap();
        assert_eq!(wrong.name, faithful.name);
        assert_ne!(
            crate::verdict_db::db_obligation_smt2(&wrong),
            crate::verdict_db::db_obligation_smt2(&faithful)
        );
        assert!(form_certificate_status(&wrong).is_err());
        // Asking about the wrong theorem first must not poison the faithful
        // form's lookup (the memo is keyed by content, not by name). On a host
        // whose checker the manifest does not qualify, the faithful form is a
        // checker-identity miss instead.
        match bound_memory_checker_qualification() {
            Ok(()) => assert_eq!(form_certificate_status(&faithful), Ok(())),
            Err(_) => assert!(
                form_certificate_status(&faithful)
                    .is_err_and(|miss| miss.contains(CHECKER_IDENTITY_MISS))
            ),
        }
        assert!(form_certificate_status(&wrong).is_err());
    }

    #[test]
    fn frame_pairs_and_spills_bind_the_expected_forms() {
        let sp = || MachOperand::Special(SpecialReg::SP);
        let cases = [
            (
                MachInst::new(
                    O::StpPreIndex,
                    vec![p(X29), p(X30), sp(), MachOperand::Imm(-16)],
                ),
                "pairmem[stp.pre.gpr.w8]",
            ),
            (
                MachInst::new(
                    O::LdpPostIndex,
                    vec![p(X29), p(X30), sp(), MachOperand::Imm(16)],
                ),
                "pairmem[ldp.post.gpr.w8]",
            ),
            (
                MachInst::new(O::StpRI, vec![p(X19), p(X20), p(SP), MachOperand::Imm(16)]),
                "pairmem[stp.offset.gpr.w8]",
            ),
            (
                MachInst::new(
                    O::LdrRI,
                    vec![
                        p(X0),
                        MachOperand::MemOp {
                            base: X29,
                            offset: -8,
                        },
                    ],
                ),
                "scalarmem[ldr.unscaled.gpr.w8.zx]",
            ),
            (
                MachInst::new(O::StrRI, vec![p(X1), p(X0), MachOperand::Imm(8)]),
                "scalarmem[str.ui.gpr.w8]",
            ),
        ];
        for (inst, query) in cases {
            match bind_bound_memory_row(&inst) {
                Some(Ok(binding)) => assert_eq!(binding.query(), query, "{inst:?}"),
                other => panic!("{inst:?} must bind {query}: {other:?}"),
            }
        }
        assert!(bind_bound_memory_row(&MachInst::new(O::AddRI, vec![])).is_none());
        // An operand-less carrier is a bound-memory opcode that binds nothing.
        assert!(matches!(
            bind_bound_memory_row(&MachInst::new(O::LdrRI, vec![])),
            Some(Err(_))
        ));
    }

    /// Every faithful form theorem holds on the evaluator's edge battery and
    /// sampled points: the sampler is never EVIDENCE for these rows, but a
    /// sampled counterexample to a faithful form would be a bug in the form
    /// itself.
    #[test]
    fn faithful_forms_are_never_refuted_by_the_evaluator() {
        let config = crate::lowering_proof::VerificationConfig::with_sample_count(512);
        for query in certifiable_bound_memory_queries() {
            let verdict =
                crate::lowering_proof::verify_by_evaluation_with_config(&query.obligation, &config);
            assert!(
                !matches!(verdict, VerificationResult::Invalid { .. }),
                "{}: {verdict:?}",
                query.obligation.name
            );
        }
    }
}
