// crates/trust-cg-eqsat/src/proof.rs - proof construction with tracked conclusions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The engine's side of section 7.1: every proof it builds goes through
//! [`Prover`], which records each proof's conclusion `(lhs, rhs, equiv?)` and
//! refuses (with an [`EngineError`]) to compose steps that do not fit: a
//! `Trans` whose middle terms differ, a `Sym` of a `refines` conclusion. The
//! conclusion of a rule step is the engine's own instantiation of the rule's
//! sides; the checker re-derives it independently. Nothing here is trusted:
//! a mistake is caught by the checker, and the composition checks only keep
//! the engine from emitting a derivation it already knows is wrong.

use std::fmt;

use crate::derivation::{DerivationBuilder, ProofRef, RuleRef, TermRef};
use crate::vocab::{OpDesc, ScalarTy};

/// An engine invariant that did not hold. The public API turns it into a
/// fail-closed decline: no output is produced from a graph the engine cannot
/// explain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EngineError(pub(crate) String);

impl fmt::Display for EngineError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "engine invariant failed: {}", self.0)
    }
}

pub(crate) type EngineResult<T> = Result<T, EngineError>;

pub(crate) fn invariant<T>(message: impl Into<String>) -> EngineResult<T> {
    Err(EngineError(message.into()))
}

/// What a proof concludes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Conclusion {
    pub(crate) lhs: TermRef,
    pub(crate) rhs: TermRef,
    pub(crate) equiv: bool,
    pub(crate) refl: bool,
}

/// A [`DerivationBuilder`] plus the conclusion of every proof in it.
#[derive(Debug, Clone)]
pub(crate) struct Prover {
    builder: DerivationBuilder,
    conclusions: Vec<Conclusion>,
}

impl Prover {
    pub(crate) fn new(function_name: &str) -> Self {
        Self {
            builder: DerivationBuilder::new(function_name),
            conclusions: Vec::new(),
        }
    }

    pub(crate) fn into_builder(self) -> DerivationBuilder {
        self.builder
    }

    fn record(&mut self, proof: ProofRef, conclusion: Conclusion) -> EngineResult<ProofRef> {
        let index = proof.index();
        if index == self.conclusions.len() {
            self.conclusions.push(conclusion);
            Ok(proof)
        } else if self.conclusions.get(index).is_some_and(|c| {
            c.lhs == conclusion.lhs && c.rhs == conclusion.rhs && c.equiv == conclusion.equiv
        }) {
            Ok(proof)
        } else {
            invariant("an interned proof has two different conclusions")
        }
    }

    pub(crate) fn conclusion(&self, proof: ProofRef) -> EngineResult<Conclusion> {
        match self.conclusions.get(proof.index()) {
            Some(c) => Ok(*c),
            None => invariant("a proof without a recorded conclusion"),
        }
    }

    // ---- terms -------------------------------------------------------------

    pub(crate) fn param(&mut self, block: u32, index: u32) -> TermRef {
        self.builder.param(block, index)
    }

    pub(crate) fn result(&mut self, block: u32, ordinal: u32, index: u32) -> TermRef {
        self.builder.result(block, ordinal, index)
    }

    pub(crate) fn constant(&mut self, ty: ScalarTy, residue: u128) -> TermRef {
        self.builder.constant(ty, residue)
    }

    pub(crate) fn op(&mut self, desc: OpDesc, args: &[TermRef]) -> TermRef {
        self.builder.op(desc, args)
    }

    // ---- proofs ------------------------------------------------------------

    pub(crate) fn refl(&mut self, term: TermRef) -> EngineResult<ProofRef> {
        let proof = self.builder.refl(term);
        self.record(
            proof,
            Conclusion {
                lhs: term,
                rhs: term,
                equiv: true,
                refl: true,
            },
        )
    }

    /// `Sym(p)`; refused for a `refines` conclusion. `Sym` of a reflexivity
    /// is that reflexivity.
    pub(crate) fn sym(&mut self, proof: ProofRef) -> EngineResult<ProofRef> {
        let c = self.conclusion(proof)?;
        if c.refl {
            return Ok(proof);
        }
        if !c.equiv {
            return invariant("Sym of a refines conclusion");
        }
        let sym = self.builder.sym(proof);
        self.record(
            sym,
            Conclusion {
                lhs: c.rhs,
                rhs: c.lhs,
                equiv: true,
                refl: false,
            },
        )
    }

    /// `Trans(p, q)`; a reflexivity on either side is dropped.
    pub(crate) fn trans(&mut self, first: ProofRef, second: ProofRef) -> EngineResult<ProofRef> {
        let a = self.conclusion(first)?;
        let b = self.conclusion(second)?;
        if a.rhs != b.lhs {
            return invariant("Trans with different middle terms");
        }
        if a.refl {
            return Ok(second);
        }
        if b.refl {
            return Ok(first);
        }
        let proof = self.builder.trans(first, second);
        self.record(
            proof,
            Conclusion {
                lhs: a.lhs,
                rhs: b.rhs,
                equiv: a.equiv && b.equiv,
                refl: false,
            },
        )
    }

    /// Fold `Trans` over a chain from the right (`Trans(s1, Trans(s2,
    /// ...))`), so chains that end alike share their suffix in the interned
    /// proof table; `start` is the term the chain starts at, used when the
    /// chain is empty.
    pub(crate) fn chain(&mut self, start: TermRef, steps: &[ProofRef]) -> EngineResult<ProofRef> {
        let Some((&last, rest)) = steps.split_last() else {
            return self.refl(start);
        };
        let mut acc = last;
        for step in rest.iter().rev() {
            acc = self.trans(*step, acc)?;
        }
        if self.conclusion(acc)?.lhs != start {
            return invariant("a chain that does not start at its start term");
        }
        Ok(acc)
    }

    /// `Congr(desc, ps)`; all reflexivities give the reflexivity of the
    /// operator term.
    pub(crate) fn congr(&mut self, desc: OpDesc, proofs: &[ProofRef]) -> EngineResult<ProofRef> {
        if proofs.len() != desc.arity() {
            return invariant("Congr with the wrong arity");
        }
        let mut lhs = Vec::with_capacity(proofs.len());
        let mut rhs = Vec::with_capacity(proofs.len());
        let mut equiv = true;
        let mut all_refl = true;
        for proof in proofs {
            let c = self.conclusion(*proof)?;
            lhs.push(c.lhs);
            rhs.push(c.rhs);
            equiv &= c.equiv;
            all_refl &= c.refl;
        }
        let lhs_term = self.op(desc, &lhs);
        if all_refl {
            return self.refl(lhs_term);
        }
        let rhs_term = self.op(desc, &rhs);
        let proof = self.builder.congr(desc, proofs);
        self.record(
            proof,
            Conclusion {
                lhs: lhs_term,
                rhs: rhs_term,
                equiv,
                refl: false,
            },
        )
    }

    pub(crate) fn rule(&mut self, name: &str, digest: [u8; 32]) -> RuleRef {
        self.builder.rule(name, digest)
    }

    /// A rule step whose conclusion the caller computed by instantiating the
    /// rule's own sides with `bindings` at `ty`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn rule_step(
        &mut self,
        rule: RuleRef,
        ty: ScalarTy,
        bindings: &[(&str, TermRef)],
        side_conditions: u32,
        lhs: TermRef,
        rhs: TermRef,
        equiv: bool,
    ) -> EngineResult<ProofRef> {
        let proof = self.builder.rule_step(rule, ty, bindings, side_conditions);
        self.record(
            proof,
            Conclusion {
                lhs,
                rhs,
                equiv,
                refl: false,
            },
        )
    }

    pub(crate) fn claim(&mut self, proof: ProofRef) {
        self.builder.claim(proof);
    }
}
