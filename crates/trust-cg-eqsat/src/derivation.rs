// crates/trust-cg-eqsat/src/derivation.rs - canonical encoder for section 7.2 derivations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The derivation byte format (`docs/eqsat-tier-e.md` section 7.2): version
//! 1 for a Tier E function, version 2 for a Tier S region
//! (`docs/eqsat-tier-s.md` section 6: version 1 plus the pinned-reduction
//! operator and the `Impl` step).
//!
//! [`DerivationBuilder`] interns terms and proofs (structurally equal entries
//! get one reference) and [`DerivationBuilder::finish`] writes the canonical
//! encoding: only entries reachable from a claim, children before parents,
//! numbered by one deterministic depth-first traversal from the claims in the
//! order they were added, the rule table sorted by name bytes, the claims
//! strictly increasing.
//!
//! The builder checks no meaning: it will encode a proof whose steps do not
//! fit together, a wrong rule digest or a residue that is too wide. That is on
//! purpose: the tests use it to forge the derivations a faulty engine could
//! emit, and only the checker decides what a derivation proves. The engine
//! writes its own derivations through this same encoder.

use std::collections::BTreeMap;

pub use crate::vocab::{BinOpCode, CastOpCode, CmpPred, OpDesc, ScalarTy, UnOpCode};

/// The magic bytes that open every derivation.
pub const MAGIC: [u8; 8] = *b"TCGEQSAT";

/// The format version of a Tier E (function) derivation.
pub const VERSION: u32 = 1;

/// The format version of a Tier S (region) derivation
/// (`docs/eqsat-tier-s.md` section 6).
pub const REGION_VERSION: u32 = 2;

/// A rule-table entry of a [`DerivationBuilder`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RuleRef(u32);

/// A term of a [`DerivationBuilder`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermRef(u32);

/// A proof of a [`DerivationBuilder`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProofRef(u32);

impl TermRef {
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

impl ProofRef {
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

/// A term entry (section 7.2 `Term`), children by builder index.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum TermEntry {
    Param {
        block: u32,
        index: u32,
    },
    Result {
        block: u32,
        ordinal: u32,
        index: u32,
    },
    Const {
        ty: ScalarTy,
        residue: u128,
    },
    Op {
        desc: OpDesc,
        args: Vec<TermRef>,
    },
}

/// A proof entry (section 7.2 `Proof`), children by builder index.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ProofEntry {
    Refl(TermRef),
    Sym(ProofRef),
    Trans(ProofRef, ProofRef),
    Congr(OpDesc, Vec<ProofRef>),
    Rule {
        rule: RuleRef,
        ty: ScalarTy,
        bindings: Vec<(String, TermRef)>,
        side_conditions: u32,
    },
    /// `Impl(leaf, order)` (version 2 only): the order-free node whose
    /// result is `leaf`, implemented by the reduction pinned at `order`.
    Impl {
        leaf: TermRef,
        order: u32,
    },
}

/// Builds one derivation. See the module docs: no meaning is checked.
#[derive(Debug, Clone)]
pub struct DerivationBuilder {
    version: u32,
    function: String,
    rules: Vec<(String, [u8; 32])>,
    rule_index: BTreeMap<(String, [u8; 32]), RuleRef>,
    terms: Vec<TermEntry>,
    term_index: BTreeMap<TermEntry, TermRef>,
    proofs: Vec<ProofEntry>,
    proof_index: BTreeMap<ProofEntry, ProofRef>,
    claims: Vec<ProofRef>,
}

fn index_u32(len: usize) -> u32 {
    // Builder tables are bounded by memory long before 2^32 entries; a
    // saturated index would only make the encoding refused by a checker.
    u32::try_from(len).unwrap_or(u32::MAX)
}

impl DerivationBuilder {
    /// A builder for a derivation about the function named `function_name`.
    #[must_use]
    pub fn new(function_name: &str) -> Self {
        Self {
            version: VERSION,
            function: function_name.to_owned(),
            rules: Vec::new(),
            rule_index: BTreeMap::new(),
            terms: Vec::new(),
            term_index: BTreeMap::new(),
            proofs: Vec::new(),
            proof_index: BTreeMap::new(),
            claims: Vec::new(),
        }
    }

    /// A builder for a version-2 derivation about the Tier S region named
    /// `region_name` (`docs/eqsat-tier-s.md` section 6).
    #[must_use]
    pub fn new_region(region_name: &str) -> Self {
        let mut builder = Self::new(region_name);
        builder.version = REGION_VERSION;
        builder
    }

    /// Register a rule-table entry `(name, digest)` (interned).
    pub fn rule(&mut self, name: &str, digest: [u8; 32]) -> RuleRef {
        let key = (name.to_owned(), digest);
        if let Some(found) = self.rule_index.get(&key) {
            return *found;
        }
        let reference = RuleRef(index_u32(self.rules.len()));
        self.rules.push(key.clone());
        self.rule_index.insert(key, reference);
        reference
    }

    fn term(&mut self, entry: TermEntry) -> TermRef {
        if let Some(found) = self.term_index.get(&entry) {
            return *found;
        }
        let reference = TermRef(index_u32(self.terms.len()));
        self.terms.push(entry.clone());
        self.term_index.insert(entry, reference);
        reference
    }

    fn proof(&mut self, entry: ProofEntry) -> ProofRef {
        if let Some(found) = self.proof_index.get(&entry) {
            return *found;
        }
        let reference = ProofRef(index_u32(self.proofs.len()));
        self.proofs.push(entry.clone());
        self.proof_index.insert(entry, reference);
        reference
    }

    /// The leaf `Param(block, index)`.
    pub fn param(&mut self, block: u32, index: u32) -> TermRef {
        self.term(TermEntry::Param { block, index })
    }

    /// The leaf `Result(block, ordinal, index)`.
    pub fn result(&mut self, block: u32, ordinal: u32, index: u32) -> TermRef {
        self.term(TermEntry::Result {
            block,
            ordinal,
            index,
        })
    }

    /// The constant `Const(ty, residue)` (the residue is not range checked).
    pub fn constant(&mut self, ty: ScalarTy, residue: u128) -> TermRef {
        self.term(TermEntry::Const { ty, residue })
    }

    /// The operator term `desc(args)` (the arity is not checked).
    pub fn op(&mut self, desc: OpDesc, args: &[TermRef]) -> TermRef {
        self.term(TermEntry::Op {
            desc,
            args: args.to_vec(),
        })
    }

    /// `Refl(t)`.
    pub fn refl(&mut self, term: TermRef) -> ProofRef {
        self.proof(ProofEntry::Refl(term))
    }

    /// `Sym(p)`.
    pub fn sym(&mut self, proof: ProofRef) -> ProofRef {
        self.proof(ProofEntry::Sym(proof))
    }

    /// `Trans(p, q)`.
    pub fn trans(&mut self, first: ProofRef, second: ProofRef) -> ProofRef {
        self.proof(ProofEntry::Trans(first, second))
    }

    /// `Congr(desc, p1..pn)` (the arity is not checked).
    pub fn congr(&mut self, desc: OpDesc, proofs: &[ProofRef]) -> ProofRef {
        self.proof(ProofEntry::Congr(desc, proofs.to_vec()))
    }

    /// `Rule(rule, ty, bindings, premises 0..side_conditions)`. Bindings are
    /// sorted by name bytes (a stable sort: repeated names are kept, in the
    /// order given, and a checker refuses them).
    pub fn rule_step(
        &mut self,
        rule: RuleRef,
        ty: ScalarTy,
        bindings: &[(&str, TermRef)],
        side_conditions: u32,
    ) -> ProofRef {
        let mut bindings: Vec<(String, TermRef)> = bindings
            .iter()
            .map(|(name, term)| ((*name).to_owned(), *term))
            .collect();
        bindings.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
        self.proof(ProofEntry::Rule {
            rule,
            ty,
            bindings,
            side_conditions,
        })
    }

    /// `Impl(leaf, order)`: the order-free node whose result is `leaf`,
    /// implemented by the reduction pinned at `order` over its operand.
    /// Version 2 only; nothing is checked (a version-1 builder encodes it
    /// too, and a checker refuses the bytes).
    pub fn implement(&mut self, leaf: TermRef, order: u32) -> ProofRef {
        self.proof(ProofEntry::Impl { leaf, order })
    }

    /// Claim `proof`'s conclusion (repeated claims are kept once).
    pub fn claim(&mut self, proof: ProofRef) {
        if !self.claims.contains(&proof) {
            self.claims.push(proof);
        }
    }

    /// The canonical encoding (section 7.2).
    #[must_use]
    pub fn finish(self) -> Vec<u8> {
        Encoder::new(&self).encode()
    }
}

/// Renumbers the reachable part of a builder and writes it.
struct Encoder<'a> {
    builder: &'a DerivationBuilder,
    term_new: Vec<Option<u32>>,
    term_order: Vec<TermRef>,
    proof_new: Vec<Option<u32>>,
    proof_order: Vec<ProofRef>,
    rules_used: Vec<bool>,
}

impl<'a> Encoder<'a> {
    fn new(builder: &'a DerivationBuilder) -> Self {
        Self {
            builder,
            term_new: vec![None; builder.terms.len()],
            term_order: Vec::new(),
            proof_new: vec![None; builder.proofs.len()],
            proof_order: Vec::new(),
            rules_used: vec![false; builder.rules.len()],
        }
    }

    /// Post-order numbering of a term and its sub-terms (iterative).
    fn visit_term(&mut self, root: TermRef) {
        let mut stack: Vec<(TermRef, bool)> = vec![(root, false)];
        while let Some((term, expanded)) = stack.pop() {
            let Some(slot) = self.term_new.get(term.index()) else {
                continue;
            };
            if slot.is_some() {
                continue;
            }
            if expanded {
                if let Some(slot) = self.term_new.get_mut(term.index()) {
                    *slot = Some(index_u32(self.term_order.len()));
                }
                self.term_order.push(term);
                continue;
            }
            stack.push((term, true));
            if let Some(TermEntry::Op { args, .. }) = self.builder.terms.get(term.index()) {
                for arg in args.iter().rev() {
                    stack.push((*arg, false));
                }
            }
        }
    }

    /// Post-order numbering of a proof, its sub-proofs and its terms.
    fn visit_proof(&mut self, root: ProofRef) {
        let mut stack: Vec<(ProofRef, bool)> = vec![(root, false)];
        while let Some((proof, expanded)) = stack.pop() {
            let Some(slot) = self.proof_new.get(proof.index()) else {
                continue;
            };
            if slot.is_some() {
                continue;
            }
            let Some(entry) = self.builder.proofs.get(proof.index()) else {
                continue;
            };
            if expanded {
                match entry {
                    ProofEntry::Refl(term) | ProofEntry::Impl { leaf: term, .. } => {
                        self.visit_term(*term);
                    }
                    ProofEntry::Rule { rule, bindings, .. } => {
                        if let Some(used) = self.rules_used.get_mut(rule.0 as usize) {
                            *used = true;
                        }
                        for (_, term) in bindings {
                            self.visit_term(*term);
                        }
                    }
                    ProofEntry::Sym(_) | ProofEntry::Trans(..) | ProofEntry::Congr(..) => {}
                }
                if let Some(slot) = self.proof_new.get_mut(proof.index()) {
                    *slot = Some(index_u32(self.proof_order.len()));
                }
                self.proof_order.push(proof);
                continue;
            }
            stack.push((proof, true));
            let children: Vec<ProofRef> = match entry {
                ProofEntry::Refl(_) | ProofEntry::Rule { .. } | ProofEntry::Impl { .. } => {
                    Vec::new()
                }
                ProofEntry::Sym(p) => vec![*p],
                ProofEntry::Trans(p, q) => vec![*p, *q],
                ProofEntry::Congr(_, ps) => ps.clone(),
            };
            for child in children.into_iter().rev() {
                stack.push((child, false));
            }
        }
    }

    fn term_number(&self, term: TermRef) -> u32 {
        self.term_new
            .get(term.index())
            .copied()
            .flatten()
            .unwrap_or(u32::MAX)
    }

    fn proof_number(&self, proof: ProofRef) -> u32 {
        self.proof_new
            .get(proof.index())
            .copied()
            .flatten()
            .unwrap_or(u32::MAX)
    }

    fn encode(mut self) -> Vec<u8> {
        let claims = self.builder.claims.clone();
        for claim in &claims {
            self.visit_proof(*claim);
        }
        // Rule table: used entries sorted by name bytes (then digest).
        let mut used: Vec<(usize, &(String, [u8; 32]))> = self
            .builder
            .rules
            .iter()
            .enumerate()
            .filter(|(index, _)| self.rules_used.get(*index).copied().unwrap_or(false))
            .collect();
        used.sort_by(|a, b| (a.1.0.as_bytes(), a.1.1).cmp(&(b.1.0.as_bytes(), b.1.1)));
        let mut rule_new = vec![u32::MAX; self.builder.rules.len()];
        for (new, (old, _)) in used.iter().enumerate() {
            if let Some(slot) = rule_new.get_mut(*old) {
                *slot = index_u32(new);
            }
        }

        let mut out = Vec::new();
        out.extend_from_slice(&MAGIC);
        put_u32(&mut out, self.builder.version);
        put_str(&mut out, &self.builder.function);
        put_u32(&mut out, index_u32(used.len()));
        for (_, (name, digest)) in &used {
            put_str(&mut out, name);
            out.extend_from_slice(digest);
        }
        put_u32(&mut out, index_u32(self.term_order.len()));
        for term in &self.term_order {
            let Some(entry) = self.builder.terms.get(term.index()) else {
                continue;
            };
            match entry {
                TermEntry::Param { block, index } => {
                    out.push(0x01);
                    put_u32(&mut out, *block);
                    put_u32(&mut out, *index);
                }
                TermEntry::Result {
                    block,
                    ordinal,
                    index,
                } => {
                    out.push(0x02);
                    put_u32(&mut out, *block);
                    put_u32(&mut out, *ordinal);
                    put_u32(&mut out, *index);
                }
                TermEntry::Const { ty, residue } => {
                    out.push(0x03);
                    out.push(ty.code());
                    out.extend_from_slice(&residue.to_le_bytes());
                }
                TermEntry::Op { desc, args } => {
                    out.push(0x04);
                    desc.encode(&mut out);
                    for arg in args {
                        put_u32(&mut out, self.term_number(*arg));
                    }
                }
            }
        }
        put_u32(&mut out, index_u32(self.proof_order.len()));
        for proof in &self.proof_order {
            let Some(entry) = self.builder.proofs.get(proof.index()) else {
                continue;
            };
            match entry {
                ProofEntry::Refl(term) => {
                    out.push(0x01);
                    put_u32(&mut out, self.term_number(*term));
                }
                ProofEntry::Sym(p) => {
                    out.push(0x02);
                    put_u32(&mut out, self.proof_number(*p));
                }
                ProofEntry::Trans(p, q) => {
                    out.push(0x03);
                    put_u32(&mut out, self.proof_number(*p));
                    put_u32(&mut out, self.proof_number(*q));
                }
                ProofEntry::Congr(desc, ps) => {
                    out.push(0x04);
                    desc.encode(&mut out);
                    for p in ps {
                        put_u32(&mut out, self.proof_number(*p));
                    }
                }
                ProofEntry::Rule {
                    rule,
                    ty,
                    bindings,
                    side_conditions,
                } => {
                    out.push(0x05);
                    put_u32(
                        &mut out,
                        rule_new.get(rule.0 as usize).copied().unwrap_or(u32::MAX),
                    );
                    out.push(ty.code());
                    put_u32(&mut out, index_u32(bindings.len()));
                    for (name, term) in bindings {
                        put_str(&mut out, name);
                        put_u32(&mut out, self.term_number(*term));
                    }
                    put_u32(&mut out, *side_conditions);
                    for premise in 0..*side_conditions {
                        put_u32(&mut out, premise);
                    }
                }
                ProofEntry::Impl { leaf, order } => {
                    out.push(0x06);
                    put_u32(&mut out, self.term_number(*leaf));
                    put_u32(&mut out, *order);
                }
            }
        }
        let mut claim_numbers: Vec<u32> = claims
            .iter()
            .map(|claim| self.proof_number(*claim))
            .collect();
        claim_numbers.sort_unstable();
        claim_numbers.dedup();
        put_u32(&mut out, index_u32(claim_numbers.len()));
        for claim in claim_numbers {
            put_u32(&mut out, claim);
        }
        out
    }
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_str(out: &mut Vec<u8>, text: &str) {
    put_u32(out, index_u32(text.len()));
    out.extend_from_slice(text.as_bytes());
}

/// The derivation with nothing to justify: the header with zero rules,
/// terms, proofs and claims (section 7.2).
#[must_use]
pub fn header_only(function_name: &str) -> Vec<u8> {
    DerivationBuilder::new(function_name).finish()
}

/// The version-2 derivation with nothing to justify
/// (`docs/eqsat-tier-s.md` section 6).
#[must_use]
pub fn region_header_only(region_name: &str) -> Vec<u8> {
    DerivationBuilder::new_region(region_name).finish()
}
