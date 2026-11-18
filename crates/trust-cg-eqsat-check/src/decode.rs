// trust-cg-eqsat-check/src/decode.rs - derivation byte format (versions 1 and 2) with canonicity refusals
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Decodes docs/eqsat-tier-e.md section 7.2 and refuses every non-canonical
//! encoding the section names: entries not topologically ordered, equal term
//! or proof entries, entries unreachable from a claim, claims not strictly
//! increasing, an unsorted or repeated rule table or binding list, and bytes
//! after the claims.
//!
//! Version 1 is a Tier E (function) derivation. Version 2 is a Tier S
//! (region) derivation (docs/eqsat-tier-s.md section 6): version 1 plus the
//! pinned-reduction opdesc and the `Impl` proof step. The caller says which
//! [`Tier`] it checks; the other version, and under Tier E both additions,
//! are refused here.
//!
//! This layer is purely syntactic: it does not type terms, look up leaves or
//! rules, or replay proofs (see `replay`). Counts are never trusted for
//! allocation; every read is bounds-checked.

use std::collections::BTreeSet;

use crate::rejection::{DecodeError, NonCanonicalKind, Rejection};
use crate::types::{ALL_BIN, ALL_CAST, ALL_PRED, ALL_UN, BinK, CastK, OpDesc, Pred, Sty, UnK};

pub(crate) const MAGIC: &[u8; 8] = b"TCGEQSAT";

/// Which derivation format the caller checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Tier {
    /// A function derivation: version 1.
    E,
    /// A region derivation: version 2.
    S,
}

impl Tier {
    pub(crate) const fn version(self) -> u32 {
        match self {
            Tier::E => 1,
            Tier::S => 2,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RawTerm {
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
        ty: Sty,
        residue: u128,
    },
    Op {
        desc: OpDesc,
        args: Vec<u32>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RawProof {
    Refl(u32),
    Sym(u32),
    Trans(u32, u32),
    Congr(OpDesc, Vec<u32>),
    Rule {
        rule: u32,
        ty: Sty,
        bindings: Vec<(String, u32)>,
        premises: Vec<u32>,
    },
    /// Version 2 only: the order-free node whose result is the leaf term
    /// `leaf`, implemented by the reduction pinned at `order`.
    Impl {
        leaf: u32,
        order: u32,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct Derivation {
    pub(crate) function: String,
    pub(crate) rules: Vec<(String, [u8; 32])>,
    pub(crate) terms: Vec<RawTerm>,
    pub(crate) proofs: Vec<RawProof>,
    pub(crate) claims: Vec<u32>,
}

pub(crate) struct Reader<'a> {
    bytes: &'a [u8],
    pub(crate) pos: usize,
    tier: Tier,
}

impl<'a> Reader<'a> {
    pub(crate) fn new(bytes: &'a [u8], tier: Tier) -> Self {
        Reader {
            bytes,
            pos: 0,
            tier,
        }
    }

    /// Refuses bytes after the last field.
    pub(crate) fn finish(&self) -> Result<(), Rejection> {
        if self.pos == self.bytes.len() {
            Ok(())
        } else {
            Err(Rejection::Decode {
                offset: self.pos,
                detail: DecodeError::TrailingBytes {
                    count: self.bytes.len() - self.pos,
                },
            })
        }
    }

    fn err(&self, detail: DecodeError) -> Rejection {
        Rejection::Decode {
            offset: self.pos,
            detail,
        }
    }

    pub(crate) fn take(&mut self, n: usize) -> Result<&'a [u8], Rejection> {
        let end = self.pos.checked_add(n).filter(|&e| e <= self.bytes.len());
        match end {
            Some(end) => {
                let out = &self.bytes[self.pos..end];
                self.pos = end;
                Ok(out)
            }
            None => Err(self.err(DecodeError::Truncated { needed: n })),
        }
    }

    pub(crate) fn u8(&mut self) -> Result<u8, Rejection> {
        Ok(self.take(1)?[0])
    }

    pub(crate) fn u32(&mut self) -> Result<u32, Rejection> {
        let b = self.take(4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }

    fn u128(&mut self) -> Result<u128, Rejection> {
        let b = self.take(16)?;
        let mut a = [0u8; 16];
        a.copy_from_slice(b);
        Ok(u128::from_le_bytes(a))
    }

    pub(crate) fn str(&mut self) -> Result<String, Rejection> {
        let len = self.u32()? as usize;
        let start = self.pos;
        let b = self.take(len)?;
        match std::str::from_utf8(b) {
            Ok(s) => Ok(s.to_owned()),
            Err(_) => Err(Rejection::Decode {
                offset: start,
                detail: DecodeError::BadUtf8,
            }),
        }
    }

    pub(crate) fn ty(&mut self, what: &'static str) -> Result<Sty, Rejection> {
        let at = self.pos;
        let code = self.u8()?;
        Sty::from_code(code).ok_or(Rejection::Decode {
            offset: at,
            detail: DecodeError::BadCode { what, code },
        })
    }

    /// Reads one code byte and maps it through `table` by `code_of`.
    fn coded<T: Copy>(
        &mut self,
        what: &'static str,
        table: &[T],
        code_of: impl Fn(T) -> u8,
    ) -> Result<T, Rejection> {
        let at = self.pos;
        let code = self.u8()?;
        table
            .iter()
            .copied()
            .find(|k| code_of(*k) == code)
            .ok_or(Rejection::Decode {
                offset: at,
                detail: DecodeError::BadCode { what, code },
            })
    }

    fn opdesc(&mut self) -> Result<OpDesc, Rejection> {
        let at = self.pos;
        let kind = self.u8()?;
        Ok(match kind {
            0x01 => {
                let k = self.coded("bin op", &ALL_BIN, BinK::code)?;
                OpDesc::Bin(k, self.ty("type")?)
            }
            0x02 => {
                let k = self.coded("unary op", &ALL_UN, UnK::code)?;
                OpDesc::Un(k, self.ty("type")?)
            }
            0x03 => {
                let p = self.coded("predicate", &ALL_PRED, Pred::code)?;
                OpDesc::Cmp(p, self.ty("type")?)
            }
            0x04 => {
                let k = self.coded("cast op", &ALL_CAST, CastK::code)?;
                let s = self.ty("source type")?;
                let d = self.ty("destination type")?;
                OpDesc::Cast(k, s, d)
            }
            0x05 => OpDesc::Select(self.ty("type")?),
            0x06 if self.tier == Tier::S => {
                let order = self.u32()?;
                OpDesc::Pinned(order, self.ty("type")?)
            }
            tag => {
                return Err(Rejection::Decode {
                    offset: at,
                    detail: DecodeError::BadTag {
                        what: "opdesc kind",
                        tag,
                    },
                });
            }
        })
    }

    /// Reads term entry `index` of a term table (section 7.2 `Term`): every
    /// operand names an earlier entry.
    pub(crate) fn term(&mut self, index: usize) -> Result<RawTerm, Rejection> {
        let at = self.pos;
        let tag = self.u8()?;
        Ok(match tag {
            0x01 => RawTerm::Param {
                block: self.u32()?,
                index: self.u32()?,
            },
            0x02 => RawTerm::Result {
                block: self.u32()?,
                ordinal: self.u32()?,
                index: self.u32()?,
            },
            0x03 => {
                let ty = self.ty("const type")?;
                RawTerm::Const {
                    ty,
                    residue: self.u128()?,
                }
            }
            0x04 => {
                let desc = self.opdesc()?;
                let mut args = Vec::new();
                for _ in 0..desc.arity() {
                    let a = self.u32()?;
                    if a as usize >= index {
                        return Err(non_canonical(NonCanonicalKind::TermOrder, index));
                    }
                    args.push(a);
                }
                RawTerm::Op { desc, args }
            }
            tag => {
                return Err(Rejection::Decode {
                    offset: at,
                    detail: DecodeError::BadTag { what: "term", tag },
                });
            }
        })
    }
}

fn non_canonical(kind: NonCanonicalKind, index: usize) -> Rejection {
    Rejection::NonCanonical { kind, index }
}

fn out_of_range(offset: usize, what: &'static str, index: u32, limit: usize) -> Rejection {
    Rejection::Decode {
        offset,
        detail: DecodeError::IndexOutOfRange { what, index, limit },
    }
}

/// Decodes a derivation of `tier`'s version and checks canonicity.
pub(crate) fn decode(bytes: &[u8], tier: Tier) -> Result<Derivation, Rejection> {
    let mut r = Reader::new(bytes, tier);
    let magic = r.take(8)?;
    if magic != MAGIC {
        return Err(Rejection::Decode {
            offset: 0,
            detail: DecodeError::BadMagic,
        });
    }
    let version_at = r.pos;
    let version = r.u32()?;
    if version != tier.version() {
        return Err(Rejection::Decode {
            offset: version_at,
            detail: DecodeError::BadVersion { version },
        });
    }
    let function = r.str()?;

    // Rule table.
    let rule_count = r.u32()?;
    let mut rules: Vec<(String, [u8; 32])> = Vec::new();
    for i in 0..rule_count as usize {
        let name = r.str()?;
        let d = r.take(32)?;
        let mut digest = [0u8; 32];
        digest.copy_from_slice(d);
        if let Some((prev, _)) = rules.last()
            && prev.as_bytes() >= name.as_bytes()
        {
            return Err(non_canonical(NonCanonicalKind::UnsortedRuleTable, i));
        }
        rules.push((name, digest));
    }

    // Terms.
    let term_count = r.u32()?;
    let mut terms: Vec<RawTerm> = Vec::new();
    for i in 0..term_count as usize {
        terms.push(r.term(i)?);
    }

    // Proofs.
    let proof_count = r.u32()?;
    let n_terms = terms.len();
    let n_rules = rules.len();
    let mut proofs: Vec<RawProof> = Vec::new();
    for i in 0..proof_count as usize {
        let at = r.pos;
        let tag = r.u8()?;
        let earlier = |r: &mut Reader<'_>| -> Result<u32, Rejection> {
            let p = r.u32()?;
            if p as usize >= i {
                return Err(non_canonical(NonCanonicalKind::ProofOrder, i));
            }
            Ok(p)
        };
        let proof = match tag {
            0x01 => {
                let t_at = r.pos;
                let t = r.u32()?;
                if t as usize >= n_terms {
                    return Err(out_of_range(t_at, "term", t, n_terms));
                }
                RawProof::Refl(t)
            }
            0x02 => RawProof::Sym(earlier(&mut r)?),
            0x03 => {
                let p = earlier(&mut r)?;
                let q = earlier(&mut r)?;
                RawProof::Trans(p, q)
            }
            0x04 => {
                let desc = r.opdesc()?;
                let mut ps = Vec::new();
                for _ in 0..desc.arity() {
                    ps.push(earlier(&mut r)?);
                }
                RawProof::Congr(desc, ps)
            }
            0x05 => {
                let rule_at = r.pos;
                let rule = r.u32()?;
                if rule as usize >= n_rules {
                    return Err(out_of_range(rule_at, "rule-table entry", rule, n_rules));
                }
                let ty = r.ty("instance type")?;
                let n = r.u32()?;
                let mut bindings: Vec<(String, u32)> = Vec::new();
                for _ in 0..n {
                    let name = r.str()?;
                    let t_at = r.pos;
                    let t = r.u32()?;
                    if t as usize >= n_terms {
                        return Err(out_of_range(t_at, "term", t, n_terms));
                    }
                    if let Some((prev, _)) = bindings.last()
                        && prev.as_bytes() >= name.as_bytes()
                    {
                        return Err(non_canonical(NonCanonicalKind::UnsortedBindings, i));
                    }
                    bindings.push((name, t));
                }
                let m = r.u32()?;
                let mut premises = Vec::new();
                for _ in 0..m {
                    premises.push(r.u32()?);
                }
                RawProof::Rule {
                    rule,
                    ty,
                    bindings,
                    premises,
                }
            }
            0x06 if tier == Tier::S => {
                let t_at = r.pos;
                let leaf = r.u32()?;
                if leaf as usize >= n_terms {
                    return Err(out_of_range(t_at, "term", leaf, n_terms));
                }
                RawProof::Impl {
                    leaf,
                    order: r.u32()?,
                }
            }
            tag => {
                return Err(Rejection::Decode {
                    offset: at,
                    detail: DecodeError::BadTag { what: "proof", tag },
                });
            }
        };
        proofs.push(proof);
    }

    // Claims.
    let claim_count = r.u32()?;
    let mut claims: Vec<u32> = Vec::new();
    for i in 0..claim_count as usize {
        let at = r.pos;
        let c = r.u32()?;
        if c as usize >= proofs.len() {
            return Err(out_of_range(at, "proof", c, proofs.len()));
        }
        if let Some(&prev) = claims.last()
            && prev >= c
        {
            return Err(non_canonical(NonCanonicalKind::ClaimsOrder, i));
        }
        claims.push(c);
    }
    r.finish()?;

    // No two equal entries.
    let mut seen_terms = BTreeSet::new();
    for (i, t) in terms.iter().enumerate() {
        if !seen_terms.insert(t) {
            return Err(non_canonical(NonCanonicalKind::DuplicateTerm, i));
        }
    }
    let mut seen_proofs = BTreeSet::new();
    for (i, p) in proofs.iter().enumerate() {
        if !seen_proofs.insert(p) {
            return Err(non_canonical(NonCanonicalKind::DuplicateProof, i));
        }
    }

    // Everything reachable from a claim.
    let mut proof_live = vec![false; proofs.len()];
    let mut term_live = vec![false; terms.len()];
    let mut rule_live = vec![false; rules.len()];
    for &c in &claims {
        proof_live[c as usize] = true;
    }
    // Proof references point backwards, so one descending sweep closes them.
    for i in (0..proofs.len()).rev() {
        if !proof_live[i] {
            continue;
        }
        match &proofs[i] {
            RawProof::Refl(t) | RawProof::Impl { leaf: t, .. } => term_live[*t as usize] = true,
            RawProof::Sym(p) => proof_live[*p as usize] = true,
            RawProof::Trans(p, q) => {
                proof_live[*p as usize] = true;
                proof_live[*q as usize] = true;
            }
            RawProof::Congr(_, ps) => {
                for p in ps {
                    proof_live[*p as usize] = true;
                }
            }
            RawProof::Rule { rule, bindings, .. } => {
                rule_live[*rule as usize] = true;
                for (_, t) in bindings {
                    term_live[*t as usize] = true;
                }
            }
        }
    }
    for i in (0..terms.len()).rev() {
        if !term_live[i] {
            continue;
        }
        if let RawTerm::Op { args, .. } = &terms[i] {
            for a in args {
                term_live[*a as usize] = true;
            }
        }
    }
    if let Some(i) = proof_live.iter().position(|l| !l) {
        return Err(non_canonical(NonCanonicalKind::UnreachableProof, i));
    }
    if let Some(i) = term_live.iter().position(|l| !l) {
        return Err(non_canonical(NonCanonicalKind::UnreachableTerm, i));
    }
    if let Some(i) = rule_live.iter().position(|l| !l) {
        return Err(non_canonical(NonCanonicalKind::UnreachableRule, i));
    }

    Ok(Derivation {
        function,
        rules,
        terms,
        proofs,
        claims,
    })
}
