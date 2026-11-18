// Copyright 2026 Andrew Yates | Apache-2.0
//! Concrete post-memory propositions from the retained original Core encoding.
//! Logical input bytes and addresses are not host allocation or call evidence.
//! Only the separate owned invocation consumer can supply those physical facts.

use crate::FunctionVerificationRequest;
use crate::function_request::FunctionDischargeContext;
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, VerificationConfig};
use crate::provenance_xcheck::ProvenanceXCheckMode;
use crate::smt::SmtExpr as E;
use crate::source_bound_frame::VoidMemorySourceQueries;
use crate::verify::VerificationResult;
use sha2::{Digest, Sha256};
use std::sync::Arc;
use trust_ir::proof::ProofDigest;
use trust_ir_build::source_byte_entry::{ByteEntryRole, CheckedByteEntrySource};

/// Candidate logical facts for two distinct, aligned, initialized words.
/// Public construction establishes no live storage, permission or observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VoidWordMemoryClaim {
    /// Logical original context address, not an allocation capability.
    pub context_address: u64,
    /// Logical original output address, not a writable borrow.
    pub output_address: u64,
    /// Initialized little-endian context word before the claimed call.
    pub context_before: u64,
    /// Initialized little-endian output word before the claimed call.
    pub output_before: u64,
    /// Claimed context word after the call.
    pub context_after: u64,
    /// Claimed output word after the call.
    pub output_after: u64,
}

/// Every original Core normal-return and post-byte proposition replayed under
/// the same captured enforcing request. Still conditional on the supplied
/// logical inputs; it is not physical invocation or current-memory authority.
pub struct ReplayedVoidWordMemoryClaim {
    claim: VoidWordMemoryClaim,
    compilation: ProofDigest,
    statement: ProofDigest,
    scope: Arc<()>,
    diagnostics: Vec<(String, Option<String>)>,
}
impl ReplayedVoidWordMemoryClaim {
    /// Conditional logical inputs and post-memory claim actually replayed.
    pub fn claim(&self) -> VoidWordMemoryClaim {
        self.claim
    }
    /// The exact all-parts compilation statement from which this was derived.
    pub fn compilation_statement(&self) -> ProofDigest {
        self.compilation
    }
    /// Identity of the geometry, normal-return and sixteen post-byte proofs.
    pub fn statement_digest(&self) -> ProofDigest {
        self.statement
    }
    /// Raw query identities and the existing formal replay provenance.
    pub fn replay_diagnostics(&self) -> &[(String, Option<String>)] {
        &self.diagnostics
    }
    pub(crate) fn belongs_to(&self, scope: &Arc<()>) -> bool {
        Arc::ptr_eq(&self.scope, scope)
    }
}

pub(crate) struct Template {
    applicable: bool,
    normal: E,
    byte: E,
    definitions: Vec<E>,
    geometry: Vec<E>,
}
impl Template {
    pub(crate) fn applicable(&self) -> bool {
        self.applicable
    }
    pub(crate) fn capture(
        source: &VoidMemorySourceQueries<'_>,
        family: &CheckedByteEntrySource<'_>,
    ) -> Self {
        Self {
            applicable: family.accesses().iter().all(|a| {
                a.offset() == 0
                    && matches!(
                        (a.role(), a.is_write()),
                        (ByteEntryRole::Context, false) | (ByteEntryRole::Output, true)
                    )
            }) && family
                .addresses()
                .iter()
                .all(|a| a.base_offset() == 0 && a.offset() == 0 && !a.is_inbounds()),
            normal: source.normal_return_obligation().trust_ir_expr.clone(),
            byte: source.memory_obligation().trust_ir_expr.clone(),
            definitions: source.inner.original_encoding_definitions().to_vec(),
            geometry: source.inner.source_geometry().to_vec(),
        }
    }

    fn problems(&self, claim: VoidWordMemoryClaim) -> Result<Vec<ProofObligation>, String> {
        if !self.applicable {
            return Err("word observation requires the original offset-zero word footprint".into());
        }
        // Price every independent substitution BEFORE cloning an inventory.
        // A replaced entry-memory leaf can introduce at most sixteen stores
        // plus their literal addresses/bytes. Counting every such root anew is
        // conservative even when the resulting array DAG shares its suffix.
        let mut nodes = 0usize;
        let mut edges = 0usize;
        for term in self
            .geometry
            .iter()
            .chain(&self.definitions)
            .chain([&self.normal, &self.byte])
        {
            let scan = crate::smt_raw_print::preflight_roots(&[term])
                .map_err(|e| format!("word observation original shape: {e}"))?;
            let memories = scan.order.iter().filter(|node| matches!(node, E::UF { name, args, .. } if name == "entry_memory" && args.is_empty())).count();
            nodes = nodes
                .saturating_add(scan.order.len())
                .saturating_add(memories.saturating_mul(81));
            edges = edges
                .saturating_add(scan.edges)
                .saturating_add(memories.saturating_mul(128));
        }
        if nodes
            .saturating_add(self.geometry.len())
            .saturating_add(4)
            .saturating_mul(18)
            > crate::smt_raw_print::MAX_NODES
            || edges
                .saturating_add(self.geometry.len() * 2)
                .saturating_add(8)
                .saturating_mul(18)
                > crate::smt_raw_print::MAX_EDGES
        {
            return Err(
                "word observation aggregate reservation exceeds unchanged graph bounds".into(),
            );
        }
        for address in [claim.context_address, claim.output_address] {
            if address == 0 || address % 8 != 0 || address.checked_add(8).is_none() {
                return Err("word observation address/extent differs".into());
            }
        }
        if claim.context_address < claim.output_address + 8
            && claim.output_address < claim.context_address + 8
        {
            return Err("word observation regions overlap".into());
        }
        // Unknown bytes remain an arbitrary array. These sixteen stores encode
        // only the supplied initialized words; no outside byte is assumed zero.
        let mut memory = E::uf(
            "word_observation_unowned_bytes",
            vec![],
            crate::memory_proofs::memory_sort(),
        );
        for (address, word) in [
            (claim.context_address, claim.context_before),
            (claim.output_address, claim.output_before),
        ] {
            for (offset, byte) in word.to_le_bytes().into_iter().enumerate() {
                memory = E::store(
                    memory,
                    E::bv_const(address + offset as u64, 64),
                    E::bv_const(byte as u64, 8),
                );
            }
        }
        let instantiate = |term: &E, observe: u64| -> Result<E, String> {
            let rewritten = term.try_rewrite_dag(&mut |node| -> Result<Option<E>, String> {
                match node {
                    E::Var { name, width: 64 } if name == "abi_x0" => {
                        Ok(Some(E::bv_const(claim.context_address, 64)))
                    }
                    E::Var { name, width: 64 } if name == "abi_x1" => {
                        Ok(Some(E::bv_const(claim.output_address, 64)))
                    }
                    E::Var { name, width: 64 } if name == "observe" => {
                        Ok(Some(E::bv_const(observe, 64)))
                    }
                    E::Var { .. } => Err("word observation has a foreign original input".into()),
                    E::UF {
                        name,
                        args,
                        ret_sort,
                    } if name == "entry_memory"
                        && args.is_empty()
                        && *ret_sort == crate::memory_proofs::memory_sort() =>
                    {
                        Ok(Some(memory.clone()))
                    }
                    _ => Ok(None),
                }
            })?;
            Ok(rewritten.unwrap_or_else(|| term.clone()))
        };
        let build = |observe: u64,
                     conclusion: E,
                     label: String,
                     include_geometry: bool|
         -> Result<ProofObligation, String> {
            let mut premises = self
                .geometry
                .iter()
                .filter(|_| include_geometry)
                .chain(&self.definitions)
                .map(|p| instantiate(p, observe))
                .collect::<Result<Vec<_>, _>>()?;
            let conclusion = instantiate(&conclusion, observe)?;
            // Existing bounded raw-shape preflight covers the complete
            // proposition. Original source typing and fixed-sort literal
            // substitutions remain separate from this resource inspection.
            let mut roots = premises.iter().collect::<Vec<_>>();
            roots.push(&conclusion);
            crate::smt_raw_print::preflight_roots(&roots)
                .map_err(|e| format!("word observation shape: {e}"))?;
            Ok(ProofObligation {
                name: label,
                trust_ir_expr: E::BoolConst(true),
                aarch64_expr: conclusion,
                inputs: vec![],
                preconditions: std::mem::take(&mut premises),
                fp_inputs: vec![],
                category: None,
                machine_side_provenance: MachineSideProvenance::StaticDb,
            })
        };
        // Prove applicability without assuming it. Only after this part is
        // independently Valid may later parts use the original geometry.
        let geometry = self
            .geometry
            .iter()
            .cloned()
            .fold(E::BoolConst(true), E::and_expr);
        let mut problems = vec![
            build(
                claim.output_address,
                geometry,
                "Original Core physical word geometry".into(),
                false,
            )?,
            build(
                claim.output_address,
                self.normal.clone(),
                "Original Core physical word normal return".into(),
                true,
            )?,
        ];
        for (role, address, word) in [
            ("context", claim.context_address, claim.context_after),
            ("output", claim.output_address, claim.output_after),
        ] {
            for (offset, byte) in word.to_le_bytes().into_iter().enumerate() {
                problems.push(build(
                    address + offset as u64,
                    self.byte.clone().eq_expr(E::bv_const(byte as u64, 8)),
                    format!("Original Core physical word {role} byte {offset}"),
                    true,
                )?);
            }
        }
        // No sixteen-fold hidden allowance: inspect the aggregate original
        // inventory before it reaches replay, under the unchanged graph caps.
        let (mut nodes, mut edges, mut payload) = (0usize, 0usize, 0usize);
        for problem in &problems {
            let roots = problem
                .preconditions
                .iter()
                .chain([&problem.trust_ir_expr, &problem.aarch64_expr])
                .collect::<Vec<_>>();
            let scan = crate::smt_raw_print::preflight_roots(&roots)
                .map_err(|e| format!("word observation original part shape: {e}"))?;
            nodes = nodes.saturating_add(scan.order.len());
            edges = edges.saturating_add(scan.edges);
            payload = payload.saturating_add(scan.payload);
            if nodes > crate::smt_raw_print::MAX_NODES
                || edges > crate::smt_raw_print::MAX_EDGES
                || payload > crate::smt_raw_print::MAX_PAYLOAD_BYTES
            {
                return Err(
                    "word observation aggregate exceeds unchanged graph/payload bounds".into(),
                );
            }
        }
        Ok(problems)
    }

    pub(crate) fn replay(
        &self,
        request: &FunctionVerificationRequest,
        compilation: ProofDigest,
        scope: Arc<()>,
        claim: VoidWordMemoryClaim,
    ) -> Result<ReplayedVoidWordMemoryClaim, String> {
        if request.mode() != ProvenanceXCheckMode::Enforce
            || !request.config_matches(&VerificationConfig::for_proof_promotion())
        {
            return Err(
                "word observation requires the original enforcing proof-promotion request".into(),
            );
        }
        let problems = self.problems(claim)?;
        let context = FunctionDischargeContext::new(request);
        let results =
            context.void_word_memory(problems.iter().map(|obligation| Part { obligation }));
        let mut hash = Sha256::new();
        hash.update(b"trust-cg.original-core-word-post-memory.v1\0");
        hash.update(compilation.bytes);
        let mut diagnostics = Vec::new();
        for (problem, (verdict, why, attempted)) in problems.iter().zip(&results) {
            let raw = request.with_policy(|| {
                crate::ay_bridge::generate_smt2_query_raw(
                    problem,
                    &crate::verdict_db::live_source_bound_config(),
                )
            });
            if !attempted || !matches!(verdict, Some(VerificationResult::Valid)) {
                return Err(format!(
                    "word post-memory replay refused {}: {verdict:?} {why:?}; original_query_sha256={:x}\nORIGINAL_WORD_OBSERVATION_QUERY_BEGIN\n{raw}ORIGINAL_WORD_OBSERVATION_QUERY_END",
                    problem.name,
                    Sha256::digest(raw.as_bytes())
                ));
            }
            hash.update((raw.len() as u64).to_le_bytes());
            hash.update(raw.as_bytes());
            diagnostics.push((format!("{:x}", Sha256::digest(raw.as_bytes())), why.clone()));
        }
        if results.len() != 18 {
            return Err("word observation lost an original part".into());
        }
        Ok(ReplayedVoidWordMemoryClaim {
            claim,
            compilation,
            statement: ProofDigest::sha256(hash.finalize().into()),
            scope,
            diagnostics,
        })
    }
}

pub(crate) struct Part<'a> {
    obligation: &'a ProofObligation,
}
impl Part<'_> {
    pub(crate) fn obligation(&self) -> &ProofObligation {
        self.obligation
    }
}
