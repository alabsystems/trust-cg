// Copyright 2026 Andrew Yates | Apache-2.0
//! Concrete original-Core return and four-word memory propositions. Logical
//! addresses/bytes remain conditional data, never allocation or call authority.
use crate::FunctionVerificationRequest;
use crate::function_request::FunctionDischargeContext;
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, VerificationConfig};
use crate::provenance_xcheck::ProvenanceXCheckMode;
use crate::smt::SmtExpr as E;
use crate::source_bound_frame::ScalarMemorySourceQueries;
use crate::verify::VerificationResult;
use sha2::{Digest, Sha256};
use std::sync::Arc;
use trust_ir::proof::ProofDigest;
use trust_ir_build::source_word_status_entry::CheckedWordStatusEntrySource;
const PARTS: usize = 4;
/// Candidate original ABI addresses, initialized bytes, post bytes and exact
/// full-width return. Public construction confers no physical permission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FourWordStatusClaim {
    /// Ordered actual input0,input1,output0,output1 logical bases.
    pub addresses: [u64; 4],
    /// Initialized little-endian words before the claimed call.
    pub before: [u64; 4],
    /// Claimed little-endian words after the claimed call.
    pub after: [u64; 4],
    /// Claimed full U64 scalar return, not an interpretation of void.
    pub status: u64,
}
/// Every original-Core geometry, normal-return, full status and post-byte
/// proposition replayed under the captured enforcing request. This is still a
/// conditional logical receipt; physical invocation has a separate owner.
pub struct ReplayedFourWordStatusClaim {
    claim: FourWordStatusClaim,
    compilation: ProofDigest,
    statement: ProofDigest,
    scope: Arc<()>,
    diagnostics: Vec<(String, Option<String>)>,
}
impl ReplayedFourWordStatusClaim {
    pub fn claim(&self) -> FourWordStatusClaim {
        self.claim
    }
    pub fn compilation_statement(&self) -> ProofDigest {
        self.compilation
    }
    pub fn statement_digest(&self) -> ProofDigest {
        self.statement
    }
    pub fn replay_diagnostics(&self) -> &[(String, Option<String>)] {
        &self.diagnostics
    }
    pub(crate) fn belongs_to(&self, scope: &Arc<()>) -> bool {
        Arc::ptr_eq(&self.scope, scope)
    }
}
/// Separately attempted replay of the negation of a failed original
/// conclusion, under all of that original part's unchanged premises. This
/// diagnostic grants no successful observation, call, image or native receipt.
#[derive(Debug)]
pub struct FourWordStatusDenialReplay {
    elapsed: std::time::Duration,
    verdict: Option<VerificationResult>,
    attempted: bool,
    why: String,
    query: Option<String>,
}
impl FourWordStatusDenialReplay {
    /// End-to-end candidate/checker replay cost, separate from original SAT.
    pub fn replay_time(&self) -> std::time::Duration {
        self.elapsed
    }
    /// Actual checker-backed outcome of the separately named denial.
    pub fn verdict(&self) -> Option<&VerificationResult> {
        self.verdict.as_ref()
    }
    /// Whether the denial was attempted within the same aggregate bounds.
    pub fn attempted(&self) -> bool {
        self.attempted
    }
    /// Exact denial query, distinct from the original failed proposition.
    pub fn query(&self) -> Option<&str> {
        self.query.as_deref()
    }
    /// Actual producer/checker attribution or refusal, never a model claim.
    pub fn why(&self) -> &str {
        &self.why
    }
}
/// A refusal retains its actual original-part verdict. Policy/geometry/shape
/// failures have no attempted part; an Unknown is never a semantic counterexample.
#[derive(Debug)]
pub struct FourWordStatusReplayRefusal {
    part: Option<String>,
    verdict: Option<VerificationResult>,
    attempted: bool,
    why: String,
    query: Option<String>,
    scalar_inputs: Option<usize>,
    denial: Option<FourWordStatusDenialReplay>,
}
impl FourWordStatusReplayRefusal {
    fn boundary(why: String) -> Self {
        Self {
            part: None,
            verdict: None,
            attempted: false,
            why,
            query: None,
            scalar_inputs: None,
            denial: None,
        }
    }
    /// Number of declared scalar inputs projected by the existing AY model
    /// parser; zero means `[]` is not a populated counterexample model.
    pub fn scalar_input_count(&self) -> Option<usize> {
        self.scalar_inputs
    }
    /// Separate original-premise denial replay; it never changes this refusal.
    pub fn denial_replay(&self) -> Option<&FourWordStatusDenialReplay> {
        self.denial.as_ref()
    }
    /// Exact named original proposition, absent before replay is admitted.
    pub fn part(&self) -> Option<&str> {
        self.part.as_deref()
    }
    /// Actual Valid/Invalid/Unknown result, never inferred from diagnostic text.
    pub fn verdict(&self) -> Option<&VerificationResult> {
        self.verdict.as_ref()
    }
    /// Whether the original enforcing replay actually attempted this part.
    pub fn attempted(&self) -> bool {
        self.attempted
    }
    /// Exact original query supplied to the existing replay owner, when attempted.
    pub fn original_query(&self) -> Option<&str> {
        self.query.as_deref()
    }
}
impl std::fmt::Display for FourWordStatusReplayRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "four-word original replay refused {:?}: {:?}; attempted={}; {}",
            self.part, self.verdict, self.attempted, self.why
        )?;
        if let Some(query) = &self.query {
            write!(
                f,
                "; original_query_sha256={:x}\n{query}",
                Sha256::digest(query.as_bytes())
            )?;
        }
        Ok(())
    }
}
impl std::error::Error for FourWordStatusReplayRefusal {}
pub(crate) struct Template {
    applicable: bool,
    normal: E,
    status: E,
    byte: E,
    definitions: Vec<E>,
    geometry: Vec<E>,
}
impl Template {
    pub(crate) fn applicable(&self) -> bool {
        self.applicable
    }
    pub(crate) fn capture(
        source: &ScalarMemorySourceQueries<'_>,
        family: &CheckedWordStatusEntrySource<'_>,
    ) -> Self {
        Self {
            applicable: family
                .accesses()
                .iter()
                .all(|a| a.offset() == 0 && a.role() < 4 && a.is_write() == (a.role() >= 2))
                && family
                    .addresses()
                    .iter()
                    .all(|a| a.base_offset() == 0 && a.offset() == 0 && !a.is_inbounds()),
            normal: source.original_normal_return().clone(),
            status: source.status_obligation().trust_ir_expr.clone(),
            byte: source.memory_obligation().trust_ir_expr.clone(),
            definitions: source.original_encoding_definitions().to_vec(),
            geometry: source.source_geometry().to_vec(),
        }
    }
    fn problems(&self, claim: FourWordStatusClaim) -> Result<Vec<ProofObligation>, String> {
        if !self.applicable {
            return Err("four-word status observation requires the original offset-zero flat word footprint".into());
        }
        // Retain every original definition in each proposition. Geometry,
        // normal return and status never depend on the final-byte observer;
        // verify that invariant before sharing their premises across the 32
        // concrete byte conclusions in one conjunction. No definition is
        // omitted, projected away or admitted as an extra assumption.
        let (mut nodes, mut edges) = (0usize, 0usize);
        for (term, copies, observer_allowed) in self
            .geometry
            .iter()
            .map(|e| (e, PARTS, false))
            .chain(self.definitions.iter().map(|e| (e, PARTS, false)))
            .chain([
                (&self.normal, 1, false),
                (&self.status, 1, false),
                (&self.byte, 32, true),
            ])
        {
            let scan = crate::smt_raw_print::preflight_roots(&[term])
                .map_err(|e| format!("four-word original shape: {e}"))?;
            if !observer_allowed
                && scan
                    .order
                    .iter()
                    .any(|node| matches!(node,E::Var{name,..} if name=="observe"))
            {
                return Err("original physical premises depend on the byte observer".into());
            }
            // 32 concrete stores add at most 161 nodes/256 edges for each
            // replaced memory leaf. Price all substitutions before cloning.
            let memories=scan.order.iter().filter(|node|matches!(node,E::UF{name,args,..} if name=="entry_memory" && args.is_empty())).count();
            nodes = nodes.saturating_add(
                scan.order
                    .len()
                    .saturating_add(memories.saturating_mul(161))
                    .saturating_mul(copies),
            );
            edges = edges.saturating_add(
                scan.edges
                    .saturating_add(memories.saturating_mul(256))
                    .saturating_mul(copies),
            );
        }
        if nodes
            .saturating_add(self.geometry.len())
            .saturating_add(128)
            > crate::smt_raw_print::MAX_NODES
            || edges
                .saturating_add(self.geometry.len().saturating_mul(2))
                .saturating_add(192)
                > crate::smt_raw_print::MAX_EDGES
        {
            return Err("four-word aggregate reservation exceeds unchanged graph bounds".into());
        }
        for (i, &a) in claim.addresses.iter().enumerate() {
            if a == 0 || a % 8 != 0 || a.checked_add(8).is_none() {
                return Err("four-word address/extent differs".into());
            }
            for &b in &claim.addresses[..i] {
                if a < b + 8 && b < a + 8 {
                    return Err("four-word regions overlap".into());
                }
            }
        }
        let mut memory = E::uf(
            "four_word_unowned_bytes",
            vec![],
            crate::memory_proofs::memory_sort(),
        );
        for (address, word) in claim.addresses.into_iter().zip(claim.before) {
            for (offset, byte) in word.to_le_bytes().into_iter().enumerate() {
                memory = E::store(
                    memory,
                    E::bv_const(address + offset as u64, 64),
                    E::bv_const(byte as u64, 8),
                );
            }
        }
        let instantiate = |term: &E, observe: u64| -> Result<E, String> {
            let result = term.try_rewrite_dag(&mut |node| -> Result<Option<E>, String> {
                match node {
                    E::Var { name, width: 64 } if name == "observe" => {
                        Ok(Some(E::bv_const(observe, 64)))
                    }
                    E::Var { name, width: 64 }
                        if ["abi_x0", "abi_x1", "abi_x2", "abi_x3"].contains(&name.as_str()) =>
                    {
                        let i = ["abi_x0", "abi_x1", "abi_x2", "abi_x3"]
                            .iter()
                            .position(|n| *n == name)
                            .unwrap();
                        Ok(Some(E::bv_const(claim.addresses[i], 64)))
                    }
                    E::Var { .. } => {
                        Err("four-word observation has a foreign original input".into())
                    }
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
            Ok(result.unwrap_or_else(|| term.clone()))
        };
        let build = |observe: u64,
                     conclusion: E,
                     label: String,
                     geometry: bool|
         -> Result<ProofObligation, String> {
            let premises = self
                .geometry
                .iter()
                .filter(|_| geometry)
                .chain(&self.definitions)
                .map(|e| instantiate(e, observe))
                .collect::<Result<Vec<_>, _>>()?;
            let conclusion = instantiate(&conclusion, observe)?;
            let roots = premises.iter().chain([&conclusion]).collect::<Vec<_>>();
            crate::smt_raw_print::preflight_roots(&roots)
                .map_err(|e| format!("four-word proposition shape: {e}"))?;
            Ok(ProofObligation {
                name: label,
                trust_ir_expr: E::BoolConst(true),
                aarch64_expr: conclusion,
                inputs: vec![],
                preconditions: premises,
                fp_inputs: vec![],
                category: None,
                machine_side_provenance: MachineSideProvenance::StaticDb,
            })
        };
        let geometry = self
            .geometry
            .iter()
            .cloned()
            .fold(E::BoolConst(true), E::and_expr);
        let mut problems = vec![
            build(
                claim.addresses[0],
                geometry,
                "Original Core four-word physical geometry".into(),
                false,
            )?,
            build(
                claim.addresses[0],
                self.normal.clone(),
                "Original Core four-word normal return".into(),
                true,
            )?,
            build(
                claim.addresses[0],
                self.status.clone().eq_expr(E::bv_const(claim.status, 64)),
                "Original Core actual U64 return".into(),
                true,
            )?,
        ];
        let mut bytes = E::BoolConst(true);
        for (address, word) in claim.addresses.into_iter().zip(claim.after) {
            for (offset, byte) in word.to_le_bytes().into_iter().enumerate() {
                bytes = bytes.and_expr(
                    instantiate(&self.byte, address + offset as u64)?
                        .eq_expr(E::bv_const(byte as u64, 8)),
                );
            }
        }
        problems.push(build(
            claim.addresses[0],
            bytes,
            "Original Core all 32 physical post bytes".into(),
            true,
        )?);
        let (mut nodes, mut edges, mut payload) = (0usize, 0usize, 0usize);
        for problem in &problems {
            let roots = problem
                .preconditions
                .iter()
                .chain([&problem.trust_ir_expr, &problem.aarch64_expr])
                .collect::<Vec<_>>();
            let scan = crate::smt_raw_print::preflight_roots(&roots)
                .map_err(|e| format!("four-word original part shape: {e}"))?;
            nodes = nodes.saturating_add(scan.order.len());
            edges = edges.saturating_add(scan.edges);
            payload = payload.saturating_add(scan.payload);
            if nodes > crate::smt_raw_print::MAX_NODES
                || edges > crate::smt_raw_print::MAX_EDGES
                || payload > crate::smt_raw_print::MAX_PAYLOAD_BYTES
            {
                return Err("four-word aggregate exceeds unchanged graph/payload bounds".into());
            }
        }
        Ok(problems)
    }
    fn replay_denial(
        &self,
        request: &FunctionVerificationRequest,
        context: &FunctionDischargeContext<'_>,
        originals: &[ProofObligation],
        original: &ProofObligation,
    ) -> FourWordStatusDenialReplay {
        let mut denial = original.clone();
        denial.name = format!("Denial of {}", original.name);
        denial.aarch64_expr = denial.aarch64_expr.not_expr();
        // The extra diagnostic shares the ORIGINAL batch's unchanged graph
        // allowance. It cannot reset a per-part budget or remove definitions.
        let mut nodes = 0usize;
        let mut edges = 0usize;
        let mut payload = 0usize;
        for problem in originals.iter().chain([&denial]) {
            let roots = problem
                .preconditions
                .iter()
                .chain([&problem.trust_ir_expr, &problem.aarch64_expr])
                .collect::<Vec<_>>();
            let scan = match crate::smt_raw_print::preflight_roots(&roots) {
                Ok(scan) => scan,
                Err(error) => {
                    return FourWordStatusDenialReplay {
                        elapsed: std::time::Duration::ZERO,
                        verdict: None,
                        attempted: false,
                        why: format!("denial original shape: {error}"),
                        query: None,
                    };
                }
            };
            nodes = nodes.saturating_add(scan.order.len());
            edges = edges.saturating_add(scan.edges);
            payload = payload.saturating_add(scan.payload);
            if nodes > crate::smt_raw_print::MAX_NODES
                || edges > crate::smt_raw_print::MAX_EDGES
                || payload > crate::smt_raw_print::MAX_PAYLOAD_BYTES
            {
                return FourWordStatusDenialReplay {
                    elapsed: std::time::Duration::ZERO,
                    verdict: None,
                    attempted: false,
                    why: "denial plus complete original batch exceeds unchanged aggregate bounds"
                        .into(),
                    query: None,
                };
            }
        }
        let query = request.with_policy(|| {
            crate::ay_bridge::generate_smt2_query_raw(
                &denial,
                &crate::verdict_db::live_source_bound_config(),
            )
        });
        let started = std::time::Instant::now();
        let (verdict, why, attempted) = context
            .four_word_status(std::iter::once(Part {
                obligation: &denial,
            }))
            .pop()
            .expect("one separate denial diagnostic");
        FourWordStatusDenialReplay {
            elapsed: started.elapsed(),
            verdict,
            attempted,
            why: why.unwrap_or_else(|| "no denial replay explanation".into()),
            query: Some(query),
        }
    }
    pub(crate) fn replay(
        &self,
        request: &FunctionVerificationRequest,
        compilation: ProofDigest,
        scope: Arc<()>,
        claim: FourWordStatusClaim,
    ) -> Result<ReplayedFourWordStatusClaim, FourWordStatusReplayRefusal> {
        if request.mode() != ProvenanceXCheckMode::Enforce
            || !request.config_matches(&VerificationConfig::for_proof_promotion())
        {
            return Err(FourWordStatusReplayRefusal::boundary(
                "four-word status observation requires original enforcing promotion request".into(),
            ));
        }
        let problems = self
            .problems(claim)
            .map_err(FourWordStatusReplayRefusal::boundary)?;
        let context = FunctionDischargeContext::new(request);
        let results =
            context.four_word_status(problems.iter().map(|obligation| Part { obligation }));
        let mut hash = Sha256::new();
        hash.update(b"trust-cg.original-core-four-word-status.v1\0");
        hash.update(compilation.bytes);
        let mut diagnostics = vec![];
        let result_count = results.len();
        for (problem, (verdict, why, attempted)) in problems.iter().zip(results) {
            let raw = request.with_policy(|| {
                crate::ay_bridge::generate_smt2_query_raw(
                    problem,
                    &crate::verdict_db::live_source_bound_config(),
                )
            });
            if !attempted || !matches!(&verdict, Some(VerificationResult::Valid)) {
                let denial = matches!(&verdict, Some(VerificationResult::Invalid { .. }))
                    .then(|| self.replay_denial(request, &context, &problems, problem));
                return Err(FourWordStatusReplayRefusal {
                    part: Some(problem.name.clone()),
                    verdict,
                    attempted,
                    why: why.unwrap_or_else(|| "no original replay explanation".into()),
                    query: Some(raw),
                    scalar_inputs: Some(problem.inputs.len()),
                    denial,
                });
            }
            hash.update((raw.len() as u64).to_le_bytes());
            hash.update(raw.as_bytes());
            diagnostics.push((format!("{:x}", Sha256::digest(raw.as_bytes())), why));
        }
        if result_count != PARTS {
            return Err(FourWordStatusReplayRefusal::boundary(
                "four-word observation lost an original part".into(),
            ));
        }
        Ok(ReplayedFourWordStatusClaim {
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
