//! Retained original-i128 CIC certificates. The context bundle is untrusted
//! proof data: every process reconstructs its complete cone with Clean before
//! a certificate can be checked. No solver or Lean producer is called here.
use crate::i128_cic_reflection::render_original_i128_goal;
use crate::lowering_proof::{MachineSideProvenance, ProofObligation};
use clean_kernel::env::ENV_SCHEMA_FINGERPRINT;
use clean_kernel::level::LeanLevelProfile;
use clean_kernel::{Environment, Expr, Name, ReferenceKernel};
use clean_olean::ClosedRecheckOptions;
use clean_olean::recheck_closed::reference_base::reference_base_closed;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::io::Read;
use std::sync::{Arc, OnceLock};

const CLEAN_REVISION: &str = "789c68a6ed9779d2d348f86ac7ec14429d75b7c2";
const BUNDLE_SCHEMA: u32 = 3;
const ENVIRONMENT_DAG_FORMAT: &str = "CLENEDG2";
const MAX_PACKET_BYTES: usize = 8 * 1024 * 1024;
const MAX_CONTEXT_BYTES: u64 = 256 * 1024 * 1024;
const MAX_COMPRESSED_BYTES: usize = 32 * 1024 * 1024;
const CONTEXT: &[u8] = include_bytes!("i128_cic/closed-environment.dag.zst");
const MANIFEST: &str = include_str!("i128_cic/BUNDLE.json");

fn sha(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// An untrusted reference to one already retained universal proof. A hint,
/// label, packet digest or enum variant never grants a favorable verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
enum Candidate {
    UnsignedLimb,
    SignedLimb,
    UnsignedConst,
}
impl Candidate {
    fn root(self) -> &'static str {
        match self {
            Self::UnsignedLimb => "Trust.Cert.CheckedMulI128Raw.original_unsigned",
            Self::SignedLimb => "Trust.Cert.CheckedMulI128Raw.original_signed",
            Self::UnsignedConst => "Trust.Cert.CheckedMulI128Raw.original_constant",
        }
    }
    fn hint(input: &ProofObligation) -> Option<Self> {
        if input
            .name
            .starts_with("CheckedUmul_I128 overflow flag -> division-free limb check")
        {
            Some(Self::UnsignedLimb)
        } else if input
            .name
            .starts_with("CheckedSmul_I128 overflow flag -> division-free limb check")
        {
            Some(Self::SignedLimb)
        } else if input
            .name
            .starts_with("CheckedUmul_I128 overflow flag -> constant-operand limit compare")
        {
            Some(Self::UnsignedConst)
        } else {
            None
        }
    }
    fn proof(self) -> Expr {
        Expr::const_(Name::from_string(self.root()), Vec::new())
    }
}
const CANDIDATES: [Candidate; 3] = [
    Candidate::UnsignedLimb,
    Candidate::SignedLimb,
    Candidate::UnsignedConst,
];

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BundleManifest {
    schema: u32,
    environment_schema: String,
    environment_dag_format: String,
    source_lean_level_profile: LeanLevelProfile,
    clean_source: String,
    roots: Vec<String>,
    raw_bytes: u64,
    raw_sha256: String,
    zstd_bytes: usize,
    zstd_sha256: String,
    closed_cone_seconds: f64,
    scope: String,
}

fn decode_bundle_manifest(
    context_bytes: &[u8],
    manifest_bytes: &[u8],
) -> Result<BundleManifest, String> {
    let manifest: BundleManifest =
        serde_json::from_slice(manifest_bytes).map_err(|e| e.to_string())?;
    let expected: Vec<_> = CANDIDATES.iter().map(|c| c.root()).collect();
    if manifest.schema != BUNDLE_SCHEMA
        || manifest.environment_dag_format != ENVIRONMENT_DAG_FORMAT
        || manifest.environment_schema != ENV_SCHEMA_FINGERPRINT
        || manifest.source_lean_level_profile != LeanLevelProfile::Lean430
        || manifest.clean_source != CLEAN_REVISION
        || manifest.roots != expected
        || manifest.raw_bytes == 0
        || manifest.raw_bytes > MAX_CONTEXT_BYTES
        || context_bytes.len() > MAX_COMPRESSED_BYTES
        || manifest.zstd_bytes != context_bytes.len()
        || sha(context_bytes) != manifest.zstd_sha256
        || !manifest.closed_cone_seconds.is_finite()
        || manifest.scope.is_empty()
    {
        return Err("retained context manifest mismatch".into());
    }
    Ok(manifest)
}

/// Private, freshly checked state. It has no deserialization implementation.
struct FreshContext {
    kernel: ReferenceKernel,
    environment_sha256: String,
}
static FRESH_CONTEXT: OnceLock<Result<Arc<FreshContext>, String>> = OnceLock::new();

fn check_context_bytes(
    context_bytes: &[u8],
    manifest_bytes: &[u8],
) -> Result<Arc<FreshContext>, String> {
    // Match the published retained payload, but actually decode/replay the
    // supplied bytes. Content identity alone is never a checked environment.
    if context_bytes.len() > MAX_COMPRESSED_BYTES
        || manifest_bytes.len() > 64 * 1024
        || context_bytes != CONTEXT
        || manifest_bytes != MANIFEST.as_bytes()
    {
        return Err("retained context differs from selected published payload".into());
    }
    let manifest = decode_bundle_manifest(context_bytes, manifest_bytes)?;
    let decoder = zstd::stream::read::Decoder::new(context_bytes).map_err(|e| e.to_string())?;
    let mut bytes = Vec::new();
    decoder
        .take(manifest.raw_bytes + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() as u64 != manifest.raw_bytes || sha(&bytes) != manifest.raw_sha256 {
        return Err("retained context bytes mismatch".into());
    }
    // Snapshot serde identity is not the owned DAG byte grammar. Bind the
    // actual envelope too; never select a legacy source epoch from data.
    if !bytes.starts_with(ENVIRONMENT_DAG_FORMAT.as_bytes()) {
        return Err("retained context is not the current owned DAG format".into());
    }
    // A deserialized Environment is NOT a trusted context. Its flags, origins,
    // receipts and imported native reducers cannot ground this fresh replay.
    let untrusted = Environment::from_dag_bincode(&bytes).map_err(|e| e.to_string())?;
    if untrusted.lean_level_profile() != LeanLevelProfile::Lean430 {
        return Err("retained context carries a different Lean level profile".into());
    }
    let roots: BTreeSet<_> = CANDIDATES
        .iter()
        .map(|c| Name::from_string(c.root()))
        .collect();
    let checked = reference_base_closed(&untrusted, &roots, &ClosedRecheckOptions::default())
        .map_err(|error| format!("retained context fenced entry refused: {error}"))?;
    let env = checked.kernel().environment();
    let standard = ["propext", "Classical.choice", "Quot.sound"];
    if !checked.report.passed()
        || !checked.report.extension_bindings_pinned
        || !checked.entry_refusals.is_empty()
        || env.lean_level_profile() != LeanLevelProfile::Lean430
        || checked.report.axioms_admitted.len() != standard.len()
        || !checked.report.axioms_admitted.iter().all(|n| {
            standard.contains(&n.as_str())
                && env.is_canonical_foundational_axiom(&Name::from_string(n))
        })
        || !roots.iter().all(|n| {
            checked.admitted.contains(n)
                && env
                    .get_const(n)
                    .is_some_and(|info| info.value.is_some() && info.level_params.is_empty())
        })
    {
        let first_refusals: Vec<_> = checked
            .report
            .refusals
            .iter()
            .take(4)
            .map(|refusal| {
                format!("{refusal:?}")
                    .chars()
                    .take(2048)
                    .collect::<String>()
            })
            .collect();
        return Err(format!(
            "retained context failed fresh dependency-closed kernel replay: \
             cone={}, units={}, constants={}, families={}, refusals={}, \
             pinned={}, axioms={:?}, first_refusals={first_refusals:?}",
            checked.report.cone_constants,
            checked.report.units,
            checked.report.constants_admitted,
            checked.report.families_replayed,
            checked.report.refusals.len(),
            checked.report.extension_bindings_pinned,
            checked.report.axioms_admitted,
        ));
    }
    let kernel = checked
        .into_kernel()
        .map_err(|report| format!("retained context incomplete fenced replay: {report:?}"))?;
    Ok(Arc::new(FreshContext {
        kernel,
        environment_sha256: manifest.raw_sha256,
    }))
}
fn context() -> Result<Arc<FreshContext>, String> {
    FRESH_CONTEXT
        .get_or_init(|| {
            std::thread::Builder::new()
                .name("i128-cic-context".into())
                .stack_size(256 * 1024 * 1024)
                .spawn(|| check_context_bytes(CONTEXT, MANIFEST.as_bytes()))
                .map_err(|e| e.to_string())?
                .join()
                .map_err(|_| "retained context worker panicked".to_owned())?
        })
        .clone()
}

/// Untrusted wire data only. `goal` and `proof` are retained lossless JSON
/// bytes of CIC terms, never deserialized into checked state. The independent
/// expected renderer and fixed proof-reference codec must reproduce them
/// byte-for-byte before the actual kernel check. Full proof bodies/context
/// reside in the identified shared retained bundle, freshly replayed above.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Wire {
    schema: u32,
    clean_revision: String,
    environment_sha256: String,
    candidate: Candidate,
    original_binding: Vec<u8>,
    original_binding_sha256: String,
    goal: Vec<u8>,
    goal_sha256: String,
    proof: Vec<u8>,
    proof_sha256: String,
}

/// A checked original-goal certificate with its retained replay packet.
/// Fields/constructor are private; untrusted wire can never deserialize into
/// this type or grant authority by supplying a label or hash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedOriginalI128Certificate {
    packet: Arc<[u8]>,
    packet_sha256: String,
    environment_sha256: String,
    goal_sha256: String,
    checker_sha256: String,
}
impl CheckedOriginalI128Certificate {
    /// Exact untrusted packet for independent replay against actual inputs.
    pub fn packet(&self) -> &[u8] {
        &self.packet
    }
    /// Retain the complete checked packet and exact shared context as ordinary
    /// files. Failure is reported; files and paths still carry no proof grade.
    pub fn persist_to(
        &self,
        dir: &std::path::Path,
    ) -> std::io::Result<crate::i128_cic_artifact::ArtifactSet> {
        crate::i128_cic_artifact::persist_retained_artifacts(
            dir,
            &self.packet,
            CONTEXT,
            MANIFEST.as_bytes(),
        )
    }
    /// Content identity, not a substitute for independent replay.
    pub fn packet_sha256(&self) -> &str {
        &self.packet_sha256
    }
    /// Identifies the retained context that was freshly checked.
    pub fn environment_sha256(&self) -> &str {
        &self.environment_sha256
    }
    /// Identifies the actual original typed equality that was checked.
    pub fn goal_sha256(&self) -> &str {
        &self.goal_sha256
    }
    /// Exact in-process checker executable observed around the actual check.
    pub fn checker_sha256(&self) -> &str {
        &self.checker_sha256
    }
    /// Producer of retained context data, not a claim about a later checker.
    pub fn context_producer_clean_revision(&self) -> &str {
        CLEAN_REVISION
    }
}

fn checked_wire(
    input: &ProofObligation,
    wire: Wire,
    packet: &[u8],
    ctx: &FreshContext,
) -> Result<CheckedOriginalI128Certificate, String> {
    if !matches!(
        input.machine_side_provenance,
        MachineSideProvenance::StaticDb
    ) {
        return Err(
            "static mathematical certificate does not license reconstructed machine provenance"
                .into(),
        );
    }
    let actual =
        render_original_i128_goal(input).map_err(|e| format!("original reflection: {e:?}"))?;
    let goal = serde_json::to_vec(actual.expected_goal()).map_err(|e| e.to_string())?;
    let proof = wire.candidate.proof();
    let proof_bytes = serde_json::to_vec(&proof).map_err(|e| e.to_string())?;
    if wire.schema != 2
        || wire.clean_revision != CLEAN_REVISION
        || wire.environment_sha256 != ctx.environment_sha256
        || wire.original_binding != actual.original_binding_bytes()
        || wire.original_binding_sha256 != sha(actual.original_binding_bytes())
        || wire.goal != goal
        || wire.goal_sha256 != sha(&goal)
        || wire.proof != proof_bytes
        || wire.proof_sha256 != sha(&proof_bytes)
    {
        return Err(
            "packet differs from independently expected original input/goal/proof/context".into(),
        );
    }
    // This is the sole certificate admission. It checks the retained existing
    // proof, BOTH actual input expressions and their full unrestricted binders.
    // No solver, simplifier, Lean producer or fresh proof construction occurs.
    let checker_path = std::env::current_exe().map_err(|e| e.to_string())?;
    let checker_sha256 = sha(&std::fs::read(&checker_path).map_err(|e| e.to_string())?);
    ctx.kernel
        .check_closed_term(actual.expected_goal(), &proof)
        .map_err(|e| format!("original CIC proof refused: {e:?}"))?;
    if sha(&std::fs::read(&checker_path).map_err(|e| e.to_string())?) != checker_sha256 {
        return Err("in-process checker file identity changed during proof check".into());
    }
    crate::proof_tool_record::note(
        crate::proof_tool_record::ProofTool::CleanCic,
        &checker_path,
        &checker_sha256,
        Some(&format!(
            "in-process Clean CIC; context-producer-clean={CLEAN_REVISION}; context-sha256={}; verifier-source={}",
            ctx.environment_sha256,
            crate::source_bound_negative_memo::VERIFIER_BUILD
        )),
    );
    Ok(CheckedOriginalI128Certificate {
        packet: Arc::from(packet),
        packet_sha256: sha(packet),
        environment_sha256: ctx.environment_sha256.clone(),
        goal_sha256: sha(&goal),
        checker_sha256,
    })
}

/// Replay only: restores an existing proof reference, reconstructs the expected
/// original goal from the independently supplied actual obligation, and checks
/// it. This entrypoint never calls the producer or a solver.
pub fn replay_original_i128_certificate(
    input: &ProofObligation,
    packet: &[u8],
) -> Result<CheckedOriginalI128Certificate, String> {
    if packet.is_empty() || packet.len() > MAX_PACKET_BYTES {
        return Err("packet size refused".into());
    }
    let wire: Wire = serde_json::from_slice(packet).map_err(|e| format!("packet codec: {e}"))?;
    let ctx = context()?;
    checked_wire(input, wire, packet, &ctx)
}

/// Independently replay an ordinary retained artifact set. The existing proof
/// and context are read from the supplied artifact bytes; no producer, solver,
/// Lean process or proof regeneration is used. The actual obligation is
/// supplied independently and its complete original typed goal is rebuilt.
/// This fresh entry deliberately bypasses the resident checked-context cache.
pub fn replay_original_i128_artifacts(
    input: &ProofObligation,
    packet: &[u8],
    context_zstd: &[u8],
    manifest: &[u8],
) -> Result<CheckedOriginalI128Certificate, String> {
    if packet.is_empty() || packet.len() > MAX_PACKET_BYTES {
        return Err("packet size refused".into());
    }
    let wire: Wire = serde_json::from_slice(packet).map_err(|e| format!("packet codec: {e}"))?;
    let ctx = check_context_bytes(context_zstd, manifest)?;
    checked_wire(input, wire, packet, &ctx)
}

/// Produce only a reference to an already retained proof, then pass the exact
/// packet through the independent replay entrypoint before returning a checked
/// capability. The name chooses a candidate, never a verdict.
pub(crate) fn try_original_i128_certificate(
    input: &ProofObligation,
    timeout_ms: u64,
) -> Option<CheckedOriginalI128Certificate> {
    let began = std::time::Instant::now();
    #[cfg(test)]
    assert!(
        !tests::FORBID_PRODUCER.load(std::sync::atomic::Ordering::SeqCst),
        "proof producer called during replay-only process"
    );
    let candidate = Candidate::hint(input)?;
    #[cfg(test)]
    tests::PRODUCER_CALLS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let actual = render_original_i128_goal(input).ok()?;
    let goal = serde_json::to_vec(actual.expected_goal()).ok()?;
    let proof = serde_json::to_vec(&candidate.proof()).ok()?;
    let ctx = context().ok()?;
    let wire = Wire {
        schema: 2,
        clean_revision: CLEAN_REVISION.to_owned(),
        environment_sha256: ctx.environment_sha256.clone(),
        candidate,
        original_binding: actual.original_binding_bytes().to_vec(),
        original_binding_sha256: sha(actual.original_binding_bytes()),
        goal_sha256: sha(&goal),
        goal,
        proof_sha256: sha(&proof),
        proof,
    };
    let packet = serde_json::to_vec(&wire).ok()?;
    let checked = replay_original_i128_certificate(input, &packet).ok()?;
    // As with AY, zero names an unlimited budget. This is a conservative
    // credit/fallback threshold; it does not cancel an in-flight kernel check.
    if let Some(dir) = trust_cg_process_env::var_os("TRUST_CG_I128_CIC_ARTIFACT_OUT") {
        checked.persist_to(std::path::Path::new(&dir)).ok()?;
    }
    if timeout_ms != 0 && began.elapsed() > std::time::Duration::from_millis(timeout_ms) {
        return None;
    }
    Some(checked)
}

#[cfg(test)]
#[path = "i128_cic_certificate_tests.rs"]
mod tests;
