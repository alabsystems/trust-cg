//! Request-local execution authority for function verification.
//!
//! These receipts bind a diagnostic report to its actual verification request;
//! they do not add source correspondence, whole-function proofs, or protection
//! against arbitrary executable-filesystem A/B/A replacement.

use crate::function_verifier::{FunctionVerificationReport, InstructionVerificationResult};
use crate::lowering_proof::{ProofObligation, VerificationConfig};
use crate::proof_database::ProofCategory;
use crate::provenance_xcheck::ProvenanceXCheckMode;
use crate::verify::VerificationResult;
use sha2::{Digest, Sha256};
use std::ffi::OsString;
use std::fmt::Write;
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicBool, Ordering},
};
use trust_cg_process_env::SanitizedChildEnv;

// Acceptance/transport controls consumed by live proof replay and the proof
// caches. Values and explicit absence are frozen, except the effective
// cert-store location is represented by its resolved absolute root (or
// store-only disabled state), and an explicit relative proof-cache root by its
// path in the captured working directory. XDG_CACHE_HOME and HOME are frozen
// as given (see `capture_policy`). Diagnostic timing flags are
// artifact-neutral.
const POLICY_KEYS: &[&str] = &[
    "TCG_NO_VERDICT_DB",
    "TCG_NO_PROOF_CACHE",
    "TCG_NO_SOLVER_SERVER",
    "TCG_CANARY_NO_CACHE",
    "TCG_NO_CERT_STORE",
    "TCG_PROOF_CERT_STORE",
    "TCG_REFINE_SOLVER",
    "TCG_RECON_SOLVER_MS",
    "TCG_CLEAN_CHECK_TIMEOUT_MS",
    "TCG_SOURCE_BOUND_NO_NEGATIVE_MEMO",
    "TCG_BLOCKING_IDENTITY",
    "TCG_NO_SOLVER_ID_CACHE",
    "TCG_PROOF_CACHE_DIR",
    "TRUST_CG_AY_TIMEOUT_MS",
    "TRUST_CG_RUN_FORMAL_PROOF_TESTS",
    "XDG_CACHE_HOME",
    "HOME",
];

/// Owned immutable policy and executable authority for one verification request.
#[derive(Clone, Debug)]
pub struct FunctionVerificationRequest {
    /// Invocation custody, distinct from reusable content identity. Clones of
    /// this request share it; a separately captured equivalent policy does not.
    capture_scope: Arc<()>,
    config: VerificationConfig,
    mode: ProvenanceXCheckMode,
    policy: Arc<Vec<(&'static str, Option<OsString>)>>,
    ay: crate::ay_bridge::FunctionAyAuthority,
    portable: crate::canary_cert::PortableVerificationAuthority,
    /// Replay authority for the committed bound-memory form certificates
    /// (`bound_memory_authority`), captured with the canary authority.
    bound_memory: crate::canary_cert::PortableVerificationAuthority,
    /// Replay authority for the committed atomic-memory form certificates
    /// (`bound_memory_authority`'s atomic rows), captured with the others.
    atomic_memory: crate::canary_cert::PortableVerificationAuthority,
    /// Replay authority for the committed NEON structure-memory form
    /// certificates (`LD1`/`ST1` post-index rows), captured with the others.
    neon_memory: crate::canary_cert::PortableVerificationAuthority,
    recording: bool,
    no_cache: bool,
    identity: Option<[u8; 32]>,
}

impl FunctionVerificationRequest {
    /// Capture once, before dispatching verification to another worker.
    /// Unavailable identity retains fresh verification, but denies reuse.
    pub fn capture(config: VerificationConfig, mode: ProvenanceXCheckMode) -> Self {
        let child_env = SanitizedChildEnv::capture_verifier();
        let policy = Arc::new(capture_policy(&child_env));
        let recording = crate::verdict_db::recording_active();
        let no_cache = trust_cg_process_env::var_os("TCG_NO_PROOF_CACHE").is_some();
        let portable = crate::canary_cert::PortableVerificationAuthority::capture(
            child_env.clone(),
            crate::canary_cert::cert_skip_enabled() && !recording,
        );
        let bound_memory = crate::canary_cert::bound_memory::capture_bound_memory_authority(
            child_env.clone(),
            crate::canary_cert::cert_skip_enabled() && !recording,
        );
        let atomic_memory = crate::canary_cert::bound_memory::ATOMIC_MEMORY_SET.capture_authority(
            child_env.clone(),
            crate::canary_cert::cert_skip_enabled() && !recording,
        );
        let neon_memory = crate::canary_cert::bound_memory::NEON_MEMORY_SET.capture_authority(
            child_env.clone(),
            crate::canary_cert::cert_skip_enabled() && !recording,
        );
        let ay = with_policy(&policy, || {
            crate::ay_bridge::FunctionAyAuthority::capture(
                child_env.clone(),
                crate::ay_bridge::AYConfig::default().timeout_ms,
            )
        });
        let mut request = Self {
            capture_scope: Arc::new(()),
            config,
            mode,
            policy,
            ay,
            portable,
            bound_memory,
            atomic_memory,
            neon_memory,
            recording,
            no_cache,
            identity: None,
        };
        if !recording && !no_cache && child_env.working_dir().is_some() {
            request.identity = request.ay.reuse_identity().map(|ay_id| {
                let mut hash =
                    request_identity_hash(crate::lowering_proof::CANONICAL_PROOF_FORMULA_PROTOCOL);
                hash.update(ay_id);
                hash.update(child_env.digest());
                hash.update(format!(
                    "{:?}:{:?}:{}",
                    request.config,
                    request.mode,
                    crate::function_verifier::precise_citations_enabled()
                ));
                for authority in [
                    &request.portable,
                    &request.bound_memory,
                    &request.atomic_memory,
                    &request.neon_memory,
                ] {
                    match authority.reusable_identity() {
                        Some(id) => {
                            hash.update([1]);
                            hash.update(id);
                        }
                        None => hash.update([0]),
                    }
                }
                for (key, value) in request.policy.iter() {
                    hash_bytes(&mut hash, key.as_bytes());
                    match value {
                        Some(value) => {
                            hash.update([1]);
                            hash_bytes(&mut hash, value.as_encoded_bytes());
                        }
                        None => hash.update([0]),
                    }
                }
                hash.finalize().into()
            });
        }
        request
    }

    pub(crate) fn same_capture(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.capture_scope, &other.capture_scope)
    }

    pub fn reuse_identity(&self) -> Option<[u8; 32]> {
        self.identity
    }

    /// Whether a committed bound-memory certificate for these exact query
    /// bytes replays under THIS request's captured authority.
    pub(crate) fn bound_memory_cert_verified(&self, smt2: &str) -> bool {
        crate::canary_cert::bound_memory::bound_memory_cert_verified_with(&self.bound_memory, smt2)
    }

    /// Whether a committed atomic-memory certificate for these exact query
    /// bytes replays under THIS request's captured authority.
    pub(crate) fn atomic_memory_cert_verified(&self, smt2: &str) -> bool {
        crate::canary_cert::bound_memory::ATOMIC_MEMORY_SET
            .cert_verified_with(&self.atomic_memory, smt2)
    }

    /// Whether a committed NEON structure-memory certificate for these exact
    /// query bytes replays under THIS request's captured authority.
    pub(crate) fn neon_memory_cert_verified(&self, smt2: &str) -> bool {
        crate::canary_cert::bound_memory::NEON_MEMORY_SET
            .cert_verified_with(&self.neon_memory, smt2)
    }

    pub(crate) fn mode(&self) -> ProvenanceXCheckMode {
        self.mode
    }
    pub(crate) fn config_matches(&self, config: &VerificationConfig) -> bool {
        self.config.sample_count == config.sample_count
            && self.config.exhaustive_threshold == config.exhaustive_threshold
            && self.config.proof_replay_policy == config.proof_replay_policy
    }
    pub(crate) fn with_policy<T>(&self, operation: impl FnOnce() -> T) -> T {
        with_policy(&self.policy, operation)
    }
    /// The admitted AY every solver verdict of this request is bound to
    /// (`None` when the identity rule admitted none; see [`Self::ay_refusal`]).
    pub fn ay_solver(&self) -> Option<&crate::ay_identity::PinnedAy> {
        self.ay.solver()
    }

    /// Why the identity rule bound no AY to this request.
    pub fn ay_refusal(&self) -> Option<&crate::ay_identity::AyIdentityRefusal> {
        self.ay.refusal()
    }

    /// The note a refusal over this request's evidence carries
    /// ([`crate::ay_bridge::request_refusal_note_for`] of
    /// [`Self::ay_refusal`]): rendered from the one resolution this request
    /// captured, never from a later one (X-HOST-P13 fourth closure audit:
    /// with the cache's symlink re-pointed between the request and its
    /// refusal, a re-resolved note was missing, or claimed no AY although AY
    /// ran).
    pub fn ay_refusal_note(&self) -> Option<String> {
        self.ay_refusal()
            .and_then(crate::ay_bridge::request_refusal_note_for)
    }

    pub(crate) fn ay(&self) -> &crate::ay_bridge::FunctionAyAuthority {
        &self.ay
    }
    pub(crate) fn may_reuse(&self) -> bool {
        !self.no_cache && !self.recording_active()
    }
    pub(crate) fn recording_active(&self) -> bool {
        self.recording || crate::verdict_db::recording_active()
    }

    /// A request that may reuse, bound to `identity` (tests of the reuse
    /// predicates that need a reusable authority on any host).
    #[cfg(test)]
    pub(crate) fn with_reuse_identity(mut self, identity: [u8; 32]) -> Self {
        self.recording = false;
        self.no_cache = false;
        self.identity = Some(identity);
        self
    }

    /// A request captured while the tier-0 recorder was armed, without arming
    /// the process-global recorder under concurrently running tests.
    #[cfg(test)]
    pub(crate) fn captured_while_recording(mut self) -> Self {
        self.recording = true;
        self.identity = None;
        self
    }
}

/// The request's frozen policy. `XDG_CACHE_HOME` and `HOME` are frozen exactly
/// as given, never anchored to the captured working directory: every cache
/// root below them (AY's private copy, the solver-identity memo, the default
/// certificate store) is resolved by `private_fs::user_cache_base`, which
/// ignores an empty or relative `XDG_CACHE_HOME` and a relative `HOME`. A
/// request therefore resolves the same AY copy, and the same refusal, as
/// process-level admission (`--print-ay-identity`, the floor's preflight,
/// `ay_bridge::solver_refusal_note`) does in the same environment and
/// file-system state. (The file system can change in between when a cache
/// path runs through a symlink another user can re-point, so a refusal over
/// a request's evidence carries the request's own resolution,
/// [`FunctionVerificationRequest::ay_refusal_note`].) Anchoring
/// them made an empty or relative `XDG_CACHE_HOME` (or an empty `HOME`) name
/// the working directory inside every request, so AY was copied below the
/// checkout, or refused there unseen (X-HOST-P13 second audit). The explicit
/// `TCG_PROOF_CERT_STORE` and `TCG_PROOF_CACHE_DIR` keep their meaning: a
/// relative or empty value names a path in the captured working directory.
fn capture_policy(child_env: &SanitizedChildEnv) -> Vec<(&'static str, Option<OsString>)> {
    let cert_store = crate::obligation_cert_store::captured_store_dir(child_env);
    POLICY_KEYS
        .iter()
        .map(|&key| {
            if key == "TCG_PROOF_CERT_STORE"
                && let Some(path) = &cert_store
            {
                return (key, Some(path.as_os_str().to_owned()));
            }
            if key == "TCG_NO_CERT_STORE" && cert_store.is_none() {
                // No usable root in this snapshot: keep only this store inert.
                // Fresh solving and its proof replay are unaffected.
                return (key, Some(OsString::from("1")));
            }
            let value = trust_cg_process_env::var_os(key).map(|value| {
                if matches!(key, "TCG_PROOF_CERT_STORE" | "TCG_PROOF_CACHE_DIR") {
                    // Parent-side certificate/identity I/O under an explicit
                    // root must use the same CWD as the captured subprocess. A
                    // PRESENT empty explicit root means the CWD; logical
                    // absence remains distinct from that path.
                    let path = std::path::Path::new(&value);
                    child_env
                        .anchor_path(path)
                        .map_or(value, |path| path.into_os_string())
                } else {
                    value
                }
            });
            (key, value)
        })
        .collect()
}

fn with_policy<T>(policy: &[(&'static str, Option<OsString>)], operation: impl FnOnce() -> T) -> T {
    trust_cg_process_env::with_env_edits(|editor| {
        for (key, value) in policy {
            match value {
                Some(value) => editor.set(key, value),
                None => editor.remove(key),
            }
        }
        operation()
    })
}

/// Which source-bound owner retained an exported obligation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SourceBoundObligationKind {
    /// An AArch64 bound ALU theorem (`ProofCategory::Arithmetic` rows).
    A64Alu,
    /// A LIR Iconst bound to one AArch64 move-wide instruction.
    A64Constant,
    /// An AArch64 body theorem: raw source/result dataflow over the allocated
    /// register file inside a bound frame ([`crate::source_bound_body`]),
    /// exported once per live copy or comparison row it credits, or the
    /// frameless whole-body theorem ([`crate::source_bound_a64_body`]),
    /// exported once per row it credits under that row's own role category
    /// ([`crate::source_bound_a64_body::a64_body_row_category`]). Each
    /// payload carries the category its sealed owner selected. A framed
    /// next-PC theorem also uses this kind, with `Branch` rows only.
    A64Body,
    /// The x86-64 whole-body theorem (`ProofCategory::X8664Lowering` rows).
    /// One theorem is exported once per value row it credits. Slice 16: a
    /// theorem stated in parts is exported with its complete, ordered part
    /// inventory ([`SourceBoundArithmeticObligation::x86_body_parts`]), which
    /// the export checks against the statement before any file is written.
    X86Body,
    /// One part of the x86-64 System V ABI envelope over final function
    /// bytes (`x86_source_bound_envelope`). A function-level theorem replayed
    /// as parts, one export per part: every export's `instruction_index` is
    /// the byte offset of the envelope's terminating RET or UD2, and its input
    /// digest binds the LIR, the function name, the exact bytes, the symbolic
    /// fixup manifest and the calling convention. It is JIT-only: the AOT
    /// proof emitter refuses it.
    X86Envelope,
}

/// One retained export: the credited row, its owner and category, the
/// theorem (shared by every row it credits), (slice 16) the parts of a
/// theorem stated in parts, (slice 19, OD-197) the obligations its credit
/// replayed claim by claim, and (slice 23, OD-205) what it carries of the
/// pairing.
type RetainedObligation = (
    usize,
    SourceBoundObligationKind,
    ProofCategory,
    Arc<ProofObligation>,
    Option<Arc<crate::x86_source_bound_body::X86BodyParts>>,
    Option<Arc<crate::x86_source_bound_body::X86BodyClaims>>,
    crate::x86_source_bound_body::X86ExportPairing,
);

type RetainedObligations = Mutex<Vec<RetainedObligation>>;

/// Slice 19 (OD-197) and slice 23 (OD-205, OD-206): how the last x86-64 body
/// theorem replayed under a context was credited: its statement's address,
/// which of the owner's theorems credited it (the paired one, or, after the
/// paired one was refuted, the one without the pairing), and the record of
/// the obligations credited claim by claim or by a generalization.
struct X86Credit {
    statement: usize,
    theorem: crate::x86_source_bound_body::X86Theorem,
    claims: Option<Arc<crate::x86_source_bound_body::X86BodyClaims>>,
}

/// One report's evidence-accounting scope, shared by nested discharge workers.
pub(crate) struct FunctionDischargeContext<'a> {
    pub(crate) request: &'a FunctionVerificationRequest,
    pub(crate) source_modules: Option<&'a crate::FunctionSourceModules<'a>>,
    bound: AtomicBool,
    exported: Option<RetainedObligations>,
    /// Slice 19 (OD-197): the last x86-64 body theorem replayed under this
    /// context (its statement's address) and the obligations its replay
    /// credited claim by claim; [`Self::retain_x86_body`] exports them.
    x86_claims: Mutex<Option<X86Credit>>,
}
impl<'a> FunctionDischargeContext<'a> {
    pub(crate) fn new(request: &'a FunctionVerificationRequest) -> Self {
        Self {
            request,
            source_modules: None,
            bound: AtomicBool::new(true),
            exported: None,
            x86_claims: Mutex::new(None),
        }
    }

    pub(crate) fn for_export(request: &'a FunctionVerificationRequest) -> Self {
        Self {
            exported: Some(Mutex::new(Vec::new())),
            ..Self::new(request)
        }
    }

    pub(crate) fn with_source_modules(
        mut self,
        source: &'a crate::FunctionSourceModules<'a>,
    ) -> Self {
        self.source_modules = Some(source);
        self
    }

    pub(crate) fn retain_alu(
        &self,
        instruction: usize,
        alu: &crate::source_bound_alu::SourceBoundAlu<'_, '_>,
    ) {
        if let Some(exports) = &self.exported {
            exports.lock().unwrap().push((
                instruction,
                SourceBoundObligationKind::A64Alu,
                ProofCategory::Arithmetic,
                Arc::new(alu.obligation().clone()),
                None,
                None,
                Default::default(),
            ));
        }
    }

    pub(crate) fn retain_constant(
        &self,
        instruction: usize,
        constant: &crate::source_bound_constant::SourceBoundConstant<'_, '_>,
    ) {
        if let Some(exports) = &self.exported {
            exports.lock().unwrap().push((
                instruction,
                SourceBoundObligationKind::A64Constant,
                ProofCategory::Arithmetic,
                Arc::new(constant.obligation().clone()),
                None,
                None,
                Default::default(),
            ));
        }
    }

    /// Retain only after TV-2 leaves this live dependency's replay verdict Formal.
    /// The sealed owner, never public report metadata, selects the category.
    pub(crate) fn retain_a64_body(
        &self,
        instruction: usize,
        body: &crate::source_bound_body::SourceBoundBody<'_, '_>,
    ) {
        if let Some(exports) = &self.exported {
            exports.lock().unwrap().push((
                instruction,
                SourceBoundObligationKind::A64Body,
                body.category(),
                Arc::new(body.obligation().clone()),
                None,
                None,
                Default::default(),
            ));
        }
    }

    pub(crate) fn retain_a64_control(
        &self,
        instruction: usize,
        control: &crate::source_bound_a64_control::SourceBoundA64Control<'_, '_>,
    ) {
        if let Some(exports) = &self.exported {
            exports.lock().unwrap().push((
                instruction,
                SourceBoundObligationKind::A64Body,
                crate::proof_database::ProofCategory::Branch,
                Arc::new(control.obligation().clone()),
                None,
                None,
                Default::default(),
            ));
        }
    }

    /// Retain the replayed frameless AArch64 whole-body theorem for one row it
    /// credited, under the category the owner gives that row's opcode. The
    /// caller retains only rows whose FINAL result (after TV-2) is still the
    /// owner's Formal verdict.
    pub(crate) fn retain_a64_whole_body(
        &self,
        instruction: usize,
        opcode: trust_cg_ir::AArch64Opcode,
        body: &crate::source_bound_a64_body::SourceBoundA64Body<'_>,
    ) {
        if let Some(exports) = &self.exported {
            exports.lock().unwrap().push((
                instruction,
                SourceBoundObligationKind::A64Body,
                crate::source_bound_a64_body::a64_body_row_category(opcode),
                Arc::new(body.obligation().clone()),
                None,
                None,
                Default::default(),
            ));
        }
    }

    /// Retain the replayed x86-64 whole-body theorem for one value row it
    /// credited (slice 16: with its part inventory, when stated in parts;
    /// both shared by every row). The caller retains only rows whose FINAL
    /// result (after TV-2 and carrier hygiene) is still the owner's Formal
    /// verdict.
    pub(crate) fn retain_x86_body(
        &self,
        instruction: usize,
        body: &crate::x86_source_bound_body::SourceBoundX86Body<'_>,
    ) {
        if let Some(exports) = &self.exported {
            // Slice 23 (OD-205): the theorem that credited the body (the
            // paired one, or the one without the pairing), with its parts,
            // its record, and (a paired one) its pairing record, from which
            // every consumer re-derives the pairing.
            let (theorem, claims) = self.x86_credit_of(body);
            let Some(statement) = body.statement_of(theorem) else {
                return;
            };
            exports.lock().unwrap().push((
                instruction,
                SourceBoundObligationKind::X86Body,
                ProofCategory::X8664Lowering,
                statement,
                body.parts_of(theorem),
                claims,
                body.export_pairing(theorem),
            ));
        }
    }

    /// Whether any source-bound theorem was retained for export. Without one,
    /// [`Self::take_exports`] returns nothing whatever the report.
    pub(crate) fn retained_any(&self) -> bool {
        self.exported
            .as_ref()
            .is_some_and(|exports| !exports.lock().unwrap().is_empty())
    }

    /// Exports leave only an enforced, failure-free report whose emitted
    /// opcode inventory is promotable, and only with the kind its
    /// architecture's owners produce (AArch64 ALU, constant or body for arch 0,
    /// x86-64 body for arch 1).
    pub(crate) fn take_exports(
        &self,
        report: &CapturedFunctionVerificationReport,
    ) -> Vec<SourceBoundArithmeticObligation> {
        let kind = match report.arch {
            0 => SourceBoundObligationKind::A64Alu,
            1 => SourceBoundObligationKind::X86Body,
            _ => return Vec::new(),
        };
        if self.request.mode() != ProvenanceXCheckMode::Enforce
            || report.report.has_failures()
            || !report.report.emitted_opcode_inventory().is_promotable()
        {
            return Vec::new();
        }
        self.exported.as_ref().map_or_else(Vec::new, |exports| {
            std::mem::take(&mut *exports.lock().unwrap())
                .into_iter()
                .filter(|(_, retained, _, _, _, _, _)| {
                    *retained == kind
                        || (report.arch == 0
                            && matches!(
                                *retained,
                                SourceBoundObligationKind::A64Constant
                                    | SourceBoundObligationKind::A64Body
                            ))
                })
                .map(
                    |(instruction, kind, category, obligation, parts, claims, pairing)| {
                        SourceBoundArithmeticObligation {
                            input: report.input,
                            function_name: report.report.function_name.clone(),
                            instruction,
                            kind,
                            category,
                            obligation,
                            parts,
                            claims,
                            pairing,
                        }
                    },
                )
                .collect()
        })
    }

    fn replay<O>(&self, owner: &O) -> Option<VerificationResult>
    where
        O: crate::source_bound_replay::SourceBoundReplay + ?Sized,
    {
        self.replay_explained(owner).0
    }
    /// [`Self::replay`], with why the verdict is `None` (diagnostic only).
    fn replay_explained<O>(&self, owner: &O) -> (Option<VerificationResult>, Option<String>)
    where
        O: crate::source_bound_replay::SourceBoundReplay + ?Sized,
    {
        let (result, bound, why) = self.request.with_policy(|| {
            crate::verdict_db::live_source_bound_replay_explained(owner, self.request)
        });
        if matches!(result, Some(VerificationResult::Valid)) && !bound {
            self.bound.store(false, Ordering::Relaxed);
        }
        (result, why)
    }
    pub(crate) fn defined_peer(
        &self,
        peer: &crate::aarch64_affine_lowering::CheckedDefinedPeerCall<'_>,
    ) -> (Option<VerificationResult>, Option<String>) {
        if !peer.matches_request(self.request) {
            return (None, Some("foreign original request capture".into()));
        }
        self.replay_explained(peer)
    }

    pub(crate) fn frame(
        &self,
        frame: &crate::source_bound_frame::SourceBoundFrame<'_>,
    ) -> Option<VerificationResult> {
        self.replay(frame)
    }
    pub(crate) fn alu(
        &self,
        alu: &crate::source_bound_alu::SourceBoundAlu<'_, '_>,
    ) -> Option<VerificationResult> {
        self.replay(alu)
    }
    pub(crate) fn constant(
        &self,
        constant: &crate::source_bound_constant::SourceBoundConstant<'_, '_>,
    ) -> Option<VerificationResult> {
        self.replay(constant)
    }

    /// Replay a holding trap expansion's register-renamed obligation under
    /// this request (L04-P12), with why the verdict is `None`.
    pub(crate) fn trap_expansion(
        &self,
        replay: &crate::aarch64_trap_expansion::TrapExpansionReplay,
    ) -> (Option<VerificationResult>, Option<String>) {
        self.replay_explained(replay)
    }

    pub(crate) fn a64_body(
        &self,
        body: &crate::source_bound_body::SourceBoundBody<'_, '_>,
    ) -> Option<VerificationResult> {
        self.a64_body_explained(body).0
    }

    pub(crate) fn a64_control(
        &self,
        control: &crate::source_bound_a64_control::SourceBoundA64Control<'_, '_>,
    ) -> Option<VerificationResult> {
        self.replay(control)
    }

    /// Replay the same raw scalar-body obligation once, retaining the diagnostic
    /// reason when no independently certified verdict is available. The reason
    /// changes neither the request binding, replay policy nor proof credit.
    pub(crate) fn a64_body_explained(
        &self,
        body: &crate::source_bound_body::SourceBoundBody<'_, '_>,
    ) -> (Option<VerificationResult>, Option<String>) {
        self.replay_explained(body)
    }

    /// Replay the frameless AArch64 whole-body theorem once, before the walk
    /// credits any of its rows; beside the verdict, why it is `None`
    /// (diagnostic).
    pub(crate) fn a64_whole_body(
        &self,
        body: &crate::source_bound_a64_body::SourceBoundA64Body<'_>,
    ) -> (Option<VerificationResult>, Option<String>) {
        self.replay_explained(body)
    }

    /// Replay the AArch64 scalar-cell caller's whole-call theorem once, before
    /// the walk credits any of its rows; beside the verdict, why it is `None`
    /// (diagnostic). The theorem is stated in parts (ruling
    /// LD-91): its part inventory is
    /// checked against the statement, then the parts are replayed serially
    /// through [`Self::original_parts`], stopping at the first without a
    /// Valid replay, under the parts credit rule of
    /// [`x86_body_parts_verdict`] (Valid only when every part is Valid; a
    /// refuted part refutes the theorem). The statement is never replayed.
    pub(crate) fn scalar_cell_caller(
        &self,
        owner: &crate::source_bound_frame::SourceBoundScalarCellCaller<'_>,
    ) -> (Option<VerificationResult>, Option<String>) {
        x86_body_parts_verdict(owner.check_parts(), owner.parts().len(), |refusal| {
            self.original_parts(owner.replay_parts(), refusal, |_, verdict, why, _| {
                (verdict, why)
            })
        })
    }

    /// Replay the parts of a memory row bound to a source-bound owner through
    /// the source-bound route, serially and in order, stopping at the first
    /// part without a Valid replay. One receipt per part, each bound to the
    /// exact query of the part it judged. A Valid replay that was not bound to
    /// this request's reusable authority clears [`Self::replays_bound`], as
    /// the frame and ALU replays do.
    pub(crate) fn memory_row(
        &self,
        row: &crate::aarch64_memory_source_binding::SourceBoundMemoryRow<'_>,
    ) -> Vec<crate::aarch64_memory_source_binding::PartReceipt> {
        row.replay_parts(|part| self.replay_explained(part))
    }
    /// Replay the parts of one memory-effect decomposition serially, in
    /// order, stopping at the first part without a Valid replay (the same
    /// discipline as [`Self::x86_envelope`]). One entry per part; beside each
    /// `None`, why (diagnostic only). A Valid part is a checked certificate
    /// RECORD, never credit, so it does not touch [`Self::replays_bound`].
    pub(crate) fn memory_effect(
        &self,
        decomposition: &crate::aarch64_memory_effect::MemoryEffectDecomposition,
    ) -> Vec<(Option<VerificationResult>, Option<String>)> {
        let mut stopped = false;
        decomposition
            .parts
            .iter()
            .map(|part| {
                if stopped {
                    return (
                        None,
                        Some("not replayed: an earlier part has no Valid replay".into()),
                    );
                }
                let (verdict, why) = self.request.with_policy(|| {
                    crate::verdict_db::live_word_bound_replay_explained(part, self.request)
                });
                stopped = !matches!(verdict, Some(VerificationResult::Valid));
                (verdict, why)
            })
            .collect()
    }
    /// Replay the x86-64 ABI envelope's parts serially, in order, stopping at
    /// the first part without a Valid replay. One entry per part: the verdict
    /// of each replayed part, and `None` for every part after the first
    /// non-Valid one (not replayed); diagnostic text retains refusals and the
    /// actual constructive producer when a Valid theorem did not run AY.
    pub(crate) fn x86_envelope(
        &self,
        envelope: &crate::x86_source_bound_envelope::SourceBoundX86Envelope<'_>,
    ) -> Vec<(Option<VerificationResult>, Option<String>)> {
        self.original_parts(envelope.replay_parts(), None, |_, verdict, why, _| {
            (verdict, why)
        })
    }

    /// One serial protocol for sealed ORIGINAL source-bound parts. Word-bound
    /// recording cannot enter it. A refused request calls no solver; the first
    /// non-Valid verdict stops replay but retains every later diagnostic row.
    /// Owner-specific callbacks retain their private IDs/outcome types without
    /// cloning queries, recapturing authority, or minting partial evidence.
    fn original_parts<P, O>(
        &self,
        parts: impl Iterator<Item = P>,
        refusal: Option<String>,
        mut outcome: impl FnMut(P, Option<VerificationResult>, Option<String>, bool) -> O,
    ) -> Vec<O>
    where
        P: crate::source_bound_replay::SourceBoundReplay,
    {
        let mut stopped = refusal.is_some();
        parts
            .map(|part| {
                if stopped {
                    return outcome(
                        part,
                        None,
                        Some(
                            refusal
                                .as_deref()
                                .unwrap_or("not replayed: an earlier part has no Valid replay")
                                .to_owned(),
                        ),
                        false,
                    );
                }
                let (verdict, why) = self.replay_explained(&part);
                stopped = !matches!(verdict, Some(VerificationResult::Valid));
                outcome(part, verdict, why, true)
            })
            .collect()
    }
    /// All original-Core read-only relations use the same exact raw replay
    /// path and captured authority as the other sealed source-bound owners.
    /// A policy mismatch runs no part; a non-Valid replay stops all later
    /// parts. The complete ordered inventory remains diagnostic, not credit.
    pub(crate) fn read_only_relations(
        &self,
        relations: &crate::read_only_replay::ReadOnlyCompilerRelations<'_>,
    ) -> Vec<crate::read_only_replay::ReadOnlyReplayOutcome> {
        use crate::read_only_replay::ReadOnlyReplayOutcome;
        let refusal = relations
            .policy_refusal(self.request)
            .map(|reason| format!("not replayed: {reason}"));
        self.original_parts(
            relations.parts(),
            refusal,
            |part, verdict, why, attempted| {
                if attempted {
                    ReadOnlyReplayOutcome::replayed(part.id(), verdict, why)
                } else {
                    ReadOnlyReplayOutcome::not_run(part.id(), why.expect("not-run reason"))
                }
            },
        )
    }

    /// The writable inventory uses the same captured ORIGINAL-query replay
    /// and complete-outcome protocol, not word-bound or statistical credit.
    pub(crate) fn scalar_memory_relations(
        &self,
        relations: &crate::read_only_replay::ScalarMemoryCompilerRelations<'_>,
    ) -> Vec<crate::read_only_replay::ScalarMemoryReplayOutcome> {
        use crate::read_only_replay::ScalarMemoryReplayOutcome;
        let refusal = relations
            .policy_refusal(self.request)
            .map(|reason| format!("not replayed: {reason}"));
        self.original_parts(
            relations.parts(),
            refusal,
            |part, verdict, why, attempted| {
                if attempted {
                    ScalarMemoryReplayOutcome::replayed(part.id(), verdict, why)
                } else {
                    ScalarMemoryReplayOutcome::not_run(part.id(), why.expect("not-run reason"))
                }
            },
        )
    }
    pub(crate) fn scalar_return_relations(
        &self,
        relations: &crate::read_only_replay::ScalarReturnCompilerRelations<'_>,
    ) -> Vec<crate::read_only_replay::ScalarReturnReplayOutcome> {
        let refusal = relations
            .policy_refusal(self.request)
            .map(|reason| format!("not replayed: {reason}"));
        self.original_parts(
            relations.parts(),
            refusal,
            |part, verdict, why, attempted| {
                crate::read_only_replay::ScalarReturnReplayOutcome::new(
                    part.id(),
                    verdict,
                    why,
                    attempted,
                )
            },
        )
    }
    /// Whether every Valid replay so far was bound to this request's
    /// reusable authority.
    pub(crate) fn replays_bound(&self) -> bool {
        self.bound.load(Ordering::Relaxed)
    }
    /// Replay the x86-64 whole-body theorem once, serially, before the
    /// per-instruction pre-pass (which never issues a solver call).
    pub(crate) fn x86_body(
        &self,
        body: &crate::x86_source_bound_body::SourceBoundX86Body<'_>,
    ) -> Option<VerificationResult> {
        self.x86_body_explained(body).0
    }

    /// Replay the same x86-64 whole-body theorem with its exact diagnostic
    /// explanation. The text is not proof credit or a replacement verdict;
    /// request binding and reuse receipts follow the unchanged replay path.
    ///
    /// Slice 16: a theorem stated in parts is replayed part by part through
    /// [`Self::original_parts`] (serial, stopping at the first part without a
    /// Valid replay), after the part inventory is checked against the
    /// statement. Its verdict is Valid only when EVERY part's replay is
    /// Valid; a refuted part refutes the theorem (the parts' conjunction);
    /// anything else is no verdict. The statement itself is never replayed.
    ///
    /// Slice 19 (OD-197): a replayed obligation (the theorem, or a part)
    /// with no verdict (neither Valid nor refuted) is replayed again claim by
    /// claim ([`x86_claims_verdict`]); the claims credit it only when every
    /// one replays Valid. The obligations so credited are recorded for the
    /// export ([`Self::retain_x86_body`]).
    ///
    /// Slice 23 (OD-206): before its claim split, such an obligation is
    /// replayed once as its generalization over its arithmetic leaves, and
    /// each claim without a verdict once as its own; a Valid generalization
    /// credits what it generalizes, anything else leaves the exact outcome
    /// ([`x86_generalized_verdict`]). The generalizations that credited are
    /// recorded with the claims.
    ///
    /// Slice 23 (OD-205): a theorem that pairs an arithmetic row states its
    /// operands equal, unconditionally, which a correct lowering may compute
    /// apart on some input (the selector's signed division divides by 1 where
    /// the source divides by -1): a model of the paired theorem's negation may
    /// violate only an operand claim, so it is no counterexample by itself.
    /// A paired theorem that is refuted is decided by the theorem without the
    /// pairing (the exact spelling of slices 1 to 22), replayed by the same
    /// route: its outcome is the body's (a refutation only ever comes from
    /// it); without one, the body has no verdict.
    pub(crate) fn x86_body_explained(
        &self,
        body: &crate::x86_source_bound_body::SourceBoundX86Body<'_>,
    ) -> (Option<VerificationResult>, Option<String>) {
        use crate::x86_source_bound_body::X86Theorem;
        // Slice 23 (OD-205): a paired theorem is replayed only once its
        // pairing record re-derives its pairing and its statement
        // (`check_pairing`); one whose record does not (or that has none) is
        // never replayed, and the theorem without the pairing is the body's
        // theorem, as when a paired build fails its check.
        if let Err(reason) = body.check_pairing() {
            let (verdict, why, claims, theorem) = if body.has_unpaired() {
                let (verdict, why, claims) = self.x86_theorem_explained(body, X86Theorem::Unpaired);
                let why = Some(format!(
                    "the paired theorem's pairing record does not re-derive it ({reason}), so it \
                     is not replayed (OD-205); the theorem without the pairing decides: {}",
                    why.as_deref().unwrap_or(match verdict {
                        Some(VerificationResult::Valid) => "Valid",
                        Some(VerificationResult::Invalid { .. }) => "refuted",
                        _ => "no independently checked proof",
                    })
                ));
                (verdict, why, claims, X86Theorem::Unpaired)
            } else {
                (
                    None,
                    Some(format!(
                        "the paired theorem's pairing record does not re-derive it ({reason}), \
                         and no theorem without the pairing decides (OD-205)"
                    )),
                    None,
                    X86Theorem::Paired,
                )
            };
            *self.x86_claims.lock().unwrap() = matches!(verdict, Some(VerificationResult::Valid))
                .then(|| X86Credit {
                    statement: Arc::as_ptr(&body.shared_obligation()) as usize,
                    theorem,
                    claims,
                });
            return (verdict, why);
        }
        let (verdict, why, claims) = self.x86_theorem_explained(body, X86Theorem::Paired);
        let refuted = matches!(verdict, Some(VerificationResult::Invalid { .. }));
        let (verdict, why, claims, theorem) = if refuted && body.is_paired() {
            let paired = match &verdict {
                Some(VerificationResult::Invalid { counterexample }) => counterexample.clone(),
                _ => String::new(),
            };
            if body.has_unpaired() {
                let (verdict, why, claims) = self.x86_theorem_explained(body, X86Theorem::Unpaired);
                let why = Some(format!(
                    "the paired theorem's negation is satisfiable ({paired}), no counterexample \
                     by itself (OD-205); the theorem without the pairing decides: {}",
                    why.as_deref().unwrap_or(match verdict {
                        Some(VerificationResult::Valid) => "Valid",
                        Some(VerificationResult::Invalid { .. }) => "refuted",
                        _ => "no independently checked proof",
                    })
                ));
                (verdict, why, claims, X86Theorem::Unpaired)
            } else {
                (
                    None,
                    Some(format!(
                        "the paired theorem's negation is satisfiable ({paired}), no \
                         counterexample by itself, and no theorem without the pairing decides \
                         (OD-205)"
                    )),
                    None,
                    X86Theorem::Paired,
                )
            }
        } else {
            (verdict, why, claims, X86Theorem::Paired)
        };
        *self.x86_claims.lock().unwrap() =
            matches!(verdict, Some(VerificationResult::Valid)).then(|| X86Credit {
                statement: Arc::as_ptr(&body.shared_obligation()) as usize,
                theorem,
                claims,
            });
        (verdict, why)
    }

    /// One theorem of `body` (`theorem`: the owner's, or the one without the
    /// pairing) replayed by the route of slices 16, 19 and 23: whole or part
    /// by part (serial, stopping at the first part without a Valid replay,
    /// after the part inventory is checked against its statement), each
    /// replayed obligation without a verdict then generalized once and split
    /// claim by claim ([`Self::x86_claims_after`]). With the record of the
    /// obligations credited claim by claim or by a generalization, when the
    /// theorem is Valid and any was.
    fn x86_theorem_explained(
        &self,
        body: &crate::x86_source_bound_body::SourceBoundX86Body<'_>,
        theorem: crate::x86_source_bound_body::X86Theorem,
    ) -> (
        Option<VerificationResult>,
        Option<String>,
        Option<Arc<crate::x86_source_bound_body::X86BodyClaims>>,
    ) {
        use crate::x86_source_bound_body::X86Theorem;
        let units = body.replayed_units_of(theorem).len();
        let mut claimed: Vec<Option<Vec<ProofObligation>>> = vec![None; units];
        let mut generalized: Vec<crate::x86_source_bound_body::X86UnitGeneralized> =
            vec![Default::default(); units];
        let in_parts = body.parts_of(theorem).is_some();
        let outcome = if !in_parts {
            let (verdict, why) = match theorem {
                X86Theorem::Paired => self.replay_explained(body),
                X86Theorem::Unpaired => match body.replay_unit_of(theorem, 0) {
                    Some(unit) => self.replay_explained(&unit),
                    None => (None, Some("no theorem without the pairing".into())),
                },
            };
            let (verdict, why, claims, general) =
                self.x86_claims_after(body, theorem, 0, verdict, why);
            if let Some(slot) = claimed.first_mut() {
                *slot = claims;
            }
            if let Some(slot) = generalized.first_mut() {
                *slot = general;
            }
            (verdict, why)
        } else {
            x86_body_parts_verdict(body.check_parts_of(theorem), units, |refusal| {
                let mut stopped = refusal.is_some();
                (0..units)
                    .map(|k| {
                        if stopped {
                            return (
                                None,
                                Some(refusal.clone().unwrap_or_else(|| {
                                    "not replayed: an earlier part has no Valid replay".into()
                                })),
                            );
                        }
                        let part = body.replay_unit_of(theorem, k).expect("a part");
                        let (verdict, why) = self.replay_explained(&part);
                        let (verdict, why, claims, general) =
                            self.x86_claims_after(body, theorem, k, verdict, why);
                        claimed[k] = claims;
                        generalized[k] = general;
                        stopped = !matches!(verdict, Some(VerificationResult::Valid));
                        (verdict, why)
                    })
                    .collect()
            })
        };
        let record = matches!(outcome.0, Some(VerificationResult::Valid))
            && (claimed.iter().any(Option::is_some)
                || generalized
                    .iter()
                    .any(crate::x86_source_bound_body::X86UnitGeneralized::any));
        let claims = record.then(|| {
            Arc::new(
                crate::x86_source_bound_body::X86BodyClaims::new(claimed)
                    .with_generalized(generalized),
            )
        });
        (outcome.0, outcome.1, claims)
    }

    /// Slice 23 (OD-206): `exact`, the outcome of an exact replay, followed
    /// by one replay of `generalized` (the same obligation's generalization)
    /// when it is neither Valid nor refuted ([`x86_generalized_verdict`]);
    /// with whether the generalization credited it.
    fn x86_generalized_after<G>(
        &self,
        exact: (Option<VerificationResult>, Option<String>),
        generalized: impl FnOnce() -> Result<G, String>,
    ) -> (Option<VerificationResult>, Option<String>, Option<G>)
    where
        G: crate::source_bound_replay::SourceBoundReplay,
    {
        if matches!(
            exact.0,
            Some(VerificationResult::Valid | VerificationResult::Invalid { .. })
        ) {
            return (exact.0, exact.1, None);
        }
        let Ok(general) = generalized() else {
            return (exact.0, exact.1, None);
        };
        let outcome = self.replay_explained(&general);
        let (verdict, why, credited) = x86_generalized_verdict(exact, outcome);
        (verdict, why, credited.then_some(general))
    }

    /// Slice 19 (OD-197): replayed obligation `unit` of `body`, whose whole
    /// replay gave `verdict`, replayed again claim by claim when that is no
    /// verdict ([`x86_claims_verdict`]); with the claims that credited it.
    /// Slice 23 (OD-206): first its generalization, once
    /// ([`Self::x86_generalized_after`]); then, claim by claim, each claim's
    /// generalization after its exact replay; with the generalizations that
    /// credited.
    fn x86_claims_after(
        &self,
        body: &crate::x86_source_bound_body::SourceBoundX86Body<'_>,
        theorem: crate::x86_source_bound_body::X86Theorem,
        unit: usize,
        verdict: Option<VerificationResult>,
        why: Option<String>,
    ) -> (
        Option<VerificationResult>,
        Option<String>,
        Option<Vec<ProofObligation>>,
        crate::x86_source_bound_body::X86UnitGeneralized,
    ) {
        use crate::x86_source_bound_body::X86UnitGeneralized;
        if matches!(
            verdict,
            Some(VerificationResult::Valid | VerificationResult::Invalid { .. })
        ) {
            return (verdict, why, None, X86UnitGeneralized::default());
        }
        let (verdict, why, whole) = self
            .x86_generalized_after((verdict, why), || body.replay_generalized_of(theorem, unit));
        if let Some(whole) = whole {
            return (
                verdict,
                why,
                None,
                X86UnitGeneralized::whole(whole.obligation().clone()),
            );
        }
        let Ok(claims) = body.replay_claims_of(theorem, unit) else {
            return (verdict, why, None, X86UnitGeneralized::default());
        };
        let mut claim_generalized: Vec<Option<ProofObligation>> = vec![None; claims.len()];
        let (verdict, why, credited) = x86_claims_verdict((verdict, why), claims.len(), |k| {
            let exact = self.replay_explained(&claims[k]);
            let (verdict, why, general) =
                self.x86_generalized_after(exact, || claims[k].generalized());
            claim_generalized[k] = general.map(|general| general.obligation().clone());
            (verdict, why)
        });
        if !credited {
            return (verdict, why, None, X86UnitGeneralized::default());
        }
        (
            verdict,
            why,
            Some(
                claims
                    .into_iter()
                    .map(|claim| claim.obligation().clone())
                    .collect(),
            ),
            X86UnitGeneralized::claims(claim_generalized),
        )
    }

    /// Slice 19 (OD-197), slice 23 (OD-205): which theorem of `body` its
    /// last replay under this context credited (the paired one unless the
    /// replay said otherwise) and the record of the obligations credited
    /// claim by claim or by a generalization.
    fn x86_credit_of(
        &self,
        body: &crate::x86_source_bound_body::SourceBoundX86Body<'_>,
    ) -> (
        crate::x86_source_bound_body::X86Theorem,
        Option<Arc<crate::x86_source_bound_body::X86BodyClaims>>,
    ) {
        let key = Arc::as_ptr(&body.shared_obligation()) as usize;
        self.x86_claims
            .lock()
            .unwrap()
            .as_ref()
            .filter(|credit| credit.statement == key)
            .map_or(
                (crate::x86_source_bound_body::X86Theorem::Paired, None),
                |credit| (credit.theorem, credit.claims.clone()),
            )
    }
}

/// THE claim-by-claim credit rule of slice 19 (OD-197). `whole` is the
/// verdict of one replayed obligation (a theorem or a part) replayed whole,
/// which was neither Valid nor refuted; `replay(k)` replays its claim `k` of
/// `count` ([`crate::x86_source_bound_body::SourceBoundX86Body::replay_claims`]),
/// serially, stopping at the first claim without a Valid replay. The
/// obligation is Valid (and `true` is returned beside it) only when EVERY
/// claim replays Valid: it is the conjunction of its claims, each stated
/// under the obligation's own definitions. A refuted claim refutes the
/// obligation (a model of the claim's query extends to the obligation's: its
/// other definitions define fresh names), its counterexample naming the
/// claim. Anything else keeps the whole replay's outcome, with the first
/// unproven claim's reason added.
pub(crate) fn x86_claims_verdict(
    whole: (Option<VerificationResult>, Option<String>),
    count: usize,
    mut replay: impl FnMut(usize) -> (Option<VerificationResult>, Option<String>),
) -> (Option<VerificationResult>, Option<String>, bool) {
    let (verdict, why) = whole;
    if count < 2
        || matches!(
            verdict,
            Some(VerificationResult::Valid | VerificationResult::Invalid { .. })
        )
    {
        return (verdict, why, false);
    }
    for k in 0..count {
        let claim = format!("claim {} of {count}", k + 1);
        match replay(k) {
            (Some(VerificationResult::Valid), _) => {}
            (Some(VerificationResult::Invalid { counterexample }), claim_why) => {
                return (
                    Some(VerificationResult::Invalid {
                        counterexample: format!("{claim}: {counterexample}"),
                    }),
                    claim_why,
                    false,
                );
            }
            (claim_verdict, claim_why) => {
                let claim_reason = match (&claim_verdict, claim_why) {
                    (Some(VerificationResult::Unknown { reason }), _) => reason.clone(),
                    (_, Some(why)) => why,
                    _ => "no independently checked proof".into(),
                };
                let why = Some(format!(
                    "{}; claim by claim (OD-197): {claim}: {claim_reason}",
                    why.as_deref().unwrap_or("no independently checked proof")
                ));
                return (verdict, why, false);
            }
        }
    }
    (Some(VerificationResult::Valid), None, true)
}

/// THE generalization credit rule of slice 23 (OD-206), OD-200's verdict
/// rule. `exact` is the outcome of an obligation's exact replay (a theorem,
/// a part or a claim) and `generalized` that of its generalization over its
/// arithmetic leaves, replayed once after it. The obligation is Valid (and
/// `true` is returned beside it) only when the exact replay was neither Valid
/// nor refuted and the generalization replays Valid: a claim proved for
/// every value of the leaves holds at the values the operations compute
/// (instantiation). Anything else keeps the exact outcome, with the
/// generalization's reason added: a satisfying model of the generalization
/// may give a leaf a value its operation never computes, so it is NO
/// counterexample ([`crate::x86_64_function_verifier::X86_BODY_GENERALIZED_SAT`]);
/// a refutation only ever comes from the exact replay, which is never
/// generalized.
pub(crate) fn x86_generalized_verdict(
    exact: (Option<VerificationResult>, Option<String>),
    generalized: (Option<VerificationResult>, Option<String>),
) -> (Option<VerificationResult>, Option<String>, bool) {
    let (verdict, why) = exact;
    if matches!(
        verdict,
        Some(VerificationResult::Valid | VerificationResult::Invalid { .. })
    ) {
        return (verdict, why, false);
    }
    let reason = match generalized {
        (Some(VerificationResult::Valid), _) => {
            return (Some(VerificationResult::Valid), None, true);
        }
        (Some(VerificationResult::Invalid { .. }), _) => {
            crate::x86_64_function_verifier::X86_BODY_GENERALIZED_SAT.to_owned()
        }
        (Some(VerificationResult::Unknown { reason }), _) => reason,
        (None, Some(why)) => why,
        (None, None) => "no independently checked proof".into(),
    };
    let why = Some(format!(
        "{}; generalized (OD-206): {reason}",
        why.as_deref().unwrap_or("no independently checked proof")
    ));
    (verdict, why, false)
}

/// THE credit rule of an x86-64 body theorem stated in parts (slice 16).
/// `inventory` is the check of its part inventory against its statement
/// ([`crate::x86_source_bound_body::check_x86_body_parts`]); when it fails, no
/// part is replayed. `replay` replays the `count` parts serially, stopping at
/// the first without a Valid replay (`original_parts`). The theorem's verdict
/// is Valid only when every part's replay is Valid; a refuted part refutes the
/// theorem (the parts' conjunction), and its counterexample names the part;
/// anything else is no verdict, with the first unproven part's reason.
pub(crate) fn x86_body_parts_verdict(
    inventory: Result<(), String>,
    count: usize,
    replay: impl FnOnce(Option<String>) -> Vec<(Option<VerificationResult>, Option<String>)>,
) -> (Option<VerificationResult>, Option<String>) {
    let refusal = inventory
        .err()
        .map(|why| format!("not replayed: the part inventory does not check: {why}"));
    let refused = refusal.clone();
    let outcomes = replay(refusal);
    if let Some(why) = refused {
        return (None, Some(why));
    }
    if outcomes.len() != count || count == 0 {
        return (
            None,
            Some(format!(
                "{} replay outcomes for a theorem of {count} parts",
                outcomes.len()
            )),
        );
    }
    for (k, (verdict, why)) in outcomes.into_iter().enumerate() {
        let part = format!("part {} of {count}", k + 1);
        match verdict {
            Some(VerificationResult::Valid) => {}
            Some(VerificationResult::Invalid { counterexample }) => {
                return (
                    Some(VerificationResult::Invalid {
                        counterexample: format!("{part}: {counterexample}"),
                    }),
                    why,
                );
            }
            Some(VerificationResult::Unknown { reason }) => {
                return (
                    Some(VerificationResult::Unknown {
                        reason: format!("{part}: {reason}"),
                    }),
                    why,
                );
            }
            None => {
                return (
                    None,
                    Some(format!(
                        "{part}: {}",
                        why.unwrap_or_else(|| "no independently checked proof".into())
                    )),
                );
            }
        }
    }
    (Some(VerificationResult::Valid), None)
}

/// Immutable source-bound theorem retained after checked source/body binding,
/// independent replay, and the final enforced provenance cross-check: an
/// AArch64 bound ALU, constant or raw body theorem or the x86-64 whole-body theorem
/// ([`SourceBoundObligationKind`]). This is an export payload, not authority
/// to skip replay or final-byte checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceBoundArithmeticObligation {
    input: [u8; 32],
    function_name: String,
    instruction: usize,
    kind: SourceBoundObligationKind,
    category: ProofCategory,
    obligation: Arc<ProofObligation>,
    /// Slice 16: the part inventory of an x86-64 body theorem stated in parts
    /// (`obligation` is then its never-replayed statement).
    parts: Option<Arc<crate::x86_source_bound_body::X86BodyParts>>,
    /// Slice 19 (OD-197): the replayed obligations of an x86-64 body theorem
    /// its credit replayed claim by claim, with their claims.
    claims: Option<Arc<crate::x86_source_bound_body::X86BodyClaims>>,
    /// Slice 23 (OD-205): whether the x86-64 body theorem is a paired one,
    /// with its pairing record ([`Self::check_x86_body_pairing`]).
    pairing: crate::x86_source_bound_body::X86ExportPairing,
}

impl SourceBoundArithmeticObligation {
    /// The export of one Valid x86-64 ABI envelope part replay.
    pub(crate) fn x86_envelope(
        input: [u8; 32],
        function_name: &str,
        terminator_offset: usize,
        obligation: ProofObligation,
    ) -> Self {
        Self {
            input,
            function_name: function_name.to_owned(),
            instruction: terminator_offset,
            kind: SourceBoundObligationKind::X86Envelope,
            category: ProofCategory::FrameLayout,
            obligation: Arc::new(obligation),
            parts: None,
            claims: None,
            pairing: Default::default(),
        }
    }
    /// The exact LIR, function name, final bytes, fixup manifest and calling
    /// convention this x86-64 ABI envelope theorem was bound to.
    pub fn matches_x86_envelope_input(
        &self,
        lir: &trust_cg_lower::Function,
        function_name: &str,
        code: &[u8],
        manifest: &[u8],
        abi: Option<crate::X86SourceBoundAbi>,
    ) -> bool {
        self.kind == SourceBoundObligationKind::X86Envelope
            && self.input == x86_envelope_input(lir, function_name, code, manifest, abi)
    }
    pub fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }
    /// Slice 16: the part inventory of an x86-64 body theorem stated in parts
    /// (its replayed obligations, in order); `None` for every other export.
    /// A consumer publishes the parts, never [`Self::obligation`] (the
    /// statement), and only after [`Self::check_x86_body_parts`].
    pub fn x86_body_parts(&self) -> Option<&crate::x86_source_bound_body::X86BodyParts> {
        self.parts.as_deref()
    }
    /// Slice 19 (OD-197): the replayed obligations of an x86-64 body
    /// theorem its credit replayed claim by claim, with their claims (`None`
    /// when none was, and for every other export).
    pub fn x86_body_claims(&self) -> Option<&crate::x86_source_bound_body::X86BodyClaims> {
        self.claims.as_deref()
    }
    /// Slice 16: the obligations a consumer replays or publishes for this
    /// export: the parts of a theorem stated in parts, once its inventory
    /// checks against the statement; else the obligation itself. Slice 19
    /// (OD-197): an obligation credited claim by claim is published as its
    /// claims, once they check as its claim split.
    pub fn replayed_obligations(&self) -> Result<Vec<&ProofObligation>, String> {
        self.check_x86_body_pairing()?;
        let units: Vec<&ProofObligation> = match &self.parts {
            Some(parts) => {
                self.check_x86_body_parts()?;
                parts.parts().iter().collect()
            }
            None => vec![&self.obligation],
        };
        let Some(claims) = &self.claims else {
            return Ok(units);
        };
        self.check_x86_body_claims()?;
        Ok(units
            .into_iter()
            .enumerate()
            .flat_map(|(k, unit)| claims.published(k, unit))
            .collect())
    }
    /// Slice 23 (OD-205): whether the exported theorem is a paired one
    /// (its statement spells the source's operation for a machine row's).
    pub fn is_x86_body_paired(&self) -> bool {
        matches!(
            self.pairing,
            crate::x86_source_bound_body::X86ExportPairing::Paired(_)
        )
    }
    /// Slice 23 (OD-205): the pairing record of a paired x86-64 body theorem
    /// (`None` for every other export, and for a paired one without it, which
    /// [`Self::check_x86_body_pairing`] refuses).
    pub fn x86_body_pairing(&self) -> Option<&crate::x86_source_bound_body::X86BodyPairing> {
        match &self.pairing {
            crate::x86_source_bound_body::X86ExportPairing::Paired(Some(pairing)) => {
                Some(pairing.as_ref())
            }
            _ => None,
        }
    }
    /// Slice 23 (OD-205): whether the exported theorem may be published as
    /// far as its pairing goes: one that pairs nothing always; a paired one
    /// only with its pairing record, once the record re-derives its pairing
    /// and its statement
    /// ([`crate::x86_source_bound_body::X86BodyPairing::check`]).
    /// [`Self::replayed_obligations`] runs it first.
    pub fn check_x86_body_pairing(&self) -> Result<(), String> {
        if self.is_x86_body_paired() && self.kind != SourceBoundObligationKind::X86Body {
            return Err(format!("a {:?} export carries a pairing", self.kind));
        }
        self.pairing.check(&self.obligation)
    }
    /// Slice 23 (OD-206): whether every generalization the record names is
    /// exactly the generalization of what it generalizes, re-derived here
    /// ([`crate::x86_source_bound_body::X86BodyClaims::check_generalized`]);
    /// always without a record. [`Self::check_x86_body_claims`] includes it.
    pub fn check_x86_body_generalized(&self) -> Result<(), String> {
        let Some(claims) = &self.claims else {
            return Ok(());
        };
        if self.kind != SourceBoundObligationKind::X86Body {
            return Err(format!(
                "a {:?} export carries body generalizations",
                self.kind
            ));
        }
        let units: Vec<&ProofObligation> = match &self.parts {
            Some(parts) => parts.parts().iter().collect(),
            None => vec![&self.obligation],
        };
        claims.check_generalized(&units)
    }
    /// Slice 19 (OD-197): whether the claim record is, obligation by
    /// obligation, exactly the claim split of the theorem's replayed
    /// obligations (its parts, or the theorem); always without one. Slice 23
    /// (OD-206): and every generalization it names, that generalization.
    pub fn check_x86_body_claims(&self) -> Result<(), String> {
        let Some(claims) = &self.claims else {
            return Ok(());
        };
        if self.kind != SourceBoundObligationKind::X86Body {
            return Err(format!("a {:?} export carries body claims", self.kind));
        }
        let units: Vec<&ProofObligation> = match &self.parts {
            Some(parts) => parts.parts().iter().collect(),
            None => vec![&self.obligation],
        };
        claims.check(&units)
    }
    /// Slice 16: whether the part inventory is exactly the split of the
    /// statement ([`crate::x86_source_bound_body::check_x86_body_parts`]);
    /// always for an export not in parts.
    pub fn check_x86_body_parts(&self) -> Result<(), String> {
        match &self.parts {
            Some(parts) if self.kind == SourceBoundObligationKind::X86Body => {
                parts.check(&self.obligation)
            }
            Some(_) => Err(format!("a {:?} export carries body parts", self.kind)),
            None => Ok(()),
        }
    }
    /// Tests only: the export a credited row of `owner` would carry (no
    /// input digest), without replaying it.
    #[cfg(test)]
    pub(crate) fn x86_body_export_for_tests(
        owner: &crate::x86_source_bound_body::SourceBoundX86Body<'_>,
    ) -> Self {
        Self {
            input: [0; 32],
            function_name: owner.source().name.clone(),
            instruction: 0,
            kind: SourceBoundObligationKind::X86Body,
            category: ProofCategory::X8664Lowering,
            obligation: owner.shared_obligation(),
            parts: owner.is_stated_in_parts().then(|| owner.shared_parts()),
            claims: None,
            pairing: owner.export_pairing(crate::x86_source_bound_body::X86Theorem::Paired),
        }
    }
    /// Tests only: this export with what it carries of the pairing replaced.
    #[cfg(test)]
    pub(crate) fn with_x86_body_pairing(
        &self,
        pairing: crate::x86_source_bound_body::X86ExportPairing,
    ) -> Self {
        Self {
            pairing,
            ..self.clone()
        }
    }
    /// Tests only: this export with its part inventory replaced.
    #[cfg(test)]
    pub(crate) fn with_x86_body_parts(
        &self,
        parts: crate::x86_source_bound_body::X86BodyParts,
    ) -> Self {
        Self {
            parts: Some(Arc::new(parts)),
            ..self.clone()
        }
    }
    /// Tests only: this export with its claim record replaced.
    #[cfg(test)]
    pub(crate) fn with_x86_body_claims(
        &self,
        claims: crate::x86_source_bound_body::X86BodyClaims,
    ) -> Self {
        Self {
            claims: Some(Arc::new(claims)),
            ..self.clone()
        }
    }
    pub fn function_name(&self) -> &str {
        &self.function_name
    }
    pub fn instruction_index(&self) -> usize {
        self.instruction
    }
    /// Which owner retained this theorem.
    pub fn kind(&self) -> SourceBoundObligationKind {
        self.kind
    }
    /// The exact category selected by the sealed owner when retaining this
    /// theorem. Report metadata must match it, not select an alternate category.
    pub fn proof_category(&self) -> ProofCategory {
        self.category
    }
    pub fn input_digest(&self) -> &[u8; 32] {
        &self.input
    }
    pub fn matches_aarch64_input(
        &self,
        function: &trust_cg_ir::MachFunction,
        lir: Option<&trust_cg_lower::Function>,
    ) -> bool {
        matches!(
            self.kind,
            SourceBoundObligationKind::A64Alu
                | SourceBoundObligationKind::A64Constant
                | SourceBoundObligationKind::A64Body
        ) && self.input == aarch64_input(function, lir)
    }
    /// The exact pre-RA stream, LIR and calling convention this x86-64 body
    /// theorem was bound to, with no module named (OD-210).
    pub fn matches_x86_input(
        &self,
        function: &trust_cg_lower::x86_64_isel::X86ISelFunction,
        lir: Option<&trust_cg_lower::Function>,
        abi: Option<crate::X86SourceBoundAbi>,
    ) -> bool {
        self.matches_x86_input_in_module(function, lir, abi, None)
    }
    /// [`Self::matches_x86_input`] under the module definitions the theorem
    /// was bound to (OD-210).
    pub fn matches_x86_input_in_module(
        &self,
        function: &trust_cg_lower::x86_64_isel::X86ISelFunction,
        lir: Option<&trust_cg_lower::Function>,
        abi: Option<crate::X86SourceBoundAbi>,
        module: Option<&crate::X86ModuleDefinitions>,
    ) -> bool {
        self.kind == SourceBoundObligationKind::X86Body
            && self.input == x86_input(function, lir, abi, module)
    }
    /// Full query identity, including actual aliases, widths and immediates.
    pub fn query_sha256(&self) -> String {
        format!(
            "{:x}",
            Sha256::digest(crate::serialize_to_smt2(&self.obligation).as_bytes())
        )
    }
}

/// Exact source/ABI routing for an AArch64 function containing only RET.
/// This is trusted structural checking, not an instruction proof or a cache
/// reuse capability. Private construction requires the complete source and
/// allocated body to match and the actual hardware stream to be exactly RET.
#[derive(Clone, Debug)]
pub struct CheckedAarch64StructuralReturn {
    input: [u8; 32],
}
impl CheckedAarch64StructuralReturn {
    /// Canonical source/machine input bound by this structural check.
    pub fn input_digest(&self) -> &[u8; 32] {
        &self.input
    }
}

/// Immutable report plus an unforgeable request/input receipt. Cloning shares
/// the owned report; no mutable report or receipt accessor is exposed.
#[derive(Clone, Debug)]
pub struct CapturedFunctionVerificationReport {
    capture_scope: Arc<()>,
    report: Arc<FunctionVerificationReport>,
    input: [u8; 32],
    arch: u8,
    identity: Option<[u8; 32]>,
    solver: Option<Arc<crate::ay_identity::PinnedAy>>,
    /// The request's refusal when it had no AY (exactly one of this and
    /// `solver` is set for every request).
    ay_refusal: Option<Arc<crate::ay_identity::AyIdentityRefusal>>,
    source_modules: Option<[u8; 32]>,
}
impl CapturedFunctionVerificationReport {
    /// Whether this report was produced by this exact captured invocation (or
    /// its clone). This is input custody only, never proof or cache authority.
    /// The existing content-based `reusable_for` contract is unchanged.
    pub fn matches_request_capture(&self, request: &FunctionVerificationRequest) -> bool {
        Arc::ptr_eq(&self.capture_scope, &request.capture_scope)
    }

    pub(crate) fn aarch64_input_digest(&self) -> Option<&[u8; 32]> {
        (self.arch == 0).then_some(&self.input)
    }
    pub fn report(&self) -> &FunctionVerificationReport {
        &self.report
    }
    /// Recheck a local, module-independent return property on the exact
    /// captured input. This does not reuse a report under another request or
    /// module: no calls, memory, value instructions or module references are
    /// admitted, and this receipt remains ineligible for proof-cache reuse.
    pub fn checked_aarch64_structural_return(
        &self,
        function: &trust_cg_ir::MachFunction,
        source: &trust_cg_lower::Function,
    ) -> Option<CheckedAarch64StructuralReturn> {
        if self.arch != 0
            || self.input != aarch64_input(function, Some(source))
            || function.name != source.name
            || self.report.precondition_failure.is_some()
            || self.report.failed_count() != 0
            || self.report.degenerate_verified_count() != 0
            || !self.report.emitted_opcode_inventory().is_promotable()
        {
            return None;
        }
        let mut hardware = None;
        for block in &function.block_order {
            for id in &function.blocks.get(block.0 as usize)?.insts {
                let inst = function.insts.get(id.0 as usize)?;
                if !inst.is_pseudo() && hardware.replace(inst).is_some() {
                    return None;
                }
            }
        }
        if hardware?.opcode != trust_cg_ir::AArch64Opcode::Ret {
            return None;
        }
        // The complete checker requires the canonical unchanged-LR operand,
        // exact flags, no clobbers and exact source/ABI return routing. The
        // encoder emits the fixed RET X30 word; installed-image replay still
        // binds the certificate to the actual published bytes.
        crate::source_bound_a64_control::CheckedFramelessLinear::bind(source, function).ok()?;
        Some(CheckedAarch64StructuralReturn { input: self.input })
    }
    /// The admitted AY (route, path, SHA-256, recorded build) that any solver
    /// verdict in this report was bound to; `None` when the request had none.
    pub fn ay_solver(&self) -> Option<&crate::ay_identity::PinnedAy> {
        self.solver.as_deref()
    }
    /// Why the request this report came from had no AY bound (`None` when it
    /// had one): the request's own resolution, carried with its evidence.
    pub fn ay_refusal(&self) -> Option<&crate::ay_identity::AyIdentityRefusal> {
        self.ay_refusal.as_deref()
    }
    /// [`FunctionVerificationRequest::ay_refusal_note`] of the request this
    /// report came from.
    pub fn ay_refusal_note(&self) -> Option<String> {
        self.ay_refusal()
            .and_then(crate::ay_bridge::request_refusal_note_for)
    }
    /// Validate attribution to this request. Cache consumers must ALSO check
    /// the architecture-specific input matcher and their existing proof gates.
    pub fn reusable_for(&self, request: &FunctionVerificationRequest) -> bool {
        self.identity.is_some() && self.identity == request.reuse_identity() && request.may_reuse()
    }
    pub fn matches_aarch64_input(
        &self,
        function: &trust_cg_ir::MachFunction,
        lir: Option<&trust_cg_lower::Function>,
    ) -> bool {
        self.source_modules.is_none()
            && self.arch == 0
            && self.input == aarch64_input(function, lir)
    }

    /// A source-bearing receipt cannot be reused through the legacy LIR-only
    /// matcher. Both original and lowered module identities must still match.
    pub fn matches_aarch64_input_with_modules(
        &self,
        function: &trust_cg_ir::MachFunction,
        lir: Option<&trust_cg_lower::Function>,
        source: &crate::FunctionSourceModules<'_>,
    ) -> bool {
        self.arch == 0
            && self.input == aarch64_input(function, lir)
            && self.source_modules.as_ref() == Some(source.digest())
    }
    /// The ABI is part of the x86-64 verifier input: a report captured under
    /// one calling convention never matches another (or none). This form
    /// names no module (OD-210).
    pub fn matches_x86_input(
        &self,
        function: &trust_cg_lower::x86_64_isel::X86ISelFunction,
        lir: Option<&trust_cg_lower::Function>,
        abi: Option<crate::X86SourceBoundAbi>,
    ) -> bool {
        self.matches_x86_input_in_module(function, lir, abi, None)
    }
    /// [`Self::matches_x86_input`] under module definitions (OD-210): the
    /// definitions that can change the function's verdict are verifier
    /// input too ([`crate::X86ModuleDefinitions::input_line`]).
    pub fn matches_x86_input_in_module(
        &self,
        function: &trust_cg_lower::x86_64_isel::X86ISelFunction,
        lir: Option<&trust_cg_lower::Function>,
        abi: Option<crate::X86SourceBoundAbi>,
        module: Option<&crate::X86ModuleDefinitions>,
    ) -> bool {
        self.source_modules.is_none()
            && self.arch == 1
            && self.input == x86_input(function, lir, abi, module)
    }
    /// Conservative resident-payload accounting; shared reports may be counted
    /// once per cache entry to avoid undercharging their retained allocations.
    pub fn estimated_payload_bytes(&self) -> usize {
        let mut size = std::mem::size_of::<Self>()
            // Conservatively charge the shared Arc allocation once per receipt.
            .saturating_add(2 * std::mem::size_of::<usize>())
            .saturating_add(self.solver.as_ref().map_or(0, |solver| {
                std::mem::size_of::<crate::ay_identity::PinnedAy>()
                    .saturating_add(solver.path().as_os_str().len())
                    .saturating_add(solver.identity().describe().len())
            }))
            .saturating_add(self.ay_refusal.as_ref().map_or(0, |refusal| {
                // The rendered refusal bounds its heap payload.
                std::mem::size_of::<crate::ay_identity::AyIdentityRefusal>()
                    .saturating_add(refusal.to_string().len())
            }))
            .saturating_add(std::mem::size_of::<FunctionVerificationReport>())
            .saturating_add(2 * std::mem::size_of::<usize>())
            .saturating_add(self.report.function_name.capacity())
            .saturating_add(self.report.instructions.capacity().saturating_mul(
                std::mem::size_of::<crate::function_verifier::InstructionReport>(),
            ));
        for row in &self.report.instructions {
            size = size.saturating_add(match &row.result {
                InstructionVerificationResult::Verified { proof_name, .. } => proof_name.capacity(),
                InstructionVerificationResult::Failed { proof_name, detail } => {
                    proof_name.capacity().saturating_add(detail.capacity())
                }
                InstructionVerificationResult::Unverified { reason }
                | InstructionVerificationResult::Skipped { reason } => reason.capacity(),
            });
        }
        match &self.report.precondition_failure {
            Some(crate::function_verifier::FunctionVerificationPreconditionFailure::LirSourceNameMismatch { source_function }) => {
                size = size.saturating_add(source_function.capacity());
            }
            // The typed mismatch may carry a checker message; its rendered
            // length bounds that heap payload.
            Some(crate::function_verifier::FunctionVerificationPreconditionFailure::SourceBoundFrameMismatch(mismatch)) => {
                size = size.saturating_add(mismatch.to_string().len());
            }
            Some(crate::function_verifier::FunctionVerificationPreconditionFailure::SourceBoundX86BodyMismatch(mismatch)) => {
                size = size.saturating_add(mismatch.to_string().len());
            }
            Some(crate::function_verifier::FunctionVerificationPreconditionFailure::SourceBoundA64BodyMismatch(mismatch)) => {
                size = size.saturating_add(mismatch.to_string().len());
            }
            Some(crate::function_verifier::FunctionVerificationPreconditionFailure::TrapGuardAccounting(failure)) => {
                size = size.saturating_add(failure.to_string().len());
            }
            _ => {}
        }
        size
    }
    pub(crate) fn finish(
        report: FunctionVerificationReport,
        input: [u8; 32],
        arch: u8,
        scope: &FunctionDischargeContext<'_>,
    ) -> Self {
        let eligible = scope.bound.load(Ordering::Relaxed)
            && scope.request.may_reuse()
            && report.precondition_failure.is_none()
            && report.genuinely_verified_count() > 0
            && report.failed_count() == 0
            && report.emitted_opcode_inventory().is_promotable();
        Self {
            capture_scope: scope.request.capture_scope.clone(),
            report: Arc::new(report),
            input,
            arch,
            identity: eligible.then(|| scope.request.reuse_identity()).flatten(),
            solver: scope.request.ay_solver().cloned().map(Arc::new),
            ay_refusal: scope.request.ay_refusal().cloned().map(Arc::new),
            source_modules: scope.source_modules.map(|source| *source.digest()),
        }
    }
}

/// No caller-selectable protocol exists on capture. The parameter only keeps
/// this domain boundary independently testable when canonical form migrates.
fn request_identity_hash(formula_protocol: &str) -> Sha256 {
    let mut hash = Sha256::new();
    hash.update(b"trust-cg.function-verification-request.v2\0");
    hash_bytes(&mut hash, formula_protocol.as_bytes());
    hash
}

fn hash_bytes(hash: &mut Sha256, bytes: &[u8]) {
    hash.update((bytes.len() as u64).to_be_bytes());
    hash.update(bytes);
}
struct HashWriter(Sha256);
impl std::fmt::Write for HashWriter {
    fn write_str(&mut self, text: &str) -> std::fmt::Result {
        self.0.update(text.as_bytes());
        Ok(())
    }
}
fn input_hash(
    arch: u8,
    write_machine: impl FnOnce(&mut HashWriter) -> std::fmt::Result,
    lir: Option<&trust_cg_lower::Function>,
) -> [u8; 32] {
    let mut writer = HashWriter(Sha256::new());
    writer.0.update(b"trust-cg.function-report-input.v1\0");
    writer.0.update([arch]);
    // HashWriter is infallible. Separate digests delimit machine/LIR streams.
    write_machine(&mut writer).expect("infallible SHA writer");
    let machine: [u8; 32] = writer.0.finalize().into();
    let mut hash = Sha256::new();
    hash.update(machine);
    match lir {
        Some(lir) => {
            let mut writer = HashWriter(Sha256::new());
            lir.write_canonical_verifier_identity(&mut writer)
                .expect("infallible SHA writer");
            hash.update([1]);
            hash.update(writer.0.finalize());
        }
        None => hash.update([0]),
    }
    hash.finalize().into()
}
pub(crate) fn aarch64_input(
    function: &trust_cg_ir::MachFunction,
    lir: Option<&trust_cg_lower::Function>,
) -> [u8; 32] {
    input_hash(
        0,
        |writer| {
            writeln!(writer, "{function:#?}")?;
            for (i, instruction) in function.insts.iter().enumerate() {
                for (j, operand) in instruction.operands.iter().enumerate() {
                    if let trust_cg_ir::MachOperand::FImm(value) = operand {
                        writeln!(writer, "{i}:{j}:{:016x}", value.to_bits())?;
                    }
                }
            }
            Ok(())
        },
        lir,
    )
}
/// The x86-64 verifier input: the pre-RA ISel identity, the calling
/// convention the compiler supplied (the source-bound body theorem depends on
/// it; `None` is every legacy entry point), the module definitions that can
/// change the function's verdict (OD-210,
/// [`crate::X86ModuleDefinitions::input_line`]: no line where none can, so
/// such a function's input is what it was before) and the exact LIR.
pub(crate) fn x86_input(
    function: &trust_cg_lower::x86_64_isel::X86ISelFunction,
    lir: Option<&trust_cg_lower::Function>,
    abi: Option<crate::X86SourceBoundAbi>,
    module: Option<&crate::X86ModuleDefinitions>,
) -> [u8; 32] {
    input_hash(
        1,
        |writer| {
            function.write_canonical_verifier_identity(writer)?;
            writeln!(writer, "x86_source_bound_abi={abi:?}")?;
            match lir.and_then(|lir| crate::X86ModuleDefinitions::input_line(module, lir)) {
                Some(line) => writeln!(writer, "{line}"),
                None => Ok(()),
            }
        },
        lir,
    )
}

/// The x86-64 ABI envelope input: the exact final bytes, the symbolic fixup
/// manifest, the machine function name, the calling convention and the exact
/// LIR. Architecture tag 2 keeps it disjoint from every report input.
pub(crate) fn x86_envelope_input(
    lir: &trust_cg_lower::Function,
    function_name: &str,
    code: &[u8],
    manifest: &[u8],
    abi: Option<crate::X86SourceBoundAbi>,
) -> [u8; 32] {
    input_hash(
        2,
        |writer| {
            writeln!(writer, "x86_abi_envelope.v1")?;
            writeln!(writer, "function={function_name:?}")?;
            writeln!(writer, "abi={abi:?}")?;
            writeln!(writer, "code={code:02x?}")?;
            writeln!(writer, "manifest={manifest:02x?}")
        },
        Some(lir),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_verifier::FunctionVerificationPreconditionFailure;
    use crate::{FunctionVerifier, X86FunctionVerifier};
    use trust_cg_ir::X86Opcode;
    use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, Signature};
    use trust_cg_lower::function::Signature as LirSignature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};

    fn without_tools<T>(f: impl FnOnce() -> T) -> T {
        trust_cg_process_env::with_env_edits(|env| {
            env.set("AY_SOLVER_PATH", "/nonexistent/function-request-ay");
            env.set(
                "TCG_EXTERNAL_CLEAN_CHECKER",
                "/nonexistent/function-request-clean",
            );
            env.set("TCG_CANARY_NO_CACHE", "1");
            env.set("TCG_NO_VERDICT_DB", "1");
            env.set("TCG_REFINE_SOLVER", "0");
            f()
        })
    }

    #[test]
    fn canonical_formula_protocol_domains_request_identity_without_authority_changes() {
        let protocol = crate::lowering_proof::CANONICAL_PROOF_FORMULA_PROTOCOL;
        let mut canonical = request_identity_hash(protocol);
        let mut other = request_identity_hash("trust-cg.proof-formula.right-spine.v1");
        let mut legacy = Sha256::new();
        legacy.update(b"trust-cg.function-verification-request.v1\0");
        for hash in [&mut canonical, &mut other, &mut legacy] {
            // Identical captured-content suffix; only canonical domain differs.
            hash.update(b"same captured tools, policy, inputs and source");
        }
        let canonical: [u8; 32] = canonical.finalize().into();
        let other: [u8; 32] = other.finalize().into();
        let legacy: [u8; 32] = legacy.finalize().into();
        assert_ne!(canonical, other);
        assert_ne!(canonical, legacy);
        assert!(crate::ay_bridge::replay_protocol_description().contains(protocol));
        without_tools(|| {
            let unavailable = FunctionVerificationRequest::capture(
                VerificationConfig::for_proof_promotion(),
                ProvenanceXCheckMode::Enforce,
            );
            assert!(unavailable.reuse_identity().is_none());
        });
    }

    /// The request resolves AY once, when captured, and carries that
    /// resolution (its refusal) into its note and every report it produces;
    /// a later resolution under another environment changes neither
    /// (X-HOST-P13 fourth closure audit: the refusal note resolved AY again
    /// and disagreed with the request when the cache's symlink was
    /// re-pointed in between).
    #[test]
    fn a_request_carries_its_own_ay_resolution_into_its_note_and_reports() {
        let verifier = FunctionVerifier::new();
        let (request, at_capture) = without_tools(|| {
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            (request, crate::ay_bridge::solver_identity_refusal())
        });
        assert_eq!(request.ay_refusal().cloned(), at_capture);
        let note = request.ay_refusal_note();
        assert_eq!(
            note,
            request
                .ay_refusal()
                .and_then(crate::ay_bridge::request_refusal_note_for)
        );
        if let Some(note) = &note {
            assert!(
                note.starts_with(crate::ay_bridge::REQUEST_REFUSAL_NOTE_HEAD)
                    && note.contains("/nonexistent/function-request-ay"),
                "{note}"
            );
        }
        // Another environment now: the process resolves otherwise, the
        // request and its reports do not.
        trust_cg_process_env::with_env_edits(|env| {
            env.set("AY_SOLVER_PATH", "relative-ay");
            env.set("TCG_REFINE_SOLVER", "0");
            // A build that records no AY refuses everything alike.
            if !matches!(
                at_capture,
                Some(crate::ay_identity::AyIdentityRefusal::Unrecorded { .. })
            ) {
                assert_ne!(crate::ay_bridge::solver_identity_refusal(), at_capture);
            }
            assert_eq!(request.ay_refusal_note(), note);
            let report = verifier.verify_with_request(&a64(vec![]), None, &request);
            assert_eq!(report.ay_refusal().cloned(), at_capture);
            assert_eq!(report.ay_refusal_note(), note);
        });
    }

    fn a64(insts: Vec<MachInst>) -> MachFunction {
        let mut function = MachFunction::new("request_test".into(), Signature::new(vec![], vec![]));
        for inst in insts {
            let id = function.push_inst(inst);
            function.append_inst(function.entry, id);
        }
        function
    }
    fn x86(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let mut function = X86ISelFunction::new(
            "request_test".into(),
            LirSignature {
                params: vec![],
                returns: vec![],
            },
        );
        function.ensure_block(Block(0));
        function.blocks.get_mut(&Block(0)).unwrap().insts = insts;
        function
    }

    #[test]
    fn request_config_mismatch_rejects_all_fields_before_evaluation() {
        without_tools(|| {
            let a = FunctionVerifier::new();
            let x = X86FunctionVerifier::new();
            let base = VerificationConfig::default();
            let mut mutations = Vec::new();
            let mut m = base.clone();
            m.sample_count += 1;
            mutations.push(m);
            let mut m = base.clone();
            m.exhaustive_threshold += 1;
            mutations.push(m);
            mutations.push(VerificationConfig::for_proof_promotion());
            for config in mutations {
                let request =
                    FunctionVerificationRequest::capture(config, ProvenanceXCheckMode::Off);
                let a_report = a.verify_with_request(&a64(vec![]), None, &request);
                let x_report = x.verify_with_request(&x86(vec![]), None, &request);
                for report in [a_report, x_report] {
                    assert!(matches!(report.report().precondition_failure,
                        Some(FunctionVerificationPreconditionFailure::VerificationRequestConfigMismatch)));
                    assert!(report.report().instructions.is_empty());
                    assert!(!report.reusable_for(&request));
                }
            }
        });
    }

    #[test]
    fn request_preserves_missing_source_and_nonvacuity_boundaries() {
        without_tools(|| {
            let a = FunctionVerifier::new();
            let x = X86FunctionVerifier::new();
            let empty_a = a64(vec![]);
            let empty_x = x86(vec![]);
            for mode in [ProvenanceXCheckMode::Off, ProvenanceXCheckMode::Enforce] {
                let ar = a.capture_request_with_mode(mode);
                let xr = x.capture_request_with_mode(mode);
                for report in [
                    a.verify_with_request(&empty_a, None, &ar),
                    x.verify_with_request(&empty_x, None, &xr),
                ] {
                    assert_eq!(report.report().genuinely_verified_count(), 0);
                    assert_eq!(
                        report.report().precondition_failure.is_some(),
                        mode == ProvenanceXCheckMode::Enforce
                    );
                    assert!(!report.reusable_for(&ar));
                    assert!(!report.reusable_for(&xr));
                }
            }
            let function = a64(vec![MachInst::new(AArch64Opcode::Nop, vec![])]);
            let request = a.capture_request_with_mode(ProvenanceXCheckMode::Off);
            let report = a.verify_with_request(&function, None, &request);
            assert_eq!(report.report().instructions.len(), 1);
            assert_eq!(report.report().genuinely_verified_count(), 0);
            assert!(!report.reusable_for(&request));
            assert!(report.matches_aarch64_input(&function, None));
            assert!(!report.matches_x86_input(&empty_x, None, None));
            assert!(
                report.estimated_payload_bytes()
                    >= std::mem::size_of::<CapturedFunctionVerificationReport>()
                        + std::mem::size_of::<FunctionVerificationReport>()
                        + std::mem::size_of::<crate::function_verifier::InstructionReport>()
            );
        });
    }

    #[test]
    fn request_input_identity_covers_operands_nan_payloads_and_exact_lir() {
        let function = a64(vec![MachInst::new(
            AArch64Opcode::Nop,
            vec![MachOperand::FImm(f64::from_bits(0x7ff8_0000_0000_0001))],
        )]);
        let baseline = aarch64_input(&function, None);
        let mut mutant = function.clone();
        mutant.name.push('x');
        assert_ne!(baseline, aarch64_input(&mutant, None));
        let mut mutant = function.clone();
        mutant.insts[0].operands[0] = MachOperand::FImm(f64::from_bits(0x7ff8_0000_0000_0002));
        assert_ne!(
            baseline,
            aarch64_input(&mutant, None),
            "Debug alone loses NaN payload identity"
        );
        let mut mutant = function.clone();
        mutant.blocks[0].insts.clear();
        assert_ne!(baseline, aarch64_input(&mutant, None));
        let lir = trust_cg_lower::Function::new(
            "request_test",
            LirSignature {
                params: vec![],
                returns: vec![],
            },
        );
        assert_ne!(baseline, aarch64_input(&function, Some(&lir)));
        let mut changed_lir = lir.clone();
        changed_lir.signature.params.push(trust_cg_lower::Type::I64);
        assert_ne!(
            aarch64_input(&function, Some(&lir)),
            aarch64_input(&function, Some(&changed_lir))
        );
        let x = x86(vec![X86ISelInst::new(X86Opcode::Nop, vec![])]);
        let mut changed_x = x.clone();
        changed_x.blocks.get_mut(&Block(0)).unwrap().insts[0]
            .operands
            .push(X86ISelOperand::Imm(9));
        assert_ne!(
            x86_input(&x, None, None, None),
            x86_input(&changed_x, None, None, None)
        );
        assert_ne!(
            x86_input(&x, Some(&lir), None, None),
            x86_input(&x, Some(&changed_lir), None, None)
        );
        // The calling convention is verifier input: no two of absent,
        // System V and Windows x64 share a digest.
        let abis = [
            None,
            Some(crate::X86SourceBoundAbi::SystemV),
            Some(crate::X86SourceBoundAbi::WindowsX64),
        ];
        for (i, a) in abis.iter().enumerate() {
            for b in &abis[i + 1..] {
                assert_ne!(
                    x86_input(&x, Some(&lir), *a, None),
                    x86_input(&x, Some(&lir), *b, None)
                );
            }
        }
        // OD-210: the module definitions are verifier input exactly where
        // they can change the verdict. A function without a division keeps
        // one digest whatever the module; one with a division has a digest per
        // state: no module named, a module that defines none of the routines
        // it may call, and one that defines its routine.
        let sysv = Some(crate::X86SourceBoundAbi::SystemV);
        let none = crate::X86ModuleDefinitions::default();
        let udiv = crate::X86ModuleDefinitions::of_symbols(["__udivti3"]);
        let sdiv = crate::X86ModuleDefinitions::of_symbols(["__divti3", "memcpy"]);
        for module in [&none, &udiv, &sdiv] {
            assert_eq!(
                x86_input(&x, Some(&lir), sysv, None),
                x86_input(&x, Some(&lir), sysv, Some(module))
            );
        }
        let mut divides = lir.clone();
        let mut block = trust_cg_lower::function::BasicBlock::default();
        block
            .instructions
            .push(trust_cg_lower::instructions::Instruction {
                opcode: trust_cg_lower::instructions::Opcode::Udiv,
                args: vec![
                    trust_cg_lower::instructions::Value(0),
                    trust_cg_lower::instructions::Value(1),
                ],
                results: vec![trust_cg_lower::instructions::Value(2)],
            });
        divides.blocks.insert(divides.entry_block, block);
        let unnamed = x86_input(&x, Some(&divides), sysv, None);
        let defines_none = x86_input(&x, Some(&divides), sysv, Some(&none));
        let defines_udiv = x86_input(&x, Some(&divides), sysv, Some(&udiv));
        assert_ne!(unnamed, defines_none);
        assert_ne!(unnamed, defines_udiv);
        assert_ne!(defines_none, defines_udiv);
        // `__divti3` is no routine of a `Udiv`: it cannot change its verdict.
        assert_eq!(
            defines_none,
            x86_input(&x, Some(&divides), sysv, Some(&sdiv))
        );
        // OD-216: another compile unit of the link unit defining the routine
        // is a state of its own, and a link unit defining none keeps the
        // digest a module defining none had (so did OD-210's own line).
        let crate_udiv = none.clone().with_link_unit(["__udivti3"]);
        let crate_other = none.clone().with_link_unit(["__divti3", "main"]);
        let defines_crate_udiv = x86_input(&x, Some(&divides), sysv, Some(&crate_udiv));
        assert_ne!(defines_crate_udiv, defines_none);
        assert_ne!(defines_crate_udiv, defines_udiv);
        assert_ne!(defines_crate_udiv, unnamed);
        assert_eq!(
            defines_none,
            x86_input(&x, Some(&divides), sysv, Some(&crate_other))
        );
        assert_eq!(
            defines_udiv,
            x86_input(
                &x,
                Some(&divides),
                sysv,
                Some(&udiv.clone().with_link_unit(["__udivti3"]))
            )
        );
        // OD-217: a C memory routine's call is read like a division's: a
        // `Memset` has a digest per state, and the state of a routine it does
        // not call (`memcpy`) is not one.
        let mut fills = lir.clone();
        let mut block = trust_cg_lower::function::BasicBlock::default();
        block
            .instructions
            .push(trust_cg_lower::instructions::Instruction {
                opcode: trust_cg_lower::instructions::Opcode::Memset,
                args: vec![
                    trust_cg_lower::instructions::Value(0),
                    trust_cg_lower::instructions::Value(1),
                    trust_cg_lower::instructions::Value(2),
                ],
                results: vec![],
            });
        fills.blocks.insert(fills.entry_block, block);
        let memset = crate::X86ModuleDefinitions::of_symbols(["memset"]);
        let crate_memset = none.clone().with_link_unit(["memset"]);
        let fills_unnamed = x86_input(&x, Some(&fills), sysv, None);
        let fills_none = x86_input(&x, Some(&fills), sysv, Some(&none));
        let fills_memset = x86_input(&x, Some(&fills), sysv, Some(&memset));
        let fills_crate_memset = x86_input(&x, Some(&fills), sysv, Some(&crate_memset));
        for (i, a) in [fills_unnamed, fills_none, fills_memset, fills_crate_memset]
            .iter()
            .enumerate()
        {
            for b in &[fills_unnamed, fills_none, fills_memset, fills_crate_memset][i + 1..] {
                assert_ne!(a, b);
            }
        }
        assert_eq!(fills_none, x86_input(&x, Some(&fills), sysv, Some(&sdiv)));
        // Without such a call, a memory routine's definition changes nothing.
        assert_eq!(
            x86_input(&x, Some(&lir), sysv, None),
            x86_input(&x, Some(&lir), sysv, Some(&crate_memset))
        );
    }

    #[test]
    fn request_policy_freezes_absence_timeout_and_relative_cache_roots() {
        without_tools(|| {
            trust_cg_process_env::with_env_edits(|env| {
                env.remove("TCG_NO_SOLVER_SERVER");
                env.remove("TCG_NO_CERT_STORE");
                env.remove("TCG_NO_PROOF_CACHE");
                env.set("TRUST_CG_AY_TIMEOUT_MS", "1234");
                env.set("TCG_PROOF_CERT_STORE", "relative-certs");
                env.set("TCG_PROOF_CACHE_DIR", "relative-cache");
                let request =
                    FunctionVerifier::new().capture_request_with_mode(ProvenanceXCheckMode::Off);
                let cwd = std::env::current_dir().unwrap();
                std::thread::spawn(move || {
                    trust_cg_process_env::with_env_edits(|changed| {
                        changed.set("TRUST_CG_AY_TIMEOUT_MS", "9999");
                        changed.set("TCG_NO_SOLVER_SERVER", "1");
                        changed.set("TCG_PROOF_CERT_STORE", "/different-certs");
                        request.with_policy(|| {
                            assert_eq!(
                                trust_cg_process_env::var("TRUST_CG_AY_TIMEOUT_MS").unwrap(),
                                "1234"
                            );
                            assert!(trust_cg_process_env::var_os("TCG_NO_SOLVER_SERVER").is_none());
                            assert_eq!(
                                trust_cg_process_env::var_os("TCG_PROOF_CERT_STORE").unwrap(),
                                cwd.join("relative-certs").as_os_str()
                            );
                            assert_eq!(
                                trust_cg_process_env::var_os("TCG_PROOF_CACHE_DIR").unwrap(),
                                cwd.join("relative-cache").as_os_str()
                            );
                        });
                        assert_eq!(
                            trust_cg_process_env::var("TRUST_CG_AY_TIMEOUT_MS").unwrap(),
                            "9999"
                        );
                    })
                })
                .join()
                .unwrap();
            })
        });
    }

    /// X-HOST-P13 second audit: the request froze an empty or relative
    /// `XDG_CACHE_HOME` (and an empty `HOME`) anchored to its working
    /// directory, so inside every request AY's private copy resolved below
    /// the checkout while process-level admission resolved `$HOME/.cache`.
    /// The request now freezes both exactly as given, and every cache root
    /// below them resolves by `private_fs::user_cache_base` inside the
    /// request exactly as outside it; only the explicit roots
    /// (`TCG_PROOF_CERT_STORE`, `TCG_PROOF_CACHE_DIR`) are anchored.
    #[test]
    fn request_cache_roots_resolve_as_the_process_does_and_never_the_working_directory() {
        let child_env = SanitizedChildEnv::capture_verifier();
        let cwd = child_env.working_dir().unwrap();
        let base = trust_cg_process_env::private_fs::current_user_cache_base;
        trust_cg_process_env::with_env_edits(|env| {
            env.remove("TCG_NO_CERT_STORE");
            env.remove("TCG_NO_PROOF_CACHE");
            env.remove("TCG_PROOF_CERT_STORE");
            env.remove("TCG_PROOF_CACHE_DIR");
            for (xdg, home, store) in [
                (Some(" relative-xdg "), "/home/u", Some("/home/u/.cache")),
                (Some(" \t "), "/home/u", Some("/home/u/.cache")),
                (Some(""), "/home/u", Some("/home/u/.cache")),
                (Some("relative"), "/home/u", Some("/home/u/.cache")),
                (None, "/home/u", Some("/home/u/.cache")),
                (Some("/xdg"), "relative-home", Some("/xdg")),
                (Some("relative"), "relative-home", None),
                (Some(""), "", None),
                (None, "relative-home", None),
            ] {
                match xdg {
                    Some(xdg) => env.set("XDG_CACHE_HOME", xdg),
                    None => env.remove("XDG_CACHE_HOME"),
                }
                env.set("HOME", home);
                let outside = base();
                let policy = capture_policy(&child_env);
                with_policy(&policy, || {
                    let case = format!("XDG_CACHE_HOME={xdg:?} HOME={home:?}");
                    assert_eq!(base(), outside, "{case}");
                    assert_eq!(
                        trust_cg_process_env::var_os("XDG_CACHE_HOME"),
                        xdg.map(std::ffi::OsString::from),
                        "frozen as given: {case}"
                    );
                    assert_eq!(
                        trust_cg_process_env::var_os("HOME").unwrap(),
                        home,
                        "frozen as given: {case}"
                    );
                    match store {
                        Some(store) => {
                            assert_eq!(outside.as_deref(), Ok(std::path::Path::new(store)));
                            assert_eq!(
                                trust_cg_process_env::var_os("TCG_PROOF_CERT_STORE").unwrap(),
                                std::path::Path::new(store)
                                    .join("trust-cg/alethe-certs")
                                    .as_os_str(),
                                "{case}"
                            );
                            assert!(trust_cg_process_env::var_os("TCG_NO_CERT_STORE").is_none());
                        }
                        None => {
                            assert!(outside.is_err(), "{case}");
                            assert!(trust_cg_process_env::var_os("TCG_PROOF_CERT_STORE").is_none());
                            assert!(trust_cg_process_env::var_os("TCG_NO_CERT_STORE").is_some());
                            assert!(
                                trust_cg_process_env::var_os("TCG_NO_PROOF_CACHE").is_none(),
                                "no root is not a global cache-disable policy"
                            );
                        }
                    }
                });
            }

            env.remove("XDG_CACHE_HOME");
            env.set("HOME", "/home/u");
            env.set("TCG_PROOF_CACHE_DIR", "");
            let policy = capture_policy(&child_env);
            with_policy(&policy, || {
                assert!(trust_cg_process_env::var_os("XDG_CACHE_HOME").is_none());
                // An explicitly empty proof-cache root still means the CWD.
                assert_eq!(
                    trust_cg_process_env::var_os("TCG_PROOF_CACHE_DIR").unwrap(),
                    cwd.join("").as_os_str()
                );
                assert_eq!(
                    trust_cg_process_env::var_os("TCG_PROOF_CERT_STORE").unwrap(),
                    "/home/u/.cache/trust-cg/alethe-certs"
                )
            });

            env.set("XDG_CACHE_HOME", " padded-ignored ");
            env.set("TCG_PROOF_CERT_STORE", " explicit-root ");
            let policy = capture_policy(&child_env);
            with_policy(&policy, || {
                assert_eq!(
                    trust_cg_process_env::var_os("TCG_PROOF_CERT_STORE").unwrap(),
                    cwd.join(" explicit-root ").as_os_str()
                )
            });

            // An explicitly empty store path historically means the CWD.
            env.set("TCG_PROOF_CERT_STORE", "");
            let policy = capture_policy(&child_env);
            with_policy(&policy, || {
                assert_eq!(
                    trust_cg_process_env::var_os("TCG_PROOF_CERT_STORE").unwrap(),
                    cwd.join("").as_os_str()
                )
            });

            env.remove("TCG_PROOF_CERT_STORE");
            env.set("HOME", "");
            env.set("XDG_CACHE_HOME", " \t ");
            let policy = capture_policy(&child_env);
            with_policy(&policy, || {
                // An empty HOME is frozen empty (no cache), not the CWD.
                assert_eq!(trust_cg_process_env::var_os("HOME").unwrap(), "");
                assert!(base().is_err());
                assert!(trust_cg_process_env::var_os("TCG_PROOF_CERT_STORE").is_none());
                assert!(trust_cg_process_env::var_os("TCG_NO_CERT_STORE").is_some());
            });
        });
    }

    #[cfg(unix)]
    struct TransportFixture {
        _dir: tempfile::TempDir,
        solver_a: std::path::PathBuf,
        solver_b: std::path::PathBuf,
        // The unit-test fixture declaration admitting exactly these two
        // solver executables' bytes (see `ay_identity::test_fixtures`).
        solver_declaration: String,
        checker_a: std::path::PathBuf,
        checker_b: std::path::PathBuf,
    }

    #[cfg(unix)]
    impl TransportFixture {
        fn new() -> Self {
            Self::with_solver_gate("")
        }
        /// The fixture with `gate` (shell lines that may answer for a query and
        /// exit before the transport proof is written) at the top of both
        /// solvers, after their argument check.
        fn with_solver_gate(gate: &str) -> Self {
            use std::os::unix::fs::PermissionsExt;
            let dir = tempfile::tempdir().unwrap();
            // Each is a new file, started once before the five-second
            // deadlines below (`test_fixtures::warm`; the guard answers that
            // start before anything is counted).
            let script = |name, body: &str| {
                use crate::ay_identity::test_fixtures::{bind_self, warm, warm_guard};
                let path = dir.path().join(name);
                std::fs::write(
                    &path,
                    bind_self(&path, &format!("#!/bin/sh\n{}\n{body}\n", warm_guard())),
                )
                .unwrap();
                std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
                warm(&path);
                path
            };
            // These counted processes qualify transport/receipt plumbing only.
            // The checker transcript is deliberately synthetic, not a proof.
            let checker = r#"printf '%s\n' "$GOVERN_AY_MB" >> "$0.calls"
printf 'External certificate verification: PASSED\nType: Alethe SMT proof\nProof status: fully verified\n'"#;
            let solver = format!(
                r#"test "$#" = 7 && test "$1" = -smt2 && test "$3" = --strict-proofs &&
test "$4" = --proof && test "$5" = "$2.alethe" && test "$6" = --proof-format && test "$7" = alethe || exit 91
printf '%s\n' "$GOVERN_AY_MB" >> "$0.calls"
{gate}
printf 'transport-only fixture proof\n' > "$5"
printf 'unsat\n'"#
            );
            let solver_a = script("solver-a", &solver);
            let solver_b = script("solver-b", &format!("# B executable\n{solver}"));
            // The override admits only these declared bytes (the same rule as
            // production, with the fixtures as the recorded AY).
            let solver_declaration =
                crate::ay_identity::test_fixtures::declare(&[&solver_a, &solver_b]);
            let checker_a = script("checker-a", checker);
            let checker_b = script("checker-b", checker);
            Self {
                _dir: dir,
                solver_a,
                solver_b,
                solver_declaration,
                checker_a,
                checker_b,
            }
        }
        fn a<T>(&self, f: impl FnOnce() -> T) -> T {
            trust_cg_process_env::with_env_edits(|env| {
                env.set("AY_SOLVER_PATH", &self.solver_a);
                env.set(
                    crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV,
                    &self.solver_declaration,
                );
                env.set("TCG_EXTERNAL_CLEAN_CHECKER", &self.checker_a);
                env.set("GOVERN_AY_MB", "128");
                env.set("TCG_NO_SOLVER_SERVER", "1");
                env.set("TCG_NO_CERT_STORE", "1");
                env.set("TCG_CANARY_NO_CACHE", "1");
                env.set("TCG_NO_VERDICT_DB", "1");
                env.set("TCG_BLOCKING_IDENTITY", "1");
                env.set("TCG_REFINE_SOLVER", "1");
                env.set("TCG_RECON_SOLVER_MS", "5000");
                env.set("TRUST_CG_AY_TIMEOUT_MS", "5000");
                env.remove("TCG_NO_PROOF_CACHE");
                f()
            })
        }
        fn b<T>(&self, f: impl FnOnce() -> T) -> T {
            trust_cg_process_env::with_env_edits(|env| {
                env.set("AY_SOLVER_PATH", &self.solver_b);
                env.set(
                    crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV,
                    &self.solver_declaration,
                );
                env.set("TCG_EXTERNAL_CLEAN_CHECKER", &self.checker_b);
                env.set("GOVERN_AY_MB", "256");
                env.set("TCG_REFINE_SOLVER", "0");
                f()
            })
        }
        fn calls(path: &std::path::Path) -> Vec<String> {
            std::fs::read_to_string(path.with_extension("calls"))
                .unwrap_or_default()
                .lines()
                .map(str::to_owned)
                .collect()
        }
    }

    /// The live replay authority captured in a request is the one that runs,
    /// even from a large-stack worker under a different ambient solver (A/B/A).
    /// The vehicle is the source-bound framed leaf `x0 + x1`: its frame
    /// envelope and its arithmetic are the obligations a proof-promotion
    /// verifier still replays live. (Registry theorems were the vehicle before
    /// substring credit was withdrawn; they no longer reach any solver, which
    /// the first assertions pin.)
    #[cfg(unix)]
    #[test]
    fn request_aarch64_captured_authority_survives_large_stack_worker_and_a_b_a() {
        use trust_cg_ir::aarch64_regs::{X0, X1, X2};
        let _serial = crate::ay_bridge::formal_solver_test_lock();
        let fixture = TransportFixture::new();
        fixture.a(|| {
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let (source, function) = crate::source_bound_alu::tests::fixture(
                64,
                AArch64Opcode::AddRR,
                MachOperand::PReg(X1),
            );
            let off = verifier.capture_request_with_mode(ProvenanceXCheckMode::Off);
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            assert!(off.reuse_identity().is_some());
            assert!(request.reuse_identity().is_some());
            for empty in [
                a64(vec![]),
                a64(vec![MachInst::new(AArch64Opcode::Nop, vec![])]),
            ] {
                let uncredited = verifier.verify_with_request(&empty, None, &off);
                assert_eq!(uncredited.report().genuinely_verified_count(), 0);
                assert!(
                    !uncredited.reusable_for(&off),
                    "ready authority cannot lend credit to an empty/skip-only report"
                );
            }
            // Withdrawn credit replays nothing live (E0.2/E0.5): a registry
            // candidate (ADRP to a symbol), an instruction-derived obligation
            // (MOVK, L07-P2) and a sampled 64-bit reconstruction stay
            // unverified and never reach the solver.
            let adrp = verifier.verify_with_request(
                &a64(vec![MachInst::new(
                    AArch64Opcode::Adrp,
                    vec![MachOperand::PReg(X0), MachOperand::Symbol("g".into())],
                )]),
                None,
                &off,
            );
            assert_eq!(adrp.report().registry_name_lookup_count(), 1);
            assert!(!adrp.reusable_for(&off));
            let movk = verifier.verify_with_request(
                &a64(vec![MachInst::new(
                    AArch64Opcode::Movk,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::Imm(7),
                        MachOperand::Imm(16),
                    ],
                )]),
                None,
                &off,
            );
            assert_eq!(movk.report().instruction_derived_count(), 1);
            assert!(!movk.reusable_for(&off));
            let sampled = verifier.verify_with_request(
                &a64(vec![MachInst::new(
                    AArch64Opcode::AddRR,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X1),
                        MachOperand::PReg(X2),
                    ],
                )]),
                None,
                &off,
            );
            assert_eq!(sampled.report().sampled_uncredited_count(), 1);
            assert!(
                !sampled.reusable_for(&off),
                "target-only reconstruction must stay non-Formal"
            );
            assert!(TransportFixture::calls(&fixture.solver_a).is_empty());
            let checker_before = TransportFixture::calls(&fixture.checker_a).len();
            let report = std::thread::scope(|scope| {
                std::thread::Builder::new()
                    .stack_size(64 * 1024 * 1024)
                    .spawn_scoped(scope, || {
                        fixture
                            .b(|| verifier.verify_with_request(&function, Some(&source), &request))
                    })
                    .unwrap()
                    .join()
                    .unwrap()
            });
            // Frame envelope (STP, MOV, LDP) and the ADD are replayed; RET is
            // covered elsewhere.
            assert_eq!(
                report.report().formally_credited_count(),
                4,
                "{:?}",
                report.report()
            );
            assert!(report.reusable_for(&request), "{:?}", report.report());
            let a_calls = TransportFixture::calls(&fixture.solver_a);
            assert!(!a_calls.is_empty() && a_calls.iter().all(|v| v == "128"));
            assert!(TransportFixture::calls(&fixture.solver_b).is_empty());
            assert!(TransportFixture::calls(&fixture.checker_a).len() > checker_before);
            assert!(
                TransportFixture::calls(&fixture.checker_a)
                    .iter()
                    .all(|v| v == "128")
            );
            let b = fixture.b(|| verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce));
            assert!(!report.reusable_for(&b));
            let warm =
                fixture.b(|| verifier.verify_with_request(&function, Some(&source), &request));
            assert!(warm.reusable_for(&request));
            assert!(
                TransportFixture::calls(&fixture.solver_b).is_empty(),
                "a repeated walk must still use the captured A authority"
            );
            let mut changed = function.clone();
            changed.insts[2].operands[2] = MachOperand::PReg(X2);
            assert!(!report.matches_aarch64_input(&changed, Some(&source)));
            assert!(
                report
                    .clone()
                    .matches_aarch64_input(&function, Some(&source))
            );

            // A real fresh no-cache solve still uses the captured A tool and
            // environment, but cannot carry reusable evidence.
            let before_no_cache = TransportFixture::calls(&fixture.solver_a).len();
            trust_cg_process_env::with_env_overrides(&[("TCG_NO_PROOF_CACHE", "1")], || {
                let no_cache = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
                let fresh =
                    fixture.b(|| verifier.verify_with_request(&function, Some(&source), &no_cache));
                assert_eq!(fresh.report().formally_credited_count(), 4);
                assert!(!fresh.reusable_for(&no_cache));
                assert!(no_cache.reuse_identity().is_none());
            });
            assert!(TransportFixture::calls(&fixture.solver_a).len() > before_no_cache);
            assert!(TransportFixture::calls(&fixture.solver_b).is_empty());

            // Identity unavailability is distinct from the no-cache policy:
            // force the real cold-hash branch, retain A's launch snapshot, and
            // use another source-bound body (`x0 - x1`) so no session proof
            // cache entry from the steps above can hide a solver call.
            let (different_source, different) = crate::source_bound_alu::tests::fixture(
                64,
                AArch64Opcode::SubRR,
                MachOperand::PReg(X1),
            );
            let before_unavailable = TransportFixture::calls(&fixture.solver_a).len();
            let mut unavailable = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            unavailable.ay = unavailable.ay.without_ready_identity();
            unavailable.identity = None;
            let fresh = fixture.b(|| {
                verifier.verify_with_request(&different, Some(&different_source), &unavailable)
            });
            assert_eq!(fresh.report().formally_credited_count(), 4);
            assert!(!fresh.reusable_for(&unavailable));
            assert!(!fresh.reusable_for(&request));
            assert!(TransportFixture::calls(&fixture.solver_a).len() > before_unavailable);
            assert!(
                TransportFixture::calls(&fixture.solver_a)
                    .iter()
                    .all(|v| v == "128")
            );
            assert!(TransportFixture::calls(&fixture.solver_b).is_empty());
        });
    }

    /// A frame record is credited by the replayed frame theorem AND a
    /// Clean-checked certificate of every memory-effect part of its word
    /// (L07-P2), through the walk itself: with a solver that proves the frame
    /// theorem (the only query that declares `entry_fp`) and answers `unknown`
    /// for everything else, the save and restore records stay `Unverified`,
    /// naming the checked theorem and the first part without a certificate,
    /// while the establishing ADD keeps the theorem's credit. The same walk
    /// with every query proved credits them
    /// (`request_aarch64_captured_authority_survives_large_stack_worker_and_a_b_a`).
    #[cfg(unix)]
    #[test]
    fn request_aarch64_frame_records_need_their_parts_beside_the_replayed_theorem() {
        use crate::aarch64_memory_source_binding::SOURCE_BOUND_MEMORY_NOT_CREDITED;
        use crate::function_verifier::InstructionVerificationResult;
        use crate::source_bound_frame::FRAME_OBLIGATION_NAME;
        use trust_cg_ir::aarch64_regs::X1;
        let _serial = crate::ay_bridge::formal_solver_test_lock();
        let fixture = TransportFixture::with_solver_gate(
            "grep -q 'declare-const entry_fp ' \"$2\" || { printf 'unknown\\n'; exit 0; }",
        );
        fixture.a(|| {
            // No positive or negative memo may stand in for a live replay.
            trust_cg_process_env::with_env_overrides(&[("TCG_NO_PROOF_CACHE", "1")], || {
                let verifier =
                    FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
                let (source, function) = crate::source_bound_alu::tests::fixture(
                    64,
                    AArch64Opcode::AddRR,
                    MachOperand::PReg(X1),
                );
                let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
                let captured = verifier.verify_with_request(&function, Some(&source), &request);
                let report = captured.report();
                assert!(report.precondition_failure.is_none(), "{report:?}");
                assert!(
                    matches!(
                        &report.instructions[1].result,
                        InstructionVerificationResult::Verified {
                            proof_name,
                            strength: crate::verify::VerificationStrength::Formal,
                            ..
                        }
                            if proof_name == FRAME_OBLIGATION_NAME
                    ),
                    "the establishing ADD keeps the replayed theorem: {:?}",
                    report.instructions[1].result
                );
                for (index, role, word) in [
                    (0, "save", "StpPreIndex 0xa9bf7bfd"),
                    (3, "restore", "LdpPostIndex 0xa8c17bfd"),
                ] {
                    let InstructionVerificationResult::Unverified { reason } =
                        &report.instructions[index].result
                    else {
                        panic!("{role}: {:?}", report.instructions[index].result);
                    };
                    assert_eq!(
                        reason,
                        &format!(
                            "{SOURCE_BOUND_MEMORY_NOT_CREDITED}: the frame theorem has a checked \
                             proof; `A64 memory effect {word}` bound to the source-bound frame's \
                             {role} record; holds in process: all 6 parts exactly; 0 of 6 parts \
                             have a Clean-checked certificate; the first without one is `fields` \
                             (AY UNKNOWN: unknown)"
                        ),
                    );
                }
                assert!(!report.emitted_opcode_inventory().is_promotable());
                assert!(!captured.reusable_for(&request));
            });
            assert!(
                !TransportFixture::calls(&fixture.solver_a).is_empty(),
                "the theorem and the parts were replayed live"
            );
        });
    }

    /// E0.5 on x86-64: the nested distinct-key pre-pass used to replay registry
    /// theorems through the captured solver from parallel workers. With
    /// registry credit withdrawn the x86-64 walk replays nothing live, so a
    /// proof-promotion verifier over 16 registry candidates spawns no solver
    /// (ambient or captured) and credits nothing.
    #[cfg(unix)]
    #[test]
    fn request_x86_registry_candidates_replay_nothing_live() {
        let _serial = crate::ay_bridge::formal_solver_test_lock();
        let fixture = TransportFixture::new();
        fixture.a(|| {
            let verifier =
                X86FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            // At least 16 instructions and two distinct queries reach the
            // nested pre-pass, not only a root worker.
            let function = x86((0..16)
                .map(|index| {
                    X86ISelInst::new(
                        if index % 2 == 0 {
                            X86Opcode::MovsdRR
                        } else {
                            X86Opcode::MovssRR
                        },
                        vec![
                            X86ISelOperand::VReg(trust_cg_ir::VReg::new(
                                0,
                                trust_cg_ir::RegClass::Fpr128,
                            )),
                            X86ISelOperand::VReg(trust_cg_ir::VReg::new(
                                1,
                                trust_cg_ir::RegClass::Fpr128,
                            )),
                        ],
                    )
                })
                .collect());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Off);
            for _ in 0..2 {
                let report = fixture.b(|| verifier.verify_with_request(&function, None, &request));
                assert_eq!(report.report().instructions.len(), 16);
                assert_eq!(
                    report.report().registry_name_lookup_count(),
                    16,
                    "{:?}",
                    report.report()
                );
                assert_eq!(report.report().verified_count(), 0);
                assert!(!report.reusable_for(&request));
                assert!(report.matches_x86_input(&function, None, None));
                assert!(!report.matches_x86_input(
                    &function,
                    None,
                    Some(crate::X86SourceBoundAbi::SystemV)
                ));
            }
            assert!(TransportFixture::calls(&fixture.solver_a).is_empty());
            assert!(TransportFixture::calls(&fixture.solver_b).is_empty());
        });
    }
}
