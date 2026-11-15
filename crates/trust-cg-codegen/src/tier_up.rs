// trust-cg-codegen - JIT tier-up over the compile service
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! JIT tier-up: install a cheap tier now, compile higher tiers in the
//! background, and hand each one to the consumer to install where it knows no
//! call is in flight.
//!
//! A JIT consumer pays compile latency before its first native call and
//! execution cost on every call after it. One optimization level cannot serve
//! both: a short run wants the cheapest compile, a long run wants the best
//! code, and a consumer that must pick one level up front either spends a
//! large compile on a run that ends quickly or runs slow code for a long time.
//! [`TierUpSession`] removes that choice. It compiles tier 0 of a
//! [`TierPlan`] on the caller's thread and returns it, then compiles each
//! higher tier on one background worker — after tier 0
//! ([`TierUpSession::start`]), concurrently with it
//! ([`TierUpSession::start_concurrent`]), or when the consumer says the code
//! is hot ([`TierUpSession::start_on_demand`] + [`TierUpSession::promote`]) —
//! and delivers it through [`TierUpSession::poll`] / [`TierUpSession::wait`]
//! or to a background installer ([`TierUpSession::install_with`]).
//!
//! # One request model
//!
//! Every tier is an ordinary compile-service [`CompileRequest`]: the base
//! request's generation, stale-generation fence, proof policy, provenance,
//! manifest and install intent, with the tier's optimization level. Two
//! fields are deliberately NOT inherited by tiers above 0: the caller's
//! [`CompileRequest::proof_tv_evidence`] (it attests one artifact, not every
//! optimization level of its source) and the cancellation token (each session
//! owns one, so [`TierUpSession::cancel`] stops only its own ladder; the base
//! token is still observed). A tier is delivered only while its request is
//! neither cancelled nor stale, checked before the tier compiles, after it
//! compiles, and again when the consumer polls — so a consumer that calls
//! [`CompileGenerationFence::mark_stale_before`] on its fence never receives
//! an artifact compiled for the superseded generation.
//!
//! [`ServiceTierBackend`] compiles a `trust_ir::Module` through
//! [`CompileService`], so each tier passes the same admission, stale/cancel
//! gates, proof-policy, install-disposition, payload-binding and
//! native-install-gate checks as any synchronous executable-memory compile
//! of the same request, and is delivered as an [`InstalledArtifact`]. A frontend with its own JIT driver implements
//! [`TierBackend`] instead and gets the same scheduling, gating and
//! refusal model for its own artifact type.
//!
//! # Invariants of every delivered tier
//!
//! * **Monotone.** Tiers arrive in plan order and a delivered tier is always
//!   higher than every tier delivered before it. The ladder stops at the
//!   first refused rung.
//! * **Same source.** A tier's source identity (for [`ServiceTierBackend`],
//!   the compiler-derived TrustIR module digest of its installed payload
//!   binding) equals tier 0's.
//! * **Same callable surface.** A tier exports exactly tier 0's entry points
//!   with tier 0's signatures, so every symbol the consumer bound stays
//!   resolvable, with the same ABI, in every tier.
//! * **Fail to the installed tier.** A higher tier that fails, is refused,
//!   is cancelled or goes stale is reported by name ([`TierRefusal::code`])
//!   and never disturbs the tier already installed; a worker that cannot be
//!   started, or panics, is reported the same way. Tier-up never takes a
//!   working tier away from the consumer.
//!
//! # What it does not do
//!
//! * It does not swap code under a running caller. The consumer installs a
//!   delivered tier at its own safe point, or through [`TierEntryTable`],
//!   which publishes new entry addresses atomically and keeps every installed
//!   tier's code mapped for the table's lifetime.
//! * It does not decide whether a higher tier pays off. A higher tier costs a
//!   background compile; a run that ends before it arrives spent that compile
//!   for nothing. The plan is the consumer's call.
//! * It does not interrupt a backend compile in progress. Cancellation is
//!   observed at the request gates, so [`TierUpSession::shutdown`] waits for
//!   the in-progress tier to finish; dropping the session cancels and
//!   detaches instead.

use std::collections::HashMap;
use std::fmt;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError, mpsc};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use serde_json::{Value, json};

use crate::async_compile_service::AsyncCompileState;
use crate::compile_service::{
    ArtifactInstallDisposition, ArtifactKind, CancellationToken, CompileDiagnostic,
    CompileGeneration, CompileGenerationFence, CompilePlan, CompileProfile, CompileRequest,
    CompileRequestId, CompileResponse, CompileService, CompileStatus, InstalledArtifact,
    RawExternBinding,
};
use crate::jit::{JitError, JitLeasedPtr, ensure_jit_execute_mode};
use crate::jit_contract::{SymbolSignature, SymbolVisibility};
use crate::pipeline::OptLevel;
use crate::target::TargetSpec;

/// Largest number of tiers one plan may carry (one per optimization level).
pub const TIER_UP_MAX_TIERS: usize = 4;

/// Stable schema tag of [`TierUpReport::to_json_value`].
pub const TIER_UP_REPORT_SCHEMA: &str = "trust-cg.tier_up.report.v1";

/// Stack reserved for the background worker. Compilation recurses through
/// the same passes as the compiler's own large-stack workers, so it gets the
/// same 16 MiB (`compiler.rs` spawns its proof workers with this size).
const TIER_UP_WORKER_STACK_BYTES: usize = 16 * 1024 * 1024;

/// Total order of optimization levels, O0 lowest.
pub const fn opt_level_rank(level: OptLevel) -> u8 {
    match level {
        OptLevel::O0 => 0,
        OptLevel::O1 => 1,
        OptLevel::O2 => 2,
        OptLevel::O3 => 3,
    }
}

/// Stable spelling of an optimization level (`"O0"` .. `"O3"`).
pub const fn opt_level_name(level: OptLevel) -> &'static str {
    match level {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
        OptLevel::O3 => "O3",
    }
}

// ---------------------------------------------------------------------------
// Plan
// ---------------------------------------------------------------------------

/// Ordered optimization levels for one module: tier 0 compiles on the
/// caller's thread, every later tier in the background.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TierPlan {
    levels: Vec<OptLevel>,
}

/// Why a [`TierPlan`] was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TierPlanError {
    /// A plan needs at least one tier.
    Empty,
    /// More tiers than there are optimization levels.
    TooManyTiers {
        /// Tiers requested.
        count: usize,
    },
    /// Levels must strictly increase: a tier that is not better than the one
    /// before it would cost a compile and could never be installed.
    NotIncreasing {
        /// Index of the offending tier.
        index: usize,
        /// The level before it.
        previous: OptLevel,
        /// Its level.
        level: OptLevel,
    },
}

impl fmt::Display for TierPlanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => write!(f, "a tier plan needs at least one tier"),
            Self::TooManyTiers { count } => write!(
                f,
                "a tier plan carries at most {TIER_UP_MAX_TIERS} tiers, got {count}"
            ),
            Self::NotIncreasing {
                index,
                previous,
                level,
            } => write!(
                f,
                "tier {index} ({}) does not raise the optimization level above tier {} ({})",
                opt_level_name(*level),
                index - 1,
                opt_level_name(*previous)
            ),
        }
    }
}

impl std::error::Error for TierPlanError {}

impl TierPlan {
    /// Build a plan from strictly increasing optimization levels.
    pub fn new(levels: impl IntoIterator<Item = OptLevel>) -> Result<Self, TierPlanError> {
        let levels: Vec<OptLevel> = levels.into_iter().collect();
        if levels.is_empty() {
            return Err(TierPlanError::Empty);
        }
        if levels.len() > TIER_UP_MAX_TIERS {
            return Err(TierPlanError::TooManyTiers {
                count: levels.len(),
            });
        }
        for (index, pair) in levels.windows(2).enumerate() {
            if opt_level_rank(pair[1]) <= opt_level_rank(pair[0]) {
                return Err(TierPlanError::NotIncreasing {
                    index: index + 1,
                    previous: pair[0],
                    level: pair[1],
                });
            }
        }
        Ok(Self { levels })
    }

    /// A plan with one tier: no background work, exactly an ordinary compile.
    pub fn single(level: OptLevel) -> Self {
        Self {
            levels: vec![level],
        }
    }

    /// The levels, tier 0 first.
    pub fn levels(&self) -> &[OptLevel] {
        &self.levels
    }

    /// Number of tiers (at least one).
    pub fn len(&self) -> usize {
        self.levels.len()
    }

    /// Always false: a plan has at least one tier.
    pub fn is_empty(&self) -> bool {
        self.levels.is_empty()
    }

    /// Tier 0's level.
    pub fn baseline(&self) -> OptLevel {
        self.levels[0]
    }

    /// The highest tier's level.
    pub fn top(&self) -> OptLevel {
        self.levels[self.levels.len() - 1]
    }

    /// Index of the highest tier.
    pub fn top_tier(&self) -> usize {
        self.levels.len() - 1
    }
}

// ---------------------------------------------------------------------------
// Backend contract
// ---------------------------------------------------------------------------

/// One tier's compile request, as a [`TierBackend`] receives it.
#[derive(Debug, Clone)]
pub struct TierRequest {
    /// Tier index in the plan (0 = the caller-thread tier).
    pub tier: usize,
    /// The tier's optimization level.
    pub opt_level: OptLevel,
    /// The compile-service request for this tier: the base request with this
    /// tier's id, profile and cancellation (see the module docs).
    pub request: CompileRequest,
}

/// Derive a tier's compile-service request from the caller's base request.
///
/// Tier 0 keeps the base request's id and cancellation token; a higher tier
/// gets `"<base id>#tier<k>-O<n>"`, the session's token and no
/// `proof_tv_evidence`. The profile keeps the base profile when its compiler
/// already runs at `opt_level`, and otherwise becomes the base profile's
/// expansion with only the optimization level changed, so tier 0 of a plan
/// whose baseline equals the request's level is exactly the caller's ordinary
/// compile.
pub fn tier_request(
    base: &CompileRequest,
    tier: usize,
    opt_level: OptLevel,
    cancellation: CancellationToken,
) -> CompileRequest {
    let mut request = base.clone();
    request.profile = tier_profile(&base.profile, opt_level);
    if tier > 0 {
        request.request_id = CompileRequestId::new(format!(
            "{}#tier{tier}-{}",
            base.request_id.as_str(),
            opt_level_name(opt_level)
        ));
        request.proof_tv_evidence = None;
        request.cancellation = cancellation;
    }
    request
}

fn tier_profile(base: &CompileProfile, opt_level: OptLevel) -> CompileProfile {
    let expanded = base.expand();
    if expanded.compiler.opt_level == opt_level && expanded.jit.opt_level == opt_level {
        return base.clone();
    }
    let mut compiler = expanded.compiler;
    compiler.opt_level = opt_level;
    let mut jit = expanded.jit;
    jit.opt_level = opt_level;
    CompileProfile::Custom { compiler, jit }
}

/// One callable entry point of a tier: its symbol and a backend-defined
/// signature identity. Two tiers are call-compatible exactly when their
/// export sets are equal.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TierExport {
    /// Canonical symbol name.
    pub symbol: String,
    /// Backend-defined identity of the entry point's ABI signature.
    pub signature: String,
}

impl TierExport {
    /// An export with the given symbol and signature identity.
    pub fn new(symbol: impl Into<String>, signature: impl Into<String>) -> Self {
        Self {
            symbol: symbol.into(),
            signature: signature.into(),
        }
    }
}

/// A compiled tier as its backend returns it.
#[derive(Debug)]
pub struct TierOutput<A> {
    /// The installable artifact.
    pub artifact: A,
    /// Every callable entry point of the artifact.
    pub exports: Vec<TierExport>,
    /// Identity of the source the tier was compiled from, when the backend
    /// can state one. Every tier must report tier 0's.
    pub source_identity: Option<String>,
}

/// A tier the backend did not produce, or produced but may not install.
#[derive(Debug, Clone)]
pub struct TierFailure {
    /// The compile-service state the tier ended in.
    pub state: AsyncCompileState,
    /// Why, with the compile service's own diagnostic codes.
    pub diagnostics: Vec<CompileDiagnostic>,
}

impl TierFailure {
    /// A failure with explicit diagnostics.
    pub fn new(state: AsyncCompileState, diagnostics: Vec<CompileDiagnostic>) -> Self {
        Self { state, diagnostics }
    }

    /// A failure with one error diagnostic.
    pub fn with_error(
        state: AsyncCompileState,
        code: &'static str,
        message: impl Into<String>,
    ) -> Self {
        Self {
            state,
            diagnostics: vec![CompileDiagnostic::error(code, message).with_phase("tier_up")],
        }
    }

    /// The first diagnostic code, or the state when there is none.
    pub fn code(&self) -> &'static str {
        self.diagnostics
            .first()
            .map(|diagnostic| diagnostic.code)
            .unwrap_or_else(|| self.state.as_str())
    }

    fn detail(&self) -> String {
        match self.diagnostics.first() {
            Some(diagnostic) => format!(
                "{} ({}): {}",
                diagnostic.code,
                self.state.as_str(),
                diagnostic.message
            ),
            None => self.state.as_str().to_owned(),
        }
    }
}

/// Compiles one tier of one source.
///
/// Implementations compile the source they own at `tier.opt_level` under
/// `tier.request` — the request is what carries the tier's generation,
/// fence, cancellation and proof policy, so a backend that routes through the
/// compile service ([`ServiceTierBackend`]) gets the service's gates for
/// free, and one that does not must honour the same fields. Tier 0 runs on
/// the caller's thread; every later tier on the session's worker, which owns
/// the backend from then on.
pub trait TierBackend: Send + 'static {
    /// The installable artifact one tier produces.
    type Artifact: Send + 'static;

    /// Compile one tier.
    fn compile_tier(
        &mut self,
        tier: &TierRequest,
    ) -> Result<TierOutput<Self::Artifact>, TierFailure>;
}

// ---------------------------------------------------------------------------
// Delivery
// ---------------------------------------------------------------------------

/// Why a higher tier was not delivered. The installed tier is unaffected.
#[derive(Debug, Clone)]
pub enum TierRefusal {
    /// The backend failed or the compile service would not install the tier.
    Failed(TierFailure),
    /// The tier was compiled from a different source than tier 0.
    SourceMismatch {
        /// Tier 0's source identity.
        expected: Option<String>,
        /// The tier's source identity.
        actual: Option<String>,
    },
    /// The tier's callable surface differs from tier 0's.
    ExportMismatch {
        /// Tier 0 exports the tier lacks (or exports with another signature).
        missing: Vec<TierExport>,
        /// Tier exports tier 0 lacks (or exports with another signature).
        unexpected: Vec<TierExport>,
    },
    /// The session or the base request was cancelled.
    Cancelled,
    /// The base request's generation became stale.
    Stale,
    /// The background worker could not be started.
    WorkerUnavailable {
        /// The spawn error.
        detail: String,
    },
    /// The backend panicked, or the worker ended without reporting the tier.
    WorkerPanicked {
        /// The panic payload, when it was a string.
        detail: String,
    },
    /// The consumer's installer ([`TierUpSession::install_with`]) refused
    /// the delivered tier; the previously installed tier stays.
    InstallFailed {
        /// The installer's reason.
        detail: String,
    },
}

impl TierRefusal {
    /// Stable lower-snake-case refusal code.
    pub fn code(&self) -> &'static str {
        match self {
            Self::Failed(_) => "tier_up.failed",
            Self::SourceMismatch { .. } => "tier_up.source_mismatch",
            Self::ExportMismatch { .. } => "tier_up.export_mismatch",
            Self::Cancelled => "tier_up.cancelled",
            Self::Stale => "tier_up.stale_generation",
            Self::WorkerUnavailable { .. } => "tier_up.worker_unavailable",
            Self::WorkerPanicked { .. } => "tier_up.worker_panicked",
            Self::InstallFailed { .. } => "tier_up.install_failed",
        }
    }

    /// Human-readable detail for logs and reports.
    pub fn detail(&self) -> String {
        match self {
            Self::Failed(failure) => failure.detail(),
            Self::SourceMismatch { expected, actual } => {
                format!("tier 0 source {expected:?}, this tier {actual:?}")
            }
            Self::ExportMismatch {
                missing,
                unexpected,
            } => format!(
                "missing {:?}, unexpected {:?}",
                missing
                    .iter()
                    .map(|export| export.symbol.as_str())
                    .collect::<Vec<_>>(),
                unexpected
                    .iter()
                    .map(|export| export.symbol.as_str())
                    .collect::<Vec<_>>()
            ),
            Self::Cancelled => "cancelled".to_owned(),
            Self::Stale => "generation is stale".to_owned(),
            Self::WorkerUnavailable { detail }
            | Self::WorkerPanicked { detail }
            | Self::InstallFailed { detail } => detail.clone(),
        }
    }
}

impl fmt::Display for TierRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.code(), self.detail())
    }
}

/// A tier ready to install.
#[derive(Debug)]
pub struct TierInstall<A> {
    /// Tier index in the plan.
    pub tier: usize,
    /// The tier's optimization level.
    pub opt_level: OptLevel,
    /// The base request's generation.
    pub generation: CompileGeneration,
    /// Wall time the backend spent compiling this tier.
    pub compile_latency: Duration,
    /// The artifact.
    pub artifact: A,
}

/// Result of polling a [`TierUpSession`].
#[derive(Debug)]
pub enum TierUpPoll<A> {
    /// A higher tier is still compiling.
    Pending,
    /// A higher tier is ready: install it where no call is in flight.
    Upgraded(TierInstall<A>),
    /// A higher tier was refused; the ladder stops and the installed tier
    /// stays.
    Refused {
        /// The refused tier.
        tier: usize,
        /// Its optimization level.
        opt_level: OptLevel,
        /// Why.
        refusal: TierRefusal,
    },
    /// Nothing more will arrive.
    Complete,
}

/// Why tier 0 itself did not compile. No session exists.
#[derive(Debug, Clone)]
pub enum TierStartFailure {
    /// The base request was cancelled or stale before tier 0 compiled.
    Refused(TierRefusal),
    /// The backend failed tier 0.
    Failed(TierFailure),
}

impl fmt::Display for TierStartFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Refused(refusal) => write!(f, "tier 0 refused: {refusal}"),
            Self::Failed(failure) => write!(f, "tier 0 failed: {}", failure.detail()),
        }
    }
}

impl std::error::Error for TierStartFailure {}

/// What happened to one tier of a session.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TierOutcome {
    /// Delivered to the consumer.
    Delivered,
    /// Refused, with [`TierRefusal::code`] and detail.
    Refused {
        /// Stable refusal code.
        code: &'static str,
        /// Detail.
        detail: String,
    },
    /// Still compiling, or never reached because the ladder stopped below it.
    NotDelivered,
}

/// One tier's record in a [`TierUpReport`].
#[derive(Debug, Clone)]
pub struct TierRecord {
    /// Tier index.
    pub tier: usize,
    /// Optimization level.
    pub opt_level: OptLevel,
    /// Backend compile wall time, when the tier was compiled.
    pub compile_latency: Option<Duration>,
    /// Outcome.
    pub outcome: TierOutcome,
}

/// Per-tier account of a session, for logs and evidence.
#[derive(Debug, Clone)]
pub struct TierUpReport {
    /// The base request id.
    pub request_id: CompileRequestId,
    /// The base request's generation.
    pub generation: CompileGeneration,
    /// Highest tier delivered to the consumer.
    pub delivered_tier: usize,
    /// Every tier of the plan, tier 0 first.
    pub tiers: Vec<TierRecord>,
}

impl TierUpReport {
    /// Stable JSON form ([`TIER_UP_REPORT_SCHEMA`]).
    pub fn to_json_value(&self) -> Value {
        json!({
            "schema": TIER_UP_REPORT_SCHEMA,
            "request_id": self.request_id.as_str(),
            "generation": self.generation.get(),
            "delivered_tier": self.delivered_tier,
            "tiers": self.tiers.iter().map(|record| {
                let (outcome, code, detail) = match &record.outcome {
                    TierOutcome::Delivered => ("delivered", None, None),
                    TierOutcome::Refused { code, detail } => {
                        ("refused", Some(*code), Some(detail.as_str()))
                    }
                    TierOutcome::NotDelivered => ("not_delivered", None, None),
                };
                json!({
                    "tier": record.tier,
                    "opt_level": opt_level_name(record.opt_level),
                    "compile_latency_ns": record
                        .compile_latency
                        .map(|latency| u64::try_from(latency.as_nanos()).unwrap_or(u64::MAX)),
                    "outcome": outcome,
                    "code": code,
                    "detail": detail,
                })
            }).collect::<Vec<_>>(),
        })
    }
}

enum TierMessage<A> {
    Compiled {
        tier: usize,
        latency: Duration,
        output: TierOutput<A>,
    },
    Failed {
        tier: usize,
        latency: Duration,
        failure: TierFailure,
    },
    Stopped {
        tier: usize,
        refusal: TierRefusal,
    },
}

/// The request-model checks every hop repeats: the base token, the session
/// token, and the base request's generation against its local and shared
/// stale-before fences (the same rule as the compile service's own gate).
#[derive(Debug, Clone)]
struct TierGate {
    base_cancellation: CancellationToken,
    session_cancellation: CancellationToken,
    generation: CompileGeneration,
    stale_before: Option<CompileGeneration>,
    fence: Option<CompileGenerationFence>,
}

impl TierGate {
    fn refusal(&self) -> Option<TierRefusal> {
        if self.base_cancellation.is_cancelled() || self.session_cancellation.is_cancelled() {
            return Some(TierRefusal::Cancelled);
        }
        let fence = self
            .fence
            .as_ref()
            .map(CompileGenerationFence::stale_before);
        let stale_before = match (self.stale_before, fence) {
            (Some(left), Some(right)) => Some(left.max(right)),
            (Some(generation), None) | (None, Some(generation)) => Some(generation),
            (None, None) => None,
        };
        if stale_before.is_some_and(|stale_before| self.generation < stale_before) {
            return Some(TierRefusal::Stale);
        }
        None
    }
}

/// A module compiled at a cheap tier now and at higher tiers in the
/// background. See the module docs for the model and its invariants.
///
/// Dropping a session cancels its ladder and detaches the worker, which stops
/// at its next request gate; [`Self::shutdown`] cancels and joins.
pub struct TierUpSession<A: Send + 'static> {
    plan: TierPlan,
    request_id: CompileRequestId,
    generation: CompileGeneration,
    gate: TierGate,
    exports: Vec<TierExport>,
    source_identity: Option<String>,
    delivered: usize,
    receiver: Option<mpsc::Receiver<TierMessage<A>>>,
    worker: Option<JoinHandle<()>>,
    /// The ladder of a [`Self::start_on_demand`] session, until
    /// [`Self::promote`] starts it.
    deferred: Option<DeferredLadder<A>>,
    records: Vec<TierRecord>,
    finished: bool,
}

/// Starts a deferred ladder's worker: the backend, base request, levels and
/// gate captured at `start_on_demand`.
type DeferredLadder<A> = Box<dyn FnOnce() -> WorkerSpawn<A> + Send>;

/// When a session's higher tiers start compiling.
enum LadderStart<B> {
    /// After tier 0, on the worker ([`TierUpSession::start`]).
    AfterBaseline,
    /// Before tier 0, on a clone of the backend
    /// ([`TierUpSession::start_concurrent`]).
    Concurrent(B),
    /// When the consumer calls [`TierUpSession::promote`]
    /// ([`TierUpSession::start_on_demand`]).
    OnDemand,
}

impl<A: Send + 'static> fmt::Debug for TierUpSession<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TierUpSession")
            .field("request_id", &self.request_id)
            .field("plan", &self.plan)
            .field("delivered", &self.delivered)
            .field("finished", &self.finished)
            .finish()
    }
}

impl<A: Send + 'static> TierUpSession<A> {
    /// Compile tier 0 of `plan` on this thread, then start the worker for
    /// the higher tiers.
    ///
    /// Returns the session and tier 0, ready to install. Only tier 0 can fail
    /// the call; everything above it is best-effort and reported through
    /// [`Self::poll`]. The higher tiers start after tier 0, so they never
    /// compete with it for the machine; see [`Self::start_concurrent`].
    pub fn start<B>(
        backend: B,
        base: CompileRequest,
        plan: TierPlan,
    ) -> Result<(Self, TierInstall<A>), TierStartFailure>
    where
        B: TierBackend<Artifact = A>,
    {
        Self::launch(backend, LadderStart::AfterBaseline, base, plan)
    }

    /// [`Self::start`], but the worker starts compiling the higher tiers
    /// BEFORE tier 0 compiles on this thread, on a clone of the backend.
    ///
    /// The top tier then arrives one top-tier compile after the call instead
    /// of one tier-0 compile plus one top-tier compile, at the price of the
    /// two compiles running at the same time: use it when the machine has a
    /// core to spare. Tier 0 is still the only thing the call waits for, and
    /// a tier-0 failure cancels the worker (it stops at its next gate).
    pub fn start_concurrent<B>(
        backend: B,
        base: CompileRequest,
        plan: TierPlan,
    ) -> Result<(Self, TierInstall<A>), TierStartFailure>
    where
        B: TierBackend<Artifact = A> + Clone,
    {
        let start = if plan.len() > 1 {
            LadderStart::Concurrent(backend.clone())
        } else {
            LadderStart::AfterBaseline
        };
        Self::launch(backend, start, base, plan)
    }

    /// [`Self::start`], but the higher tiers do not start compiling until the
    /// consumer calls [`Self::promote`] — typically when its own counters say
    /// the code is hot enough to repay a higher tier's compile. A run that
    /// never promotes pays for tier 0 only. Until then [`Self::poll`] reports
    /// `Pending`.
    pub fn start_on_demand<B>(
        backend: B,
        base: CompileRequest,
        plan: TierPlan,
    ) -> Result<(Self, TierInstall<A>), TierStartFailure>
    where
        B: TierBackend<Artifact = A>,
    {
        Self::launch(backend, LadderStart::OnDemand, base, plan)
    }

    /// Start a deferred ladder ([`Self::start_on_demand`]). Returns whether
    /// this call started it; a session that was never deferred, was already
    /// promoted, or has finished returns `false`. The same gates apply: a
    /// cancelled or stale ladder starts, reports its refusal at the first
    /// gate, and compiles nothing.
    pub fn promote(&mut self) -> bool {
        let Some(deferred) = self.deferred.take() else {
            return false;
        };
        if self.finished {
            return false;
        }
        let (receiver, spawned) = deferred();
        self.attach_worker(receiver, spawned);
        true
    }

    /// Whether this session still waits for [`Self::promote`].
    pub fn awaiting_promotion(&self) -> bool {
        self.deferred.is_some()
    }

    fn launch<B>(
        mut backend: B,
        start: LadderStart<B>,
        base: CompileRequest,
        plan: TierPlan,
    ) -> Result<(Self, TierInstall<A>), TierStartFailure>
    where
        B: TierBackend<Artifact = A>,
    {
        let gate = TierGate {
            base_cancellation: base.cancellation.clone(),
            session_cancellation: CancellationToken::new(),
            generation: base.generation,
            stale_before: base.stale_before,
            fence: base.generation_fence.clone(),
        };
        if let Some(refusal) = gate.refusal() {
            return Err(TierStartFailure::Refused(refusal));
        }
        let (early_worker, on_demand) = match start {
            LadderStart::Concurrent(worker_backend) => (
                Some(spawn_worker(
                    worker_backend,
                    base.clone(),
                    plan.levels().to_vec(),
                    gate.clone(),
                    &base.request_id,
                )),
                false,
            ),
            LadderStart::AfterBaseline => (None, false),
            LadderStart::OnDemand => (None, true),
        };
        let baseline = plan.baseline();
        let tier0 = TierRequest {
            tier: 0,
            opt_level: baseline,
            request: tier_request(&base, 0, baseline, base.cancellation.clone()),
        };
        let started = Instant::now();
        let output = match backend.compile_tier(&tier0) {
            Ok(output) => output,
            Err(failure) => {
                // No session: stop an early worker at its next gate; its
                // handle and channel are dropped (detached).
                gate.session_cancellation.cancel();
                return Err(TierStartFailure::Failed(failure));
            }
        };
        let compile_latency = started.elapsed();

        let mut exports = output.exports;
        exports.sort();
        exports.dedup();
        let mut records: Vec<TierRecord> = plan
            .levels()
            .iter()
            .enumerate()
            .map(|(tier, &opt_level)| TierRecord {
                tier,
                opt_level,
                compile_latency: None,
                outcome: TierOutcome::NotDelivered,
            })
            .collect();
        records[0].compile_latency = Some(compile_latency);
        records[0].outcome = TierOutcome::Delivered;

        let mut session = Self {
            request_id: base.request_id.clone(),
            generation: base.generation,
            gate,
            exports,
            source_identity: output.source_identity,
            delivered: 0,
            receiver: None,
            worker: None,
            deferred: None,
            records,
            finished: plan.len() == 1,
            plan,
        };
        if !session.finished {
            if on_demand {
                let levels = session.plan.levels().to_vec();
                let gate = session.gate.clone();
                let request_id = session.request_id.clone();
                session.deferred = Some(Box::new(move || {
                    spawn_worker(backend, base, levels, gate, &request_id)
                }));
            } else {
                let (receiver, spawned) = match early_worker {
                    Some(early) => early,
                    None => spawn_worker(
                        backend,
                        base,
                        session.plan.levels().to_vec(),
                        session.gate.clone(),
                        &session.request_id,
                    ),
                };
                session.attach_worker(receiver, spawned);
            }
        }
        let install = TierInstall {
            tier: 0,
            opt_level: baseline,
            generation: session.generation,
            compile_latency,
            artifact: output.artifact,
        };
        Ok((session, install))
    }

    fn attach_worker(
        &mut self,
        receiver: mpsc::Receiver<TierMessage<A>>,
        spawned: std::io::Result<JoinHandle<()>>,
    ) {
        self.receiver = Some(receiver);
        match spawned {
            Ok(worker) => self.worker = Some(worker),
            Err(error) => {
                // No worker: the ladder stops at tier 0, which the caller
                // already holds. Reported on the next poll.
                self.pending_refusal(
                    1,
                    TierRefusal::WorkerUnavailable {
                        detail: error.to_string(),
                    },
                );
            }
        }
    }

    // A refusal the session itself decided before any message: queue it so
    // `poll` reports it exactly like a worker-reported one.
    fn pending_refusal(&mut self, tier: usize, refusal: TierRefusal) {
        let (sender, receiver) = mpsc::channel();
        // The receiver is local and alive, so this send cannot fail.
        let _ = sender.send(TierMessage::Stopped { tier, refusal });
        self.receiver = Some(receiver);
    }

    /// The plan this session runs.
    pub fn plan(&self) -> &TierPlan {
        &self.plan
    }

    /// Highest tier delivered to the consumer so far.
    pub fn delivered_tier(&self) -> usize {
        self.delivered
    }

    /// Tier 0's callable surface, sorted.
    pub fn exports(&self) -> &[TierExport] {
        &self.exports
    }

    /// Whether nothing more will be delivered.
    pub fn is_finished(&self) -> bool {
        self.finished
    }

    /// Stop the ladder: no tier compiled after this call is delivered. The
    /// worker stops at its next request gate.
    pub fn cancel(&self) {
        self.gate.session_cancellation.cancel();
    }

    /// Non-blocking: report the next tier event, if any.
    pub fn poll(&mut self) -> TierUpPoll<A> {
        if self.finished {
            return TierUpPoll::Complete;
        }
        if self.deferred.is_some() {
            return TierUpPoll::Pending;
        }
        let Some(receiver) = self.receiver.as_ref() else {
            self.finished = true;
            return TierUpPoll::Complete;
        };
        match receiver.try_recv() {
            Ok(message) => self.accept(message),
            Err(mpsc::TryRecvError::Empty) => TierUpPoll::Pending,
            Err(mpsc::TryRecvError::Disconnected) => self.worker_ended(),
        }
    }

    /// Block until the next tier event. A session still awaiting
    /// [`Self::promote`] returns `Pending` instead of blocking forever.
    pub fn wait(&mut self) -> TierUpPoll<A> {
        if self.finished {
            return TierUpPoll::Complete;
        }
        if self.deferred.is_some() {
            return TierUpPoll::Pending;
        }
        let Some(receiver) = self.receiver.as_ref() else {
            self.finished = true;
            return TierUpPoll::Complete;
        };
        match receiver.recv() {
            Ok(message) => self.accept(message),
            Err(mpsc::RecvError) => self.worker_ended(),
        }
    }

    /// Block until the next tier event or `timeout`, whichever is first.
    pub fn wait_timeout(&mut self, timeout: Duration) -> TierUpPoll<A> {
        if self.finished {
            return TierUpPoll::Complete;
        }
        if self.deferred.is_some() {
            return TierUpPoll::Pending;
        }
        let Some(receiver) = self.receiver.as_ref() else {
            self.finished = true;
            return TierUpPoll::Complete;
        };
        match receiver.recv_timeout(timeout) {
            Ok(message) => self.accept(message),
            Err(mpsc::RecvTimeoutError::Timeout) => TierUpPoll::Pending,
            Err(mpsc::RecvTimeoutError::Disconnected) => self.worker_ended(),
        }
    }

    /// The per-tier account so far.
    pub fn report(&self) -> TierUpReport {
        TierUpReport {
            request_id: self.request_id.clone(),
            generation: self.generation,
            delivered_tier: self.delivered,
            tiers: self.records.clone(),
        }
    }

    /// Cancel the ladder, wait for the worker to stop, and return the final
    /// account. A tier compiling when this is called finishes first (it is
    /// then discarded); drop the session instead to not wait.
    pub fn shutdown(mut self) -> TierUpReport {
        self.cancel();
        self.receiver = None;
        if let Some(worker) = self.worker.take() {
            // A worker that panicked outside the backend's guard has nothing
            // left to report; the account below already says what arrived.
            let _ = worker.join();
        }
        self.finished = true;
        self.report()
    }

    fn accept(&mut self, message: TierMessage<A>) -> TierUpPoll<A> {
        match message {
            TierMessage::Compiled {
                tier,
                latency,
                output,
            } => {
                self.record_latency(tier, latency);
                if let Some(refusal) = self.gate.refusal() {
                    return self.refuse(tier, refusal);
                }
                if output.source_identity != self.source_identity {
                    return self.refuse(
                        tier,
                        TierRefusal::SourceMismatch {
                            expected: self.source_identity.clone(),
                            actual: output.source_identity,
                        },
                    );
                }
                let mut exports = output.exports;
                exports.sort();
                exports.dedup();
                if exports != self.exports {
                    let missing = self
                        .exports
                        .iter()
                        .filter(|export| exports.binary_search(export).is_err())
                        .cloned()
                        .collect();
                    let unexpected = exports
                        .iter()
                        .filter(|export| self.exports.binary_search(export).is_err())
                        .cloned()
                        .collect();
                    return self.refuse(
                        tier,
                        TierRefusal::ExportMismatch {
                            missing,
                            unexpected,
                        },
                    );
                }
                if tier <= self.delivered || tier > self.plan.top_tier() {
                    return self.refuse(
                        tier,
                        TierRefusal::WorkerPanicked {
                            detail: format!(
                                "tier {tier} arrived out of order after tier {}",
                                self.delivered
                            ),
                        },
                    );
                }
                self.delivered = tier;
                self.records[tier].outcome = TierOutcome::Delivered;
                if tier == self.plan.top_tier() {
                    self.finished = true;
                    self.receiver = None;
                }
                TierUpPoll::Upgraded(TierInstall {
                    tier,
                    opt_level: self.plan.levels()[tier],
                    generation: self.generation,
                    compile_latency: latency,
                    artifact: output.artifact,
                })
            }
            TierMessage::Failed {
                tier,
                latency,
                failure,
            } => {
                self.record_latency(tier, latency);
                self.refuse(tier, TierRefusal::Failed(failure))
            }
            TierMessage::Stopped { tier, refusal } => self.refuse(tier, refusal),
        }
    }

    fn record_latency(&mut self, tier: usize, latency: Duration) {
        if let Some(record) = self.records.get_mut(tier) {
            record.compile_latency = Some(latency);
        }
    }

    fn refuse(&mut self, tier: usize, refusal: TierRefusal) -> TierUpPoll<A> {
        let tier = tier.min(self.plan.top_tier());
        self.records[tier].outcome = TierOutcome::Refused {
            code: refusal.code(),
            detail: refusal.detail(),
        };
        // The ladder stops: tell a still-running worker to stop at its next
        // gate, and deliver nothing further.
        self.cancel();
        self.finished = true;
        self.receiver = None;
        TierUpPoll::Refused {
            tier,
            opt_level: self.plan.levels()[tier],
            refusal,
        }
    }

    fn worker_ended(&mut self) -> TierUpPoll<A> {
        self.receiver = None;
        if let Some(worker) = self.worker.take() {
            // The channel is disconnected, so the worker has returned (or is
            // unwinding past its last send); joining cannot wait on a compile.
            let _ = worker.join();
        }
        let next = self.delivered + 1;
        if next <= self.plan.top_tier() {
            return self.refuse(
                next,
                TierRefusal::WorkerPanicked {
                    detail: "the tier-up worker ended without reporting this tier".to_owned(),
                },
            );
        }
        self.finished = true;
        TierUpPoll::Complete
    }
}

impl<A: Send + 'static> TierUpSession<A> {
    /// Hand every higher tier to `install` as it is delivered, on a
    /// background thread, so the consumer never polls.
    ///
    /// `install` receives exactly the tiers [`Self::wait`] would return, in
    /// order, after the same checks; it runs on the installer thread, so it
    /// must publish the tier the way any cross-thread swap is published (for
    /// example [`TierEntryTable::install`], or its own atomic slots). An
    /// `Err` stops the ladder: that tier is recorded as
    /// `tier_up.install_failed` and the previously installed tier stays.
    pub fn install_with<F>(self, mut install: F) -> TierInstaller
    where
        F: FnMut(TierInstall<A>) -> Result<(), String> + Send + 'static,
    {
        let cancellation = self.gate.session_cancellation.clone();
        let name = format!("trust-cg-tier-install:{}", self.request_id.as_str());
        let mut session = self;
        let spawned = std::thread::Builder::new().name(name).spawn(move || {
            loop {
                let previous = session.delivered;
                match session.wait() {
                    TierUpPoll::Upgraded(tier) => {
                        let index = tier.tier;
                        if let Err(detail) = install(tier) {
                            session.install_failed(index, previous, detail);
                            break;
                        }
                    }
                    TierUpPoll::Pending => {}
                    TierUpPoll::Refused { .. } | TierUpPoll::Complete => break,
                }
            }
            session.shutdown()
        });
        match spawned {
            Ok(thread) => TierInstaller {
                cancellation,
                thread: Some(thread),
                unstarted: None,
            },
            Err(error) => {
                // The session moved into the failed spawn's closure and was
                // dropped with it, which cancelled its ladder.
                TierInstaller {
                    cancellation,
                    thread: None,
                    unstarted: Some(error.to_string()),
                }
            }
        }
    }

    fn install_failed(&mut self, tier: usize, previous: usize, detail: String) {
        let refusal = TierRefusal::InstallFailed { detail };
        self.records[tier].outcome = TierOutcome::Refused {
            code: refusal.code(),
            detail: refusal.detail(),
        };
        self.delivered = previous;
        self.cancel();
        self.finished = true;
        self.receiver = None;
    }
}

/// A session driven by a background installer
/// ([`TierUpSession::install_with`]).
///
/// Dropping it cancels the ladder and detaches the installer thread;
/// [`Self::join`] cancels nothing and waits for the ladder to end.
#[derive(Debug)]
pub struct TierInstaller {
    cancellation: CancellationToken,
    thread: Option<JoinHandle<TierUpReport>>,
    unstarted: Option<String>,
}

impl TierInstaller {
    /// Stop the ladder: no tier compiled after this call is installed.
    pub fn cancel(&self) {
        self.cancellation.cancel();
    }

    /// Whether the ladder has ended (every tier installed, or refused).
    pub fn is_finished(&self) -> bool {
        self.thread
            .as_ref()
            .is_none_or(std::thread::JoinHandle::is_finished)
    }

    /// Wait for the ladder to end and return the session's account. `Err`
    /// when the installer thread could not be started (nothing above tier 0
    /// was installed) or panicked.
    pub fn join(mut self) -> Result<TierUpReport, String> {
        if let Some(error) = self.unstarted.take() {
            return Err(format!(
                "the tier installer thread was not started: {error}"
            ));
        }
        match self.thread.take() {
            Some(thread) => thread
                .join()
                .map_err(|_| "the tier installer thread panicked".to_owned()),
            None => Err("the tier installer was already joined".to_owned()),
        }
    }
}

impl Drop for TierInstaller {
    fn drop(&mut self) {
        if self.thread.is_some() {
            self.cancellation.cancel();
        }
    }
}

impl<A: Send + 'static> Drop for TierUpSession<A> {
    fn drop(&mut self) {
        // Never block the consumer: the worker observes the cancellation at
        // its next gate and exits; its handle is detached.
        self.gate.session_cancellation.cancel();
    }
}

type WorkerSpawn<A> = (
    mpsc::Receiver<TierMessage<A>>,
    std::io::Result<JoinHandle<()>>,
);

fn spawn_worker<B: TierBackend>(
    backend: B,
    base: CompileRequest,
    levels: Vec<OptLevel>,
    gate: TierGate,
    request_id: &CompileRequestId,
) -> WorkerSpawn<B::Artifact> {
    let (sender, receiver) = mpsc::channel();
    let spawned = std::thread::Builder::new()
        .name(format!("trust-cg-tier-up:{}", request_id.as_str()))
        .stack_size(TIER_UP_WORKER_STACK_BYTES)
        .spawn(move || run_worker(backend, base, levels, gate, sender));
    (receiver, spawned)
}

fn run_worker<B: TierBackend>(
    mut backend: B,
    base: CompileRequest,
    levels: Vec<OptLevel>,
    gate: TierGate,
    sender: mpsc::Sender<TierMessage<B::Artifact>>,
) {
    for (tier, &opt_level) in levels.iter().enumerate().skip(1) {
        if let Some(refusal) = gate.refusal() {
            let _ = sender.send(TierMessage::Stopped { tier, refusal });
            return;
        }
        let request = TierRequest {
            tier,
            opt_level,
            request: tier_request(&base, tier, opt_level, gate.session_cancellation.clone()),
        };
        let started = Instant::now();
        let compiled = catch_unwind(AssertUnwindSafe(|| backend.compile_tier(&request)));
        let latency = started.elapsed();
        let message = match compiled {
            Err(payload) => {
                let detail = payload
                    .downcast_ref::<&str>()
                    .map(|text| (*text).to_owned())
                    .or_else(|| payload.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "non-string panic payload".to_owned());
                let _ = sender.send(TierMessage::Stopped {
                    tier,
                    refusal: TierRefusal::WorkerPanicked { detail },
                });
                return;
            }
            Ok(Err(failure)) => {
                let _ = sender.send(TierMessage::Failed {
                    tier,
                    latency,
                    failure,
                });
                return;
            }
            Ok(Ok(output)) => {
                if let Some(refusal) = gate.refusal() {
                    drop(output);
                    let _ = sender.send(TierMessage::Stopped { tier, refusal });
                    return;
                }
                TierMessage::Compiled {
                    tier,
                    latency,
                    output,
                }
            }
        };
        if sender.send(message).is_err() {
            // The session is gone; nobody will install anything.
            return;
        }
    }
}

// ---------------------------------------------------------------------------
// The compile-service backend
// ---------------------------------------------------------------------------

/// Compiles a `trust_ir::Module` to executable memory through
/// [`CompileService`], one request per tier.
///
/// A tier is delivered exactly when the same request, compiled synchronously
/// through the service, would install: the service returns
/// [`CompileStatus::Compiled`] with an installable disposition (its
/// admission, stale/cancel gates, proof policy and proof/TV report all
/// passed) and [`CompileResponse::into_installed_artifact`] accepts it (the
/// installed payload binding revalidates against the live buffer and the
/// direct-install native gate admits it). Exports are the compiler-derived
/// exported symbols of that binding with their compiler-derived signatures;
/// the source identity is the binding's TrustIR module digest.
///
/// Cloning shares the module and copies the service configuration, so
/// [`TierUpSession::start_concurrent`] can compile two tiers at once.
#[derive(Clone)]
pub struct ServiceTierBackend {
    service: CompileService,
    target_spec: TargetSpec,
    module: Arc<trust_ir::Module>,
    extern_symbols: Vec<RawExternBinding>,
}

impl fmt::Debug for ServiceTierBackend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ServiceTierBackend")
            .field("target_spec", &self.target_spec)
            .field("module", &self.module.name)
            .field("extern_symbols", &self.extern_symbols.len())
            .finish()
    }
}

impl ServiceTierBackend {
    /// A backend for `module` on `target_spec`, binding `extern_symbols` in
    /// every tier exactly as [`CompileService::compile_plan_with_extern_symbols`]
    /// binds them. The addresses must stay valid while any tier's code can
    /// run, as for any executable-memory compile.
    pub fn new(
        service: CompileService,
        target_spec: TargetSpec,
        module: Arc<trust_ir::Module>,
        extern_symbols: &HashMap<String, *const u8>,
    ) -> Self {
        let mut extern_symbols: Vec<RawExternBinding> = extern_symbols
            .iter()
            .map(|(symbol, address)| RawExternBinding::new(symbol.clone(), *address as usize))
            .collect();
        extern_symbols.sort_by(|left, right| left.symbol.cmp(&right.symbol));
        Self {
            service,
            target_spec,
            module,
            extern_symbols,
        }
    }

    /// [`Self::new`] with the target the base request's profile selects, as
    /// [`CompilePlan::for_request`] derives it.
    pub fn for_request(
        service: CompileService,
        base: &CompileRequest,
        module: Arc<trust_ir::Module>,
        extern_symbols: &HashMap<String, *const u8>,
    ) -> Self {
        let target_spec = CompilePlan::for_request(base.clone()).target_spec();
        Self::new(service, target_spec, module, extern_symbols)
    }
}

/// Signature identity for a compiler-derived symbol signature.
fn signature_identity(signature: &SymbolSignature) -> String {
    format!(
        "{}({:?})->({:?}){}",
        signature.abi,
        signature.params,
        signature.returns,
        if signature.variadic { "..." } else { "" }
    )
}

/// The compile-service outcome of a response that did not install, in the
/// async facade's state vocabulary.
fn uninstalled_state(response: &CompileResponse) -> AsyncCompileState {
    match response.status {
        CompileStatus::Compiled => match response.disposition {
            ArtifactInstallDisposition::ProfileOnly => AsyncCompileState::ProfileOnly,
            ArtifactInstallDisposition::Installable | ArtifactInstallDisposition::Rejected => {
                AsyncCompileState::Rejected
            }
        },
        CompileStatus::Cancelled => AsyncCompileState::Cancelled,
        CompileStatus::Stale => AsyncCompileState::StaleGeneration,
        CompileStatus::Rejected => AsyncCompileState::Rejected,
        CompileStatus::Failed => AsyncCompileState::Failed,
    }
}

impl TierBackend for ServiceTierBackend {
    type Artifact = InstalledArtifact;

    fn compile_tier(
        &mut self,
        tier: &TierRequest,
    ) -> Result<TierOutput<InstalledArtifact>, TierFailure> {
        if tier.request.artifact_kind != ArtifactKind::ExecutableMemory {
            return Err(TierFailure::with_error(
                AsyncCompileState::Rejected,
                "tier_up.not_executable_memory",
                "tier-up installs executable memory; an object request has nothing to install",
            ));
        }
        let extern_symbols: HashMap<String, *const u8> = self
            .extern_symbols
            .iter()
            .map(|binding| (binding.symbol.clone(), binding.address as *const u8))
            .collect();
        let plan = CompilePlan::new(tier.request.clone(), self.target_spec);
        let response =
            self.service
                .compile_plan_with_extern_symbols(plan, &self.module, &extern_symbols);
        if response.status != CompileStatus::Compiled
            || response.disposition != ArtifactInstallDisposition::Installable
        {
            let state = uninstalled_state(&response);
            return Err(TierFailure::new(state, response.diagnostics));
        }
        let mut diagnostics = response.diagnostics.clone();
        let Some(installed) = response.into_installed_artifact() else {
            diagnostics.push(
                CompileDiagnostic::error(
                    "tier_up.install_refused",
                    "the compile service refused to install this tier's artifact",
                )
                .with_phase("tier_up"),
            );
            return Err(TierFailure::new(AsyncCompileState::Rejected, diagnostics));
        };
        let binding = installed.metadata.installed_payload_binding.as_ref();
        let exports = match binding {
            Some(binding) => binding
                .symbols
                .iter()
                .filter(|symbol| symbol.visibility == SymbolVisibility::Exported)
                .map(|symbol| {
                    TierExport::new(symbol.name.clone(), signature_identity(&symbol.signature))
                })
                .collect(),
            None => installed
                .metadata
                .exported_entrypoints
                .iter()
                .map(|entry| TierExport::new(entry.name.clone(), String::new()))
                .collect(),
        };
        let source_identity = binding.map(|binding| binding.trust_ir_module_sha256.clone());
        Ok(TierOutput {
            artifact: installed,
            exports,
            source_identity,
        })
    }
}

// ---------------------------------------------------------------------------
// Swap on install
// ---------------------------------------------------------------------------

/// Why a [`TierEntryTable`] refused a tier.
#[derive(Debug)]
pub enum TierEntryError {
    /// A table needs at least one entry.
    Empty,
    /// The same symbol was named twice.
    DuplicateSymbol(String),
    /// A named entry did not resolve in the tier's executable buffer.
    Unresolved {
        /// The tier.
        tier: usize,
        /// The symbol.
        symbol: String,
        /// The JIT's reason.
        error: JitError,
    },
    /// Caller-owned addresses do not match the table's symbols one to one.
    AddressCount {
        /// The tier.
        tier: usize,
        /// Symbols in the table.
        expected: usize,
        /// Addresses supplied.
        actual: usize,
    },
    /// A caller-owned address was null.
    NullAddress {
        /// The tier.
        tier: usize,
        /// The symbol.
        symbol: String,
    },
    /// The tier is not higher than the installed one.
    NotNewer {
        /// The refused tier.
        tier: usize,
        /// The installed tier.
        installed: usize,
    },
}

impl fmt::Display for TierEntryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => write!(f, "a tier entry table needs at least one entry"),
            Self::DuplicateSymbol(symbol) => write!(f, "entry `{symbol}` is named twice"),
            Self::Unresolved {
                tier,
                symbol,
                error,
            } => write!(f, "tier {tier} does not resolve entry `{symbol}`: {error}"),
            Self::AddressCount {
                tier,
                expected,
                actual,
            } => write!(
                f,
                "tier {tier} supplies {actual} addresses for {expected} entries"
            ),
            Self::NullAddress { tier, symbol } => {
                write!(
                    f,
                    "tier {tier} supplies a null address for entry `{symbol}`"
                )
            }
            Self::NotNewer { tier, installed } => write!(
                f,
                "tier {tier} is not higher than the installed tier {installed}"
            ),
        }
    }
}

impl std::error::Error for TierEntryError {}

/// What keeps one installed tier's code mapped for the table's lifetime.
enum TierKeepalive {
    // Ownership only: each lease keeps its tier's mapping read-execute until
    // the table drops, so every address a caller ever loaded stays valid.
    #[allow(dead_code)]
    Leases(Vec<JitLeasedPtr>),
    // The caller's owner of the code (for example its own executable
    // library), held for the same reason.
    #[allow(dead_code)]
    Owned(Box<dyn std::any::Any + Send + Sync>),
}

/// Entry points that follow the installed tier.
///
/// Callers load an entry's address per call ([`Self::entry`], one atomic
/// acquire load) and call it; [`Self::install`] resolves every entry in the
/// new tier first and then publishes the new addresses. The table holds an
/// execution lease on every tier it ever installed, so an address loaded
/// from it — including one a thread is executing when a newer tier is
/// installed — stays mapped for as long as the table lives.
///
/// Entries switch one at a time: two consecutive loads may see different
/// tiers. That is sound exactly because every tier of a [`TierUpSession`] is
/// a compile of the same source with the same callable surface; calls
/// between entries inside one tier's code stay in that tier.
pub struct TierEntryTable {
    symbols: Box<[String]>,
    slots: Box<[AtomicUsize]>,
    installed_tier: AtomicUsize,
    retained: Mutex<Vec<TierKeepalive>>,
}

impl fmt::Debug for TierEntryTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TierEntryTable")
            .field("symbols", &self.symbols)
            .field("installed_tier", &self.installed_tier())
            .finish()
    }
}

fn lease_entries(
    symbols: &[String],
    tier: usize,
    artifact: &InstalledArtifact,
) -> Result<Vec<JitLeasedPtr>, TierEntryError> {
    symbols
        .iter()
        .map(|symbol| {
            artifact
                .buffer
                .leased_symbol_ptr(symbol)
                .map_err(|error| TierEntryError::Unresolved {
                    tier,
                    symbol: symbol.clone(),
                    error,
                })
        })
        .collect()
}

fn checked_addresses(
    symbols: &[String],
    tier: usize,
    addresses: &[*const u8],
) -> Result<Vec<usize>, TierEntryError> {
    if addresses.len() != symbols.len() {
        return Err(TierEntryError::AddressCount {
            tier,
            expected: symbols.len(),
            actual: addresses.len(),
        });
    }
    symbols
        .iter()
        .zip(addresses)
        .map(|(symbol, address)| {
            if address.is_null() {
                Err(TierEntryError::NullAddress {
                    tier,
                    symbol: symbol.clone(),
                })
            } else {
                Ok(*address as usize)
            }
        })
        .collect()
}

impl TierEntryTable {
    /// A table over `symbols`, all resolved in `artifact` (tier `tier`).
    pub fn new<I, S>(
        symbols: I,
        tier: usize,
        artifact: &InstalledArtifact,
    ) -> Result<Self, TierEntryError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let symbols: Vec<String> = symbols.into_iter().map(Into::into).collect();
        if symbols.is_empty() {
            return Err(TierEntryError::Empty);
        }
        let mut seen = std::collections::HashSet::with_capacity(symbols.len());
        for symbol in &symbols {
            if !seen.insert(symbol.as_str()) {
                return Err(TierEntryError::DuplicateSymbol(symbol.clone()));
            }
        }
        let leases = lease_entries(&symbols, tier, artifact)?;
        let slots = leases
            .iter()
            .map(|lease| AtomicUsize::new(lease.as_ptr() as usize))
            .collect();
        Ok(Self {
            symbols: symbols.into_boxed_slice(),
            slots,
            installed_tier: AtomicUsize::new(tier),
            retained: Mutex::new(vec![TierKeepalive::Leases(leases)]),
        })
    }

    /// Publish `artifact` (tier `tier`) as the target of every entry.
    ///
    /// All-or-nothing: every entry is resolved before any address changes.
    /// Refuses a tier that is not higher than the installed one.
    pub fn install(&self, tier: usize, artifact: &InstalledArtifact) -> Result<(), TierEntryError> {
        let leases = lease_entries(&self.symbols, tier, artifact)?;
        let addresses: Vec<usize> = leases.iter().map(|lease| lease.as_ptr() as usize).collect();
        self.publish(tier, &addresses, TierKeepalive::Leases(leases))
    }

    /// A table over `symbols` whose tier-`tier` code the caller owns: the
    /// general form for a frontend whose artifact is not an
    /// [`InstalledArtifact`] (for example its own JIT driver's library).
    ///
    /// # Safety
    ///
    /// Each address must be the executable entry of the same-index symbol,
    /// with the ABI every tier of that symbol shares, and `keepalive` must
    /// keep that code mapped and executable for as long as `keepalive`
    /// lives (the table holds it until the table drops).
    pub unsafe fn from_owned_addresses<I, S>(
        symbols: I,
        tier: usize,
        addresses: &[*const u8],
        keepalive: Box<dyn std::any::Any + Send + Sync>,
    ) -> Result<Self, TierEntryError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let symbols: Vec<String> = symbols.into_iter().map(Into::into).collect();
        if symbols.is_empty() {
            return Err(TierEntryError::Empty);
        }
        let mut seen = std::collections::HashSet::with_capacity(symbols.len());
        for symbol in &symbols {
            if !seen.insert(symbol.as_str()) {
                return Err(TierEntryError::DuplicateSymbol(symbol.clone()));
            }
        }
        let addresses = checked_addresses(&symbols, tier, addresses)?;
        let slots = addresses
            .iter()
            .map(|&address| AtomicUsize::new(address))
            .collect();
        Ok(Self {
            symbols: symbols.into_boxed_slice(),
            slots,
            installed_tier: AtomicUsize::new(tier),
            retained: Mutex::new(vec![TierKeepalive::Owned(keepalive)]),
        })
    }

    /// [`Self::install`] for caller-owned code (see
    /// [`Self::from_owned_addresses`]).
    ///
    /// # Safety
    ///
    /// As for [`Self::from_owned_addresses`], for `addresses` and `keepalive`.
    pub unsafe fn install_owned_addresses(
        &self,
        tier: usize,
        addresses: &[*const u8],
        keepalive: Box<dyn std::any::Any + Send + Sync>,
    ) -> Result<(), TierEntryError> {
        let addresses = checked_addresses(&self.symbols, tier, addresses)?;
        self.publish(tier, &addresses, TierKeepalive::Owned(keepalive))
    }

    fn publish(
        &self,
        tier: usize,
        addresses: &[usize],
        keepalive: TierKeepalive,
    ) -> Result<(), TierEntryError> {
        let mut retained = self.retained.lock().unwrap_or_else(PoisonError::into_inner);
        let installed = self.installed_tier.load(Ordering::Acquire);
        if tier <= installed {
            return Err(TierEntryError::NotNewer { tier, installed });
        }
        for (slot, &address) in self.slots.iter().zip(addresses) {
            slot.store(address, Ordering::Release);
        }
        self.installed_tier.store(tier, Ordering::Release);
        retained.push(keepalive);
        Ok(())
    }

    /// The entry symbols, in table order.
    pub fn symbols(&self) -> &[String] {
        &self.symbols
    }

    /// Table index of `symbol`.
    pub fn index_of(&self, symbol: &str) -> Option<usize> {
        self.symbols
            .iter()
            .position(|candidate| candidate == symbol)
    }

    /// The installed tier's address of entry `index`.
    ///
    /// The address stays executable while `self` lives. Calling it requires
    /// the caller's ABI to match the compiled signature, and on Apple
    /// Silicon a thread in JIT execute mode ([`Self::prepare_current_thread`]).
    pub fn entry(&self, index: usize) -> Option<*const u8> {
        self.slots
            .get(index)
            .map(|slot| slot.load(Ordering::Acquire) as *const u8)
    }

    /// Highest tier installed.
    pub fn installed_tier(&self) -> usize {
        self.installed_tier.load(Ordering::Acquire)
    }

    /// Put the current thread in JIT execute mode (Apple Silicon `MAP_JIT`;
    /// a no-op elsewhere). Call once on each thread before calling entries.
    pub fn prepare_current_thread(&self) {
        ensure_jit_execute_mode();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A backend over integers: tier artifacts are `(tier, opt rank)`, with
    /// scripted failures, panics, export drift and a gate on a channel so a
    /// test can hold a tier mid-compile.
    struct ScriptedBackend {
        exports: Vec<TierExport>,
        fail_at: Option<usize>,
        panic_at: Option<usize>,
        drift_at: Option<usize>,
        source_drift_at: Option<usize>,
        hold: Option<(usize, mpsc::Receiver<()>)>,
        seen: Arc<Mutex<Vec<(usize, OptLevel, String, bool)>>>,
    }

    impl ScriptedBackend {
        fn new() -> Self {
            Self {
                exports: vec![
                    TierExport::new("b", "extern_c(i64)->(i64)"),
                    TierExport::new("a", "extern_c()->(i64)"),
                ],
                fail_at: None,
                panic_at: None,
                drift_at: None,
                source_drift_at: None,
                hold: None,
                seen: Arc::new(Mutex::new(Vec::new())),
            }
        }
    }

    impl TierBackend for ScriptedBackend {
        type Artifact = (usize, u8);

        fn compile_tier(
            &mut self,
            tier: &TierRequest,
        ) -> Result<TierOutput<(usize, u8)>, TierFailure> {
            self.seen.lock().unwrap().push((
                tier.tier,
                tier.opt_level,
                tier.request.request_id.as_str().to_owned(),
                tier.request.proof_tv_evidence.is_some(),
            ));
            if let Some((at, receiver)) = &self.hold
                && *at == tier.tier
            {
                receiver.recv().unwrap();
            }
            if self.panic_at == Some(tier.tier) {
                panic!("scripted backend panic at tier {}", tier.tier);
            }
            if self.fail_at == Some(tier.tier) {
                return Err(TierFailure::with_error(
                    AsyncCompileState::Failed,
                    "compile.backend",
                    "scripted failure",
                ));
            }
            let mut exports = self.exports.clone();
            if self.drift_at == Some(tier.tier) {
                exports[0].signature = "extern_c(i32)->(i64)".to_owned();
            }
            let source = if self.source_drift_at == Some(tier.tier) {
                "other-source"
            } else {
                "source"
            };
            Ok(TierOutput {
                artifact: (tier.tier, opt_level_rank(tier.opt_level)),
                exports,
                source_identity: Some(source.to_owned()),
            })
        }
    }

    fn base(id: &str) -> CompileRequest {
        CompileRequest::new(id, CompileGeneration::new(7))
    }

    fn o0_o1_o2() -> TierPlan {
        TierPlan::new([OptLevel::O0, OptLevel::O1, OptLevel::O2]).unwrap()
    }

    fn drain<A: Send + 'static>(session: &mut TierUpSession<A>) -> Vec<TierUpPoll<A>> {
        let mut events = Vec::new();
        loop {
            match session.wait() {
                TierUpPoll::Complete => return events,
                TierUpPoll::Pending => unreachable!("wait never reports pending"),
                event => events.push(event),
            }
        }
    }

    #[test]
    fn plans_must_be_non_empty_bounded_and_strictly_increasing() {
        assert_eq!(TierPlan::new([]), Err(TierPlanError::Empty));
        assert_eq!(
            TierPlan::new([OptLevel::O0; 5]),
            Err(TierPlanError::TooManyTiers { count: 5 })
        );
        assert_eq!(
            TierPlan::new([OptLevel::O1, OptLevel::O1]),
            Err(TierPlanError::NotIncreasing {
                index: 1,
                previous: OptLevel::O1,
                level: OptLevel::O1,
            })
        );
        assert_eq!(
            TierPlan::new([OptLevel::O0, OptLevel::O2, OptLevel::O1]),
            Err(TierPlanError::NotIncreasing {
                index: 2,
                previous: OptLevel::O2,
                level: OptLevel::O1,
            })
        );
        let plan = TierPlan::new([OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3]).unwrap();
        assert_eq!(plan.baseline(), OptLevel::O0);
        assert_eq!(plan.top(), OptLevel::O3);
        assert_eq!(plan.top_tier(), 3);
        assert!(!plan.is_empty());
    }

    #[test]
    fn tier_requests_change_only_the_level_id_token_and_evidence() {
        let mut request = base("module");
        let fence = CompileGenerationFence::new();
        request.generation_fence = Some(fence.clone());
        request.stale_before = Some(CompileGeneration::new(3));
        let session_token = CancellationToken::new();

        // HostJitFast is O1: a tier at O1 keeps the profile untouched.
        let tier0 = tier_request(&request, 0, OptLevel::O1, request.cancellation.clone());
        assert!(matches!(tier0.profile, CompileProfile::HostJitFast));
        assert_eq!(tier0.request_id, request.request_id);

        let tier1 = tier_request(&request, 1, OptLevel::O2, session_token.clone());
        assert_eq!(tier1.request_id.as_str(), "module#tier1-O2");
        assert_eq!(tier1.generation, request.generation);
        assert_eq!(tier1.stale_before, request.stale_before);
        assert!(tier1.proof_tv_evidence.is_none());
        let CompileProfile::Custom { compiler, jit } = &tier1.profile else {
            panic!("a changed level is a custom profile");
        };
        let expanded = request.profile.expand();
        assert_eq!(compiler.opt_level, OptLevel::O2);
        assert_eq!(jit.opt_level, OptLevel::O2);
        assert_eq!(compiler.target, expanded.compiler.target);
        assert_eq!(
            compiler.enable_jit_fast_regalloc,
            expanded.compiler.enable_jit_fast_regalloc
        );
        // The session token cancels the tier, not the caller's request.
        session_token.cancel();
        assert!(tier1.cancellation.is_cancelled());
        assert!(!request.cancellation.is_cancelled());
        // The fence is shared, not copied.
        fence.mark_stale_before(CompileGeneration::new(100));
        assert_eq!(
            tier1.generation_fence.as_ref().unwrap().stale_before(),
            CompileGeneration::new(100)
        );
    }

    #[test]
    fn a_ladder_delivers_every_tier_in_order_then_completes() {
        let backend = ScriptedBackend::new();
        let seen = Arc::clone(&backend.seen);
        let (mut session, tier0) =
            TierUpSession::start(backend, base("ladder"), o0_o1_o2()).unwrap();
        assert_eq!((tier0.tier, tier0.artifact), (0, (0, 0)));
        assert_eq!(tier0.generation, CompileGeneration::new(7));
        let events = drain(&mut session);
        let delivered: Vec<_> = events
            .iter()
            .map(|event| match event {
                TierUpPoll::Upgraded(install) => (install.tier, install.artifact),
                other => panic!("unexpected {other:?}"),
            })
            .collect();
        assert_eq!(delivered, [(1, (1, 1)), (2, (2, 2))]);
        assert_eq!(session.delivered_tier(), 2);
        assert!(session.is_finished());
        assert!(matches!(session.poll(), TierUpPoll::Complete));
        let seen = seen.lock().unwrap().clone();
        assert_eq!(
            seen.iter()
                .map(|(tier, level, id, _)| (*tier, *level, id.as_str()))
                .collect::<Vec<_>>(),
            [
                (0, OptLevel::O0, "ladder"),
                (1, OptLevel::O1, "ladder#tier1-O1"),
                (2, OptLevel::O2, "ladder#tier2-O2"),
            ]
        );
        let report = session.shutdown();
        assert_eq!(report.delivered_tier, 2);
        assert!(
            report
                .tiers
                .iter()
                .all(|record| record.outcome == TierOutcome::Delivered
                    && record.compile_latency.is_some())
        );
        let json = report.to_json_value();
        assert_eq!(json["schema"], TIER_UP_REPORT_SCHEMA);
        assert_eq!(json["tiers"][2]["opt_level"], "O2");
        assert_eq!(json["tiers"][2]["outcome"], "delivered");
    }

    /// Tier 0 blocks until tier 1 has STARTED: only a concurrent start can
    /// finish. Clones share the rendezvous.
    #[derive(Clone)]
    struct RendezvousBackend {
        tier1_started: Arc<(Mutex<bool>, std::sync::Condvar)>,
    }

    impl TierBackend for RendezvousBackend {
        type Artifact = usize;

        fn compile_tier(&mut self, tier: &TierRequest) -> Result<TierOutput<usize>, TierFailure> {
            let (started, signal) = &*self.tier1_started;
            if tier.tier == 0 {
                let guard = started.lock().unwrap();
                let (guard, timeout) = signal
                    .wait_timeout_while(guard, Duration::from_secs(60), |started| !*started)
                    .unwrap();
                if timeout.timed_out() || !*guard {
                    return Err(TierFailure::with_error(
                        AsyncCompileState::Failed,
                        "test.no_overlap",
                        "tier 1 never started while tier 0 compiled",
                    ));
                }
            } else {
                *started.lock().unwrap() = true;
                signal.notify_all();
            }
            Ok(TierOutput {
                artifact: tier.tier,
                exports: vec![TierExport::new("f", "sig")],
                source_identity: None,
            })
        }
    }

    #[test]
    fn a_concurrent_start_compiles_the_top_tier_while_tier_zero_compiles() {
        let backend = RendezvousBackend {
            tier1_started: Arc::new((Mutex::new(false), std::sync::Condvar::new())),
        };
        let plan = TierPlan::new([OptLevel::O0, OptLevel::O2]).unwrap();
        let (mut session, tier0) =
            TierUpSession::start_concurrent(backend, base("concurrent"), plan).unwrap();
        assert_eq!(tier0.artifact, 0);
        match session.wait() {
            TierUpPoll::Upgraded(install) => assert_eq!((install.tier, install.artifact), (1, 1)),
            other => panic!("expected the top tier, got {other:?}"),
        }
        assert!(matches!(session.wait(), TierUpPoll::Complete));
    }

    #[test]
    fn a_concurrent_start_whose_tier_zero_fails_stops_its_worker() {
        #[derive(Clone)]
        struct FailZero {
            compiled: Arc<Mutex<Vec<usize>>>,
            release: Arc<(Mutex<bool>, std::sync::Condvar)>,
        }
        impl TierBackend for FailZero {
            type Artifact = usize;
            fn compile_tier(
                &mut self,
                tier: &TierRequest,
            ) -> Result<TierOutput<usize>, TierFailure> {
                if tier.tier == 0 {
                    return Err(TierFailure::with_error(
                        AsyncCompileState::Failed,
                        "compile.backend",
                        "tier 0 fails",
                    ));
                }
                // Hold tier 1 until the test has seen the start failure.
                let (released, signal) = &*self.release;
                let guard = released.lock().unwrap();
                let _guard = signal
                    .wait_timeout_while(guard, Duration::from_secs(60), |released| !*released)
                    .unwrap();
                self.compiled.lock().unwrap().push(tier.tier);
                Ok(TierOutput {
                    artifact: tier.tier,
                    exports: Vec::new(),
                    source_identity: None,
                })
            }
        }
        let compiled = Arc::new(Mutex::new(Vec::new()));
        let release = Arc::new((Mutex::new(false), std::sync::Condvar::new()));
        let backend = FailZero {
            compiled: Arc::clone(&compiled),
            release: Arc::clone(&release),
        };
        let failure =
            TierUpSession::start_concurrent(backend, base("fail-zero"), o0_o1_o2()).unwrap_err();
        assert!(matches!(failure, TierStartFailure::Failed(_)));
        *release.0.lock().unwrap() = true;
        release.1.notify_all();
        // The worker finishes tier 1, sees the cancellation at its gate and
        // never starts tier 2.
        let deadline = Instant::now() + Duration::from_secs(30);
        while Arc::strong_count(&compiled) > 1 && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(1));
        }
        assert_eq!(Arc::strong_count(&compiled), 1, "the worker exits");
        assert!(compiled.lock().unwrap().iter().all(|tier| *tier < 2));
    }

    #[test]
    fn a_background_installer_installs_every_tier_in_order() {
        let (session, tier0) =
            TierUpSession::start(ScriptedBackend::new(), base("installer"), o0_o1_o2()).unwrap();
        let installed = Arc::new(Mutex::new(vec![tier0.artifact]));
        let sink = Arc::clone(&installed);
        let installer = session.install_with(move |tier| {
            sink.lock().unwrap().push(tier.artifact);
            Ok(())
        });
        let report = installer.join().unwrap();
        assert_eq!(*installed.lock().unwrap(), [(0, 0), (1, 1), (2, 2)]);
        assert_eq!(report.delivered_tier, 2);
    }

    #[test]
    fn an_installer_error_stops_the_ladder_at_the_installed_tier() {
        let (session, _) =
            TierUpSession::start(ScriptedBackend::new(), base("installer-err"), o0_o1_o2())
                .unwrap();
        let installer = session.install_with(|tier| {
            if tier.tier == 2 {
                Err("the consumer's table refused tier 2".to_owned())
            } else {
                Ok(())
            }
        });
        let report = installer.join().unwrap();
        assert_eq!(report.delivered_tier, 1);
        assert_eq!(report.tiers[1].outcome, TierOutcome::Delivered);
        assert!(matches!(
            &report.tiers[2].outcome,
            TierOutcome::Refused {
                code: "tier_up.install_failed",
                detail,
            } if detail.contains("refused tier 2")
        ));
    }

    #[test]
    fn a_cancelled_installer_installs_nothing_more() {
        let (release, hold) = mpsc::channel();
        let mut backend = ScriptedBackend::new();
        backend.hold = Some((1, hold));
        let (session, _) =
            TierUpSession::start(backend, base("installer-cancel"), o0_o1_o2()).unwrap();
        let installed = Arc::new(Mutex::new(Vec::new()));
        let sink = Arc::clone(&installed);
        let installer = session.install_with(move |tier| {
            sink.lock().unwrap().push(tier.tier);
            Ok(())
        });
        installer.cancel();
        let _ = release.send(());
        let report = installer.join().unwrap();
        assert!(installed.lock().unwrap().is_empty());
        assert_eq!(report.delivered_tier, 0);
    }

    #[test]
    fn an_owned_address_table_swaps_and_retains_every_owner() {
        struct Owner(Arc<std::sync::atomic::AtomicUsize>);
        impl Drop for Owner {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }
        let dropped = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        // The table never calls these addresses; it only publishes them.
        let tier0 = [0x1000 as *const u8, 0x2000 as *const u8];
        let tier1 = [0x3000 as *const u8, 0x4000 as *const u8];
        // SAFETY: nothing calls the fake addresses; the owners are inert.
        let table = unsafe {
            TierEntryTable::from_owned_addresses(
                ["a", "b"],
                0,
                &tier0,
                Box::new(Owner(Arc::clone(&dropped))),
            )
        }
        .unwrap();
        assert_eq!(table.entry(1), Some(0x2000 as *const u8));
        // SAFETY: as above.
        unsafe {
            assert!(matches!(
                table.install_owned_addresses(1, &tier1[..1], Box::new(())),
                Err(TierEntryError::AddressCount {
                    expected: 2,
                    actual: 1,
                    ..
                })
            ));
            assert!(matches!(
                table.install_owned_addresses(1, &[tier1[0], std::ptr::null()], Box::new(())),
                Err(TierEntryError::NullAddress { .. })
            ));
            table
                .install_owned_addresses(1, &tier1, Box::new(Owner(Arc::clone(&dropped))))
                .unwrap();
            assert!(matches!(
                table.install_owned_addresses(1, &tier0, Box::new(())),
                Err(TierEntryError::NotNewer {
                    tier: 1,
                    installed: 1
                })
            ));
        }
        assert_eq!(table.entry(0), Some(0x3000 as *const u8));
        assert_eq!(table.installed_tier(), 1);
        assert_eq!(
            dropped.load(Ordering::SeqCst),
            0,
            "every tier's owner is retained"
        );
        drop(table);
        assert_eq!(dropped.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn an_on_demand_ladder_compiles_nothing_until_promoted() {
        let backend = ScriptedBackend::new();
        let seen = Arc::clone(&backend.seen);
        let (mut session, tier0) =
            TierUpSession::start_on_demand(backend, base("on-demand"), o0_o1_o2()).unwrap();
        assert_eq!(tier0.artifact, (0, 0));
        assert!(session.awaiting_promotion());
        assert!(matches!(session.poll(), TierUpPoll::Pending));
        assert!(matches!(session.wait(), TierUpPoll::Pending));
        assert_eq!(seen.lock().unwrap().len(), 1, "only tier 0 compiled");
        assert!(session.promote());
        assert!(!session.promote(), "promotion starts the ladder once");
        let delivered: Vec<_> = drain(&mut session)
            .into_iter()
            .map(|event| match event {
                TierUpPoll::Upgraded(install) => install.tier,
                other => panic!("unexpected {other:?}"),
            })
            .collect();
        assert_eq!(delivered, [1, 2]);

        // Never promoted: dropping it compiles nothing more.
        let backend = ScriptedBackend::new();
        let seen = Arc::clone(&backend.seen);
        let (session, _) =
            TierUpSession::start_on_demand(backend, base("never"), o0_o1_o2()).unwrap();
        let report = session.shutdown();
        assert_eq!(report.delivered_tier, 0);
        assert_eq!(seen.lock().unwrap().len(), 1);

        // Promoting a stale ladder reports the staleness and compiles nothing.
        let backend = ScriptedBackend::new();
        let seen = Arc::clone(&backend.seen);
        let fence = CompileGenerationFence::new();
        let mut request = base("stale-promote");
        request.generation_fence = Some(fence.clone());
        let (mut session, _) =
            TierUpSession::start_on_demand(backend, request, o0_o1_o2()).unwrap();
        fence.mark_stale_before(CompileGeneration::new(8));
        assert!(session.promote());
        assert!(matches!(
            session.wait(),
            TierUpPoll::Refused {
                tier: 1,
                refusal: TierRefusal::Stale,
                ..
            }
        ));
        assert_eq!(seen.lock().unwrap().len(), 1);
    }

    #[test]
    fn a_single_tier_plan_starts_no_worker() {
        let (mut session, tier0) = TierUpSession::start(
            ScriptedBackend::new(),
            base("single"),
            TierPlan::single(OptLevel::O2),
        )
        .unwrap();
        assert_eq!(tier0.artifact, (0, 2));
        assert!(session.worker.is_none());
        assert!(matches!(session.poll(), TierUpPoll::Complete));
    }

    #[test]
    fn a_failed_tier_stops_the_ladder_and_keeps_the_installed_tier() {
        let mut backend = ScriptedBackend::new();
        backend.fail_at = Some(1);
        let seen = Arc::clone(&backend.seen);
        let (mut session, _) = TierUpSession::start(backend, base("fail"), o0_o1_o2()).unwrap();
        match session.wait() {
            TierUpPoll::Refused {
                tier,
                opt_level,
                refusal: TierRefusal::Failed(failure),
            } => {
                assert_eq!((tier, opt_level), (1, OptLevel::O1));
                assert_eq!(failure.code(), "compile.backend");
                assert_eq!(failure.state, AsyncCompileState::Failed);
            }
            other => panic!("expected a refusal, got {other:?}"),
        }
        assert_eq!(session.delivered_tier(), 0);
        assert!(matches!(session.poll(), TierUpPoll::Complete));
        let report = session.shutdown();
        assert_eq!(seen.lock().unwrap().len(), 2, "tier 2 never compiles");
        assert_eq!(report.tiers[2].outcome, TierOutcome::NotDelivered);
        assert!(matches!(
            report.tiers[1].outcome,
            TierOutcome::Refused {
                code: "tier_up.failed",
                ..
            }
        ));
    }

    #[test]
    fn a_tier_zero_failure_is_the_start_failure() {
        let mut backend = ScriptedBackend::new();
        backend.fail_at = Some(0);
        let failure = TierUpSession::start(backend, base("fail0"), o0_o1_o2()).unwrap_err();
        assert!(matches!(failure, TierStartFailure::Failed(_)), "{failure}");
    }

    #[test]
    fn a_backend_panic_is_a_named_refusal() {
        let mut backend = ScriptedBackend::new();
        backend.panic_at = Some(2);
        let (mut session, _) = TierUpSession::start(backend, base("panic"), o0_o1_o2()).unwrap();
        assert!(matches!(session.wait(), TierUpPoll::Upgraded(_)));
        match session.wait() {
            TierUpPoll::Refused {
                tier: 2,
                refusal: TierRefusal::WorkerPanicked { detail },
                ..
            } => assert!(detail.contains("scripted backend panic"), "{detail}"),
            other => panic!("expected a panic refusal, got {other:?}"),
        }
        assert_eq!(session.delivered_tier(), 1);
    }

    #[test]
    fn a_tier_with_another_surface_or_source_is_refused() {
        let mut backend = ScriptedBackend::new();
        backend.drift_at = Some(1);
        let (mut session, _) = TierUpSession::start(backend, base("drift"), o0_o1_o2()).unwrap();
        match session.wait() {
            TierUpPoll::Refused {
                tier: 1,
                refusal:
                    TierRefusal::ExportMismatch {
                        missing,
                        unexpected,
                    },
                ..
            } => {
                assert_eq!(missing, [TierExport::new("b", "extern_c(i64)->(i64)")]);
                assert_eq!(unexpected, [TierExport::new("b", "extern_c(i32)->(i64)")]);
            }
            other => panic!("expected an export refusal, got {other:?}"),
        }

        let mut backend = ScriptedBackend::new();
        backend.source_drift_at = Some(2);
        let (mut session, _) = TierUpSession::start(backend, base("source"), o0_o1_o2()).unwrap();
        assert!(matches!(session.wait(), TierUpPoll::Upgraded(_)));
        assert!(matches!(
            session.wait(),
            TierUpPoll::Refused {
                tier: 2,
                refusal: TierRefusal::SourceMismatch { .. },
                ..
            }
        ));
    }

    #[test]
    fn a_generation_made_stale_mid_compile_is_never_delivered() {
        let (release, hold) = mpsc::channel();
        let mut backend = ScriptedBackend::new();
        backend.hold = Some((1, hold));
        let fence = CompileGenerationFence::new();
        let mut request = base("stale");
        request.generation_fence = Some(fence.clone());
        let (mut session, _) = TierUpSession::start(backend, request, o0_o1_o2()).unwrap();
        assert!(matches!(session.poll(), TierUpPoll::Pending));
        // The consumer supersedes generation 7 while tier 1 is compiling.
        fence.mark_stale_before(CompileGeneration::new(8));
        release.send(()).unwrap();
        assert!(matches!(
            session.wait(),
            TierUpPoll::Refused {
                tier: 1,
                refusal: TierRefusal::Stale,
                ..
            }
        ));
        assert_eq!(session.delivered_tier(), 0);
        assert!(matches!(session.wait(), TierUpPoll::Complete));
    }

    #[test]
    fn a_tier_that_goes_stale_after_compiling_is_refused_at_poll() {
        let (release, hold) = mpsc::channel();
        let mut backend = ScriptedBackend::new();
        backend.hold = Some((2, hold));
        let fence = CompileGenerationFence::new();
        let mut request = base("stale-at-poll");
        request.generation_fence = Some(fence.clone());
        let seen = Arc::clone(&backend.seen);
        let (mut session, _) = TierUpSession::start(backend, request, o0_o1_o2()).unwrap();
        // The worker sends tier 1 before it starts tier 2, so once tier 2 is
        // seen (and held), tier 1 sits compiled in the channel.
        let deadline = Instant::now() + Duration::from_secs(30);
        while seen.lock().unwrap().len() < 3 && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(1));
        }
        assert_eq!(seen.lock().unwrap().len(), 3);
        fence.mark_stale_before(CompileGeneration::new(8));
        match session.wait() {
            TierUpPoll::Refused {
                tier: 1,
                refusal: TierRefusal::Stale,
                ..
            } => {}
            other => panic!("expected the queued tier to be refused as stale, got {other:?}"),
        }
        release.send(()).unwrap();
        let report = session.shutdown();
        assert_eq!(report.delivered_tier, 0);
        assert!(matches!(
            report.tiers[1].outcome,
            TierOutcome::Refused {
                code: "tier_up.stale_generation",
                ..
            }
        ));
    }

    #[test]
    fn cancelling_or_dropping_a_session_stops_its_ladder() {
        let (release, hold) = mpsc::channel();
        let mut backend = ScriptedBackend::new();
        backend.hold = Some((1, hold));
        let seen = Arc::clone(&backend.seen);
        let (mut session, _) = TierUpSession::start(backend, base("cancel"), o0_o1_o2()).unwrap();
        session.cancel();
        // The worker may have stopped at its pre-compile gate and dropped
        // the backend (and this channel's receiver) already.
        let _ = release.send(());
        assert!(matches!(
            session.wait(),
            TierUpPoll::Refused {
                refusal: TierRefusal::Cancelled,
                ..
            }
        ));
        let report = session.shutdown();
        assert!(
            seen.lock().unwrap().iter().all(|(tier, ..)| *tier < 2),
            "tier 2 never compiles"
        );
        assert_eq!(report.delivered_tier, 0);

        // The base request's own token stops the ladder too.
        let (release, hold) = mpsc::channel();
        let mut backend = ScriptedBackend::new();
        backend.hold = Some((1, hold));
        let request = base("base-cancel");
        let token = request.cancellation.clone();
        let (mut session, _) = TierUpSession::start(backend, request, o0_o1_o2()).unwrap();
        token.cancel();
        // The worker may have stopped at its pre-compile gate and dropped
        // the backend (and this channel's receiver) already.
        let _ = release.send(());
        assert!(matches!(
            session.wait(),
            TierUpPoll::Refused {
                refusal: TierRefusal::Cancelled,
                ..
            }
        ));

        // Drop detaches without waiting for a held compile.
        let (release, hold) = mpsc::channel();
        let mut backend = ScriptedBackend::new();
        backend.hold = Some((1, hold));
        let seen = Arc::clone(&backend.seen);
        let (session, _) = TierUpSession::start(backend, base("drop"), o0_o1_o2()).unwrap();
        drop(session);
        // The worker may have stopped at its pre-compile gate and dropped
        // the backend (and this channel's receiver) already.
        let _ = release.send(());
        let deadline = Instant::now() + Duration::from_secs(30);
        while Arc::strong_count(&seen) > 1 && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(1));
        }
        assert_eq!(Arc::strong_count(&seen), 1, "the detached worker exits");
        assert!(
            seen.lock().unwrap().iter().all(|(tier, ..)| *tier < 2),
            "tier 2 never compiles"
        );
    }

    #[test]
    fn a_cancelled_or_stale_base_request_compiles_nothing() {
        let request = base("pre-cancelled");
        request.cancellation.cancel();
        let backend = ScriptedBackend::new();
        let seen = Arc::clone(&backend.seen);
        assert!(matches!(
            TierUpSession::start(backend, request, o0_o1_o2()),
            Err(TierStartFailure::Refused(TierRefusal::Cancelled))
        ));
        let mut request = base("pre-stale");
        request.stale_before = Some(CompileGeneration::new(8));
        assert!(matches!(
            TierUpSession::start(ScriptedBackend::new(), request, o0_o1_o2()),
            Err(TierStartFailure::Refused(TierRefusal::Stale))
        ));
        assert!(seen.lock().unwrap().is_empty());
    }

    #[test]
    fn higher_tiers_do_not_inherit_the_callers_artifact_evidence() {
        let backend = ScriptedBackend::new();
        let seen = Arc::clone(&backend.seen);
        let mut request = base("evidence");
        request.proof_tv_evidence = Some(crate::compile_service::ProofTvEvidenceOutcome {
            verdict: crate::compile_service::ProofTvVerdict::Accepted,
            rejection_code: None,
            diagnostic_reason: "attests tier 0's artifact only".to_owned(),
        });
        let (mut session, _) = TierUpSession::start(backend, request, o0_o1_o2()).unwrap();
        drain(&mut session);
        let seen = seen.lock().unwrap().clone();
        assert_eq!(
            seen.iter()
                .map(|(_, _, _, evidence)| *evidence)
                .collect::<Vec<_>>(),
            [true, false, false]
        );
    }
}
