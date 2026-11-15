// trust-cg-verify - negative memo for source-bound live replay
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! "This exact source-bound query did not certify under this exact
//! configuration": remembered, so an identical later replay returns the same
//! non-credit outcome without running AY again.
//!
//! # Why
//!
//! A source-bound theorem AY does not certify (its strict certification
//! rejects its own proof and it answers `(:reason-unknown (incomplete
//! self-check-rejected))`, a disclosed hole, a timeout) was solved from
//! scratch at every occurrence: once by a codegen unit's batched compile,
//! again by the rustc bridge's per-function fallback after the batch failed,
//! and again for every byte-identical body in any unit or process. The
//! positive receipts cover only `Verified` and counterexamples. Measured
//! before this memo on slice 5 (LIMITATIONS.md): a three-function probe crate
//! took 148.6 s (four solves of one query), and the Darwin x86-64 `core`
//! census rose from 2597 s to 4726 s.
//!
//! # What an entry can say
//!
//! Only that the live replay did NOT certify, and how
//! ([`UncertifiedOutcome`], the exact reason text AY or the checker gave, the
//! time it was recorded and what the solve cost). A hit becomes a
//! [`WithheldCredit`], whose only conversion is
//! [`WithheldCredit::non_credit_result`]: `AYResult::Unknown` with the
//! recorded reason, or `AYResult::Timeout`. No entry holds an `AYResult`, and
//! no code path turns an entry into `Verified`, `SolverUnsat`, a
//! counterexample, or a reuse receipt (`ay_bridge::PreparedAyQuery` refuses a
//! receipt to every result whose source is
//! [`crate::ay_bridge::AyVerdictSource::NegativeMemo`]). The memo can
//! therefore only WITHHOLD credit, never grant it.
//!
//! Only outcomes measured to be properties of the query are recorded
//! ([`UncertifiedOutcome::classify`]): AY's strict self-check rejecting its own
//! proof, a disclosed incomplete certificate, the working checker rejecting
//! the exact proof, each from a solve that had the processor (see "Which
//! certification failures are recorded"), a timeout of a query that used
//! its budget, and (OD-223) a Clean check of AY's proof that used the
//! checker's own deadline (a `checker-timeout`, never a solver `timeout`).
//! Every other
//! `unknown` (memory or resource exhaustion, an interrupt, an internal error, a
//! split limit, AY's model gate) and every error is solved again at its next
//! occurrence. An outcome that follows a SAT verdict (the model query timing
//! out) is never recorded, and deletes the key's entry, so no hit can stand in
//! for a known SAT.
//!
//! # Which timeouts are recorded
//!
//! The proof check is not the solve (OD-223). A replay's solver deadlines (the
//! resident and one-shot solves, the model query) and its checker deadlines
//! (the Clean check of AY's proof under
//! [`crate::obligation_cert_store::proof_check_timeout_ms`], the checker's
//! capability probe) are noted apart ([`NegativeMemoScope::note_deadline_expiry`],
//! [`NegativeMemoScope::note_check_expiry`]). A solver `Timeout` is judged on
//! the solver's expiries alone and a [`UncertifiedOutcome::CheckerTimeout`] on
//! the checker's alone, each by the rule below, so a checker overrun is never
//! recorded as a solver timeout and a recorded checker timeout names the
//! checker deadline it ran out of (part of the key).
//!
//! A replay's budgets are wall-clock deadlines, and a deadline also expires
//! when the solver spent the time waiting for a processor: on a host running
//! dozens of builds (load 40-80 measured on 2026-09-30) the solves of bodies
//! that certify at rest timed out, and recording those turned a transient of
//! the HOST into a non-credit answered for the key's whole retry budget, so
//! proof-required builds and the proof tests failed on every busy machine. The
//! subprocess supervisor therefore measures, immediately before it kills a
//! child whose deadline expired, the CPU time the child's whole process group
//! consumed under that deadline ([`crate::subprocess::DeadlineExpiry`]; AY
//! solves in a worker it forks into that group). A `Timeout` is recorded only
//! when the replay saw at least one deadline expire and every expiry it saw
//! used at least [`BUDGET_EXHAUSTING_CPU_PERCENT`] percent of its budget in CPU
//! time ([`exhausted_budget`]): the query, not the host, ran out. An expiry
//! below that share, one that was not measured (a platform without
//! per-process accounting, an unreadable member, a resident server whose
//! deadline ran out before the query reached it), and a `Timeout` no
//! supervised deadline produced (AY printing `timeout`, the checker's
//! capability probe) are load-dependent or unexplained: nothing is recorded
//! and an existing entry for the key is left as it is.
//!
//! # Which certification failures are recorded
//!
//! AY's strict certification is itself bounded by wall-clock time inside AY
//! (the toolchain AY 0.27.0 build 10530 gives its proof-producing bit-blast 3
//! s of wall clock, retried three times), so a solve starved of a processor
//! answers `(incomplete self-check-rejected)` for a body that certifies at
//! rest: on 2026-10-01 two `core` bodies Valid in one census came back
//! uncertified in the next, run at load 16 on four cores. A certification
//! failure is therefore recorded only when every fresh solve of the replay
//! completed with a measured process-group CPU time of at least
//! [`PROCESSOR_HELD_CPU_PERCENT`] percent of its wall-clock time
//! (`subprocess::run_measured`, read at the exit while the exited leader is
//! unreaped, so AY's reaped worker is included) and at least one did
//! ([`held_processor`]). A starved or unmeasured completion records nothing
//! and leaves an existing entry as it is.
//!
//! The memo is consulted inside the shared exact-query funnel strictly AFTER
//! the positive tiers (the in-process `Verified` memo and the per-box Alethe
//! certificate store), so a proof any process has minted is still consumed
//! first; a live `Verified` or counterexample for the key deletes the entry.
//!
//! # Key
//!
//! [`NegativeMemoIdentity::key`] hashes every input the replay's outcome
//! depends on: the SHA-256 of the exact query bytes as replayed; the
//! existing v2 query key (`verdict_cache_key_v2`: AY's content digest, the
//! CT-9 solver identity, over those bytes); the admitted AY's recorded
//! identity (build banner, digest, overlay); the positive-reuse authority id
//! (AY path and digest, the Clean checker's path and digest, the sanitized
//! child environment including its working directory); the checker digest;
//! the solve budget in milliseconds; the checker's own deadline in
//! milliseconds (OD-223, so an entry recorded under a shorter checker deadline
//! never answers a replay with a longer one); whether models are produced; whether the
//! resident AY route is live; [`replay_protocol`] (rendered from the command
//! builders the replay itself uses); and [`VERIFIER_BUILD`], the SHA-256 of
//! this crate's and `trust-cg-process-env`'s sources recorded by `build.rs`,
//! so an entry never crosses builds whose replay or verdict code differ. Any
//! difference is another key.
//!
//! # Tiers
//!
//! * In-process: a process-wide map (FIFO-bounded), covering the CT-BATCH
//!   fallback's second replay and repeated bodies across codegen units.
//! * Per-box: one file per key under [`STORE_NAMESPACE`] inside the Alethe
//!   certificate store (`obligation_cert_store::negative_memo_dir`: the same
//!   location and kill switches). Every read-modify-write and delete holds
//!   the namespace's advisory lock (`.lock`, `flock`), so a concurrent
//!   `Verified` delete is never undone by a reuse count written back; an
//!   entry is published by a fresh temporary file renamed over it. Only a
//!   regular file is opened, without following links and without blocking;
//!   a missing, non-regular, truncated, corrupt, oversized, foreign-schema,
//!   foreign-key or self-inconsistent entry is a miss. Each recording prunes
//!   a bounded window of expired or unreadable entries and stale staging
//!   files.
//!
//! # Retry policy
//!
//! AY's outcome on identical bytes is not deterministic under load, so every
//! tier bounds how long an entry answers ([`RetryPolicy`]): a per-box entry
//! answers a bounded number of later processes (backing off with each
//! consecutive failed re-solve) and nothing older than its age bound; an
//! entry inside one process answers a bounded number of hits within a bounded
//! window, so a long-lived verifying process (the JIT replays through the same
//! path) also retries. The next occurrence after any bound solves the query
//! again and refreshes the entry (or deletes it). Concurrent processes can
//! lose a reuse increment only by the lock failing to be taken, in which case
//! the per-box tier is skipped for that occurrence (it is solved).
//!
//! # Switches
//!
//! Inactive under `TCG_NO_PROOF_CACHE`, while the tier-0 recorder is armed,
//! without a capable independent checker (no reuse authority exists then),
//! and in a build that could not record [`VERIFIER_BUILD`]. The per-box tier
//! also follows `TCG_NO_CERT_STORE`.
//! [`crate::diag::source_bound_negative_memo_disabled`] (the tracked bridge
//! knob `-Ztrust-ir-cg-args=source-bound-no-negative-memo`, or
//! `TCG_SOURCE_BOUND_NO_NEGATIVE_MEMO` outside the bridge) bypasses it
//! entirely: nothing is read or written.

use std::collections::{HashMap, VecDeque};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use sha2::{Digest, Sha256};

use crate::ay_bridge::{AYResult, AyVerdictSource};
use crate::subprocess::DeadlineExpiry;

/// First line of every per-box entry. Another schema is a miss. v3: a
/// recorded `Timeout` means the query used its budget in CPU time (see the
/// module docs), and the entry carries that CPU time; a v2 timeout may have
/// been a starved solve, so v2 entries are never read. v4: a recorded
/// certification failure comes from solves that had the processor; a v3 one
/// may have been a starved solve's, so v3 entries are never read. v5 (slice
/// 19, OD-197): the x86-64 body owner's replay follows a resident deadline
/// with one fresh replay of the query (`ay_bridge`), so a `Timeout` is
/// recorded for its queries only when BOTH routes ran out of a budget they
/// used (every deadline the replay saw, the resident one and the fresh
/// retry's, exhausted its budget in CPU time, [`exhausted_budget`]); a v4
/// entry may record a resident deadline alone, which the fresh route might
/// have answered, so v4 entries are never read. v6 (OD-223): the Clean check
/// of AY's proof has its own deadline, separate from the solve budget, and a
/// check that runs out of it is a `checker-timeout` keyed by that deadline;
/// a v5 `timeout` may be a checker overrun under the 30 s solve budget the
/// check then shared (`u64::leading_zeros`, census s23final: AY answers in
/// 7.6-8.0 s, Clean needs 41-53 s), and nothing in a v5 entry says which
/// deadline expired, so v5 entries are never read.
pub(crate) const SCHEMA: &str = "tcg-source-bound-negative-memo-v6";

/// The per-box tier's directory inside the certificate store.
pub(crate) const STORE_NAMESPACE: &str = "source-bound-negative-v6";

/// The share of a deadline's budget, in percent, that the solver's process
/// group must have consumed in CPU time for its expiry to say the QUERY ran
/// out of the budget rather than the host. A CPU-bound solve that has a
/// processor to itself accrues CPU time at the wall-clock rate (AY's worker:
/// 2.94 s in 3 s, and 0.999 s in 1.0 s for a busy control, on this host at
/// load 9 on 18 cores, 2026-10-01); the margin below 100 covers process start
/// and scheduling noise on a lightly loaded host, while a solve starved by a
/// host at two to four times its core count accrues well under it.
pub(crate) const BUDGET_EXHAUSTING_CPU_PERCENT: u128 = 90;

/// The share of a completed solve's wall-clock time, in percent, that its
/// process group must have spent in CPU time for the solve to have had the
/// processor, so that a certification failure it ended in is the query's and
/// not the host's (AY's certification has its own wall-clock bound). The same
/// margin as a deadline's: a CPU-bound solve with a processor to itself
/// accrues CPU time at the wall-clock rate.
pub(crate) const PROCESSOR_HELD_CPU_PERCENT: u128 = 90;

/// Whether a completed solve that took `wall` and used `cpu` had the
/// processor: a measured CPU time of at least [`PROCESSOR_HELD_CPU_PERCENT`]
/// percent of a nonzero wall-clock time.
pub(crate) fn held_processor(wall: Duration, cpu: Option<Duration>) -> bool {
    let Some(cpu) = cpu else { return false };
    wall > Duration::ZERO
        && cpu.as_nanos().saturating_mul(100)
            >= wall.as_nanos().saturating_mul(PROCESSOR_HELD_CPU_PERCENT)
}

/// Whether `expiry` is evidence that the query exhausted its budget: a
/// measured CPU time of at least [`BUDGET_EXHAUSTING_CPU_PERCENT`] percent of
/// a nonzero budget. An unmeasured expiry is never such evidence.
pub(crate) fn exhausted_budget(expiry: &DeadlineExpiry) -> bool {
    let Some(cpu) = expiry.cpu else {
        return false;
    };
    !expiry.limit.is_zero()
        && cpu.as_nanos() * 100 >= expiry.limit.as_nanos() * BUDGET_EXHAUSTING_CPU_PERCENT
}

/// The verifier's source identity (`build.rs`, `verifier_source_digest.rs`):
/// empty when it could not be recorded, which switches the memo off.
pub(crate) const VERIFIER_BUILD: &str = env!("VERIFIER_SOURCE_SHA256");

/// AY's published reason when its mandatory strict certification rejects
/// its own proof (`computed UNSAT rejected by mandatory strict certification:
/// strict UNSAT proof validation failed: step t1 uses unverified trust rule`
/// on stderr), on the resident and the fresh route alike.
pub(crate) const SELF_CHECK_REJECTED: &str = "(:reason-unknown (incomplete self-check-rejected))";

/// The fixed parts of a source-bound live replay
/// (`ay_bridge::replay_protocol_description`), rendered once per process.
pub(crate) fn replay_protocol() -> &'static str {
    static PROTOCOL: OnceLock<String> = OnceLock::new();
    PROTOCOL.get_or_init(crate::ay_bridge::replay_protocol_description)
}

/// Upper bound on a per-box entry read from disk (an entry is a few hundred
/// bytes; anything larger is not ours).
const MAX_ENTRY_BYTES: u64 = 64 * 1024;

/// Process-wide bound on remembered entries (FIFO eviction, like the other
/// in-process proof memos).
const PROCESS_CAPACITY: usize = 4_096;

/// How long a per-box operation waits for the namespace lock before it gives
/// up (the operation is then skipped: a lookup misses, a write is dropped).
const LOCK_WAIT: Duration = Duration::from_secs(2);

/// Entries (and staging files) one recording examines for pruning.
const PRUNE_WINDOW: usize = 32;

/// Directory entries a pruning pass lists at most.
const PRUNE_LISTING_CAP: usize = 16_384;

/// Age after which an orphaned staging file (a writer that died between
/// staging and rename) is removed.
const STALE_STAGING: Duration = Duration::from_secs(10 * 60);

/// How a live replay failed to certify. The only statements an entry makes,
/// and only the outcomes measured to be properties of the query.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum UncertifiedOutcome {
    /// AY's strict certification rejected its own proof ([`SELF_CHECK_REJECTED`]).
    SelfCheckRejected,
    /// AY's certificate header disclosed holes, trusted steps or foreign
    /// assumptions.
    IncompleteCertificate,
    /// The identity-pinned working checker rejected the exact proof.
    CheckerRejected,
    /// The solve ran out of its budget having used it: recorded only with
    /// that CPU evidence (see the module docs).
    Timeout,
    /// OD-223: AY answered `unsat` and the Clean check of its exact proof ran
    /// out of the checker's own deadline having used it: recorded only with
    /// that CPU evidence, under a key that names the checker deadline.
    CheckerTimeout,
}

impl UncertifiedOutcome {
    /// Every variant (tests enumerate them).
    pub(crate) const ALL: [Self; 5] = [
        Self::SelfCheckRejected,
        Self::IncompleteCertificate,
        Self::CheckerRejected,
        Self::Timeout,
        Self::CheckerTimeout,
    ];

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::SelfCheckRejected => "self-check-rejected",
            Self::IncompleteCertificate => "incomplete-certificate",
            Self::CheckerRejected => "checker-rejected",
            Self::Timeout => "timeout",
            Self::CheckerTimeout => "checker-timeout",
        }
    }

    /// Whether the outcome is a deadline's (its entry then carries the CPU
    /// time that justified recording it).
    fn is_deadline(self) -> bool {
        matches!(self, Self::Timeout | Self::CheckerTimeout)
    }

    fn from_label(label: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|kind| kind.label() == label)
    }

    /// Classify a LIVE replay result. `None` for every result the memo must
    /// not record: `Verified`, a counterexample, `SolverUnsat`, an error, and
    /// every `Unknown` but the three certification failures (AY's strict
    /// self-check rejection, a disclosed incomplete certificate, the working
    /// checker's rejection) and the checker timeout
    /// ([`crate::ay_bridge::CLEAN_CHECK_TIMEOUT`]). In particular AY's other `(:reason-unknown …)`
    /// answers (memout, resourceout, interrupted, internal_error, a split
    /// limit) describe the host, not the query, and its model gate names an
    /// AY defect; each keeps its live solve, like any unrecognized reason.
    pub(crate) fn classify(result: &AYResult) -> Option<(Self, String)> {
        let reason = match result {
            AYResult::Timeout => return Some((Self::Timeout, String::new())),
            AYResult::Unknown(reason) => reason,
            AYResult::Verified
            | AYResult::SolverUnsat
            | AYResult::CounterExample(_)
            | AYResult::Error(_) => return None,
        };
        let kind = if reason == SELF_CHECK_REJECTED {
            Self::SelfCheckRejected
        } else if reason.starts_with(crate::ay_bridge::CLEAN_CHECK_TIMEOUT) {
            Self::CheckerTimeout
        } else if reason.starts_with("incomplete AY proof certificate:") {
            Self::IncompleteCertificate
        } else if reason.starts_with("AY reported UNSAT but")
            && reason.contains(crate::ay_bridge::WORKING_CHECKER_REJECTED_THIS_PROOF)
        {
            Self::CheckerRejected
        } else {
            return None;
        };
        if crate::gap_classify::ay_reason_is_soundness_gate_refusal(reason) {
            return None;
        }
        Some((kind, reason.clone()))
    }

    /// The result this outcome replays as (never credit).
    fn replayed(self, reason: &str) -> AYResult {
        match self {
            Self::Timeout => AYResult::Timeout,
            Self::SelfCheckRejected
            | Self::IncompleteCertificate
            | Self::CheckerRejected
            | Self::CheckerTimeout => AYResult::Unknown(reason.to_owned()),
        }
    }
}

/// Every input the replayed outcome depends on (see the module docs).
pub(crate) struct NegativeMemoIdentity<'a> {
    /// The exact query bytes as replayed.
    pub(crate) smt2: &'a str,
    /// `verdict_cache_key_v2(ay content digest, smt2)`.
    pub(crate) query_key: &'a str,
    /// The admitted AY's recorded identity (`AyIdentity::describe`: build
    /// banner, digest and overlay).
    pub(crate) ay_identity: &'a str,
    /// The positive-reuse authority id: AY path and digest, checker path and
    /// digest, sanitized child environment.
    pub(crate) authority_id: [u8; 32],
    /// The independent checker's content digest.
    pub(crate) checker_sha256: &'a str,
    /// The solve budget.
    pub(crate) timeout_ms: u64,
    /// OD-223: the Clean check's own deadline
    /// ([`crate::obligation_cert_store::proof_check_timeout_ms`]).
    pub(crate) checker_timeout_ms: u64,
    /// Whether a SAT answer is enriched with a model.
    pub(crate) produce_models: bool,
    /// Whether the resident AY route is live for this query.
    pub(crate) resident_route: bool,
    /// Slice 19 (OD-197): whether a resident deadline is followed by one
    /// fresh replay of the query (the x86-64 body owner's queries).
    pub(crate) fresh_after_resident_timeout: bool,
    /// Slice 23 (OD-206): whether the query is an x86-64 body obligation's
    /// generalization over its arithmetic leaves (a route of its own: its
    /// bytes differ from the exact obligation's too, so no entry of one ever
    /// answers the other).
    pub(crate) generalized: bool,
    /// [`replay_protocol`].
    pub(crate) replay_protocol: &'a str,
    /// [`VERIFIER_BUILD`].
    pub(crate) verifier_build: &'a str,
}

/// The key of one negative entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct NegativeMemoKey([u8; 32]);

impl NegativeMemoKey {
    pub(crate) fn hex(&self) -> String {
        self.0.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn from_hex(text: &str) -> Option<Self> {
        if text.len() != 64 {
            return None;
        }
        let mut bytes = [0u8; 32];
        for (index, byte) in bytes.iter_mut().enumerate() {
            let pair = text.get(index * 2..index * 2 + 2)?;
            if !pair
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            {
                return None;
            }
            *byte = u8::from_str_radix(pair, 16).ok()?;
        }
        Some(Self(bytes))
    }
}

impl NegativeMemoIdentity<'_> {
    pub(crate) fn key(&self) -> NegativeMemoKey {
        let mut hasher = Sha256::new();
        hasher.update(b"trust-cg.source-bound-negative-memo.key.v4\0");
        let smt2_sha256: [u8; 32] = Sha256::digest(self.smt2.as_bytes()).into();
        part(&mut hasher, b"smt2-sha256", &smt2_sha256);
        part(&mut hasher, b"query-key", self.query_key.as_bytes());
        part(&mut hasher, b"ay-identity", self.ay_identity.as_bytes());
        part(&mut hasher, b"authority", &self.authority_id);
        part(
            &mut hasher,
            b"checker-sha256",
            self.checker_sha256.as_bytes(),
        );
        part(&mut hasher, b"timeout-ms", &self.timeout_ms.to_be_bytes());
        part(
            &mut hasher,
            b"checker-timeout-ms",
            &self.checker_timeout_ms.to_be_bytes(),
        );
        part(
            &mut hasher,
            b"produce-models",
            &[u8::from(self.produce_models)],
        );
        part(
            &mut hasher,
            b"resident-route",
            &[u8::from(self.resident_route)],
        );
        part(
            &mut hasher,
            b"fresh-after-resident-timeout",
            &[u8::from(self.fresh_after_resident_timeout)],
        );
        part(&mut hasher, b"generalized", &[u8::from(self.generalized)]);
        part(
            &mut hasher,
            b"replay-protocol",
            self.replay_protocol.as_bytes(),
        );
        part(
            &mut hasher,
            b"verifier-build",
            self.verifier_build.as_bytes(),
        );
        part(&mut hasher, b"schema", SCHEMA.as_bytes());
        NegativeMemoKey(hasher.finalize().into())
    }
}

fn part(hasher: &mut Sha256, label: &[u8], bytes: &[u8]) {
    hasher.update((label.len() as u64).to_be_bytes());
    hasher.update(label);
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

/// When an entry stops being honoured and the next occurrence solves again.
///
/// Per-box: the reuse budget (later processes that may reuse an entry) backs
/// off with the entry's confirmations: an entry whose query failed on its
/// only live replay may be reused by `base_reuses` later processes, and each
/// further consecutive failed re-solve doubles that, up to `max_reuses`. A
/// first failure can be a load-dependent outcome of a query that usually
/// certifies, so it is retried soon; a query that has failed every re-solve
/// is retried rarely. In one process: an entry answers at most
/// `process_hits` hits within `process_window` of entering the process. The
/// age bound applies to every entry in every tier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RetryPolicy {
    /// Later processes an entry with one confirmation may answer.
    pub(crate) base_reuses: u32,
    /// The largest per-box reuse budget any entry reaches.
    pub(crate) max_reuses: u32,
    /// Age after which an entry answers nothing, in any tier.
    pub(crate) max_age: Duration,
    /// Hits an entry answers inside one process before it is solved again.
    pub(crate) process_hits: u32,
    /// How long after entering one process an entry answers there.
    pub(crate) process_window: Duration,
}

impl RetryPolicy {
    /// The measured default; the justification is in LIMITATIONS.md and
    /// `reports/2026-09-30-ay-strict-selfcheck-nondeterminism/README.md`.
    pub(crate) const DEFAULT: Self = Self {
        base_reuses: 2,
        max_reuses: 32,
        max_age: Duration::from_secs(24 * 60 * 60),
        process_hits: 64,
        process_window: Duration::from_secs(60 * 60),
    };

    /// The later processes an entry with `confirmations` consecutive failed
    /// live replays may answer before the next re-solve.
    pub(crate) fn reuse_budget(&self, confirmations: u32) -> u32 {
        let doublings = confirmations.saturating_sub(1).min(31);
        self.base_reuses
            .saturating_mul(1u32 << doublings)
            .min(self.max_reuses.max(self.base_reuses))
    }

    /// Recorded at most `max_age` ago, and not after `now`.
    fn fresh(&self, entry: &Entry, now_ms: u64) -> bool {
        within(entry.recorded_unix_ms, now_ms, self.max_age)
    }

    /// Whether one more process may reuse a per-box entry.
    fn admits_reuse(&self, entry: &Entry, now_ms: u64) -> bool {
        entry.reuses < self.reuse_budget(entry.confirmations) && self.fresh(entry, now_ms)
    }

    /// Whether an entry held by this process answers one more hit.
    fn admits_process_hit(&self, slot: &ProcessSlot, now_ms: u64) -> bool {
        slot.hits < self.process_hits
            && within(slot.entered_ms, now_ms, self.process_window)
            && self.fresh(&slot.entry, now_ms)
    }
}

/// `then` is at most `bound` before `now`, and not after it.
fn within(then_ms: u64, now_ms: u64, bound: Duration) -> bool {
    let bound_ms = u64::try_from(bound.as_millis()).unwrap_or(u64::MAX);
    now_ms >= then_ms && now_ms - then_ms <= bound_ms
}

/// One remembered non-certified replay.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Entry {
    outcome: UncertifiedOutcome,
    /// The exact `Unknown` text (empty for a timeout).
    reason: String,
    recorded_unix_ms: u64,
    /// Wall time of the live replay that recorded it.
    solve_ms: u64,
    /// For a `Timeout` or a `CheckerTimeout`, the largest CPU time (rounded
    /// up to a millisecond) of the budget-exhausting deadline expiries (the
    /// solver's, or the checker's) that justified recording it; zero for
    /// every other outcome.
    cpu_ms: u64,
    /// Later processes that reused the entry since that replay.
    reuses: u32,
    /// Consecutive live replays of this key that did not certify.
    confirmations: u32,
}

impl Entry {
    fn serialize(&self, key: &NegativeMemoKey) -> String {
        format!(
            "{SCHEMA}\nkey:{}\noutcome:{}\nrecorded-unix-ms:{}\nsolve-ms:{}\ncpu-ms:{}\nreuses:{}\nconfirmations:{}\nreason-bytes:{}\n{}\nend\n",
            key.hex(),
            self.outcome.label(),
            self.recorded_unix_ms,
            self.solve_ms,
            self.cpu_ms,
            self.reuses,
            self.confirmations,
            self.reason.len(),
            self.reason,
        )
    }

    /// Strict parse. `None` (a miss) on any deviation, including an entry
    /// recorded for another key, a reason that does not classify as the
    /// entry's own outcome label, and a CPU time that does not fit it (a
    /// solver or checker timeout without one, any other outcome with one).
    fn parse(text: &str, key: &NegativeMemoKey) -> Option<Self> {
        let mut rest = text;
        if next_line(&mut rest)? != SCHEMA
            || next_line(&mut rest)?.strip_prefix("key:")? != key.hex()
        {
            return None;
        }
        let outcome =
            UncertifiedOutcome::from_label(next_line(&mut rest)?.strip_prefix("outcome:")?)?;
        let recorded_unix_ms = number(next_line(&mut rest)?, "recorded-unix-ms:")?;
        let solve_ms = number(next_line(&mut rest)?, "solve-ms:")?;
        let cpu_ms = number(next_line(&mut rest)?, "cpu-ms:")?;
        let reuses = u32::try_from(number(next_line(&mut rest)?, "reuses:")?).ok()?;
        let confirmations = u32::try_from(number(next_line(&mut rest)?, "confirmations:")?).ok()?;
        let length = usize::try_from(number(next_line(&mut rest)?, "reason-bytes:")?).ok()?;
        let reason = rest.get(..length)?.to_owned();
        if rest.get(length..)? != "\nend\n"
            || confirmations == 0
            || outcome.is_deadline() != (cpu_ms > 0)
        {
            return None;
        }
        // The reason must be one this outcome is recorded for: a stored
        // label cannot vouch for text that would not have been recorded.
        match UncertifiedOutcome::classify(&outcome.replayed(&reason)) {
            Some((kind, text)) if kind == outcome && text == reason => {}
            _ => return None,
        }
        Some(Self {
            outcome,
            reason,
            recorded_unix_ms,
            solve_ms,
            cpu_ms,
            reuses,
            confirmations,
        })
    }
}

/// The line at the start of `rest` (without its newline), advancing past it.
fn next_line<'t>(rest: &mut &'t str) -> Option<&'t str> {
    let (head, tail) = rest.split_once('\n')?;
    *rest = tail;
    Some(head)
}

/// A `<prefix><decimal digits>` field.
fn number(line: &str, prefix: &str) -> Option<u64> {
    let digits = line.strip_prefix(prefix)?;
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

/// Which tier answered a hit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MemoTier {
    Process,
    Store,
}

impl MemoTier {
    fn label(self) -> &'static str {
        match self {
            Self::Process => "process",
            Self::Store => "store",
        }
    }
}

/// A negative-memo hit: an earlier live replay of this exact query under this
/// exact configuration did not certify. It carries no verdict, only the
/// recorded outcome; see [`Self::non_credit_result`].
#[derive(Clone, Debug)]
pub(crate) struct WithheldCredit {
    outcome: UncertifiedOutcome,
    reason: String,
    tier: MemoTier,
    reuses: u32,
    reuse_budget: u32,
    process_hits: u32,
    age: Duration,
    solve_ms: u64,
    cpu_ms: u64,
    confirmations: u32,
}

impl WithheldCredit {
    /// The only result a hit can become: the recorded `Unknown` reason, or
    /// `Timeout`. Never `Verified`, `SolverUnsat` or a counterexample.
    pub(crate) fn non_credit_result(&self) -> AYResult {
        self.outcome.replayed(&self.reason)
    }

    #[cfg(test)]
    pub(crate) fn outcome(&self) -> UncertifiedOutcome {
        self.outcome
    }

    #[cfg(test)]
    pub(crate) fn tier(&self) -> MemoTier {
        self.tier
    }

    /// One diagnostic line (never parsed for authority).
    pub(crate) fn describe(&self) -> String {
        format!(
            "tier={} kind={} reuses={}/{} process_hit={} age_s={} recorded_solve_ms={} recorded_cpu_ms={} confirmations={}",
            self.tier.label(),
            self.outcome.label(),
            self.reuses,
            self.reuse_budget,
            self.process_hits,
            self.age.as_secs(),
            self.solve_ms,
            self.cpu_ms,
            self.confirmations,
        )
    }
}

/// One replay's view of the memo: its key, its per-box directory (`None`:
/// in-process tier only), its retry policy, whether the replay saw a SAT
/// verdict, and the solver and checker deadline expiries it saw (apart).
pub(crate) struct NegativeMemoScope {
    key: NegativeMemoKey,
    store: Option<PathBuf>,
    policy: RetryPolicy,
    sat_verdict: AtomicBool,
    /// The solver's deadline expiries.
    solver: ExpiryEvidence,
    /// OD-223: the checker's deadline expiries.
    checker: ExpiryEvidence,
    /// A fresh solve completed with the processor ([`held_processor`]).
    held_completion: AtomicBool,
    /// A fresh solve completed starved or unmeasured.
    unheld_completion: AtomicBool,
}

impl NegativeMemoScope {
    pub(crate) fn new(key: NegativeMemoKey, store: Option<PathBuf>, policy: RetryPolicy) -> Self {
        Self {
            key,
            store,
            policy,
            sat_verdict: AtomicBool::new(false),
            solver: ExpiryEvidence::default(),
            checker: ExpiryEvidence::default(),
            held_completion: AtomicBool::new(false),
            unheld_completion: AtomicBool::new(false),
        }
    }

    #[cfg(test)]
    pub(crate) fn key(&self) -> NegativeMemoKey {
        self.key
    }

    /// The replay saw AY answer SAT on its verdict query: whatever it ends in
    /// is not recorded, and the key's entry is deleted.
    pub(crate) fn note_sat_verdict(&self) {
        self.sat_verdict.store(true, Ordering::Relaxed);
    }

    /// A solver deadline of the replay (the resident or fresh solve, the
    /// model query) expired. `expiry` is what the supervisor measured; `None`
    /// when the deadline was not a supervised one (it ran out before the query
    /// reached the solver, or a component reported the timeout itself). A
    /// `Timeout` is recorded only if every solver expiry of the replay
    /// [`exhausted_budget`].
    pub(crate) fn note_deadline_expiry(&self, expiry: Option<DeadlineExpiry>) {
        self.solver.note(expiry);
    }

    /// OD-223: a checker deadline of the replay (the Clean check of AY's
    /// proof; `None` for the checker's capability probe, which checks no
    /// query's proof) expired. A `CheckerTimeout` is recorded only if every
    /// checker expiry of the replay [`exhausted_budget`]; a checker expiry
    /// never makes a solver `Timeout` recordable, nor withholds one.
    pub(crate) fn note_check_expiry(&self, expiry: Option<DeadlineExpiry>) {
        self.checker.note(expiry);
    }

    /// A fresh solve of the replay ran to completion in `wall`, its process
    /// group using `cpu` (`None`: not measured). A certification failure is
    /// recorded only if every completion of the replay [`held_processor`].
    pub(crate) fn note_solve_completion(&self, wall: Duration, cpu: Option<Duration>) {
        if held_processor(wall, cpu) {
            self.held_completion.store(true, Ordering::Relaxed);
        } else {
            self.unheld_completion.store(true, Ordering::Relaxed);
        }
    }

    /// Whether this replay's certification failure is recordable: at least
    /// one fresh solve completed and every one of them had the processor.
    fn certification_failure_recordable(&self) -> bool {
        self.held_completion.load(Ordering::Relaxed)
            && !self.unheld_completion.load(Ordering::Relaxed)
    }

    /// Honour an entry for this key, or `None`: no entry, or a bound of the
    /// retry policy is spent (the caller then solves). A per-box read counts
    /// one reuse and keeps the entry in this process, where it answers up to
    /// the process budget.
    pub(crate) fn lookup(&self) -> Option<WithheldCredit> {
        self.lookup_at(now_unix_ms())
    }

    fn lookup_at(&self, now_ms: u64) -> Option<WithheldCredit> {
        let in_process = {
            let mut memo = process_memo().lock().unwrap_or_else(|p| p.into_inner());
            match memo.entries.get_mut(&self.key) {
                Some(slot) if !self.policy.admits_process_hit(slot, now_ms) => return None,
                Some(slot) => {
                    slot.hits += 1;
                    Some((slot.entry.clone(), slot.hits))
                }
                None => None,
            }
        };
        let (entry, process_hits, tier) = match in_process {
            Some((entry, hits)) => (entry, hits, MemoTier::Process),
            None => (self.reuse_from_store(now_ms)?, 1, MemoTier::Store),
        };
        Some(WithheldCredit {
            outcome: entry.outcome,
            reason: entry.reason,
            tier,
            reuses: entry.reuses,
            reuse_budget: self.policy.reuse_budget(entry.confirmations),
            process_hits,
            age: Duration::from_millis(now_ms.saturating_sub(entry.recorded_unix_ms)),
            solve_ms: entry.solve_ms,
            cpu_ms: entry.cpu_ms,
            confirmations: entry.confirmations,
        })
    }

    /// The per-box read-modify-write of one reuse, under the namespace lock:
    /// the entry is read, its reuse counted and written back, and it enters
    /// this process, with no delete able to interleave.
    fn reuse_from_store(&self, now_ms: u64) -> Option<Entry> {
        let dir = self.store.as_deref()?;
        let _lock = StoreLock::acquire(dir)?;
        let mut entry = read_entry(dir, &self.key)?;
        if !self.policy.admits_reuse(&entry, now_ms) {
            return None;
        }
        entry.reuses += 1;
        write_entry(dir, &self.key, &entry).ok()?;
        process_memo()
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .insert(
                self.key,
                ProcessSlot {
                    entry: entry.clone(),
                    hits: 1,
                    entered_ms: now_ms,
                },
            );
        Some(entry)
    }

    /// Record what a replay produced. Only a `LiveSolve` outcome the memo
    /// classifies, from a replay that saw no SAT verdict, creates or refreshes
    /// an entry: a `Timeout` only when every solver deadline expiry of the
    /// replay used its budget in CPU time, a `CheckerTimeout` only when every
    /// checker deadline expiry did, a certification failure only when every
    /// fresh solve of the replay had the processor; a `Verified` or a
    /// counterexample (from any source), or any outcome after a SAT verdict,
    /// deletes it; every other result (errors, unclassified reasons, a
    /// starved, unmeasured or unexplained timeout or completion, a memo's own
    /// replay, a solver that did not run) leaves it.
    pub(crate) fn observe(&self, result: &AYResult, source: &AyVerdictSource, solve: Duration) {
        self.observe_at(result, source, solve, now_unix_ms());
    }

    fn observe_at(
        &self,
        result: &AYResult,
        source: &AyVerdictSource,
        solve: Duration,
        now_ms: u64,
    ) {
        if self.sat_verdict.load(Ordering::Relaxed)
            || matches!(result, AYResult::Verified | AYResult::CounterExample(_))
        {
            self.forget();
            return;
        }
        if *source != AyVerdictSource::LiveSolve {
            return;
        }
        let Some((outcome, reason)) = UncertifiedOutcome::classify(result) else {
            return;
        };
        let cpu_ms = if outcome.is_deadline() {
            // A solver timeout is judged on the solver's expiries, a checker
            // timeout on the checker's (OD-223).
            let (evidence, whose) = if outcome == UncertifiedOutcome::Timeout {
                (&self.solver, "solver")
            } else {
                (&self.checker, "checker")
            };
            let Some(cpu_ms) = evidence.recordable_cpu_ms() else {
                if crate::diag::solve_trace_enabled() {
                    eprintln!(
                        "TCG_SOLVE_TRACE source_bound_negative_memo_skip {} not recorded: \
                         the replay's {whose} deadline expiries do not all show \
                         {BUDGET_EXHAUSTING_CPU_PERCENT}% of the deadline used in CPU time \
                         (exhausting={} starved_or_unmeasured={}) solve_ms={}",
                        outcome.label(),
                        evidence.exhausting.load(Ordering::Relaxed),
                        evidence.unproven.load(Ordering::Relaxed),
                        solve.as_millis(),
                    );
                }
                return;
            };
            cpu_ms
        } else {
            if !self.certification_failure_recordable() {
                if crate::diag::solve_trace_enabled() {
                    eprintln!(
                        "TCG_SOLVE_TRACE source_bound_negative_memo_skip {} not recorded: \
                         the replay's fresh solves did not all spend \
                         {PROCESSOR_HELD_CPU_PERCENT}% of their wall-clock time in CPU time \
                         (held={} starved_or_unmeasured={}) solve_ms={}",
                        outcome.label(),
                        self.held_completion.load(Ordering::Relaxed),
                        self.unheld_completion.load(Ordering::Relaxed),
                        solve.as_millis(),
                    );
                }
                return;
            }
            0
        };
        let solve_ms = u64::try_from(solve.as_millis()).unwrap_or(u64::MAX);
        let record = |previous: Option<u32>| Entry {
            outcome,
            reason: reason.clone(),
            recorded_unix_ms: now_ms,
            solve_ms,
            cpu_ms,
            reuses: 0,
            confirmations: previous.map_or(1, |count| count.saturating_add(1)),
        };
        let in_process = {
            let memo = process_memo().lock().unwrap_or_else(|p| p.into_inner());
            memo.entries
                .get(&self.key)
                .map(|slot| slot.entry.confirmations)
        };
        let lock = self.store.as_deref().and_then(StoreLock::acquire);
        let entry = match (&self.store, &lock) {
            (Some(dir), Some(_)) => {
                let entry = record(
                    in_process
                        .or_else(|| read_entry(dir, &self.key).map(|entry| entry.confirmations)),
                );
                let _ = write_entry(dir, &self.key, &entry);
                prune(dir, &self.policy, now_ms, &self.key);
                entry
            }
            _ => record(in_process),
        };
        process_memo()
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .insert(
                self.key,
                ProcessSlot {
                    entry,
                    hits: 0,
                    entered_ms: now_ms,
                },
            );
        drop(lock);
    }

    /// Delete the key's entry in both tiers. The per-box delete holds the
    /// namespace lock, so it serializes with every reuse write-back.
    fn forget(&self) {
        let dir = self.store.as_deref();
        let on_disk =
            dir.is_some_and(|dir| std::fs::symlink_metadata(entry_path(dir, &self.key)).is_ok());
        let lock = if on_disk {
            dir.and_then(StoreLock::acquire)
        } else {
            None
        };
        process_memo()
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .remove(&self.key);
        if let Some(dir) = dir
            && on_disk
        {
            let _ = std::fs::remove_file(entry_path(dir, &self.key));
        }
        drop(lock);
    }
}

/// The deadline expiries of one kind (the solver's, or the checker's) that a
/// replay saw.
#[derive(Default)]
struct ExpiryEvidence {
    /// A deadline expired with evidence that it was used.
    exhausting: AtomicBool,
    /// A deadline expired WITHOUT that evidence (starved or unmeasured).
    unproven: AtomicBool,
    /// The largest CPU time, in nanoseconds, of the exhausting expiries.
    cpu_nanos: AtomicU64,
}

impl ExpiryEvidence {
    fn note(&self, expiry: Option<DeadlineExpiry>) {
        match expiry {
            Some(expiry) if exhausted_budget(&expiry) => {
                let cpu = expiry.cpu.unwrap_or_default();
                let nanos = u64::try_from(cpu.as_nanos()).unwrap_or(u64::MAX);
                self.cpu_nanos.fetch_max(nanos, Ordering::Relaxed);
                self.exhausting.store(true, Ordering::Relaxed);
            }
            _ => self.unproven.store(true, Ordering::Relaxed),
        }
    }

    /// The CPU time (in milliseconds, rounded up) that makes a timeout of
    /// this kind recordable: at least one deadline expired and every one of
    /// them was used. `None`: a starved, unmeasured or unexplained timeout,
    /// which is not recorded.
    fn recordable_cpu_ms(&self) -> Option<u64> {
        if !self.exhausting.load(Ordering::Relaxed) || self.unproven.load(Ordering::Relaxed) {
            return None;
        }
        let nanos = self.cpu_nanos.load(Ordering::Relaxed);
        Some(nanos.div_ceil(1_000_000)).filter(|ms| *ms > 0)
    }
}

fn entry_path(dir: &Path, key: &NegativeMemoKey) -> PathBuf {
    dir.join(format!("{}.negmemo", key.hex()))
}

/// The per-box namespace's advisory lock: an exclusive `flock` on
/// `<dir>/.lock`, held for one read-modify-write or delete. The lock file is
/// never removed, so every holder locks the same inode.
struct StoreLock {
    _file: std::fs::File,
}

impl StoreLock {
    fn acquire(dir: &Path) -> Option<Self> {
        trust_cg_process_env::private_fs::create_private_dir_all(dir).ok()?;
        let path = dir.join(".lock");
        let file = open_regular(&path, true)?;
        let deadline = Instant::now() + LOCK_WAIT;
        loop {
            match file.try_lock() {
                Ok(()) => return Some(Self { _file: file }),
                Err(std::fs::TryLockError::WouldBlock) if Instant::now() < deadline => {
                    std::thread::sleep(Duration::from_millis(2));
                }
                Err(_) => return None,
            }
        }
    }
}

/// Open `path` only if it is a regular file: its type is checked before the
/// open (so a FIFO or device is never opened), the open never follows a link
/// and never blocks, and the opened file must still be a regular file (an
/// entry renamed over in between is another regular file, which is fine).
/// `create` makes a missing file (the lock).
fn open_regular(path: &Path, create: bool) -> Option<std::fs::File> {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_file() => {}
        Ok(_) => return None,
        Err(error) if create && error.kind() == std::io::ErrorKind::NotFound => {}
        Err(_) => return None,
    }
    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    if create {
        options.write(true).create(true);
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
            .mode(0o600);
    }
    let file = options.open(path).ok()?;
    file.metadata().ok()?.file_type().is_file().then_some(file)
}

fn read_entry(dir: &Path, key: &NegativeMemoKey) -> Option<Entry> {
    let file = open_regular(&entry_path(dir, key), false)?;
    if file.metadata().ok()?.len() > MAX_ENTRY_BYTES {
        return None;
    }
    let mut text = String::new();
    file.take(MAX_ENTRY_BYTES + 1)
        .read_to_string(&mut text)
        .ok()?;
    if text.len() as u64 > MAX_ENTRY_BYTES {
        return None;
    }
    Entry::parse(&text, key)
}

/// Publish `entry` atomically: a fresh temporary file in the same directory,
/// renamed over the entry. Callers hold the namespace lock.
fn write_entry(dir: &Path, key: &NegativeMemoKey, entry: &Entry) -> std::io::Result<()> {
    trust_cg_process_env::private_fs::create_private_dir_all(dir)?;
    let mut staged = tempfile::Builder::new()
        .prefix(".negmemo-")
        .tempfile_in(dir)?;
    // No fsync: a file a crash leaves incomplete parses as a miss.
    staged.write_all(entry.serialize(key).as_bytes())?;
    staged
        .persist(entry_path(dir, key))
        .map(|_| ())
        .map_err(|error| error.error)
}

/// Remove, from a bounded window of the namespace (positioned by `seed`, so
/// successive recordings visit all of it), every entry that no longer
/// answers (older than the age bound, recorded in the future, unreadable,
/// not a regular file) and every staging file a dead writer left. Callers
/// hold the namespace lock.
fn prune(dir: &Path, policy: &RetryPolicy, now_ms: u64, seed: &NegativeMemoKey) {
    let Ok(listing) = std::fs::read_dir(dir) else {
        return;
    };
    let mut names: Vec<std::ffi::OsString> = listing
        .take(PRUNE_LISTING_CAP)
        .filter_map(|entry| entry.ok().map(|entry| entry.file_name()))
        .collect();
    if names.is_empty() {
        return;
    }
    names.sort();
    let start = (usize::from(seed.0[0]) << 8) | usize::from(seed.0[1]);
    let count = names.len();
    for offset in 0..PRUNE_WINDOW.min(count) {
        let name = &names[(start + offset) % count];
        let Some(text) = name.to_str() else {
            continue;
        };
        let path = dir.join(name);
        if let Some(hex) = text.strip_suffix(".negmemo") {
            let keep = NegativeMemoKey::from_hex(hex)
                .and_then(|key| read_entry(dir, &key))
                .is_some_and(|entry| policy.fresh(&entry, now_ms));
            let is_dir = std::fs::symlink_metadata(&path).is_ok_and(|m| m.is_dir());
            if !keep && !is_dir {
                let _ = std::fs::remove_file(&path);
            }
        } else if text.starts_with(".negmemo-")
            && let Ok(metadata) = std::fs::symlink_metadata(&path)
            && metadata.file_type().is_file()
            && metadata
                .modified()
                .ok()
                .and_then(|modified| modified.elapsed().ok())
                .is_some_and(|age| age > STALE_STAGING)
        {
            let _ = std::fs::remove_file(&path);
        }
    }
}

fn now_unix_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |elapsed| {
            u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
        })
}

/// An entry held by this process: the entry, the hits it answered here and
/// when it entered the process (recorded here, or read from the store).
struct ProcessSlot {
    entry: Entry,
    hits: u32,
    entered_ms: u64,
}

#[derive(Default)]
struct ProcessMemo {
    entries: HashMap<NegativeMemoKey, ProcessSlot>,
    order: VecDeque<NegativeMemoKey>,
}

impl ProcessMemo {
    fn insert(&mut self, key: NegativeMemoKey, slot: ProcessSlot) {
        if self.entries.insert(key, slot).is_none() {
            self.order.push_back(key);
        }
        while self.entries.len() > PROCESS_CAPACITY {
            match self.order.pop_front() {
                Some(evicted) => {
                    self.entries.remove(&evicted);
                }
                None => break,
            }
        }
    }

    fn remove(&mut self, key: &NegativeMemoKey) {
        if self.entries.remove(key).is_some() {
            self.order.retain(|candidate| candidate != key);
        }
    }
}

fn process_memo() -> &'static Mutex<ProcessMemo> {
    static MEMO: OnceLock<Mutex<ProcessMemo>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(ProcessMemo::default()))
}

/// Serializes the tests that clear or assert on the process-wide tier.
#[cfg(test)]
pub(crate) fn test_lock() -> std::sync::MutexGuard<'static, ()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// Forget every in-process entry, as a new process would start (tests hold
/// [`test_lock`]).
#[cfg(test)]
pub(crate) fn forget_process_tier_for_test() {
    let mut memo = process_memo().lock().unwrap_or_else(|p| p.into_inner());
    memo.entries.clear();
    memo.order.clear();
}

#[cfg(test)]
#[path = "source_bound_negative_memo_tests.rs"]
mod tests;
