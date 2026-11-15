// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! This host's qualification record, and the one way to read it.
//!
//! The per-host record is private to this module: the recorded gaps this
//! host's pair certifies ([`CERTIFIED_HERE_BY_HOST`]), the outcomes it
//! reaches for another reason ([`OUTCOME_HERE_BY_HOST`]), the gaps it adds
//! ([`ALSO_UNCERTIFIED_HERE_BY_HOST`]) and the answers that depend on the
//! deadline ([`DEADLINE_BOUND_HERE_BY_HOST`]), with every function that
//! reads them. Outside this module the record is reachable only through the
//! `pub(crate)` readers below, each of which takes a [`QualifiedPair`], and
//! only [`assert_qualification_replayer`] can construct one (its field is
//! private here too). Every lane lives in this module's parent,
//! `x86_source_bound_body::tests`, or in one of its siblings, and neither
//! can name a private item of this module, so Rust's privacy, not a
//! convention each lane must remember, keeps every lane from comparing with
//! this record, or branching on it, before it has checked the pair
//! (DR-PER-HOST-QUALIFIED-PAIR-20261015, "Every lane checks the pair").

use super::{
    QUALIFIED_AY, ReplayIdentity, SELF_CHECK_REJECTED, Uncertified, current_host_triple,
    qualified_clean_sha256, replay_identity,
};

/// Evidence that the replayer pair a lane admitted is the pair this
/// host's outcomes were recorded with ([`assert_qualification_replayer`]).
///
/// Every reader of this module's record takes one: the per-host gap view
/// ([`recorded_gaps`], [`recorded_gap_labels`], [`gap_applies_here`],
/// [`gap_branch_here`]), the per-host outcome and class
/// ([`recorded_outcome`], [`recorded_proof_gate_class`]) and the
/// deadline-bound record ([`deadline_answer_here`], [`settle_here`],
/// [`deadline_bound_entries_here`]).
///
/// What it does not gate: the per-slice tables (each `KNOWN_UNCERTIFIED*`
/// and the encoding-outcome tables, such as slice 1's `UF_WORLD_OUTCOMES`,
/// slice 6's `REJECTED_SPELLINGS` and the memory lane's
/// `MEMORY_ENCODING_OUTCOMES`) are plain constants of `tests` and its lane
/// modules, which any lane can read. Lanes read them to list labels or to
/// print a gap's recorded tool output, before or after the check, and
/// compare outcomes with them after it: slices 1, 6, 9 and 16 and the memory
/// lane compare with one directly. That ordering is each lane's own, not the
/// compiler's: slice 16's two lanes check the pair, drop the witness and
/// compare with their own tables alone. Slice 9's spellings lane and slice
/// 17's mis-model lane check the pair last and read no table; they hold each
/// replay to being refuted or not. A lane that replays under the admitted
/// pair and reads no record needs no witness; it says why where it runs.
pub(crate) struct QualifiedPair(());

/// The libtest filter of a host's qualification (`--lib _qualification`).
/// On `aarch64-apple-darwin` the record's
/// `reports/perf/2026-10-16-darwin-aarch64-ay12713-qualification/commands/qualify.sh`
/// runs it, then the explicit lane, and checks how many lanes each ran; the
/// x86-64 hosts' records have no such command, and the filter runs there by
/// hand with that host's qualified Clean named.
/// [`assert_qualification_replayer`] refuses a lane whose test name it does
/// not select, so a lane that reads this record but is named outside the
/// filter fails wherever it runs (the default library suite).
const QUALIFICATION_FILTER: &str = "_qualification";

/// Refuse to compare pinned qualification outcomes under another replayer
/// pair: a different AY or checker can certify or reject differently, and a
/// changed outcome there is a re-qualification, not a regression. Returns
/// the evidence every reader of a recorded outcome requires.
///
/// It also refuses a lane that the qualification command's filter
/// ([`QUALIFICATION_FILTER`]) does not select, read from the name libtest
/// gives the lane's thread (its full test path). Every lane that reads this
/// record calls this before it reads it (some only after all their
/// replays), so such a lane named outside the command fails wherever it
/// runs; slice 1's and slice 4's credit lanes sat outside it until
/// 2026-10-17. The command itself checks how many lanes it ran
/// (DR-PER-HOST-QUALIFIED-PAIR-20261015, "Every lane fails closed").
#[track_caller]
pub(crate) fn assert_qualification_replayer(
    edits: &[(&'static str, std::ffi::OsString)],
) -> QualifiedPair {
    let lane = std::thread::current().name().map(str::to_owned);
    assert!(
        lane.as_deref()
            .is_some_and(|name| name.contains(QUALIFICATION_FILTER)),
        "lane {lane:?} reads the host qualification record, but the qualification command's \
         filter `--lib {QUALIFICATION_FILTER}` does not select it, so no qualification runs \
         it: name the lane (or its module) with `{QUALIFICATION_FILTER}`"
    );
    let identity = replay_identity(edits).expect("admitted by replay_environment");
    let Some(qualified_clean) = qualified_clean_sha256() else {
        panic!(
            "no qualified replayer pair is recorded for host {}; its outcomes are evidence \
             about nothing. Record one in QUALIFIED_CLEAN_SHA256_BY_HOST from a real run on \
             it, with the recorded gaps and encoding outcomes, before comparing",
            current_host_triple()
        );
    };
    assert!(
        is_qualified_pair(&identity, qualified_clean),
        "the pinned qualification outcomes for host {} were measured with [{QUALIFIED_AY}] \
         and Clean sha256 {qualified_clean}; this host admits [{}] and Clean sha256 {}. \
         Re-qualify: review every outcome printed above, then update the recorded gaps, the \
         encoding outcomes, LIMITATIONS.md and this host's entry together",
        current_host_triple(),
        identity.ay,
        identity.clean_sha256
    );
    QualifiedPair(())
}

/// Whether `identity` is the recorded pair: the AY's build identity equal to
/// [`QUALIFIED_AY`] and the checker's bytes the host's `qualified_clean`.
/// Equality on the build identity alone, not a search of the AY's whole
/// description, whose route and path the operator chooses.
fn is_qualified_pair(identity: &ReplayIdentity, qualified_clean: &str) -> bool {
    identity.ay_build.as_deref() == Some(QUALIFIED_AY) && identity.clean_sha256 == qualified_clean
}

/// Recorded gaps that THIS host's replayer pair CERTIFIES, per host triple.
///
/// Removing a gap is a STRENGTHENING, not a relaxation: it records that an
/// obligation now carries a proof the recorded pair could not produce. AY
/// build 12713 certifies three obligations on `x86_64-unknown-linux-gnu` that
/// the Darwin pair timed out on, measured 2026-10-15 against the printed
/// outcome of each (DR-QUALIFIED-PAIR-IS-DARWIN-ONLY-20261015). A budget
/// explanation was refuted first: at 240 s, 8x the lane's 30 s deadline, the
/// set is unchanged. On `aarch64-apple-darwin` (AY build 12713, Clean
/// `92bcc8979`, measured 2026-10-16) `SubU128` and `SlotU128` certify inside
/// the 30 s deadline on every run (8.4-27.2 s, the slowest at load 54-71),
/// and `EarlyExit`, which certifies on all but one, is deadline-bound there
/// ([`DEADLINE_BOUND_HERE_BY_HOST`]).
///
/// A label here must CERTIFY on the named host. If it stops certifying the
/// test fails, because the gap is then missing from the recorded set.
///
/// `SlotU128` certified on both hosts too, and `EarlyExit` on Linux; since
/// slice 18's spelling (OD-187 and OD-188) neither is a gap of its table on
/// the Darwin x86-64 pair, so every host holds them to certifying without an
/// entry here. The two hosts' other entries (and `aarch64-apple-darwin`'s
/// deadline-bound ones below) were measured on the spelling before slice 18,
/// which moved every conjunctive theorem's bytes: they are re-qualified only
/// by a run on their own host (the slice-18 report lists what that run must
/// re-measure).
///
/// That run on `aarch64-apple-darwin` (2026-10-19, AY build 12713,
/// `commands/qualify.sh` of the host's report on slice 18's code, section
/// "Gates on the merged tree onto 787d8e25c") held every entry of this host
/// but one row: slice 10's `MulU64`, which the Darwin x86-64 pair still times
/// out on at 30 s, certifies here inside the deadline (16.95 s at a 1-minute
/// load near 5, and again in its credit lane), so both slice-10 lanes failed
/// on the recorded gap. It is this host's entry since then.
///
/// Since 2026-10-19 [`QUALIFIED_AY`] is AY build 13556 (OD-190), which
/// certifies `SubU128` on the Darwin x86-64 pair, so it is no gap of its
/// table and the two `SubU128` entries below name no recorded gap: every
/// host holds it to certifying. The `aarch64-apple-darwin` entries are kept
/// as that host's record of AY build 12713; the pair check refuses it until
/// it runs build 13556 and re-measures its own outcomes.
///
/// `x86_64-unknown-linux-gnu` HAS re-measured, on 2026-10-20 with AY build
/// 13556 (`ebde49de3`, binary SHA-256 `393e1bc9…`, a native stage-1 build
/// installed at the build compiler's sysroot `bin/ay`) and the same Clean
/// (`9547de64…`): `-p trust-cg-verify --lib x86_source_bound_body` read 366
/// passed, 4 failed, and the four were this host's two gap lanes for slice 10
/// and slice 14, each failing because an obligation it RECORDED as a gap now
/// certifies. Build 13556 is the whole difference; nothing else moved.
/// Slice 10's `MulU64` certifies here in 13.52-13.59 s inside the 30 s
/// deadline, three runs at 1-minute loads 0.47-0.88, where build 12713 timed
/// out, so it is this host's entry below. Slice 14's `GuardedUdiv` and
/// `GuardThenCall` certify in 166-174 ms and 109 ms, three runs at loads
/// 0.64-1.86, where build 12713 needed a 300 s budget: they are removed from
/// [`ALSO_UNCERTIFIED_HERE_BY_HOST`]. At 0.1-0.2 s against a 30 s deadline
/// neither is near it, so neither becomes deadline-bound. Slice 14's own
/// recorded gaps `UdivConst` and `UremConst32` still time out at 30.01 s on
/// every run, unchanged.
/// Report: `reports/perf/2026-10-20-linux-x86-64-ay13556-requalification/`.
const CERTIFIED_HERE_BY_HOST: &[(&str, &str)] = &[
    ("x86_64-unknown-linux-gnu", "SubU128"),
    ("x86_64-unknown-linux-gnu", "MulU64"),
    ("aarch64-apple-darwin", "SubU128"),
    ("aarch64-apple-darwin", "MulU64"),
];

/// A recorded gap's outcome on a host that reaches it differently, per host
/// triple: `(host, label, outcome)`.
///
/// Neither a strengthening nor a weakening — the obligation is uncertified on
/// both pairs and only the REASON differs, so recording the reason this pair
/// actually gives is the truthful entry. An unlisted (host, label) keeps the
/// table's own outcome.
const OUTCOME_HERE_BY_HOST: &[(&str, &str, &str, &str)] = &[
    // `MulI16` is uncertified on both pairs — AY bit-blasts a multiplier and
    // has no Alethe derivation for one — but the two pairs stop for different
    // reasons: the Darwin pair ran out its deadline, while AY build 12713 on
    // this host answers `unknown` because its own self-check rejected the
    // incomplete proof. Recording the reason this pair gives keeps the
    // outcome exact; the obligation is credited by neither.
    (
        "x86_64-unknown-linux-gnu",
        "MulI16",
        "Unknown(\"(:reason-unknown (incomplete self-check-rejected))\")",
        // A proof-authority rejection is SOUNDNESS class, where a deadline is
        // a capacity one. Both leave the row Unverified — the live
        // source-bound lanes never credit and never fail such a row — so the
        // obligation is uncredited under either pair; only the reason the
        // lane records differs.
        "SOUNDNESS",
    ),
];

/// Gaps THIS host's pair hits that the recorded pair did not, per host triple
/// and per table label, with the same evidence every recorded gap carries.
///
/// An entry records LESS proving than the baseline, so it must state the
/// measured offline answer, exactly as the tables do — whether the obligation
/// certifies given time (a budget difference) or not at all (a capability one,
/// as for `MulU128`, which answers `unknown` at eight times the deadline).
/// The lane's 30 s deadline is deliberately left alone: raising it would move
/// the recorded sets of every host, which is not one host's call to make.
///
/// EMPTY since 2026-10-20. It held two entries, both for
/// `x86_64-unknown-linux-gnu` and both slice 14's: `GuardedUdiv` and
/// `GuardThenCall`, which AY build 12713 could not answer inside the lane's
/// 30 s deadline on this host (they needed a 300 s budget; measured
/// 2026-10-15). Under [`QUALIFIED_AY`], build 13556, they certify in
/// 166-174 ms and 109 ms, three runs each at 1-minute loads 0.64-1.86 —
/// 0.1-0.2 s against a 30 s deadline, so neither is near it and neither
/// becomes deadline-bound. Removing them records MORE proving, so the
/// baseline is unchanged and nothing here is weakened; the entries are gone
/// rather than relaxed. Report:
/// `reports/perf/2026-10-20-linux-x86-64-ay13556-requalification/`.
const ALSO_UNCERTIFIED_HERE_BY_HOST: &[(&str, &str, Uncertified)] = &[];

/// One obligation whose answer at the lane's 30 s deadline depends on the
/// host's state ([`DEADLINE_BOUND_HERE_BY_HOST`]).
pub(crate) struct DeadlineBound {
    /// The case label.
    pub(crate) label: &'static str,
    /// Every answer measured for it at the deadline on the host, as the lane
    /// prints it ([`stable_outcome`](super::stable_outcome)) with the class
    /// `proof_gate` gives it; [`VERIFIED_ANSWER`] when some runs certify.
    pub(crate) answers: &'static [(&'static str, &'static str)],
    /// The measured frequency of each answer, and the offline answer.
    pub(crate) tool_output: &'static str,
}

impl DeadlineBound {
    /// Whether some runs certify it at the deadline on the host.
    pub(crate) fn some_runs_certify(&self) -> bool {
        self.answers.contains(&VERIFIED_ANSWER)
    }

    /// Whether `(outcome, class)` is one of the answers measured for it.
    pub(crate) fn is_measured(&self, outcome: &str, class: &str) -> bool {
        self.answers.contains(&(outcome, class))
    }
}

/// A run that certifies.
const VERIFIED_ANSWER: (&str, &str) = ("Verified", "PASS");
/// A run past the deadline.
const TIMEOUT_ANSWER: (&str, &str) = ("Timeout", "PENDING(solver-capacity)");
/// A run in which AY rejects its own proof.
const SELF_CHECK_REJECTED_ANSWER: (&str, &str) = (SELF_CHECK_REJECTED, "SOUNDNESS");

/// Obligations whose answer at the lane's 30 s deadline depends on the
/// host's state, per host triple and table. On a host shared with other
/// builds, an obligation that needs most of the deadline answers one way on
/// one run and another way on the next, so a record of one answer makes its
/// lane fail on a coin toss and none of [`CERTIFIED_HERE_BY_HOST`],
/// [`OUTCOME_HERE_BY_HOST`] or [`ALSO_UNCERTIFIED_HERE_BY_HOST`] is true of
/// it. An entry names every answer measured there, outcome and `proof_gate`
/// class, and a gap lane accepts no other:
///
/// * one that some runs certify is in no recorded gap list
///   ([`recorded_gaps`]); its gap lane drops it only when it carries a
///   measured answer ([`settle_here`]), and its credit lane takes every bound
///   row credited or every bound row awaiting replay, never a mix
///   ([`gap_branch_here`]). An awaiting row does not say why it awaits, so
///   the credit lane cannot hold that answer to the measured ones; the gap
///   lane, which reads the answer, is what refuses an unmeasured one;
/// * one that no run certifies stays a recorded gap, and its lane accepts any
///   of its measured answers for it ([`deadline_answer_here`],
///   [`settle_here`]).
///
/// An entry takes effect only in a lane that reads these helpers (slices 1,
/// 12, 14, 20 and 24c); a lane that does not keeps its exact comparison, so an entry
/// for its table fails it closed. Slice 1 reads only an entry that no run
/// certifies: one that some runs certify drops its label from
/// [`recorded_gap_labels`], which slice 1's gap lane still lists whenever the
/// label does not certify, so that lane fails closed on it. The 30 s lanes
/// cannot notice a label some runs certify ceasing to certify on its host
/// altogether, since they accept `Timeout` for it on every run; the explicit
/// lane
/// [`host_qualification_replays_each_deadline_bound_label_with_the_recorded_budget`](super::host_qualification_replays_each_deadline_bound_label_with_the_recorded_budget)
/// replays every entry with the record's 300 s budget and fails if one such
/// label does not certify there, or if a label no run certifies does or
/// gives an answer not measured for it. The lane's 30 s deadline is not
/// raised for these: that would move every host's recorded set.
const DEADLINE_BOUND_HERE_BY_HOST: &[(&str, &str, DeadlineBound)] = &[
    // `aarch64-apple-darwin`, AY build 12713 with Clean 92bcc8979, measured
    // 2026-10-16 through the recording run (confirm 4), at 1-minute loads of
    // 4 to 71 from other builds on 18 CPUs (`reports/perf/2026-10-16-darwin-
    // aarch64-ay12713-qualification/`). A lane run counts once per obligation:
    // measure 0 to confirm 4, seven runs.
    (
        "aarch64-apple-darwin",
        "KNOWN_UNCERTIFIED",
        DeadlineBound {
            label: "MulI16",
            answers: &[SELF_CHECK_REJECTED_ANSWER, TIMEOUT_ANSWER],
            tool_output: "ay (AY build 12713, aarch64-apple-darwin): rejects its own incomplete \
                 proof of the 16-bit multiply (`step t1 uses unsupported hole rule`) in 17.6-19.0 \
                 s offline at load 8-10 (6 of 6), 20.8 s with twelve replays at once (3 of 3) \
                 and 18.9-29.9 s in the lane (6 of 7 runs); the seventh lane run, at load \
                 54-71, ran past the 30 s deadline first. Uncertified either way, under both \
                 classes; the Linux pair's reason, and the Darwin x86-64 pair's deadline",
        },
    ),
    (
        "aarch64-apple-darwin",
        "KNOWN_UNCERTIFIED_SLICE_TWELVE",
        DeadlineBound {
            label: "EarlyExit",
            answers: &[VERIFIED_ANSWER, TIMEOUT_ANSWER],
            tool_output: "ay + clean (AY build 12713, Clean 92bcc8979, aarch64-apple-darwin): \
                 certifies in 17.1-18.6 s offline at 1-minute load 8-10 (6 of 6) and in 20.5 s \
                 with twelve replays at once (3 of 3); in the lane with this pair, at loads of 9 \
                 to 71, in 23.0-38.1 s on 5 of 6 runs (AY inside its 30 s, Clean's check after) \
                 and once past the 30 s deadline, at load 24-47. Load, not capability",
        },
    ),
    // These two certify in a few seconds on some runs and take minutes on
    // others, clustered in time; the 1-minute load does not separate the two
    // (`GuardedUdiv` fast at 9-71 and slow at 8-37, `GuardThenCall` fast at
    // 24-58 and slow at 8-71). `GuardThenCall` ran past the deadline in 5 of
    // the 7 lane runs.
    (
        "aarch64-apple-darwin",
        "KNOWN_UNCERTIFIED_SLICE_FOURTEEN",
        DeadlineBound {
            label: "GuardedUdiv",
            answers: &[VERIFIED_ANSWER, TIMEOUT_ANSWER],
            tool_output: "ay (AY build 12713, aarch64-apple-darwin): 3 of 19 attempts ran past the \
                 30 s deadline (the lane's own replay in 2 of 7 runs; an offline 300 s replay of \
                 its dumped query `unsat` after 75.0 s), 16 certified in 1.6-5.3 s; every \
                 offline `unsat` is `unproved_steps=0 trust_free=yes` and Clean 92bcc8979 fully \
                 verifies it. Budget, not capability",
        },
    ),
    (
        "aarch64-apple-darwin",
        "KNOWN_UNCERTIFIED_SLICE_FOURTEEN",
        DeadlineBound {
            label: "GuardThenCall",
            answers: &[VERIFIED_ANSWER, TIMEOUT_ANSWER],
            tool_output: "ay (AY build 12713, aarch64-apple-darwin): 10 of 19 attempts ran past \
                 the 30 s deadline (the lane's own replay in 5 of 7 runs; 4 of 8 back-to-back \
                 offline 30 s replays; an offline 300 s replay `unsat` after 164.4 s), 9 \
                 certified in 3.3-6.8 s; every offline `unsat` is `unproved_steps=0 \
                 trust_free=yes` and Clean 92bcc8979 fully verifies it. Budget, not capability",
        },
    ),
    // `x86_64-apple-darwin`, AY build 13556 with Clean 5f09e36c (`QUALIFIED_AY`,
    // the `x86-stage1-ay13556` overlay), measured 2026-10-26 for slice 20's
    // variable `I128` shifts (OD-194) at 1-minute loads of 3.2 to 4.0 from
    // other agents' builds and AY runs on 4 cores
    // (`reports/perf/2026-10-26-darwin-x86-64-slice20-rules/`): each needs
    // about the whole 30 s deadline, so its lane answer is a coin toss.
    (
        "x86_64-apple-darwin",
        "KNOWN_UNCERTIFIED_SLICE_TWENTY",
        DeadlineBound {
            label: "U128ShlMasked",
            answers: &[VERIFIED_ANSWER, TIMEOUT_ANSWER],
            tool_output: "ay + clean (AY build 13556, Clean 5f09e36c, x86_64-apple-darwin): in \
                 the lane certified once (40.4 s with Clean's check) and once past the 30 s \
                 deadline; offline at the 30 s budget certified 2 of 2 in 28.4-28.8 s of AY \
                 (42.7 MB proof, Clean 6.5-6.7 s), at 300 s in 28.4 s. Load, not capability",
        },
    ),
    (
        "x86_64-apple-darwin",
        "KNOWN_UNCERTIFIED_SLICE_TWENTY",
        DeadlineBound {
            label: "U128LshrMasked",
            answers: &[VERIFIED_ANSWER, TIMEOUT_ANSWER],
            tool_output: "ay + clean (AY build 13556, Clean 5f09e36c, x86_64-apple-darwin): in \
                 the lane certified once (41.3 s with Clean's check) and once past the 30 s \
                 deadline; offline at the 30 s budget AY answered unsat after 31.0 and 33.7 s \
                 (past its own timeout; 40.3 MB proof, Clean 6.9-7.0 s), at 300 s in 32.7 s. \
                 Budget, not capability",
        },
    ),
    (
        "x86_64-apple-darwin",
        "KNOWN_UNCERTIFIED_SLICE_TWENTY",
        DeadlineBound {
            label: "I128AshrMasked",
            answers: &[VERIFIED_ANSWER, TIMEOUT_ANSWER],
            tool_output: "ay + clean (AY build 13556, Clean 5f09e36c, x86_64-apple-darwin): in \
                 the lane past the 30 s deadline 2 of 2; offline at the 30 s budget `unknown` \
                 at 30.5 s once and unsat after 36.5 s once (AY past its own timeout; 66.6 MB \
                 proof, Clean 7.7 s), at 300 s in 37.5 s (Clean 8.0 s). Budget, not \
                 capability",
        },
    ),
    // `x86_64-apple-darwin`, the same pair, measured 2026-11-05/06 for slice
    // 24c's composition (OD-228) at 1-minute loads of 14 to 43 from other
    // lanes' builds and replays on 8 logical CPUs
    // (`reports/perf/2026-11-05-darwin-x86-64-slice24c-segments/`): slice
    // 9's `SlotJoin` through the O2 pipeline, four segments with private slot
    // bytes in one query, needs about the whole 30 s deadline.
    (
        "x86_64-apple-darwin",
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR_C",
        DeadlineBound {
            label: "s9 SlotJoin O2",
            answers: &[VERIFIED_ANSWER, TIMEOUT_ANSWER],
            tool_output: "ay + clean (AY build 13556, Clean 5f09e36c, x86_64-apple-darwin): in \
                 the lane certified once in 29.5 s; offline at the 30 s budget unsat after \
                 29.6 and 24.0 s at load 15-16, `unknown` (timeout) after 55.9 s and unsat \
                 after 43.0 s (AY past its own timeout) at load 24-26, and `unknown` at \
                 30.6 s three of three with three replays at once (load 43); at 300 s unsat \
                 in 25.9 s (load 14). Budget, not capability",
        },
    ),
];

/// This host's deadline-bound entry for `label` in `table_name`, if any.
fn deadline_bound_here(table_name: &str, label: &str) -> Option<&'static DeadlineBound> {
    let host = current_host_triple();
    DEADLINE_BOUND_HERE_BY_HOST
        .iter()
        .find(|(triple, name, bound)| {
            *triple == host && *name == table_name && bound.label == label
        })
        .map(|(_, _, bound)| bound)
}

/// Whether some runs certify `label` of `table_name` on this host and others
/// do not ([`DEADLINE_BOUND_HERE_BY_HOST`]).
fn certifies_sometimes_here(table_name: &str, label: &str) -> bool {
    deadline_bound_here(table_name, label).is_some_and(DeadlineBound::some_runs_certify)
}

/// For a label deadline-bound on this host, whether `(outcome, class)` is
/// one of its measured answers, printing the recorded evidence; `None` for
/// any other label, which its lane holds to its recorded outcome.
pub(crate) fn deadline_answer_here(
    table_name: &str,
    label: &str,
    outcome: &str,
    class: &str,
    _qualified: &QualifiedPair,
) -> Option<bool> {
    deadline_bound_here(table_name, label).map(|bound| {
        note_deadline_bound(bound, outcome);
        bound.is_measured(outcome, class)
    })
}

/// Print a deadline-bound label's answer next to its recorded evidence, as
/// the lanes print a recorded gap's tool output.
fn note_deadline_bound(bound: &DeadlineBound, outcome: &str) {
    eprintln!(
        "X86_BODY_DEADLINE_BOUND label={} outcome={outcome} measured answers={:?} recorded tool \
         output: {}",
        bound.label, bound.answers, bound.tool_output
    );
}

/// A gap lane's `(label, outcome, proof_gate class)` list as `(label,
/// outcome)`, with this host's deadline-bound gaps of `table_name` settled:
/// one that some runs certify is dropped when it carries a measured answer,
/// and one that no run certifies takes its recorded outcome when it does. An
/// answer is measured only when its outcome and its class both are. Any other
/// answer is marked unmeasured, which no recorded outcome equals, so the
/// comparison with [`recorded_gaps`] refuses it even where the outcome alone
/// matches a recorded one.
pub(crate) fn settle_here(
    observed: Vec<(String, String, &'static str)>,
    table: &'static [Uncertified],
    table_name: &str,
    qualified: &QualifiedPair,
) -> Vec<(String, String)> {
    observed
        .into_iter()
        .filter_map(|(label, outcome, class)| {
            match deadline_answer_here(table_name, &label, &outcome, class, qualified) {
                None => Some((label, outcome)),
                Some(false) => Some((
                    label,
                    format!(
                        "{outcome} / {class}: not an answer measured for it at the deadline on \
                         this host"
                    ),
                )),
                Some(true) if certifies_sometimes_here(table_name, &label) => None,
                Some(true) => {
                    let recorded = table
                        .iter()
                        .chain(also_uncertified_here(table_name))
                        .find(|gap| gap.label == label)
                        .map_or(outcome, |gap| recorded_outcome(gap, qualified).to_owned());
                    Some((label, recorded))
                }
            }
        })
        .collect()
}

/// This host's extra gaps for `table`, in the order the lane produces them
/// (after the table's own, which the shape iteration reaches first).
fn also_uncertified_here(table_name: &str) -> Vec<&'static Uncertified> {
    let host = current_host_triple();
    ALSO_UNCERTIFIED_HERE_BY_HOST
        .iter()
        .filter(|(triple, name, _)| *triple == host && *name == table_name)
        .map(|(_, _, gap)| gap)
        .collect()
}

/// Whether `label` is one this host certifies though the table records a gap.
fn certified_here(label: &str) -> bool {
    let host = current_host_triple();
    CERTIFIED_HERE_BY_HOST
        .iter()
        .any(|(triple, gap)| *triple == host && *gap == label)
}

/// The outcome to hold a gap to on this host: its per-host override, else the
/// table's recorded outcome.
pub(crate) fn recorded_outcome(gap: &Uncertified, _qualified: &QualifiedPair) -> &'static str {
    let host = current_host_triple();
    OUTCOME_HERE_BY_HOST
        .iter()
        .find(|(triple, label, _, _)| *triple == host && *label == gap.label)
        .map_or(gap.outcome, |(_, _, outcome, _)| *outcome)
}

/// The proof-gate class to hold a gap to on this host. It moves with
/// [`recorded_outcome`]: the class is a function of the outcome, so a per-host
/// outcome without its class would hold the row to a class its own outcome
/// cannot produce.
pub(crate) fn recorded_proof_gate_class(
    gap: &Uncertified,
    _qualified: &QualifiedPair,
) -> &'static str {
    let host = current_host_triple();
    OUTCOME_HERE_BY_HOST
        .iter()
        .find(|(triple, label, _, _)| *triple == host && *label == gap.label)
        .map_or(gap.proof_gate_class, |(_, _, _, class)| *class)
}

/// The recorded gaps that still apply on this host, as `(label, outcome)`:
/// the table minus what this host certifies, with per-host outcomes applied.
/// A gap that some runs certify here ([`DEADLINE_BOUND_HERE_BY_HOST`]) is in
/// neither this list nor, once settled ([`settle_here`]), the lane's.
pub(crate) fn recorded_gaps(
    table: &'static [Uncertified],
    table_name: &str,
    qualified: &QualifiedPair,
) -> Vec<(String, String)> {
    table
        .iter()
        .filter(|gap| !certified_here(gap.label))
        .chain(also_uncertified_here(table_name))
        .filter(|gap| !certifies_sometimes_here(table_name, gap.label))
        .map(|gap| {
            (
                gap.label.to_owned(),
                recorded_outcome(gap, qualified).to_owned(),
            )
        })
        .collect()
}

/// Whether `table`'s gap for `label` applies on THIS host: recorded, and not
/// one this host certifies. The credit lanes branch on it — a shape with a gap
/// has every bound row awaiting replay, a shape without one must carry body
/// credit — so they must read the same per-host view as the gap lanes, or a
/// newly certified shape is held to the uncertified branch.
pub(crate) fn gap_applies_here(
    table: &'static [Uncertified],
    table_name: &str,
    label: &str,
    _qualified: &QualifiedPair,
) -> bool {
    !certifies_sometimes_here(table_name, label)
        && ((table.iter().any(|gap| gap.label == label) && !certified_here(label))
            || also_uncertified_here(table_name)
                .iter()
                .any(|gap| gap.label == label))
}

/// Whether a credit lane holds `label`'s rows to the gap branch (every bound
/// row awaiting replay, no failure, no export) on this host: its gap applies
/// here ([`gap_applies_here`]), or some runs certify it here
/// ([`DEADLINE_BOUND_HERE_BY_HOST`]) and this replay left `awaiting` rows
/// awaiting. One awaiting row of such a gap holds it to all of them, so a mix
/// of credited and awaiting rows fails either way.
pub(crate) fn gap_branch_here(
    table: &'static [Uncertified],
    table_name: &str,
    label: &str,
    awaiting: usize,
    qualified: &QualifiedPair,
) -> bool {
    gap_applies_here(table, table_name, label, qualified)
        || (certifies_sometimes_here(table_name, label) && awaiting > 0)
}

/// [`recorded_gaps`]' labels only, for the lanes that compare labels.
pub(crate) fn recorded_gap_labels(
    table: &'static [Uncertified],
    table_name: &str,
    _qualified: &QualifiedPair,
) -> Vec<&'static str> {
    table
        .iter()
        .filter(|gap| !certified_here(gap.label))
        .chain(also_uncertified_here(table_name))
        .filter(|gap| !certifies_sometimes_here(table_name, gap.label))
        .map(|gap| gap.label)
        .collect()
}

/// This host's deadline-bound entries ([`DEADLINE_BOUND_HERE_BY_HOST`]), as
/// `(table, entry)`, for the explicit lane that replays them.
pub(crate) fn deadline_bound_entries_here(
    _qualified: &QualifiedPair,
) -> Vec<(&'static str, &'static DeadlineBound)> {
    let host = current_host_triple();
    DEADLINE_BOUND_HERE_BY_HOST
        .iter()
        .filter(|(triple, ..)| *triple == host)
        .map(|(_, table_name, bound)| (*table_name, bound))
        .collect()
}

/// The witness refuses a lane that the qualification command's filter does
/// not select, before it reads anything: this test's own name carries no
/// [`QUALIFICATION_FILTER`]. The 37 lanes that take a witness are the
/// positive control.
#[test]
#[should_panic(expected = "does not select it, so no qualification runs it")]
fn the_pair_witness_refuses_a_lane_the_command_does_not_select() {
    let _ = assert_qualification_replayer(&[]);
}

/// The pair is the recorded AY build and the recorded checker bytes, each by
/// equality: an AY whose path spells [`QUALIFIED_AY`] is not that AY, and
/// neither half stands in for the other. The 37 lanes that take a witness
/// are the positive control on the recorded pair itself.
#[test]
fn the_pair_witness_compares_the_ay_build_not_its_description() {
    let clean = "c".repeat(64);
    let other_build = "ay 0.27.0 build 12714 commit b1b0b9de07af146c1244633189f92971a3347db9";
    let pair = |ay_build: Option<&str>, clean_sha256: &str| ReplayIdentity {
        ay: format!(
            "route=override ay=/tmp/{QUALIFIED_AY}/ay identity=[{} sha256 {}]",
            ay_build.unwrap_or("unit-test fixture"),
            "a".repeat(64)
        ),
        ay_build: ay_build.map(str::to_owned),
        ay_banner: String::new(),
        clean_sha256: clean_sha256.to_owned(),
    };
    assert!(is_qualified_pair(&pair(Some(QUALIFIED_AY), &clean), &clean));
    // The description names QUALIFIED_AY in its path in each case below.
    assert!(!is_qualified_pair(&pair(Some(other_build), &clean), &clean));
    assert!(!is_qualified_pair(&pair(None, &clean), &clean));
    assert!(!is_qualified_pair(
        &pair(Some(QUALIFIED_AY), &"d".repeat(64)),
        &clean
    ));
}
