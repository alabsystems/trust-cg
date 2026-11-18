// trust-cg-verify - hint-driven prefetch of certificate replays
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Start a warm compile's certificate replays before the compile asks for them.
//!
//! # What it changes
//!
//! A warm compile credits each stored Alethe certificate only after the
//! external Clean checker replays it in a fresh process
//! ([`crate::obligation_cert_store`]). The rustc bridge discharges its
//! MIR-to-trust-ir refinement obligations one after another while it lowers
//! MIR, so every replay (about 4 ms of process start-up each) and the start of
//! the resident AY server (about 9 ms) sat on the compile's critical path:
//! 55 to 105 ms of a 0.38 s warm compile of each beat-llvm program, against a
//! 12 ms LLVM backend (measured 2026-10-01, M4 Max, Trust 9192).
//!
//! The same replays happen in the same compile of the same crate every time.
//! So each compile records the certificates it consumed (and whether it
//! queried the resident AY server) as a per-compile *hint*, and the next
//! compile of the same scope replays those certificates on the identity-warm
//! thread while rustc's front end runs, after AY admission. Its replays
//! populate the in-process positive replay memo; when lowering then asks for
//! the same certificate it finds the memo entry instead of starting a checker.
//!
//! # Why this changes no verdict
//!
//! A hint is an untrusted scheduling input, like the verdict files the solver
//! funnel never credits. It names certificate files only. Prefetching one runs
//! exactly the replay the consume path runs (`consume_verified_text`: binding
//! to the admitted AY, the exact SMT2 bytes, the recorded checker identity and
//! a full `clean cert verify-external --verbose` re-check in this process), and
//! only a successful replay enters the memo, under the key the consume path
//! derives from the verdict key, the solver identity, the exact query, the
//! complete certificate bytes and the checker/environment context. A query
//! that differs from the certificate's own SMT2, a certificate that changed
//! after the prefetch, or a different checker or environment derives another
//! key and is replayed again. A failed prefetch caches nothing, so the
//! consume path replays it again and then solves live, as before. Pre-starting
//! the resident server starts the same admitted binary, under the same
//! authority, that the first resident query would start; queries are isolated
//! by `(reset)` either way.
//!
//! The cost of a stale or hostile hint is wasted replays on a background
//! thread, never a credited verdict. Replays the compile does need are not run
//! twice: the consume path and the prefetch share one in-flight registry, so a
//! query for a certificate the prefetch is replaying waits for that replay.
//!
//! # Scope and storage
//!
//! The frontend names the compile with [`set_scope`] (the rustc bridge hashes
//! the input path, crate name, metadata, target, optimization level and crate
//! types) before it starts the identity warm. Hints live
//! under the certificate store, `<store>/replay-hints/<scope>.hint`, and follow
//! the store's switches: with no store (`TCG_NO_CERT_STORE`,
//! `TCG_NO_PROOF_CACHE`) or while the verdict DB records, nothing is read,
//! prefetched or written. A process that never calls [`set_scope`] (the CLI,
//! TY, the test suites) is unaffected. A hint's modification time is its last
//! use (it is set when the hint is read or written), and the store's sweep
//! evicts hints by it over [`REPLAY_HINT_CAP_BYTES`].
//!
//! # End of the compile
//!
//! [`persist`] also ends the prefetch: no replay starts after it, and it waits
//! for the one in progress (one checker process, under the replay's own
//! deadline), so a compile that ends before its prefetch (a stale hint naming
//! certificates this compile does not use) leaves no checker process or staged
//! certificate behind when the process exits.

use std::collections::HashSet;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

use sha2::{Digest, Sha256};

/// First line of every hint file.
const HINT_SCHEMA: &str = "tcg-replay-hints-v1";

/// The most certificates one hint names. Equal to the replay memo's capacity:
/// prefetching more would evict the first entries before they are used.
pub(crate) const MAX_HINTED_REPLAYS: usize = 4_096;

/// The most bytes read from one hint file (4,096 keys of 65 bytes plus the
/// header lines fit well inside it).
const MAX_HINT_BYTES: u64 = 512 * 1024;

/// Subdirectory of the certificate store that holds the hints.
pub(crate) const HINT_NAMESPACE: &str = "replay-hints";

/// The most bytes of hints the store keeps: 64 MiB. Hints are evicted by the
/// certificates' rule (least recently used first, by modification time; a
/// read and a write each mark a use) in a sweep of their own, started with
/// the certificates' ([`crate::obligation_cert_store::note_store_grew`]).
/// `TCG_PROOF_REPLAY_HINT_CAP_BYTES` overrides it for tests and benchmarks
/// only, as a rustc-bridge compile refuses `TCG_*`. On m18 on 2026-11-12 the
/// store held 306,348 hints in 1.2 GiB, 4 KiB on average, most of them for
/// scopes of worktrees long gone (a scope hashes the input path). 64 MiB
/// keeps about 16,000 of that size; an evicted hint costs its scope's next
/// compile its prefetch only.
pub(crate) const REPLAY_HINT_CAP_BYTES: u64 = 64 << 20;

/// What one hint file says: the certificates the scope's last compile
/// consumed or published, in first-use order, and whether it queried the
/// resident AY server.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ReplayHint {
    pub(crate) keys: Vec<String>,
    pub(crate) resident_solver: bool,
}

impl ReplayHint {
    fn serialize(&self) -> String {
        let mut out = String::with_capacity(64 + self.keys.len() * 65);
        out.push_str(HINT_SCHEMA);
        out.push('\n');
        out.push_str(if self.resident_solver {
            "resident-solver:1\n"
        } else {
            "resident-solver:0\n"
        });
        for key in &self.keys {
            out.push_str(key);
            out.push('\n');
        }
        out
    }

    /// Parse a hint. A wrong schema or a malformed header is no hint at all; a
    /// malformed key line is skipped (it could only name a file to replay).
    pub(crate) fn parse(text: &str) -> Option<Self> {
        let mut lines = text.lines();
        if lines.next()? != HINT_SCHEMA {
            return None;
        }
        let resident_solver = match lines.next()? {
            "resident-solver:1" => true,
            "resident-solver:0" => false,
            _ => return None,
        };
        let mut seen = HashSet::new();
        let mut keys = Vec::new();
        for line in lines {
            if keys.len() == MAX_HINTED_REPLAYS {
                break;
            }
            if is_verdict_key(line) && seen.insert(line) {
                keys.push(line.to_owned());
            }
        }
        Some(Self {
            keys,
            resident_solver,
        })
    }
}

/// A verdict key is a lowercase hex SHA-256 (it is also a file name).
pub(crate) fn is_verdict_key(text: &str) -> bool {
    text.len() == 64
        && text
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

/// The digest a frontend names its compile with: SHA-256 over labelled,
/// length-framed parts.
pub fn scope_digest(parts: &[(&str, &[u8])]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-cg.replay-hint-scope.v1\0");
    for (label, value) in parts {
        hasher.update((label.len() as u64).to_be_bytes());
        hasher.update(label.as_bytes());
        hasher.update((value.len() as u64).to_be_bytes());
        hasher.update(value);
    }
    hasher.finalize().into()
}

static SCOPE: OnceLock<[u8; 32]> = OnceLock::new();

/// Name this process's compile so its certificate replays can be prefetched
/// from, and recorded into, the scope's hint. Call it once, before the
/// identity warm starts; a second call is ignored and returns `false`.
pub fn set_scope(scope: [u8; 32]) -> bool {
    SCOPE.set(scope).is_ok()
}

fn scope_hex() -> Option<String> {
    let scope = SCOPE.get()?;
    Some(scope.iter().map(|byte| format!("{byte:02x}")).collect())
}

fn hint_path() -> Option<PathBuf> {
    if crate::verdict_db::recording_active() {
        return None;
    }
    let dir = crate::obligation_cert_store::replay_hint_dir()?.join(HINT_NAMESPACE);
    Some(dir.join(format!("{}.hint", scope_hex()?)))
}

/// Certificates this process consumed or published, in first-use order.
#[derive(Default)]
struct UsedKeys {
    order: Vec<String>,
    seen: HashSet<String>,
}

fn used_keys() -> &'static Mutex<UsedKeys> {
    static USED: OnceLock<Mutex<UsedKeys>> = OnceLock::new();
    USED.get_or_init(|| Mutex::new(UsedKeys::default()))
}
static RESIDENT_QUERIED: AtomicBool = AtomicBool::new(false);
/// The hint this process read, so an unchanged one is not rewritten.
static LOADED: Mutex<Option<ReplayHint>> = Mutex::new(None);
static PREFETCHED: AtomicU64 = AtomicU64::new(0);
/// Set by [`persist`]: no hinted startup or prefetch replay starts after it.
static STOPPED: AtomicBool = AtomicBool::new(false);
/// Held for authority capture/resident startup and each replay, and taken by
/// [`persist`] after [`STOPPED`], so neither can start after the stop returns.
static REPLAYING: Mutex<()> = Mutex::new(());

/// Record that the compile itself (not the prefetch) consumed or published
/// the certificate named `verdict_key`.
pub(crate) fn note_used(verdict_key: &str) {
    if SCOPE.get().is_none() || !is_verdict_key(verdict_key) {
        return;
    }
    let mut used = used_keys().lock().unwrap_or_else(|p| p.into_inner());
    if used.order.len() < MAX_HINTED_REPLAYS && used.seen.insert(verdict_key.to_owned()) {
        used.order.push(verdict_key.to_owned());
    }
}

/// Record that a query of this compile was exchanged with the resident AY.
pub(crate) fn note_resident_query() {
    RESIDENT_QUERIED.store(true, Ordering::Relaxed);
}

/// Certificates the prefetch replayed successfully in this process.
pub fn prefetched_replays() -> u64 {
    PREFETCHED.load(Ordering::Relaxed)
}

/// Read this scope's hint, marking it used.
fn read_hint() -> Option<ReplayHint> {
    read_used_hint_at(&hint_path()?)
}

/// Read the hint at `path` and, when there is one, mark it used
/// ([`crate::obligation_cert_store::mark_used`]).
fn read_used_hint_at(path: &std::path::Path) -> Option<ReplayHint> {
    let hint = read_hint_at(path)?;
    crate::obligation_cert_store::mark_used(path);
    Some(hint)
}

fn read_hint_at(path: &std::path::Path) -> Option<ReplayHint> {
    let file = std::fs::File::open(path).ok()?;
    if !file.metadata().ok()?.is_file() {
        return None;
    }
    let mut text = String::new();
    file.take(MAX_HINT_BYTES).read_to_string(&mut text).ok()?;
    ReplayHint::parse(&text)
}

/// Run on the identity-warm thread once AY is admitted: replay the scope's
/// hinted certificates under the authority the compile's queries will use,
/// after pre-starting the resident AY server if the last compile queried it.
pub(crate) fn prefetch_after_admission(solver: &crate::ay_identity::PinnedAy) {
    if SCOPE.get().is_none() {
        return;
    }
    let Some(hint) = read_hint() else {
        return;
    };
    *LOADED.lock().unwrap_or_else(|p| p.into_inner()) = Some(hint.clone());
    let timeout_ms = crate::ay_bridge::AYConfig::default().timeout_ms;
    let Some(authority) = run_prefetch_start(&STOPPED, &REPLAYING, || {
        // Authority capture can run a checker capability probe. It shares
        // the stop barrier with the optional resident start and replays.
        let authority = crate::verification_authority::VerificationAuthority::capture_with_timeout(
            solver, timeout_ms,
        );
        if authority.checker().is_some() {
            crate::process_cost::mark("replay_prefetch_begin");
            if hint.resident_solver {
                // AY initializes in its own process while replays below run.
                crate::ay_bridge::prestart_resident_server(&authority);
            }
        }
        authority
    }) else {
        return;
    };
    if authority.checker().is_none() {
        return;
    }
    for key in &hint.keys {
        if STOPPED.load(Ordering::Acquire) {
            break;
        }
        let _replaying = REPLAYING.lock().unwrap_or_else(|p| p.into_inner());
        if STOPPED.load(Ordering::Acquire) {
            break;
        }
        if crate::obligation_cert_store::prefetch_stored_cert(key, &authority, timeout_ms) {
            PREFETCHED.fetch_add(1, Ordering::Relaxed);
        }
    }
    crate::process_cost::mark("replay_prefetch_end");
}

/// Serialize prefetch authority capture and the optional resident start
/// with the same stop barrier as replays. The second check covers a stop
/// that wins while this thread waits for the lock. A concurrent stop waits
/// until a checker probe or spawn/exit-cleanup registration has completed.
fn run_prefetch_start<T>(
    stopped: &AtomicBool,
    replaying: &Mutex<()>,
    start: impl FnOnce() -> T,
) -> Option<T> {
    if stopped.load(Ordering::Acquire) {
        return None;
    }
    let _replaying = replaying.lock().unwrap_or_else(|p| p.into_inner());
    if stopped.load(Ordering::Acquire) {
        return None;
    }
    Some(start())
}

fn stop_prefetch_state(stopped: &AtomicBool, replaying: &Mutex<()>) {
    stopped.store(true, Ordering::Release);
    drop(replaying.lock().unwrap_or_else(|p| p.into_inner()));
}

/// End the prefetch: no hinted startup or replay starts after this returns,
/// and an operation in progress, if any, has finished. An existing resident
/// server retains its ordinary exit-time cleanup.
fn stop_prefetch() {
    stop_prefetch_state(&STOPPED, &REPLAYING);
}

/// What [`persist`] did.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PersistOutcome {
    /// No scope, no store, or the verdict DB is recording.
    Inactive,
    /// The hint on disk already says this.
    Unchanged,
    /// Nothing was used and no hint existed, so none was created.
    Empty,
    /// The hint was written.
    Written,
    /// Writing failed; the next compile simply prefetches less.
    Failed,
}

/// Write this compile's hint for the next compile of the scope: the
/// certificates it consumed or published, and whether it queried the resident
/// AY server. Call it once the compile's proof work is done: it also ends the
/// prefetch (see the module docs, "End of the compile").
pub fn persist() -> PersistOutcome {
    if SCOPE.get().is_some() {
        stop_prefetch();
    }
    let Some(path) = hint_path() else {
        return PersistOutcome::Inactive;
    };
    let hint = {
        let used = used_keys().lock().unwrap_or_else(|p| p.into_inner());
        ReplayHint {
            keys: used.order.clone(),
            resident_solver: RESIDENT_QUERIED.load(Ordering::Relaxed),
        }
    };
    let loaded = LOADED.lock().unwrap_or_else(|p| p.into_inner()).clone();
    let outcome = write_hint_into_store(&path, &hint, loaded.as_ref());
    if outcome == PersistOutcome::Written {
        *LOADED.lock().unwrap_or_else(|p| p.into_inner()) = Some(hint);
    }
    outcome
}

/// [`write_hint_at`] the hint at `path`, in a store's
/// [`HINT_NAMESPACE`] folder, and when it is written tell the store it grew
/// ([`crate::obligation_cert_store::note_store_grew`]), which sweeps the
/// store's folders when their sweeps are due.
fn write_hint_into_store(
    path: &std::path::Path,
    hint: &ReplayHint,
    loaded: Option<&ReplayHint>,
) -> PersistOutcome {
    let outcome = write_hint_at(path, hint, loaded);
    if outcome == PersistOutcome::Written
        && let Some(store) = path.parent().and_then(std::path::Path::parent)
    {
        crate::obligation_cert_store::note_store_grew(store);
    }
    outcome
}

/// Write `hint` to `path` unless `loaded` (the hint this process read there)
/// already says it, or it names nothing and no hint is there.
fn write_hint_at(
    path: &std::path::Path,
    hint: &ReplayHint,
    loaded: Option<&ReplayHint>,
) -> PersistOutcome {
    match loaded {
        Some(previous) if previous == hint => return PersistOutcome::Unchanged,
        // No hint was read. Still do not create one for a compile that uses
        // no certificate, unless a stale one is on disk.
        None if hint.keys.is_empty() && !hint.resident_solver && !path.exists() => {
            return PersistOutcome::Empty;
        }
        _ => {}
    }
    let Some(dir) = path.parent() else {
        return PersistOutcome::Failed;
    };
    if trust_cg_process_env::private_fs::create_private_dir_all(dir).is_err() {
        return PersistOutcome::Failed;
    }
    let Ok(mut staged) = tempfile::NamedTempFile::new_in(dir) else {
        return PersistOutcome::Failed;
    };
    if staged.write_all(hint.serialize().as_bytes()).is_err() {
        return PersistOutcome::Failed;
    }
    match staged.persist(path) {
        Ok(_) => PersistOutcome::Written,
        Err(_) => PersistOutcome::Failed,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(byte: char) -> String {
        std::iter::repeat_n(byte, 64).collect()
    }

    #[test]
    fn a_hint_round_trips() {
        let hint = ReplayHint {
            keys: vec![key('a'), key('0'), key('f')],
            resident_solver: true,
        };
        assert_eq!(ReplayHint::parse(&hint.serialize()), Some(hint));
        let empty = ReplayHint::default();
        assert_eq!(ReplayHint::parse(&empty.serialize()), Some(empty));
    }

    #[test]
    fn a_malformed_hint_names_nothing_it_cannot_name() {
        assert_eq!(ReplayHint::parse(""), None);
        assert_eq!(
            ReplayHint::parse(&format!(
                "tcg-replay-hints-v0\nresident-solver:0\n{}\n",
                key('a')
            )),
            None
        );
        assert_eq!(
            ReplayHint::parse(&format!(
                "{HINT_SCHEMA}\nresident-solver:yes\n{}\n",
                key('a')
            )),
            None
        );
        // Key lines that are not lowercase 64-hex digests, or repeat, are
        // skipped: they could only name a file to replay.
        let text = format!(
            "{HINT_SCHEMA}\nresident-solver:0\n{}\n../../etc/passwd\n{}\n{}\n{}\n",
            key('a'),
            key('A'),
            key('a'),
            &key('b')[..63],
        );
        assert_eq!(
            ReplayHint::parse(&text),
            Some(ReplayHint {
                keys: vec![key('a')],
                resident_solver: false,
            })
        );
    }

    #[test]
    fn a_hint_names_at_most_the_replay_memo_capacity() {
        let mut text = format!("{HINT_SCHEMA}\nresident-solver:0\n");
        for n in 0..(MAX_HINTED_REPLAYS + 10) {
            text.push_str(&format!("{n:064x}\n"));
        }
        let hint = ReplayHint::parse(&text).expect("well-formed hint");
        assert_eq!(hint.keys.len(), MAX_HINTED_REPLAYS);
        assert_eq!(hint.keys[0], format!("{:064x}", 0));
    }

    #[test]
    fn a_written_hint_reads_back_and_is_rewritten_only_when_it_changes() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join(HINT_NAMESPACE).join("scope.hint");
        let empty = ReplayHint::default();
        // Nothing used and nothing on disk: no file is created.
        assert_eq!(write_hint_at(&path, &empty, None), PersistOutcome::Empty);
        assert!(!path.exists());
        let hint = ReplayHint {
            keys: vec![key('a'), key('b')],
            resident_solver: true,
        };
        assert_eq!(write_hint_at(&path, &hint, None), PersistOutcome::Written);
        assert_eq!(read_hint_at(&path), Some(hint.clone()));
        // The same hint as the one read is not rewritten.
        assert_eq!(
            write_hint_at(&path, &hint, Some(&hint)),
            PersistOutcome::Unchanged
        );
        // A compile that used nothing replaces a stale hint on disk.
        assert_eq!(write_hint_at(&path, &empty, None), PersistOutcome::Written);
        assert_eq!(read_hint_at(&path), Some(empty));
        // Nothing but the hint is left in its directory (no staged file).
        let names: Vec<_> = std::fs::read_dir(path.parent().unwrap())
            .unwrap()
            .map(|entry| entry.unwrap().file_name())
            .collect();
        assert_eq!(names, vec![std::ffi::OsString::from("scope.hint")]);
    }

    #[test]
    fn an_oversized_hint_is_read_only_up_to_its_bound() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("big.hint");
        let mut text = format!("{HINT_SCHEMA}\nresident-solver:0\n");
        let mut n = 0u64;
        while (text.len() as u64) < MAX_HINT_BYTES * 2 {
            text.push_str(&format!("{n:064x}\n"));
            n += 1;
        }
        std::fs::write(&path, &text).unwrap();
        let hint = read_hint_at(&path).expect("the bounded prefix parses");
        assert!(hint.keys.len() <= MAX_HINTED_REPLAYS);
        assert!((hint.keys.len() as u64) * 65 <= MAX_HINT_BYTES);
    }

    #[test]
    fn a_late_hinted_start_is_stopped_before_authority_or_resident_work() {
        use std::sync::{Arc, mpsc};
        use std::time::Duration;

        let stopped = Arc::new(AtomicBool::new(false));
        let replaying = Arc::new(Mutex::new(()));
        let starts = Arc::new(AtomicU64::new(0));
        let (ready_tx, ready_rx) = mpsc::channel();
        let (resume_tx, resume_rx) = mpsc::channel();
        let warm = {
            let stopped = Arc::clone(&stopped);
            let replaying = Arc::clone(&replaying);
            let starts = Arc::clone(&starts);
            std::thread::spawn(move || {
                // Pause after reading a hint, before authority capture or
                // resident startup. The callback represents that real work.
                ready_tx.send(()).unwrap();
                resume_rx.recv_timeout(Duration::from_secs(5)).unwrap();
                run_prefetch_start(&stopped, &replaying, || {
                    starts.fetch_add(1, Ordering::Relaxed);
                })
            })
        };
        ready_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        stop_prefetch_state(&stopped, &replaying);
        assert!(stopped.load(Ordering::Acquire));
        assert_eq!(starts.load(Ordering::Relaxed), 0);
        resume_tx.send(()).unwrap();
        assert!(warm.join().unwrap().is_none());
        assert_eq!(starts.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn an_active_hinted_start_runs_once_and_cannot_restart_after_stop() {
        let stopped = AtomicBool::new(false);
        let replaying = Mutex::new(());
        let starts = AtomicU64::new(0);
        assert_eq!(
            run_prefetch_start(&stopped, &replaying, || {
                starts.fetch_add(1, Ordering::Relaxed);
            }),
            Some(())
        );
        stop_prefetch_state(&stopped, &replaying);
        assert_eq!(
            run_prefetch_start(&stopped, &replaying, || {
                starts.fetch_add(1, Ordering::Relaxed);
            }),
            None
        );
        assert_eq!(starts.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn stop_waits_for_an_active_hinted_start_and_then_declines_restart() {
        use std::sync::{Arc, mpsc};
        use std::time::{Duration, Instant};

        let stopped = Arc::new(AtomicBool::new(false));
        let replaying = Arc::new(Mutex::new(()));
        let starts = Arc::new(AtomicU64::new(0));
        let (entered_tx, entered_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let (started_tx, started_rx) = mpsc::channel();
        let warm = {
            let stopped = Arc::clone(&stopped);
            let replaying = Arc::clone(&replaying);
            let starts = Arc::clone(&starts);
            std::thread::spawn(move || {
                let result = run_prefetch_start(&stopped, &replaying, || {
                    starts.fetch_add(1, Ordering::Relaxed);
                    entered_tx.send(()).unwrap();
                    release_rx.recv_timeout(Duration::from_secs(20)).unwrap();
                });
                started_tx.send(result).unwrap();
            })
        };
        // Receiving this proves the real startup callback holds the mutex.
        entered_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        let (stop_done_tx, stop_done_rx) = mpsc::channel();
        let stopper = {
            let stopped = Arc::clone(&stopped);
            let replaying = Arc::clone(&replaying);
            std::thread::spawn(move || {
                stop_prefetch_state(&stopped, &replaying);
                stop_done_tx.send(()).unwrap();
            })
        };
        let deadline = Instant::now() + Duration::from_secs(5);
        while !stopped.load(Ordering::Acquire) && Instant::now() < deadline {
            std::thread::yield_now();
        }
        let flag_was_set = stopped.load(Ordering::Acquire);
        // The flag shows the stop request was published. The held mutex
        // prevents a correct stopper from completing before startup returns.
        // Give even a broken nonwaiting stop a bounded chance to report return.
        let early_stop = stop_done_rx.recv_timeout(Duration::from_secs(1));
        release_tx.send(()).unwrap();
        let started = started_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        if matches!(early_stop, Err(mpsc::RecvTimeoutError::Timeout)) {
            stop_done_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        }
        warm.join().unwrap();
        stopper.join().unwrap();
        assert!(flag_was_set, "stop did not reach its flag within the bound");
        assert!(
            matches!(early_stop, Err(mpsc::RecvTimeoutError::Timeout)),
            "stop returned before the active startup callback was released"
        );
        assert_eq!(started, Some(()));
        assert_eq!(starts.load(Ordering::Relaxed), 1);
        assert_eq!(
            run_prefetch_start(&stopped, &replaying, || {
                starts.fetch_add(1, Ordering::Relaxed);
            }),
            None
        );
        assert_eq!(starts.load(Ordering::Relaxed), 1);
    }

    /// Set the modification time of the file at `path` to `hours` ago.
    fn used_hours_ago(path: &std::path::Path, hours: u64) {
        std::fs::File::options()
            .write(true)
            .open(path)
            .unwrap()
            .set_modified(
                std::time::SystemTime::now() - std::time::Duration::from_secs(3600 * hours),
            )
            .unwrap();
    }

    #[test]
    fn replay_hint_eviction_removes_the_least_recently_used_over_the_cap() {
        let store = tempfile::tempdir().unwrap();
        let hints = store.path().join(HINT_NAMESPACE);
        let hint = ReplayHint {
            keys: vec![key('a')],
            resident_solver: false,
        };
        // Four hints, the first used longest ago.
        let paths: Vec<_> = (0..4)
            .map(|index| {
                let path = hints.join(format!("{index:064x}.hint"));
                assert_eq!(write_hint_at(&path, &hint, None), PersistOutcome::Written);
                used_hours_ago(&path, 10 - index);
                path
            })
            .collect();
        let size = std::fs::metadata(&paths[0]).unwrap().len();
        // A fifth written the way `persist` writes one, over a cap of four:
        // the write starts the sweep, which removes the least recently used
        // down to nine tenths of the cap, leaving three.
        let fifth = hints.join(format!("{:064x}.hint", 4));
        let cap = (4 * size).to_string();
        assert_eq!(
            trust_cg_process_env::with_env_overrides(
                &[(crate::obligation_cert_store::HINT_CAP_ENV, &cap)],
                || write_hint_into_store(&fifth, &hint, None)
            ),
            PersistOutcome::Written
        );
        crate::obligation_cert_store::wait_for_sweep_for_test(store.path());
        for (index, path) in paths.iter().enumerate() {
            assert_eq!(path.exists(), index >= 2, "hint {index}");
        }
        assert!(fifth.exists());
    }

    #[test]
    fn replay_hint_read_marks_the_hint_used() {
        let store = tempfile::tempdir().unwrap();
        let path = store.path().join(HINT_NAMESPACE).join("scope.hint");
        let hint = ReplayHint {
            keys: vec![key('b')],
            resident_solver: true,
        };
        assert_eq!(write_hint_at(&path, &hint, None), PersistOutcome::Written);
        used_hours_ago(&path, 10);
        assert_eq!(read_used_hint_at(&path), Some(hint));
        let since_use = std::time::SystemTime::now()
            .duration_since(std::fs::metadata(&path).unwrap().modified().unwrap())
            .unwrap_or_default();
        assert!(
            since_use < std::time::Duration::from_secs(3600),
            "a read is a use: the hint's last use is now, not ten hours ago"
        );
    }

    #[test]
    fn scope_digests_frame_their_parts() {
        let a = scope_digest(&[("input", b"ab"), ("crate", b"c")]);
        let b = scope_digest(&[("input", b"a"), ("crate", b"bc")]);
        let c = scope_digest(&[("input", b"ab"), ("crate", b"c")]);
        assert_ne!(a, b);
        assert_eq!(a, c);
    }
}
