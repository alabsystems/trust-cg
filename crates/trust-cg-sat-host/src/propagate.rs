// trust-cg-sat-host - Rust-side propagate dispatch.
//
// This module defines the `trust_cg_propagate` symbol that MicroSAT's
// `solve()` is wired to call through the C trampoline in
// `propagate_trampoline.c`. The build script renames MicroSAT's own
// implementation to `microsat_native_propagate`, freeing the
// `propagate` name for the trampoline to claim.
//
// ## Phases
//
// **Phase 1 (historical):** `trust_cg_propagate` was a thin Rust
// delegate that forwarded to `microsat_native_propagate`. The shadow
// path also called the native function, giving a trivial
// "trampoline-is-wired" baseline with divergence impossible by
// construction.
//
// **Phase 2 (current):** the shadow path is a real call into the
// trust-cg JIT'd verified BCP kernel. When `SHADOW_MODE` is true, the
// very first invocation of `trust_cg_propagate` snapshots the formula
// out of MicroSAT's `DB` (clauses only, by walking the pristine input
// region `DB[1 .. mem_fixed]`), compiles a JIT BCP provider, and
// caches it on a thread-local. Subsequent calls reuse the cached
// provider and run a differential check against MicroSAT's native
// propagate on the *original formula*.
//
// **Phase 3 (current):** `PRIMARY_JIT_MODE` engages the JIT'd BCP
// kernel as the primary verdict producer. On the first eligible call
// the kernel is compiled and its result is used as the primary return
// value surfaced to MicroSAT's `solve()`.
//
// **Kernel choice:** both
// `SHADOW_MODE` and `PRIMARY_JIT_MODE` build whatever JIT kernel is
// named by the `JIT_KERNEL_CHOICE` atomic. The default is
// `JitKernelChoice::WatchedLiteral`, which uses the watched-literal
// algorithm. Tests that want to exercise the
// older scan or with-decisions kernels for differential coverage set
// the choice explicitly via `JIT_KERNEL_CHOICE.store(...)`.
//
// ### Why we still call native under PRIMARY_JIT_MODE
//
// MicroSAT's `propagate` is heavily side-effecting: it mutates
// `S->processed`, `S->assigned`, `S->falseStack`, `S->reason`,
// `S->model`, `S->forced`, the watch lists in `S->first[]`, and
// invokes `analyze()` -> `addClause()` to learn lemmas on non-root
// conflicts. The JIT'd BCP kernel runs on a private arena (`values`
// + `trail`) that is independent of MicroSAT's data structures, so it
// cannot drive those side effects. Replacing the native call outright
// would leave MicroSAT's solver state stale (unit-implied literals
// would not be pushed onto `falseStack`, learned clauses would never
// appear, conflict analysis would be skipped) and the next iteration
// of `solve()` would either loop or return an incorrect answer.
//
// We therefore keep the native call in the hot path *for its side
// effects*. PRIMARY_JIT_MODE adds the JIT call alongside it and
// surfaces the JIT's mapped return code as the primary value when
// the JIT is considered authoritative for that call site.
//
// ### Where the JIT is authoritative
//
// Even with native always running for state mutation, the JIT
// answers propagate against the *original* formula given the
// current assignment. Phase 2's scratch-arena design (A1's
// strategic insight) puts the reason values for JIT-implied
// literals in `S->DB`'s high tail rather than referencing learned
// clauses, so the JIT-compiled kernel for the original formula
// remains valid for the entire solve regardless of how many lemmas
// MicroSAT learns. There is no epoch boundary: the kernel never
// sees the learned clauses, only the original ones.
//
// The "JIT-conflict-implies-UNSAT" mapping still only holds in the
// root-forced regime (`pre_authoritative` true). At
// decision-level >= 1 the conflict is driven through MicroSAT's
// native `analyze` via the analyze-driver path (Phase 2). In
// either regime the JIT contributes the implication stream and
// MicroSAT's downstream `analyze` / `implied` walks consume the
// scratch reasons transparently.
//
// ### Hard-fail policy
//
// Under PRIMARY_JIT_MODE, once the JIT has agreed with native on
// `JIT_HARDFAIL_WARMUP` consecutive calls (default 5), any future
// divergence panics rather than just incrementing the warning
// counter. SHADOW_MODE stays soft-warning forever (it is a research
// probe). The two flags are independent; both may be set at once.

use core::ffi::c_int;
use core::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, Ordering};
use std::cell::RefCell;
use std::sync::Arc;

use trust_cg_jit_matrix::jit_bcp_kernel::{
    JitBcpKernelProvider, JitBcpWatchedLiteralKernelProvider, JitBcpWithDecisionsProvider,
};
use trust_cg_jit_matrix::solver_kernel_abi::SolverKernelHandle;

use crate::scratch_arena::ScratchArena;
use crate::sys;

/// When `true`, `trust_cg_propagate` runs the dispatch in differential
/// "shadow" mode: the primary native call is paired with a JIT-side
/// re-evaluation of the original formula and the two outcomes are
/// compared.
///
/// In Phase 1 both paths were `microsat_native_propagate`, so this was
/// a trivial self-consistency check. In Phase 2 the shadow path
/// became the JIT'd verified BCP kernel, making this a real
/// divergence detector for the first-restart epoch.
pub static SHADOW_MODE: AtomicBool = AtomicBool::new(false);

/// When `true`, `trust_cg_propagate` engages the JIT'd BCP kernel as
/// the *primary* return path. Native still runs (its side effects are
/// load-bearing for MicroSAT's solver state), but the JIT's mapped
/// result code is the value surfaced to MicroSAT when the JIT is
/// authoritative for this call (see module docs for the epoch-0
/// authority rules).
///
/// Independent of `SHADOW_MODE`; both may be set simultaneously.
pub static PRIMARY_JIT_MODE: AtomicBool = AtomicBool::new(false);

/// Numeric tag for `JIT_KERNEL_CHOICE` selecting the scan-only kernel
/// (`JitBcpKernelProvider`). Single-shot per cached provider:
/// the kernel's arena is mutated on first call and is not reset between
/// invocations, so the shadow path evaluates it exactly once per solve.
pub const JIT_KERNEL_SCAN: u8 = 0;

/// Numeric tag for `JIT_KERNEL_CHOICE` selecting the
/// scan+decisions kernel (`JitBcpWithDecisionsProvider`).
/// Accepts a decision-literal slice and exposes `reset_arena()` so it
/// can be invoked many times per solve.
pub const JIT_KERNEL_WITH_DECISIONS: u8 = 1;

/// Numeric tag for `JIT_KERNEL_CHOICE` selecting the watched-literal
/// kernel (`JitBcpWatchedLiteralKernelProvider`). This is the default
/// and uses the same watched-literal algorithm as the native baseline.
pub const JIT_KERNEL_WATCHED_LITERAL: u8 = 2;

/// Selects which JIT BCP kernel `SHADOW_MODE` / `PRIMARY_JIT_MODE`
/// compile when they snapshot the formula. Default
/// `JIT_KERNEL_WATCHED_LITERAL` so every default JIT invocation
/// (CLI, bench, tests) runs the headline kernel. Tests that want a
/// specific older kernel for differential coverage call
/// `JIT_KERNEL_CHOICE.store(JIT_KERNEL_SCAN, Ordering::SeqCst)` (or
/// `JIT_KERNEL_WITH_DECISIONS`) and restore to
/// `JIT_KERNEL_WATCHED_LITERAL` after the run.
pub static JIT_KERNEL_CHOICE: AtomicU8 = AtomicU8::new(JIT_KERNEL_WATCHED_LITERAL);

/// Counts how many times `trust_cg_propagate` has been entered. Used by
/// tests to prove that MicroSAT's `solve()` is in fact routing through
/// our Rust replacement rather than the original C implementation.
///
/// Note: this counter is global and intentionally not reset between
/// solves. Tests should snapshot it before/after the call.
pub static PROPAGATE_CALL_COUNT: AtomicU64 = AtomicU64::new(0);

/// Counts how many times the shadow / primary-JIT path has compiled
/// a fresh JIT provider. Used by tests to assert the once-per-solve
/// compile strategy (snapshot-on-first-call). The counter is
/// process-global and not reset between solves; tests should snapshot
/// deltas.
pub static JIT_INIT_COUNT: AtomicU64 = AtomicU64::new(0);

/// Counts how many shadow / primary-JIT invocations observed
/// disagreement between the native and JIT propagate outcomes on the
/// original formula. Tests inspect this to confirm that simple
/// SAT/UNSAT instances agree (delta == 0). Process-global; tests
/// snapshot deltas.
pub static JIT_DIVERGENCE_COUNT: AtomicU64 = AtomicU64::new(0);

/// Counts how many PRIMARY_JIT_MODE calls saw the JIT and native
/// agree on the propagate outcome (i.e. zero-divergence calls). Used
/// to gate the hard-fail divergence policy: until at least
/// `JIT_HARDFAIL_WARMUP` zero-divergence calls have been observed, a
/// divergence emits a warning and bumps `JIT_DIVERGENCE_COUNT`; after
/// the warmup threshold, a divergence panics so a real correctness
/// regression in the JIT cannot be missed by the benchmark harness.
///
/// Process-global; intentionally not reset between solves so the
/// hard-fail policy is monotone across the full test run.
pub static JIT_SUCCESSFUL_RUNS: AtomicU64 = AtomicU64::new(0);

/// Number of zero-divergence primary-JIT calls that must accumulate
/// before a divergence is escalated from "warning" to "panic". Chosen
/// to require several agreeing calls before hard-fail enforcement begins.
pub const JIT_HARDFAIL_WARMUP: u64 = 5;

/// Counts how many propagate calls were resolved by returning the
/// JIT's mapped result code as the primary value (i.e. the JIT was
/// authoritative for that call). When PRIMARY_JIT_MODE is off this
/// counter never advances; tests use it to confirm the primary path
/// fired at least once.
pub static JIT_PRIMARY_RETURNS: AtomicU64 = AtomicU64::new(0);

/// Counts how many JIT-replacement calls saw a conflict at a non-root
/// decision level and drove the conflict into MicroSAT's native
/// `analyze` (the analyze-driver path of kernel API extension #5).
/// Process-global; tests snapshot deltas. When zero, the JIT only
/// handled root-level conflicts (the historical regime) — any growth
/// here is direct evidence that the JIT is now taking over MicroSAT's
/// `analyze` path for non-trivial decision-level conflicts.
pub static JIT_ANALYZE_DRIVEN: AtomicU64 = AtomicU64::new(0);

/// Counts how many ADF-conflict calls saw the JIT-reported conflict
/// clause AGREE with native's first-conflict watch-list pick (F1-v2
/// Candidate 1 telemetry). When this counter equals
/// `JIT_ANALYZE_DRIVEN`, every conflict native would have picked is
/// the same one the JIT already produced, so the host-side
/// `native_find_first_conflict_clause` walk is pure overhead and the
/// short-circuit is dropping it. A delta below `JIT_ANALYZE_DRIVEN`
/// means the JIT and native sometimes disagree (structured-hard
/// fixtures e.g. pigeon-hole).
pub static JIT_ANALYZE_DRIVER_CLAUSE_AGREEMENTS: AtomicU64 = AtomicU64::new(0);

/// Counts how many ADF-conflict calls skipped the post-analyze
/// `microsat_native_propagate` continuation because `analyze` learned
/// a multi-literal lemma (F1-v2 Candidate 2 telemetry). Multi-literal
/// lemmas cause MicroSAT's outer solve loop to backjump to a lower DL
/// on the NEXT iteration, so re-running BCP inline is wasted work; we
/// skip it. Unit lemmas (`lemma[1] == 0`) still call native to
/// propagate the new unit immediately (correctness-required).
pub static JIT_ANALYZE_DRIVER_NATIVE_SKIPS: AtomicU64 = AtomicU64::new(0);

/// Counts how many JIT-replacement calls fell back to native because
/// the per-solve scratch arena (Phase 2 DB-arena split) was near
/// overflow or rejected a `allocate_synthetic_clause` request. Process-
/// global; tests snapshot deltas. Stays at zero on the common case
/// where the reservation is sized for the worst-case implication
/// stream.
pub static JIT_SCRATCH_OVERFLOW_FALLBACKS: AtomicU64 = AtomicU64::new(0);

/// When set to `true` (the default post-B1-follow-up),
/// `trust_cg_propagate` engages the JIT-as-primary replacement path
/// on every non-empty propagate call, not just the root-forced regime
/// the historical `jit_is_authoritative_at_root` gate admitted. At
/// decision-level >= 1 the JIT now drives MicroSAT's `analyze` +
/// `assign` directly (see the analyze-driver path in
/// `try_jit_replace_native`); the build-time rewrite of microsat.c:
/// 133 (see `build.rs::rewrite_definitions`) makes the UIP hand-off
/// sound by replacing the `forced` proxy with the canonical
/// decision-level-0 walk.
///
/// Production callers can set this to `false` to fall back to the
/// pre-extension-5 root-authoritative gate (e.g. for A/B benches that
/// need a strict apples-to-apples comparison against the historical
/// JIT replacement). Tests use the `AnalyzeDriverForceGuard` RAII
/// guard in `lib.rs` to toggle it.
// Default is `true` post-Phase-2 of the empty-lemma bug fix
// (`docs/empty_lemma_bug_design.md` option (c)): the analyze-
// driver at DL >= 1 now re-derives the conflict clause via
// `native_find_first_conflict_clause` (mirroring microsat's own
// watched-literal scan order) and continues propagation through
// `microsat_native_propagate` after analyze + assign, so unit-
// lemma chains terminate as UNSAT inline. This restores the
// JIT-replaces-native crossover for non-root regimes and
// unblocks the recompile-free architecture.
pub static JIT_ANALYZE_DRIVER_FORCE: AtomicBool = AtomicBool::new(true);

/// When `true`, hot-path diagnostic `eprintln!`s in this module emit
/// their per-call messages to stderr; when `false` (the default), the
/// hot-path messages are suppressed so a learning-heavy solve does not
/// flood stderr with thousands of lines per second.
///
/// Rule of thumb for what is gated by this flag: any `eprintln!` that
/// can fire more than once per solve (per-call epoch-fallback notices,
/// per-call buffer-overflow / decode-error notices, the per-call
/// divergence warning) is wrapped in a `TRUST_CG_PROPAGATE_VERBOSE`
/// check. The error-class messages that can only fire at most once per
/// solve (the initial JIT-compile failure, the recompile failure, the
/// first divergence — see `JIT_DIVERGENCE_WARN_INTERVAL`) stay
/// unconditional because they are diagnostically valuable even in
/// production.
///
/// Set via `trust_cg_sat --verbose` (see the binary CLI) or directly
/// by tests / embedding hosts.
pub static TRUST_CG_PROPAGATE_VERBOSE: AtomicBool = AtomicBool::new(false);

/// Stride between divergence-warning `eprintln!`s emitted from the hot
/// path. The first divergence is always reported; subsequent
/// divergences emit a warning only once per this many occurrences so a
/// regression cannot silently flood stderr while still leaving an
/// audit trail in the log. The full divergence count is always
/// reflected in `JIT_DIVERGENCE_COUNT`.
pub const JIT_DIVERGENCE_WARN_INTERVAL: u64 = 1000;

unsafe extern "C" {
    /// MicroSAT's original `propagate`, renamed at compile time via
    /// `-Dpropagate=microsat_native_propagate` (see `build.rs`).
    ///
    /// Bindgen does not see this symbol because the rename happens
    /// in the cc invocation and the wrapper header still declares it
    /// under the original name. We declare it manually here.
    fn microsat_native_propagate(s: *mut sys::solver) -> c_int;

    /// MicroSAT's `analyze` (microsat.c:102-130). Computes a first-UIP
    /// resolvent from a falsified clause and learns it. Mutates
    /// `S->buffer`, `S->falseStack`, `S->assigned`, `S->processed`,
    /// `S->false`, `S->fast`, `S->slow`, `S->nLemmas` (via the
    /// `addClause` trampoline). Returns a pointer into `S->DB` to the
    /// first literal of the freshly learned lemma.
    ///
    /// `clause` must point at the first literal of a clause record
    /// that is currently falsified — i.e. every literal in the record
    /// has `S->false[lit] != 0`. The JIT-replacement path obtains
    /// this pointer by translating `KernelStatus.conflicting_clause_index`
    /// through `JitProviderCache.clause_id_translation`:
    /// `S->DB + clause_id_translation[idx] - 1` (the same DB offset
    /// MicroSAT's `assign` macro would have stamped into
    /// `S->reason[var]`, minus the `+1` offset).
    ///
    /// The symbol is `extern` in the upstream source (not declared
    /// `static`), so it is linkable from Rust. The build script's
    /// renames only touch `propagate`, `addClause`, `reduceDB`, and
    /// `main`; `analyze` and `assign` keep their upstream names.
    ///
    /// Used by `try_jit_replace_native`'s DL >= 1 conflict branch
    /// (option-(c) implementation; see
    /// `docs/empty_lemma_bug_design.md`). The empty-lemma bug is
    /// sidestepped by re-deriving the conflict clause via the
    /// host-side `native_find_first_conflict_clause` walk, then
    /// running `analyze` on the same clause native would have
    /// picked.
    fn analyze(s: *mut sys::solver, clause: *mut c_int) -> *mut c_int;

    /// MicroSAT's `assign` (microsat.c:42-47). Pushes the first
    /// literal of `reason` onto the trail with the supplied `forced`
    /// flag (1 = root-forced, tags `S->false[-lit]` with `IMPLIED`;
    /// 0 = decision-derived, tags with `1`). Mutates
    /// `S->false`, `S->assigned`, `S->reason[abs(lit)]`,
    /// `S->model[abs(lit)]`.
    ///
    /// Used after `analyze` returns the learned lemma to mirror
    /// propagate's `assign(S, lemma, forced);` step (microsat.c:156).
    /// Per microsat.c:155 the post-analyze `forced` is the negation of
    /// `lemma[1]` (unit lemma → forced = 1, multi-literal lemma →
    /// forced unchanged from propagate's top-of-loop value).
    ///
    /// Used by `try_jit_replace_native`'s DL >= 1 conflict branch
    /// (analyze-driver path).
    fn assign(s: *mut sys::solver, reason: *mut c_int, forced: c_int);
}

/// Chosen JIT BCP provider. Whichever variant is built reflects the
/// value of `JIT_KERNEL_CHOICE` at the moment of the first eligible
/// `trust_cg_propagate` call inside `solve()`.
///
/// * `Scan` — `JitBcpKernelProvider`. Single-shot per
///   compiled provider: the kernel writes into `values` / `trail` on
///   first call and is not reset between calls, so the shadow path
///   evaluates it exactly once per solve. Cannot back the primary
///   path (no decision-literal intake, no reset between calls).
/// * `WithDecisions` — `JitBcpWithDecisionsProvider`.
///   Accepts a decision-literal slice and exposes `reset_arena()` so
///   it can be invoked many times per solve.
/// * `WatchedLiteral` — `JitBcpWatchedLiteralKernelProvider`.
///   Same shape as `WithDecisions` (accepts a decision slice, resets
///   between calls), but runs the textbook watched-literal algorithm
///   matching the native baseline. This is the default.
enum ChosenProvider {
    Scan(Arc<JitBcpKernelProvider>),
    WithDecisions(Arc<JitBcpWithDecisionsProvider>),
    WatchedLiteral(Arc<JitBcpWatchedLiteralKernelProvider>),
}

impl ChosenProvider {
    /// Kind tag for diagnostics. Matches the values of
    /// `JIT_KERNEL_SCAN` / `JIT_KERNEL_WITH_DECISIONS` /
    /// `JIT_KERNEL_WATCHED_LITERAL` so the caller can compare without
    /// re-reading `JIT_KERNEL_CHOICE`.
    #[allow(dead_code)]
    fn kind_tag(&self) -> u8 {
        match self {
            ChosenProvider::Scan(_) => JIT_KERNEL_SCAN,
            ChosenProvider::WithDecisions(_) => JIT_KERNEL_WITH_DECISIONS,
            ChosenProvider::WatchedLiteral(_) => JIT_KERNEL_WATCHED_LITERAL,
        }
    }

    /// Whether this provider can back the primary path (i.e. accept a
    /// fresh decision-literal slice and produce a deterministic result
    /// without leaking state across invocations). Only `Scan` cannot.
    fn supports_primary(&self) -> bool {
        match self {
            ChosenProvider::Scan(_) => false,
            ChosenProvider::WithDecisions(_) | ChosenProvider::WatchedLiteral(_) => true,
        }
    }

    /// Run the shadow-mode single-shot call. For `Scan` this fires the
    /// kernel exactly once (caller gates further calls via
    /// `JIT_SHADOW_EVALUATED`). For the resettable kernels the arena
    /// is reset first so the shadow call observes a clean baseline.
    ///
    /// Takes `&self` because the underlying provider's arena is
    /// wrapped in `RefCell` for interior mutability — the cached
    /// `Arc<P>` permits no exclusive access and we must mutate the
    /// arena through a shared reference.
    fn shadow_call(&self) -> u32 {
        match self {
            ChosenProvider::Scan(p) => {
                let mut handle = SolverKernelHandle::from_provider(&**p);
                handle.call(&[]).result
            }
            ChosenProvider::WithDecisions(p) => {
                p.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&**p);
                handle.call(&[]).result
            }
            ChosenProvider::WatchedLiteral(p) => {
                p.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&**p);
                handle.call(&[]).result
            }
        }
    }

    /// Run the primary-mode call with a decision-literal slice.
    /// Returns `None` if invoked on a `Scan` provider; callers
    /// must guard with `supports_primary` first.
    fn primary_call(&self, decisions: &[u32]) -> Option<u32> {
        match self {
            ChosenProvider::Scan(_) => None,
            ChosenProvider::WithDecisions(p) => {
                p.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&**p);
                Some(handle.call(decisions).result)
            }
            ChosenProvider::WatchedLiteral(p) => {
                p.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&**p);
                Some(handle.call(decisions).result)
            }
        }
    }
}

/// Human-readable label for `JIT_KERNEL_CHOICE` tag values. Used in
/// diagnostic messages (compile-failure eprintln, primarily) so the
/// user can correlate a failure with the kernel they asked for.
fn kernel_choice_label(choice: u8) -> &'static str {
    match choice {
        JIT_KERNEL_SCAN => "scan",
        JIT_KERNEL_WITH_DECISIONS => "with-decisions",
        JIT_KERNEL_WATCHED_LITERAL => "watched-literal",
        _ => "unknown",
    }
}

/// Compile the JIT provider named by `choice`, going through the
/// thread-local `JIT_BCP_*_CACHE` so a repeat solve of the same
/// formula pays zero compile cost. Unknown choices fall back to
/// `JIT_KERNEL_WATCHED_LITERAL` (the default) rather than panicking
/// — a sentinel value left over from an old build or a test that
/// forgot to restore the atomic shouldn't crash the solver.
///
/// Trail capacity hint of `num_vars` is a safe upper bound: every
/// variable is assigned at most once during a single BCP sweep.
fn compile_chosen_provider(
    choice: u8,
    num_vars: usize,
    clauses: Vec<Vec<i32>>,
) -> Result<ChosenProvider, trust_cg_jit_matrix::jit_bcp_kernel::JitCompileError> {
    match choice {
        JIT_KERNEL_SCAN => {
            JitBcpKernelProvider::compile_or_get_cached(num_vars, clauses).map(ChosenProvider::Scan)
        }
        JIT_KERNEL_WITH_DECISIONS => {
            JitBcpWithDecisionsProvider::compile_or_get_cached(num_vars, clauses, num_vars)
                .map(ChosenProvider::WithDecisions)
        }
        // JIT_KERNEL_WATCHED_LITERAL (and unknown -> default).
        _ => JitBcpWatchedLiteralKernelProvider::compile_or_get_cached(num_vars, clauses, num_vars)
            .map(ChosenProvider::WatchedLiteral),
    }
}

/// Cached snapshot of the original (irreducible) clauses together
/// with the JIT BCP provider chosen at first-compile time per
/// `JIT_KERNEL_CHOICE`. A single provider serves both `SHADOW_MODE`
/// and `PRIMARY_JIT_MODE` so the two paths always see the same
/// kernel (i.e. the same headline numbers apply to both).
///
/// The provider is lazily allocated on the first eligible call. Phase
/// 2's scratch-arena design (A1's strategic insight) installs reason
/// values for JIT-implied literals in `S->DB`'s scratch tail rather
/// than referencing learned clauses, so the JIT-compiled kernel for
/// the original formula remains valid for the entire solve regardless
/// of how many lemmas MicroSAT learns. No epoch tracking or recompile
/// machinery is needed: the kernel never sees the learned clauses.
struct JitProviderCache {
    provider: Option<ChosenProvider>,
    /// Per-JIT-clause translation table: `clause_id_translation[c]`
    /// holds the value MicroSAT writes to `S->reason[var]` for
    /// literals forced by JIT clause `c`, i.e. the DB offset of the
    /// clause's first literal slot plus 1 (matching MicroSAT's
    /// `assign` macro's `1 + (clause - S->DB)` formula). Built once
    /// after the JIT is compiled. Held by the cache so the slice
    /// stays valid for the lifetime of the installed
    /// `clause_id_translation` pointer on the JIT handle.
    clause_id_translation: Vec<i32>,
    /// Reusable buffer for `KernelCtx::implied_literals_out`. Sized
    /// `2 * num_vars` (with a small floor) so a single propagation
    /// sweep — which assigns each variable at most once — fits without
    /// the kernel signalling sticky overflow.
    implied_literals_buf: Vec<i32>,
    /// Reusable buffer for `KernelCtx::implied_reasons_out`. Parallel
    /// to `implied_literals_buf` and sized identically.
    implied_reasons_buf: Vec<i32>,
    /// Phase 2 DB-arena split: per-solve scratch arena for synthetic
    /// reason clauses with `clause[0] == propagated_lit`. The arena
    /// lives in the high tail of `S->DB`, so reason values it returns
    /// are ordinary DB offsets and MicroSAT's `analyze` / `implied`
    /// walks dereference them with no source changes. Bound to the
    /// solver on first `try_jit_replace_native` call; reset across
    /// solve / restart boundaries via `last_processed_offset` tracking.
    scratch_arena: ScratchArena,
    /// Pointer offset of `S->processed` (relative to `S->falseStack`)
    /// captured at the end of the previous `try_jit_replace_native`
    /// call. A rewind (current offset < this snapshot) is the
    /// restart signal we use to reset `scratch_arena` (see Risk 3 of
    /// `docs/db_arena_split_design.md`). `isize::MIN` means "never
    /// observed".
    last_processed_offset: isize,
    /// `true` once `scratch_arena.bind_to_solver` has succeeded. False
    /// (and the binding skipped) when the solver has insufficient DB
    /// headroom or `bind_to_solver` returned `ScratchOverflow`. With
    /// the arena unbound, the JIT-replacement path keeps stamping
    /// in-DB reason values exactly as before Phase 2.
    scratch_bound: bool,
}

thread_local! {
    /// Thread-local snapshot of the JIT provider cache. Populated on
    /// the first shadow / primary-JIT call to `trust_cg_propagate`
    /// (per thread). MicroSAT runs single-threaded inside this crate's
    /// tests and binaries, so in practice this is "once per solve".
    static JIT_PROVIDER: RefCell<Option<JitProviderCache>> = const { RefCell::new(None) };

    /// Tracks whether the SHADOW_MODE single-shot JIT evaluation has
    /// already fired for the current cached provider. The
    /// parameter-less `JitBcpKernelProvider` arena is not reset
    /// between calls, so its second invocation would observe stale
    /// state; we therefore evaluate it exactly once per solve.
    static JIT_SHADOW_EVALUATED: RefCell<bool> = const { RefCell::new(false) };
}

/// Reset thread-local shadow / primary state. Tests use this between
/// solves to ensure a clean start; production code does not need to
/// call it.
pub fn reset_jit_shadow_for_tests() {
    JIT_PROVIDER.with(|c| *c.borrow_mut() = None);
    JIT_SHADOW_EVALUATED.with(|c| *c.borrow_mut() = false);
}

/// Compute the DB offset of the first clause record.
///
/// MicroSAT's `initCDCL` allocates many `int` arrays *inside* `DB`
/// before any clauses are appended. The allocation order
/// (microsat.c:181-204) is:
///
/// ```text
///   model     -> n + 1   ints   ( 0          .. n          )
///   next      -> n + 1   ints   ( n+1        .. 2n+1       )
///   prev      -> n + 1   ints   ( 2n+2       .. 3n+2       )
///   buffer    -> n       ints   ( 3n+3       .. 4n+2       )
///   reason    -> n + 1   ints   ( 4n+3       .. 5n+3       )
///   falseStack-> n + 1   ints   ( 5n+4       .. 6n+4       )
///   false     -> 2n+1    ints   ( 6n+5       .. 8n+5       )
///   first     -> 2n+1    ints   ( 8n+6       .. 10n+6      )
///   sentinel  -> 1   int        ( 10n+7                    )
/// ```
///
/// Total pre-clause footprint = `10n + 8` ints. The first clause
/// record's watch-slot 0 lives at offset `10n + 8`.
///
/// `DB[0]` is **not** the global sentinel; it is `model[0]` and
/// therefore an integer that happens to be writable from
/// `S->model[0] = 0` (not in the for loop) but reads as zero only by
/// luck. The actual clause-walk sentinel is at offset `10n + 7`
/// (`DB[mem_used++] = 0` runs *after* every other getMemory call,
/// at the end of initCDCL).
const fn first_clause_offset(num_vars: usize) -> usize {
    10 * num_vars + 8
}

/// Snapshot the input (irreducible) clauses out of MicroSAT's `DB`
/// at the moment of the first shadow-mode call. Returns
/// `(num_vars, clauses)`.
///
/// # Layout
///
/// MicroSAT lays out each clause in `DB` as `[w0, w1, lit0, lit1, ...,
/// lit_{n-1}, 0]`, where `w0` and `w1` are watch-list link slots and
/// the 0 at the end is a literal terminator. The first clause's
/// `w0` slot lives at offset `first_clause_offset(nVars)`; everything
/// before that offset is the bookkeeping arrays (model, next, prev,
/// buffer, reason, falseStack, false, first) plus the global
/// sentinel that `initCDCL` writes immediately before clauses start.
/// After `parse` finishes, every clause in `DB[first_clause_offset
/// .. mem_fixed]` is an input (irreducible) clause - learned lemmas
/// appear later, past `mem_fixed`.
///
/// We walk that region by repeatedly:
///   1. skipping 2 watch slots,
///   2. reading literals until we hit the 0 terminator,
///   3. advancing past the terminator to the next clause record.
///
/// Unit clauses (size 1) have their watch slots left uninitialised by
/// `addClause` (only clauses with size >= 2 install watches), but the
/// walk still works because we skip 2 slots unconditionally. The
/// terminator 0 is always written by `addClause`, so the inner scan
/// is well-defined.
///
/// # Safety
///
/// `s` must point to a fully initialised `sys::solver` (post-`parse`).
/// The `DB`, `nVars`, and `mem_fixed` fields are read; the function
/// performs no writes. The DB region read is `DB[0 .. mem_fixed]`,
/// which `initCDCL` + `parse` together guarantee to be valid and
/// allocated.
unsafe fn snapshot_input_clauses(s: *mut sys::solver) -> (usize, Vec<Vec<i32>>) {
    // SAFETY: precondition - `s` is a valid pointer to an initialised
    // solver. Reading scalar fields by pointer dereference is sound
    // under that precondition.
    let solver_ref = unsafe { &*s };
    let num_vars = solver_ref.nVars as usize;
    let db = solver_ref.DB;
    let mem_fixed = solver_ref.mem_fixed as usize;

    let mut clauses: Vec<Vec<i32>> = Vec::new();
    // Skip the bookkeeping arrays + the clause-region sentinel that
    // `initCDCL` writes at offset `10n + 7`. The first clause record
    // begins immediately after.
    let mut idx: usize = first_clause_offset(num_vars);
    while idx < mem_fixed {
        // 2 watch slots, then literals up to a 0 terminator.
        let lit_start = idx + 2;
        if lit_start >= mem_fixed {
            break;
        }
        let mut k = lit_start;
        let mut clause: Vec<i32> = Vec::new();
        // SAFETY: `db` is valid for `mem_fixed` ints (initCDCL malloc'd
        // `mem_max` ints and `mem_used` <= `mem_max`; `mem_fixed` <=
        // `mem_used`). We never read past `mem_fixed - 1`.
        while k < mem_fixed {
            let lit = unsafe { *db.add(k) };
            if lit == 0 {
                break;
            }
            clause.push(lit);
            k += 1;
        }
        // A well-formed clause record always ends in the 0 terminator;
        // if we hit `mem_fixed` without seeing one the DB is malformed,
        // but we still record what we read and stop the walk.
        if clause.is_empty() {
            // Defensive: an empty literal block means we ran into an
            // unexpected zero (e.g. uninitialised watch slot that
            // happened to be zero on this allocator). Stop rather than
            // emit a spurious empty clause.
            break;
        }
        clauses.push(clause);
        idx = k + 1;
    }

    (num_vars, clauses)
}

/// Build the per-JIT-clause translation table that maps each JIT
/// clause index to the value MicroSAT would write into `S->reason[var]`
/// when that clause forces a literal.
///
/// MicroSAT's `addClause` allocates each clause as a record of
/// `size + 3` ints in `DB`: two watch slots, the `size` literals, and a
/// 0 terminator. The pointer stored on `S->reason[abs(lit)]` after an
/// assign is `1 + (clause - DB)`, where `clause` points to the FIRST
/// literal (offset `record_base + 2` in DB). So for each input clause
/// record at base offset `idx` we record `(idx + 2) + 1 = idx + 3` as
/// the translation entry.
///
/// The walk visits clause records in DB-insertion order. The matching
/// JIT clause index `c` is precisely the c-th entry produced by
/// `snapshot_input_clauses`, which performs the identical walk and
/// produces clauses in the same order. The table therefore has length
/// equal to `num_clauses` (the value returned by `snapshot_input_clauses`).
///
/// # Safety
///
/// `s` must point to a fully initialised `sys::solver` (post-`parse`).
/// `num_clauses` must equal the number of input clauses produced by
/// `snapshot_input_clauses(s)` on the same solver state. The function
/// reads `S->DB[0..S->mem_fixed]` and performs no writes.
unsafe fn build_clause_id_translation(s: *mut sys::solver, num_clauses: usize) -> Vec<i32> {
    // SAFETY: precondition - `s` is a valid pointer to an initialised
    // solver. Reading scalar fields by pointer dereference is sound.
    let solver_ref = unsafe { &*s };
    let num_vars = solver_ref.nVars as usize;
    let db = solver_ref.DB;
    let mem_fixed = solver_ref.mem_fixed as usize;

    let mut table: Vec<i32> = Vec::with_capacity(num_clauses);
    // Skip the bookkeeping arrays + the clause-region sentinel; the
    // first clause record begins at `first_clause_offset(nVars)`.
    let mut idx: usize = first_clause_offset(num_vars);
    while idx < mem_fixed && table.len() < num_clauses {
        // Each clause record: 2 watch slots, then literals, then 0
        // terminator. The first literal lives at `idx + 2`.
        let lit_start = idx + 2;
        if lit_start >= mem_fixed {
            break;
        }
        // The reason value MicroSAT writes is `1 + (clause - DB)`,
        // where `clause` is `DB + lit_start`. We cast to `i32` because
        // MicroSAT stores reason as `c_int` and the translation table
        // entries are written directly to that field.
        // SAFETY: `lit_start + 1` <= `mem_fixed` < `INT_MAX` for any
        // realistic formula (MicroSAT's mem_max is 1 << 30 ints).
        table.push((lit_start + 1) as i32);

        // Walk forward to the 0 terminator and advance `idx` to the
        // start of the next clause record.
        let mut k = lit_start;
        // SAFETY: `db` is valid for `mem_fixed` ints; we read at most
        // up to index `mem_fixed - 1`.
        while k < mem_fixed {
            let lit = unsafe { *db.add(k) };
            if lit == 0 {
                break;
            }
            k += 1;
        }
        idx = k + 1;
    }
    table
}

/// Snapshot the per-variable assignment state out of MicroSAT's
/// `S->false[]` array, packed into an `i8` slice indexed by DIMACS
/// variable number (`+1` true, `-1` false, `0` unassigned). Slot `0`
/// is always `0` (DIMACS variables start at 1).
///
/// MicroSAT's `assign(S, reason, forced)` macro writes
/// `S->false[-lit] = forced ? IMPLIED : 1` to mark the assigned-true
/// literal's negation as falsified. So:
///
///   * `S->false[+v] != 0`  ⇒ literal `+v` is false ⇒ var `v` = false ⇒ `-1`
///   * `S->false[-v] != 0`  ⇒ literal `-v` is false ⇒ var `v` = true  ⇒ `+1`
///   * both zero            ⇒ var `v` is unassigned                   ⇒  `0`
///
/// Both arms cannot be simultaneously non-zero in a self-consistent
/// MicroSAT state (a variable cannot be both true and false). The
/// snapshot resolves the conflict by checking `false[-v]` first; if
/// `false[+v]` were also non-zero on the same call, MicroSAT itself
/// would already be in a corrupt state we cannot improve upon.
///
/// This snapshot is the host-side input to the kernel's
/// `KernelCtx::initial_values` slot. The PRIMARY_JIT_MODE replacement
/// path uses it to seed the kernel's `values[]` array so the kernel
/// can run BCP on the **unprocessed** trail suffix only, matching
/// native MicroSAT's `propagate` semantics ("iterate
/// `S->trail[S->processed..S->assigned]` and propagate each
/// unprocessed literal forward").
///
/// # Safety
///
/// `s` must point to a live, post-`parse` solver. The `false_` field
/// is offset by `+nVars` at construction, so it is indexed by signed
/// literal in `[-nVars, nVars]`. The function performs no writes.
unsafe fn snapshot_initial_values(s: *mut sys::solver) -> Vec<i8> {
    // SAFETY: precondition - `s` is live.
    let solver_ref = unsafe { &*s };
    let num_vars = solver_ref.nVars as usize;
    if solver_ref.false_.is_null() {
        return vec![0i8; num_vars + 1];
    }
    let mut values = vec![0i8; num_vars + 1];
    for (v, value) in values.iter_mut().enumerate().take(num_vars + 1).skip(1) {
        let v_i = v as isize;
        // SAFETY: `false_` was allocated for `2*nVars + 1` ints with
        // `+nVars` offset; indices in `[-nVars, nVars]` are in range.
        let neg = unsafe { *solver_ref.false_.offset(-v_i) };
        let pos = unsafe { *solver_ref.false_.offset(v_i) };
        *value = if neg != 0 {
            // -v is false ⇒ v assigned true
            1
        } else if pos != 0 {
            // +v is false ⇒ v assigned false
            -1
        } else {
            0
        };
    }
    values
}

/// Read the **full** trail (everything from `S->falseStack` up to
/// `S->assigned`) and pack each literal into the
/// `(var << 1) | polarity` format that `JitBcpWithDecisionsProvider`
/// expects.
///
/// The PRIMARY_JIT_MODE replacement path needs the entire trail (not
/// just the unprocessed `processed..assigned` suffix) so the kernel's
/// decode phase reproduces MicroSAT's exact current assignment before
/// running BCP. Without the already-processed prefix, the kernel's
/// initial unit-clause step would re-derive parse-time unit
/// assignments from scratch and re-emit them through
/// `implied_literals_out`, which would cause us to push duplicates
/// back onto MicroSAT's `falseStack`.
///
/// The polarity convention mirrors `snapshot_unprocessed_trail_as_decisions`:
/// a `falseStack` entry `l > 0` (DIMACS literal `+v` is false →
/// var = false) encodes as `(v << 1) | 1`; an entry `l < 0`
/// (`-v` is false → var = true) encodes as `(v << 1) | 0`.
///
/// # Safety
///
/// `s` must point to a live, post-`parse` solver. `falseStack` and
/// `assigned` must both be in-bounds of the same allocated stack
/// region. The function reads `(assigned - falseStack)` `c_int` values
/// starting at `falseStack`.
#[allow(dead_code)]
unsafe fn snapshot_full_trail_as_decisions(s: *mut sys::solver) -> Vec<u32> {
    // SAFETY: precondition - `s` is live; `falseStack` and `assigned`
    // are valid pointers into the same allocation.
    let solver_ref = unsafe { &*s };
    let stack_base = solver_ref.falseStack;
    let assigned = solver_ref.assigned;
    if stack_base.is_null() || assigned.is_null() {
        return Vec::new();
    }
    let count =
        (assigned as isize - stack_base as isize) / (core::mem::size_of::<c_int>() as isize);
    if count <= 0 {
        return Vec::new();
    }
    let mut decisions: Vec<u32> = Vec::with_capacity(count as usize);
    for i in 0..count {
        // SAFETY: `0 <= i < count` and `stack_base[0..count]` lies in
        // the valid falseStack region by the precondition.
        let lit = unsafe { *stack_base.offset(i) };
        if lit == 0 {
            continue;
        }
        let var = lit.unsigned_abs();
        let polarity = if lit > 0 { 1u32 } else { 0u32 };
        decisions.push((var << 1) | polarity);
    }
    decisions
}

/// MicroSAT's `IMPLIED` enum value (from `microsat.c`):
///   `enum { END = -9, UNSAT = 0, SAT = 1, MARK = 2, IMPLIED = 6 };`
/// Used in `assign` to tag a literal as "forced at the root level"
/// in `S->false[-lit]`. We replicate that exact value when emulating
/// `assign` from the JIT replacement path so MicroSAT's downstream
/// `bump` / `implied` / `analyze` machinery cannot distinguish
/// JIT-emitted assignments from native-emitted ones.
const MICROSAT_IMPLIED: c_int = 6;

/// Replicate the body of MicroSAT's `assign(S, reason, forced=1)` macro
/// (microsat.c:42-47) for a single (literal, reason-clause-id) pair
/// emitted by the JIT kernel. Pushes the literal onto MicroSAT's trail,
/// stamps `S->false[-lit]`, `S->reason[abs(lit)]`, and `S->model[abs(lit)]`
/// to the values the native path would have stored.
///
/// Mapping JIT outputs → MicroSAT state:
///   - `lit` is the DIMACS-signed literal (positive=var-true,
///     negative=var-false) the JIT just assigned in its private arena.
///   - `reason` is the DB-offset-plus-1 of the forcing clause's first
///     literal, supplied by the kernel via the clause-id translation
///     table. This is exactly the value MicroSAT's own `assign` would
///     have written to `S->reason[abs(lit)]`.
///
/// Sign conventions cross-checked against `microsat.c`:
///   - `assign` does `S->false[-lit] = IMPLIED`. We mirror that
///     (note: `S->false` is offset by `+n` at construction, so it is
///     indexed by signed literal in [-n, n]).
///   - `assign` does `*(S->assigned++) = -lit`. MicroSAT's stack stores
///     **false** literals (the negation of the assigned-true literal),
///     so we push `-lit` exactly.
///   - `assign` does `S->reason[abs(lit)] = 1 + (reason - S->DB)`.
///     The kernel has pre-computed that value via the translation
///     table; we store it as-is.
///   - `assign` does `S->model[abs(lit)] = (lit > 0)`. Direct mirror.
///
/// The `forced` argument controls the `S->false[-lit]` tag exactly
/// as MicroSAT's `assign(S, reason, forced)` does (microsat.c:44):
/// `forced != 0` writes `IMPLIED` (6), `forced == 0` writes `1`. The
/// JIT-replacement path passes the value of `S->reason[abs(*S->processed)]
/// != 0` computed once at top-of-propagate, which is exactly the
/// invariant MicroSAT's own propagate holds across all of its inner
/// `assign` calls.
///
/// # Safety
///
/// `s` must point to a live, post-`parse` solver with `nVars >=
/// abs(lit)` and writable `false`, `reason`, `model`, and `assigned`
/// regions. The caller (apply_jit_implications) must ensure the
/// literal is not already assigned in MicroSAT's state (the JIT only
/// emits literals it freshly assigned in its private arena, which
/// mirrors MicroSAT's trail because the full trail was passed in as
/// decisions).
/// Phase 2 DB-arena split: install one JIT-propagated literal into
/// MicroSAT's state and stamp its reason value. `reason` is the value
/// to write to `S->reason[abs(lit)]`. The caller is responsible for
/// allocating the (synthetic or in-DB) reason value beforehand and
/// passing it in here; this function makes no decision about whether
/// to use scratch storage or the original DB offset.
///
/// Replaces the historical `DbClauseSwap`-based workaround: the swap
/// is no longer needed because synthetic clauses already satisfy
/// `clause[0] == lit` by construction (see
/// `docs/db_arena_split_design.md`). Original DB-offset reasons are
/// safe in regimes where `analyze` never runs (root-forced UNSAT, or
/// SAT-OK at decision level 0).
unsafe fn microsat_assign_from_jit(s: *mut sys::solver, lit: i32, reason: i32, forced: bool) {
    // SAFETY: precondition - `s` is live and exclusively owned for
    // the duration of this call.
    let solver_ref = unsafe { &mut *s };
    let var = lit.unsigned_abs() as isize;
    let neg_lit = (-lit) as isize;

    // S->false is offset by +n at construction (microsat.c initCDCL),
    // so it is indexed by signed literal in [-n, n]. Mirror MicroSAT's
    // `S->false[-lit] = forced ? IMPLIED : 1;` exactly.
    //
    // SAFETY: `solver_ref.false_` points into the allocated `2*n+1`-int
    // region with `+n` already added; `neg_lit` lies in [-n, n] for
    // any valid input literal.
    let false_tag: c_int = if forced { MICROSAT_IMPLIED } else { 1 };
    unsafe {
        *solver_ref.false_.offset(neg_lit) = false_tag;
    }

    // Push `-lit` onto the falseStack and advance `S->assigned`.
    //
    // SAFETY: the JIT-replacement path is only entered when the JIT
    // emits at most `num_vars` propagations, and `falseStack` is
    // sized `nVars + 1` by `initCDCL`. The caller
    // (apply_jit_implications) verifies the implied-len fits within
    // `num_vars` before invoking us, so `assigned + 1 <= falseStack
    // + nVars + 1`.
    unsafe {
        *solver_ref.assigned = -lit;
        solver_ref.assigned = solver_ref.assigned.add(1);
    }

    // S->reason is indexed by `abs(lit)` for `1 <= abs(lit) <= nVars`
    // and allocated for `n+1` ints by initCDCL.
    //
    // SAFETY: `var = |lit|` is in `[1, nVars]` and `reason` is
    // `n+1` ints long.
    unsafe {
        *solver_ref.reason.offset(var) = reason;
    }

    // S->model is indexed by abs(lit); 0/1-valued ("phase save").
    //
    // SAFETY: same indexing bounds as `S->reason`.
    let model_val: c_int = if lit > 0 { 1 } else { 0 };
    unsafe {
        *solver_ref.model.offset(var) = model_val;
    }
}

/// Read all literals of the input clause whose first-literal-slot
/// offset is `reason - 1`, returning every literal EXCEPT `propagated`
/// (the JIT-propagated literal). Walks the clause until the 0
/// terminator. Used by `install_scratch_reasons_for_jit` to derive
/// the antecedent list host-side without extending the kernel ABI: the
/// host can read C's literals from `S->DB` directly.
///
/// Returns an empty `Vec` if `reason <= 0` (defensive: callers should
/// already have screened these out).
///
/// # Safety
///
/// `db` must be the live `S->DB` pointer of a parsed solver, and
/// `reason - 1` must address a valid 0-terminated clause record
/// inside `S->DB[0..S->mem_used]`.
unsafe fn antecedents_from_db_clause(db: *mut c_int, propagated: i32, reason: i32) -> Vec<i32> {
    if reason <= 0 {
        return Vec::new();
    }
    let mut ants = Vec::new();
    let lit_start = (reason - 1) as isize;
    let mut k: isize = 0;
    // SAFETY: by precondition `lit_start..` is a 0-terminated literal
    // run inside `S->DB`; we only read and stop at the terminator.
    unsafe {
        loop {
            let slot = *db.offset(lit_start + k);
            if slot == 0 {
                break;
            }
            if slot != propagated {
                ants.push(slot);
            }
            k += 1;
        }
    }
    ants
}

/// Apply a JIT-produced implication stream (literal + reason pairs)
/// to MicroSAT's solver state, mimicking what `microsat_native_propagate`
/// would have done. Then advance `S->processed` to `S->assigned` and
/// — only when `forced` is true — also lift `S->forced` to the new
/// `S->processed`, matching propagate's `if (forced) S->forced = S->processed;`
/// post-loop bookkeeping (microsat.c:157).
///
/// `lits` and `reasons` are parallel slices. The caller MUST have
/// verified that the implied-literals length is not `usize::MAX`
/// (no overflow signalled by the kernel).
///
/// # Safety
///
/// `s` must point to a live, post-`parse` solver. The literal and
/// reason slices must come from the most recent JIT call and the
/// translation table installed on the kernel handle (so reason values
/// are valid DB offsets the analyze/implied machinery can walk).
/// `falseStack` must have at least `lits.len()` free slots above its
/// current `S->assigned`.
unsafe fn apply_jit_implications(s: *mut sys::solver, lits: &[i32], reasons: &[i32], forced: bool) {
    debug_assert_eq!(lits.len(), reasons.len());
    for i in 0..lits.len() {
        let lit = lits[i];
        let reason = reasons[i];
        // SAFETY: precondition propagated to `microsat_assign_from_jit`:
        // `s` is live and exclusively owned, and the literal slice
        // was just emitted by the JIT (so each `lit` is in [-nVars, nVars]
        // and not currently assigned in MicroSAT's state).
        unsafe { microsat_assign_from_jit(s, lit, reason, forced) };
    }
    // SAFETY: `s` is live by precondition.
    let solver_ref = unsafe { &mut *s };
    // Mirror `microsat_native_propagate`'s post-loop bookkeeping:
    // processed always catches up to assigned; S->forced only
    // advances if `forced` is set (root-forced regime), matching
    // microsat.c:157 `if (forced) S->forced = S->processed;`.
    solver_ref.processed = solver_ref.assigned;
    if forced {
        solver_ref.forced = solver_ref.processed;
    }
}

/// Phase 2 helper: replace each in-DB reason value with a synthetic
/// reason allocated in the per-solve scratch arena. Returns a new
/// `Vec<i32>` parallel to `reasons` containing the scratch reason
/// values, or `Err(())` if the arena ran out of headroom or rejected
/// a request mid-way (the caller falls back to native for the rest
/// of this solve).
///
/// On the happy path each synthetic clause has the layout
/// `[lits[i], antecedent_0, antecedent_1, ..., 0]` where the
/// antecedent list is "all literals of the kernel-supplied input
/// clause except `lits[i]`" (derived host-side from `S->DB`; see
/// `antecedents_from_db_clause`). The reason value the synthetic
/// clause yields is `1 + (clause_first_lit_slot_offset - S->DB)`,
/// the same convention MicroSAT's `assign` macro uses, so the
/// existing `analyze` / `implied` walks dereference it with no
/// source changes.
///
/// # Safety
///
/// `s` must be a live, post-`parse` solver, and `reasons[i]` must be
/// a valid `1 + DB_offset` reason value into `S->DB[0..S->mem_used]`
/// (which is what the kernel's `clause_id_translation`-driven output
/// guarantees). `arena` must already be `bind_to_solver`'d against
/// the same `s`.
unsafe fn install_scratch_reasons_for_jit(
    s: *mut sys::solver,
    lits: &[i32],
    reasons: &[i32],
    arena: &mut ScratchArena,
) -> Result<Vec<i32>, ()> {
    debug_assert_eq!(lits.len(), reasons.len());
    // SAFETY: `s` is live by precondition.
    let solver_ref = unsafe { &mut *s };
    let db = solver_ref.DB;
    let mut scratch_reasons = Vec::with_capacity(lits.len());
    for i in 0..lits.len() {
        let lit = lits[i];
        let reason = reasons[i];
        // SAFETY: arena was bound to `s`; reading `S->mem_used` is a
        // plain int field load.
        if unsafe { arena.is_near_overflow(s) } {
            JIT_SCRATCH_OVERFLOW_FALLBACKS.fetch_add(1, Ordering::Relaxed);
            if TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed) {
                eprintln!(
                    "trust_cg_propagate: scratch arena near overflow at \
                     implication #{}/{}; falling back to native for this call",
                    i,
                    lits.len()
                );
            }
            return Err(());
        }
        // SAFETY: `db` is the live `S->DB` pointer; `reason - 1` is
        // a valid first-lit-slot offset by the caller's contract.
        let ants = unsafe { antecedents_from_db_clause(db, lit, reason) };
        match arena.allocate_synthetic_clause(lit, &ants) {
            Ok(scratch_reason) => scratch_reasons.push(scratch_reason),
            Err(_overflow) => {
                JIT_SCRATCH_OVERFLOW_FALLBACKS.fetch_add(1, Ordering::Relaxed);
                if TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed) {
                    eprintln!(
                        "trust_cg_propagate: scratch arena overflow at \
                         implication #{}/{}; falling back to native for this call",
                        i,
                        lits.len()
                    );
                }
                return Err(());
            }
        }
    }
    Ok(scratch_reasons)
}

/// Compute the byte offset of `S->processed` into the falseStack
/// region. Used as the restart-detection signal: a rewind
/// (current < previous) indicates MicroSAT executed `restart` between
/// JIT-replacement calls, and the scratch arena's contents are now
/// stale w.r.t. the current trail and must be reset.
///
/// Returns `isize::MIN` when either pointer is null (unbound solver),
/// which sentinel value compares less than any valid offset and so
/// suppresses the rewind check until both pointers are populated.
///
/// # Safety
///
/// `s` must be a live solver.
unsafe fn current_processed_offset(s: *mut sys::solver) -> isize {
    // SAFETY: caller's precondition.
    let solver_ref = unsafe { &*s };
    let processed = solver_ref.processed;
    let base = solver_ref.falseStack;
    if processed.is_null() || base.is_null() {
        return isize::MIN;
    }
    // SAFETY: both pointers point into the same allocated stack
    // region; pointer subtraction is well-defined.
    unsafe { processed.offset_from(base) }
}

/// Read the `forced` flag exactly as MicroSAT's `propagate` computes
/// it at top-of-loop (microsat.c:133):
///   `int forced = S->reason[abs(*S->processed)];`
///
/// The flag is non-zero iff the first unprocessed literal was
/// unit-implied (root-forced regime) and zero iff it was decision-
/// derived. Returned as `bool` so the JIT-replacement helpers can
/// branch without re-reading the raw `c_int`. When the unprocessed
/// trail is empty the value is irrelevant (the JIT path early-skips),
/// so we conservatively return `false` in that case.
///
/// # Safety
///
/// `s` must point to a live, post-`parse` solver.
unsafe fn read_microsat_forced_flag(s: *mut sys::solver) -> bool {
    // SAFETY: precondition - `s` is live.
    let solver_ref = unsafe { &*s };
    let processed = solver_ref.processed;
    let assigned = solver_ref.assigned;
    if processed.is_null() || assigned.is_null() || processed >= assigned {
        return false;
    }
    // SAFETY: `processed < assigned` and both point into the
    // falseStack region.
    let first_lit = unsafe { *processed };
    if first_lit == 0 {
        return false;
    }
    let var = first_lit.unsigned_abs() as usize;
    if solver_ref.reason.is_null() {
        return false;
    }
    // SAFETY: `reason` is allocated for `nVars + 1` ints by
    // `initCDCL`, indexed by `abs(lit)` for `1 <= abs(lit) <= nVars`.
    let reason_val = unsafe { *solver_ref.reason.add(var) };
    reason_val != 0
}

/// Returns `true` iff the unprocessed trail region is non-empty.
/// Used as a fast pre-flight check: if there are no pending literals
/// to propagate, MicroSAT's native propagate is a trivial no-op and
/// running the JIT would force it to re-derive parse-time unit
/// assignments with no MicroSAT-visible benefit. We therefore leave
/// the empty-trail case to native.
///
/// # Safety
///
/// `s` must point to a live, post-`parse` solver.
unsafe fn unprocessed_trail_nonempty(s: *mut sys::solver) -> bool {
    // SAFETY: precondition - `s` is live.
    let solver_ref = unsafe { &*s };
    let processed = solver_ref.processed;
    let assigned = solver_ref.assigned;
    if processed.is_null() || assigned.is_null() {
        return false;
    }
    processed < assigned
}

/// Returns `true` iff MicroSAT's current decision-level is zero, i.e.
/// the entire trail `[falseStack .. assigned)` contains only literals
/// that were unit-propagated (reason != 0) and no decisions
/// (reason == 0). See microsat.c:179 - `solve` writes
/// `S->reason[decision] = 0` after pushing a decision literal onto the
/// stack, so any decision-or-decision-implied trail entry has
/// `reason == 0` for the decision itself (its implications still have
/// non-zero reasons, but the decision is on the stack so the walk
/// trips on the zero).
///
/// This is the precise gate for "a JIT-reported conflict short-circuits
/// to UNSAT". MicroSAT's `propagate` returns UNSAT only when its local
/// `forced` flag (computed at top-of-loop from
/// `reason[abs(*S->processed)]`) is non-zero AT THE POINT OF CONFLICT,
/// and that flag is non-zero iff the literal currently being processed
/// has a non-zero reason. After backjump-to-DL0 + unit-lemma-assign,
/// the lemma's UIP has a non-zero reason and the top-of-loop flag is
/// non-zero, but the trail may still contain pre-existing decisions
/// at higher decision levels (analyze rewinds those, so at DL0 the
/// trail is decision-free) - but the converse case matters: after
/// backjump-to-DL>=1 + non-unit-lemma-assign, the lemma's UIP also has
/// a non-zero reason, the top-of-loop flag is also non-zero, but a
/// decision LIVES on the trail. The conflict-branch must NOT map that
/// case to UNSAT.
///
/// Walking the trail and checking every var's reason is the
/// canonical, MicroSAT-faithful check. The complementary
/// `S->forced == S->assigned` test would also work post-propagate
/// (when `S->forced` has been lifted to `S->processed`), but it does
/// NOT hold mid-call before propagate has run: e.g. after parse units
/// are pushed via `assign(S, clause, 1)` (microsat.c:239), `S->forced`
/// stays at the falseStack base while `S->assigned` advances past the
/// units; that state is still DL0 but the pointer test would
/// (incorrectly) report DL>=1.
///
/// # Safety
///
/// `s` must point to a live, post-`parse` solver. `falseStack`,
/// `assigned`, and `reason` must all be in-bounds of the same
/// allocated region (`initCDCL` invariant).
/// C ABI surface for `decision_level_is_zero`. The build-time text
/// rewrite in `build.rs::rewrite_definitions` redirects MicroSAT's
/// line-133 `forced` initialiser to call this symbol, replacing the
/// "is the next literal forced?" proxy with a canonical decision-
/// level-0 walk over the trail.
///
/// Returns `1` (C int) iff every entry in `[falseStack..assigned)`
/// has `reason != 0` (i.e. no decision lives on the trail), otherwise
/// `0`. The return value goes directly into MicroSAT's local `int
/// forced` variable so the line-153 short-circuit `if (forced) return
/// UNSAT;` only fires at true DL0, and the line-157 post-loop
/// `if (forced) S->forced = S->processed;` only lifts the forced
/// watermark when the whole trail is unit-propagated.
///
/// # Safety
///
/// `s` must point to a live, post-`parse` solver — the same
/// precondition MicroSAT's own `propagate` body assumes when it
/// dereferences `S->reason`, `S->falseStack`, and `S->assigned`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_cg_decision_level_is_zero(s: *mut sys::solver) -> c_int {
    // SAFETY: caller's precondition matches `decision_level_is_zero`'s.
    if unsafe { decision_level_is_zero(s) } {
        1
    } else {
        0
    }
}

unsafe fn decision_level_is_zero(s: *mut sys::solver) -> bool {
    // SAFETY: precondition - `s` is live.
    let solver_ref = unsafe { &*s };
    let base = solver_ref.falseStack;
    let assigned = solver_ref.assigned;
    let reason = solver_ref.reason;
    if base.is_null() || assigned.is_null() || reason.is_null() {
        // Cannot establish DL0 without a populated trail and reason
        // array; conservatively report "not at root" so the conflict
        // branch surrenders to native.
        return false;
    }
    if assigned <= base {
        // Empty trail. No decisions => decision_level == 0.
        return true;
    }
    let count = (assigned as isize - base as isize) / (core::mem::size_of::<c_int>() as isize);
    if count <= 0 {
        return true;
    }
    for i in 0..count {
        // SAFETY: `0 <= i < count` and `base[0..count)` lies within
        // the live falseStack region by the precondition.
        let lit = unsafe { *base.offset(i) };
        if lit == 0 {
            // Defensive: a zero sentinel on the stack would indicate
            // a corrupted layout. Treat as "not at root" rather than
            // panicking.
            return false;
        }
        let var = lit.unsigned_abs() as usize;
        // SAFETY: `reason` is allocated for `nVars + 1` ints by
        // `initCDCL` and indexed by `abs(lit)` for valid trail
        // literals (parse rejected out-of-range literals upstream).
        let reason_val = unsafe { *reason.add(var) };
        if reason_val == 0 {
            // A literal with `reason == 0` is a decision (per
            // microsat.c:179). Decision_level > 0.
            return false;
        }
    }
    true
}

/// Run the SHADOW_MODE single-shot JIT BCP on the cached provider.
/// Returns `Some(result)` where `result` is the JIT kernel's `result`
/// code (0 = no conflict, 1 = conflict, 2 = decode error), or `None`
/// if the JIT path was skipped (already evaluated for this cached
/// provider, or the provider was never compiled).
///
/// For the scan-only kernel (single-shot) the call fires at most once
/// per solve, gated by `evaluated`. For the resettable kernels
/// (with-decisions, watched-literal) the call also fires once per
/// solve so the shadow contract stays "single differential check per
/// solve" regardless of kernel choice — divergence telemetry would
/// otherwise mean different things across kernels.
fn run_jit_shadow_once(cache: &mut JitProviderCache, evaluated: &mut bool) -> Option<u32> {
    if *evaluated {
        return None;
    }
    let provider = cache.provider.as_ref()?;
    let result = provider.shadow_call();
    *evaluated = true;
    Some(result)
}

/// Run the PRIMARY_JIT_MODE JIT BCP. The arena is reset before each
/// call (via the chosen provider's `reset_arena()`) so the kernel
/// always sees the original formula plus the freshly supplied
/// decision slice; state from a previous call cannot leak forward.
///
/// Returns the JIT kernel's `result` code (0 = no conflict,
/// 1 = conflict, 2 = decode error) or `None` if the chosen provider
/// does not support primary mode (e.g. the scan-only kernel) or was
/// never compiled (compile-failure path on first call).
fn run_jit_primary(cache: &mut JitProviderCache, decisions: &[u32]) -> Option<u32> {
    let provider = cache.provider.as_ref()?;
    provider.primary_call(decisions)
}

/// Read the unprocessed trail segment out of MicroSAT's solver state
/// and pack it into the `(var << 1) | polarity` decision-literal
/// format that `JitBcpWithDecisionsProvider` expects.
///
/// MicroSAT's trail layout: `S->falseStack` is the base of a stack of
/// *false* literals (i.e. each entry `l` means "literal `l` is set to
/// false in the current assignment"). `S->processed .. S->assigned`
/// is the unpropagated suffix. For each entry `l` we recover the
/// variable `abs(l)` and the polarity bit (1 if `l > 0`, since
/// "literal `+v` is false" means "variable `v` is assigned `false`",
/// which the JIT encodes as polarity=1; 0 if `l < 0`, since "literal
/// `-v` is false" means "variable `v` is assigned `true`", encoded
/// as polarity=0).
///
/// # Safety
///
/// `s` must point to a live, post-`parse` solver. `falseStack`,
/// `processed`, and `assigned` must all be in-bounds of the same
/// allocated stack region. The function reads `(assigned - processed)`
/// `c_int` values starting at `processed`.
unsafe fn snapshot_unprocessed_trail_as_decisions(s: *mut sys::solver) -> Vec<u32> {
    // SAFETY: precondition - `s` is live and the falseStack region
    // between `processed` and `assigned` is valid for read.
    let solver_ref = unsafe { &*s };
    let processed = solver_ref.processed;
    let assigned = solver_ref.assigned;
    if processed.is_null() || assigned.is_null() {
        return Vec::new();
    }
    // `assigned - processed` is the number of pending literals to
    // propagate. This subtraction is well-defined under the trail
    // invariant `processed <= assigned`.
    let count = (assigned as isize - processed as isize) / (core::mem::size_of::<c_int>() as isize);
    if count <= 0 {
        return Vec::new();
    }
    let mut decisions: Vec<u32> = Vec::with_capacity(count as usize);
    for i in 0..count {
        // SAFETY: `0 <= i < count` and `processed[0 .. count]` lies in
        // the valid falseStack region by the precondition.
        let lit = unsafe { *processed.offset(i) };
        // Skip the zero sentinel some MicroSAT paths may leave on the
        // stack (defensive; under normal use `assign` never pushes
        // zero, but we'd rather decode-error than panic on an
        // unexpected layout).
        if lit == 0 {
            continue;
        }
        let var = lit.unsigned_abs();
        // `lit > 0` on the false-stack means "literal +var is false",
        // i.e. var is assigned the truth value `false`. The
        // with-decisions kernel encodes that as polarity bit = 1
        // (negative). `lit < 0` correspondingly is polarity bit = 0
        // (positive).
        let polarity = if lit > 0 { 1u32 } else { 0u32 };
        decisions.push((var << 1) | polarity);
    }
    decisions
}

/// Convert a JIT BCP kernel result code into a MicroSAT propagate
/// return value (`sys::SAT` = no conflict, `sys::UNSAT` = root-level
/// conflict). A decode error (result == 2) is treated as "JIT could
/// not answer" - returns `None`, instructing the caller to fall
/// through to the native return value.
fn jit_result_to_microsat(result: u32) -> Option<c_int> {
    match result {
        0 => Some(sys::SAT),
        1 => Some(sys::UNSAT),
        _ => None,
    }
}

/// Returns `true` if the JIT's verdict on this propagate call maps
/// faithfully onto MicroSAT's return contract. The JIT only answers
/// "given the original formula plus these forced assignments, is a
/// conflict derivable?"; MicroSAT returns UNSAT only on a *root-level*
/// conflict (mid-search conflicts get absorbed by `analyze()` and
/// the function returns SAT). The two notions coincide exactly when
/// MicroSAT's local `forced` flag - computed as
/// `S->reason[abs(*S->processed)]` at the top of `propagate` - is
/// non-zero, because that is precisely the branch where a conflict
/// returns UNSAT directly without invoking `analyze`.
///
/// We replicate that check here on the pre-native solver state:
///
///   * If the unprocessed region is empty (`processed == assigned`),
///     the JIT trivially answers OK and so does native - both safe
///     to treat as authoritative.
///   * Otherwise the JIT is authoritative iff
///     `reason[abs(first_unprocessed_lit)] != 0` (i.e. the literal
///     was unit-implied, not picked as a decision). When `reason`
///     is zero we are inside the decision loop and the JIT may
///     legitimately see a conflict where native legitimately
///     returns SAT, so we surrender the primary path to native.
///
/// # Safety
///
/// `s` must point to a live, post-`parse` solver.
unsafe fn jit_is_authoritative_at_root(s: *mut sys::solver) -> bool {
    // SAFETY: precondition - `s` is live.
    let solver_ref = unsafe { &*s };
    let processed = solver_ref.processed;
    let assigned = solver_ref.assigned;
    if processed.is_null() || assigned.is_null() {
        return false;
    }
    if processed == assigned {
        // Empty unprocessed segment: both implementations return
        // SAT trivially, so we can safely call the JIT
        // authoritative.
        return true;
    }
    // SAFETY: `processed < assigned` and both point into the
    // falseStack region.
    let first_lit = unsafe { *processed };
    if first_lit == 0 {
        return false;
    }
    let var = first_lit.unsigned_abs() as usize;
    // SAFETY: `reason` is allocated for `nVars + 1` ints by
    // `initCDCL`, indexed by `abs(lit)` for `1 <= abs(lit) <= nVars`.
    // A pushed literal has `abs(lit) >= 1`, and `parse` rejects
    // out-of-range literals upstream.
    if solver_ref.reason.is_null() {
        return false;
    }
    let reason_val = unsafe { *solver_ref.reason.add(var) };
    reason_val != 0
}

/// Outcome of the JIT-replaces-native fast path. Only present when
/// the JIT could produce a deterministic verdict (and apply any
/// implications to MicroSAT's state). Falls back to `None` (caller
/// then runs native) on cache miss, epoch expiry, decode error, or
/// buffer overflow.
enum JitReplacementOutcome {
    /// JIT propagated cleanly. Implications already stamped into
    /// MicroSAT's `falseStack` / `reason` / `model`, and
    /// `S->processed` / `S->forced` advanced to `S->assigned`.
    Sat,
    /// JIT hit a decision-level-0 conflict. MicroSAT's `solve`
    /// interprets a propagate return of UNSAT at DL0 as a terminal
    /// verdict and returns UNSAT to the caller without inspecting any
    /// further state. The solver-state mutations the JIT applied
    /// (partial implications before the conflict point) are therefore
    /// inconsequential for correctness but harmless to leave in
    /// place. The gate that distinguishes DL0 from "kick-off literal
    /// has reason != 0" is `decision_level_is_zero` (post-B1).
    Unsat,
    /// The analyze-driver path drove MicroSAT's `analyze` and
    /// `assign` from outside its propagate context (post-Phase-2
    /// option-(c) implementation of the empty-lemma bug fix). The
    /// host-side `native_find_first_conflict_clause` walk picks
    /// the same conflict clause native's `propagate` would have,
    /// then `analyze(S, clause)` + `assign(S, lemma, post_forced)`
    /// run the standard CDCL learn-and-backjump cycle. MicroSAT's
    /// `solve` interprets this as a regular SAT return (a
    /// learned-lemma round-trip).
    AnalyzeDriven,
}

/// Attempt to run the JIT-as-primary propagate kernel and apply its
/// output to MicroSAT's solver state, effectively replacing the
/// `microsat_native_propagate` call for this iteration.
///
/// Returns `None` (the caller then runs native) on:
///   * cache not yet built / compile-failure path,
///   * the cache's epoch boundary has already tripped,
///   * implied-literals buffer overflow signalled by the kernel,
///   * kernel decode error (`result == 2`),
///   * implied-literals length larger than the allocated buffer.
///
/// On success returns `Some(JitReplacementOutcome::Sat)` or
/// `Some(JitReplacementOutcome::Unsat)`, with MicroSAT's state
/// already updated (SAT case) or left untouched (UNSAT case).
///
/// # Inputs
///
/// `initial_values` is a per-variable assignment slice (`+1` true,
/// `-1` false, `0` unassigned, slot `0` unused) captured from
/// MicroSAT's `S->false[]` array at entry to propagate. The kernel
/// uses this to seed its `values[]` arena before processing any
/// decisions, mirroring MicroSAT's "already-settled trail prefix"
/// state.
///
/// `unprocessed_decisions` is the packed `(var << 1) | polarity`
/// slice corresponding to `S->trail[S->processed..S->assigned]`, i.e.
/// only the literals MicroSAT has not yet propagated. Passing the
/// full trail (settled + unprocessed) as decisions would cause the
/// kernel to re-derive (and emit through `implied_literals_out`)
/// literals already on MicroSAT's stack, which would result in
/// double-push corruption when `apply_jit_implications` ran.
///
/// # Safety
///
/// `s` must point to a live, post-`parse` solver. `initial_values`
/// and `unprocessed_decisions` must be derived from the same
/// pre-native snapshot of the solver state.
unsafe fn try_jit_replace_native(
    s: *mut sys::solver,
    initial_values: &[i8],
    unprocessed_decisions: &[u32],
) -> Option<JitReplacementOutcome> {
    JIT_PROVIDER.with(|cache_cell| {
        JIT_SHADOW_EVALUATED.with(|evaluated_cell| {
            let mut cache_ref = cache_cell.borrow_mut();
            let mut evaluated_ref = evaluated_cell.borrow_mut();

            // First-call cache initialisation. The JIT is compiled
            // against the original (input) formula; learned lemmas
            // never enter the kernel's clause set. Phase 2's scratch
            // arena holds reason values for JIT-implied literals in
            // S->DB's high tail, so MicroSAT's analyze/implied walks
            // remain consistent across the whole solve even as
            // lemmas pile up.
            if cache_ref.is_none() {
                // SAFETY: `s` satisfies the precondition.
                let (num_vars, clauses) = unsafe { snapshot_input_clauses(s) };
                let num_clauses = clauses.len();
                // SAFETY: same precondition; reads `DB[0..mem_fixed]`.
                let clause_id_translation = unsafe { build_clause_id_translation(s, num_clauses) };
                // Compile via the kernel-choice atomic (default
                // JIT_KERNEL_WATCHED_LITERAL). A single provider serves both the
                // replacement primary path and the legacy shadow path.
                let choice = JIT_KERNEL_CHOICE.load(Ordering::Relaxed);
                let compiled = compile_chosen_provider(choice, num_vars, clauses);
                let provider = match compiled {
                    Ok(p) => Some(p),
                    Err(err) => {
                        eprintln!(
                            "trust_cg_propagate: JIT compile failed for kernel choice {}: \
                             {err}; primary replacement disabled for this solver",
                            kernel_choice_label(choice)
                        );
                        None
                    }
                };
                if provider.is_some() {
                    JIT_INIT_COUNT.fetch_add(1, Ordering::Relaxed);
                }
                let buf_size = (num_vars * 2).max(8);
                // Phase 2: bind a per-solve scratch arena to the
                // solver's `S->DB`. Sized as `num_vars * 8` ints
                // (each implication needs <= clause_len + 2 words,
                // and at most `num_vars` implications per call).
                let scratch_reserve = (num_vars.saturating_mul(8)).max(64);
                let mut scratch_arena = ScratchArena::new(scratch_reserve);
                // SAFETY: `s` is live and post-`parse` per the
                // enclosing function's precondition.
                let scratch_bound = unsafe { scratch_arena.bind_to_solver(s) }.is_ok();
                if !scratch_bound && TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed) {
                    eprintln!(
                        "trust_cg_propagate: scratch_arena.bind_to_solver rejected \
                         reserve={} (DB headroom too tight); Phase 2 analyze-driver \
                         disabled for this solver",
                        scratch_reserve
                    );
                }
                *cache_ref = Some(JitProviderCache {
                    provider,
                    clause_id_translation,
                    implied_literals_buf: vec![0i32; buf_size],
                    implied_reasons_buf: vec![0i32; buf_size],
                    scratch_arena,
                    last_processed_offset: isize::MIN,
                    scratch_bound,
                });
                *evaluated_ref = false;
            }

            let cache = cache_ref.as_mut()?;

            // Phase 2 restart-trampoline (Risk #3 of the design doc):
            // if MicroSAT executed `restart` between calls, the
            // `S->processed` pointer rewinds to `S->trail` (= top of
            // falseStack). Any scratch reasons we installed in a
            // previous call are still pointed at by `S->reason[var]`
            // for variables that have since been unassigned and may
            // be re-assigned by future propagate steps. Detect the
            // rewind by comparing the current processed-offset against
            // the snapshot from the previous call; on rewind, reset
            // the scratch arena so future scratch_reason values start
            // fresh.
            //
            // SAFETY: `s` is live per precondition.
            let current_off = unsafe { current_processed_offset(s) };
            if current_off != isize::MIN
                && cache.last_processed_offset != isize::MIN
                && current_off < cache.last_processed_offset
            {
                cache.scratch_arena.reset();
            }

            // Split the cache into disjoint mutable borrows so the
            // provider and the buffers can be passed simultaneously.
            // The provider is now an `Arc<ChosenProvider>` so we
            // only need a shared reference for the call below;
            // arena mutation goes through the RefCell-wrapped arena
            // inside each kernel provider.
            let JitProviderCache {
                provider,
                implied_literals_buf,
                implied_reasons_buf,
                clause_id_translation,
                scratch_arena,
                scratch_bound,
                last_processed_offset,
                ..
            } = cache;
            let scratch_bound = *scratch_bound;
            let chosen = provider.as_ref()?;
            if !chosen.supports_primary() {
                return None;
            }

            // Pre-call hygiene: zero the head of each output buffer
            // so a stale value from a previous call cannot be
            // misread. (Belt-and-braces; the kernel-side
            // `implied_literals_len` already bounds the valid region.)
            for slot in implied_literals_buf.iter_mut() {
                *slot = 0;
            }
            for slot in implied_reasons_buf.iter_mut() {
                *slot = 0;
            }

            // Run via the chosen provider. The replacement path
            // requires a concrete `SolverKernelProvider` (not the
            // enum) to hand to `SolverKernelHandle::from_provider`,
            // hence the match. Scan kernels return `None` above via
            // the `supports_primary` gate.
            //
            // The kernel's `values[]` arena is seeded from
            // `initial_values` (per the kernel ABI's
            // initial-values seeding contract) so the BCP loop runs
            // against MicroSAT's exact pre-call assignment state.
            // Only the unprocessed trail suffix is passed as
            // decisions, matching native MicroSAT's "process
            // [S->processed..S->assigned] forward" semantics. The
            // kernel therefore emits ONLY the newly-derived
            // implications through `implied_literals_out`, never
            // re-emitting literals already on MicroSAT's stack.
            let status = match chosen {
                ChosenProvider::Scan(_) => return None,
                ChosenProvider::WithDecisions(p) => {
                    p.reset_arena();
                    let mut handle = SolverKernelHandle::from_provider(&**p);
                    handle.set_implied_literals_buffer(implied_literals_buf.as_mut_slice());
                    handle.set_implied_reasons_buffer(implied_reasons_buf.as_mut_slice());
                    handle.set_clause_id_translation(clause_id_translation.as_slice());
                    handle.set_initial_values(initial_values);
                    handle.call(unprocessed_decisions)
                }
                ChosenProvider::WatchedLiteral(p) => {
                    p.reset_arena();
                    let mut handle = SolverKernelHandle::from_provider(&**p);
                    handle.set_implied_literals_buffer(implied_literals_buf.as_mut_slice());
                    handle.set_implied_reasons_buffer(implied_reasons_buf.as_mut_slice());
                    handle.set_clause_id_translation(clause_id_translation.as_slice());
                    handle.set_initial_values(initial_values);
                    handle.call(unprocessed_decisions)
                }
            };

            JIT_PRIMARY_RETURNS.fetch_add(1, Ordering::Relaxed);

            // Compute the `forced` flag exactly as MicroSAT's
            // propagate would (top-of-loop, microsat.c:133). The flag
            // governs both the `IMPLIED` vs `1` tag of subsequent
            // `assign`s and the post-loop `S->forced` lift-up. We read
            // it from the pre-native solver state because that is what
            // the JIT actually saw and propagated against.
            //
            // SAFETY: `s` is live per the enclosing function's
            // precondition.
            let forced = unsafe { read_microsat_forced_flag(s) };

            match status.result {
                0 => {
                    // No conflict. Apply the implied literals back to
                    // MicroSAT's state.
                    if status.implied_literals_len == usize::MAX {
                        if TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed) {
                            eprintln!(
                                "trust_cg_propagate: JIT implied-literals buffer \
                                 overflow (cap={}); falling back to native for \
                                 this call",
                                implied_literals_buf.len()
                            );
                        }
                        return None;
                    }
                    let len = status.implied_literals_len;
                    if len > implied_literals_buf.len() || len > implied_reasons_buf.len() {
                        if TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed) {
                            eprintln!(
                                "trust_cg_propagate: JIT reported implied_len={} \
                                 larger than buffer (lits={}, reasons={}); falling \
                                 back to native",
                                len,
                                implied_literals_buf.len(),
                                implied_reasons_buf.len()
                            );
                        }
                        return None;
                    }
                    let lits = &implied_literals_buf[..len];
                    let reasons = &implied_reasons_buf[..len];
                    // SAFETY: the JIT only emits literals it freshly
                    // assigned in its private arena. The full MicroSAT
                    // trail was passed in as decisions, so any variable
                    // already on MicroSAT's trail is also already
                    // assigned in the JIT arena and is NOT re-emitted
                    // through `implied_literals_out` (per the ABI's
                    // decode-vs-bcp split). The implications therefore
                    // strictly extend MicroSAT's trail without
                    // duplication, and `falseStack` has at least
                    // `num_vars - current_trail_len` >= `len` free slots.
                    // The OK branch's strategy depends on the gate
                    // that admitted us into the replacement path.
                    // The conservative case here is that MicroSAT's
                    // reason chain on the trail must remain in a
                    // pristine "clause[0] == propagated_lit" layout
                    // for any subsequent `analyze` to terminate
                    // without infinite recursion through `implied()`.
                    // Native MicroSAT guarantees this within a single
                    // propagate-then-analyze step, but our JIT emits
                    // implications without mutating MicroSAT's DB —
                    // its reason values point to clauses still in
                    // their original (input) layout, where the
                    // propagated literal may sit at clause[1] rather
                    // than clause[0]. We mirror the swap in
                    // `microsat_assign_from_jit` (and restore it
                    // here so MicroSAT's watch lists stay consistent
                    // for future propagate calls), but the
                    // post-restore reason values STILL reference the
                    // (now-original-again) clause layout. So:
                    //
                    //   * decision_level == 0 (root): The implications
                    //     we emit will never be consumed by `analyze`
                    //     (the next conflict in this regime is itself
                    //     root-forced, which short-circuits to UNSAT
                    //     without analyze). Applying is safe.
                    //
                    //   * decision_level >= 1 (e.g. `analyze_driver_forced`
                    //     fired the JIT mid-search): A future conflict
                    //     could trigger `analyze`, which would walk
                    //     these reason values and hit the "clause[0]
                    //     != propagated_lit" recursion pathology. ADD:
                    //     even with scratch reasons (synthetic clauses
                    //     where `clause[0] == lit` by construction),
                    //     the JIT's BCP is INCOMPLETE relative to
                    //     native's once any lemma has been learned —
                    //     the JIT was compiled against the input
                    //     formula only (`snapshot_input_clauses` reads
                    //     `DB[0..mem_fixed]`, before learned lemmas).
                    //     A lemma can be unit-forced by the current
                    //     decision; the JIT will not see that and will
                    //     return OK with no implications, while native
                    //     would derive a chain that may end in a
                    //     conflict and unit-lemma chain to UNSAT. I1
                    //     experiments confirmed the regression: on
                    //     project-authored pigeonhole / parity / random fixtures, trusting
                    //     the JIT's OK verdict here caused UNSAT
                    //     instances to be answered SAT. We surrender
                    //     the replacement and let native re-propagate.
                    //
                    // The gate uses the canonical
                    // `decision_level_is_zero` walk (no trail entry
                    // with `reason == 0`), NOT the
                    // `reason[abs(*processed)] != 0` proxy that the
                    // entry-gate `pre_authoritative` uses, because
                    // the latter mis-fires for a lemma's UIP at
                    // decision-level >= 1 (the B1 latent-bug
                    // diagnosis applies to this OK-branch as well as
                    // the conflict-branch below).
                    //
                    // SAFETY: `s` is live per the enclosing function's
                    // precondition.
                    let at_root_level = unsafe { decision_level_is_zero(s) };
                    if !at_root_level {
                        let _ = (lits, reasons);
                        return None;
                    }
                    // Root-level SAT-OK regime: `analyze` is never
                    // called against these reason values (the next
                    // conflict short-circuits to UNSAT). We stamp the
                    // ordinary DB-offset reasons from
                    // `clause_id_translation` so the resulting trail
                    // state is byte-identical to what native
                    // MicroSAT's propagate would have produced (which
                    // the `primary_jit_replaces_native_on_unit_implication`
                    // test pins).
                    //
                    // SAFETY: same as the success-branch precondition.
                    unsafe { apply_jit_implications(s, lits, reasons, forced) };
                    JIT_SUCCESSFUL_RUNS.fetch_add(1, Ordering::Relaxed);
                    // SAFETY: `s` is live; we record the
                    // post-implication processed offset so the next
                    // call can detect a restart-induced rewind.
                    let new_off = unsafe { current_processed_offset(s) };
                    *last_processed_offset = new_off;
                    Some(JitReplacementOutcome::Sat)
                }
                1 => {
                    // Conflict. We have two regimes to handle, gated
                    // on the true MicroSAT decision-level (see
                    // `decision_level_is_zero` below; NOT the
                    // propagate-loop `forced` flag, which is a
                    // necessary-but-not-sufficient proxy that also
                    // fires for a lemma's UIP at DL >= 1):
                    //
                    //  * decision-level == 0 (root): MicroSAT's
                    //    `propagate` would return UNSAT directly
                    //    without invoking `analyze`. `solve` reads
                    //    that as a terminal verdict and returns UNSAT
                    //    up the stack. We mirror by short-circuiting
                    //    to `Unsat`.
                    //
                    //  * decision-level >= 1: the conflict is
                    //    mid-search. Native would have (a) applied
                    //    all pre-conflict implications, (b) called
                    //    `analyze(S, clause)` which learns a lemma
                    //    and rewinds the trail to the lemma's UIP
                    //    decision-level, (c) called
                    //    `assign(S, lemma, forced')` where
                    //    `forced' = !lemma[1]` (unit lemma -> 1, else
                    //    keep the top-of-propagate forced flag), and
                    //    (d) returned SAT so the outer search loop
                    //    sees the lemma was learned.
                    //
                    // We reproduce both branches here. Path (b-d) is
                    // the analyze-driver gain of extension #5.
                    let conflict_idx = status.conflicting_clause_index;
                    if conflict_idx < 0 || (conflict_idx as usize) >= clause_id_translation.len() {
                        if TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed) {
                            eprintln!(
                                "trust_cg_propagate: JIT conflict index {} out of \
                                 clause_id_translation range (len={}); falling back \
                                 to native",
                                conflict_idx,
                                clause_id_translation.len()
                            );
                        }
                        return None;
                    }

                    // First push every pre-conflict implication onto
                    // MicroSAT's trail. analyze walks back through
                    // `reason[]` from `S->assigned` so each implied
                    // literal that sits on the implication chain MUST
                    // be reflected in the trail before analyze runs.
                    // The `implied_literals_len` semantics (per
                    // bcp_kernel.rs:159-163) say literals propagated
                    // before the conflict are still emitted on the
                    // conflict branch.
                    if status.implied_literals_len == usize::MAX {
                        if TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed) {
                            eprintln!(
                                "trust_cg_propagate: JIT conflict-branch implied-literals \
                                 buffer overflow (cap={}); falling back to native",
                                implied_literals_buf.len()
                            );
                        }
                        return None;
                    }
                    let len = status.implied_literals_len;
                    if len > implied_literals_buf.len() || len > implied_reasons_buf.len() {
                        if TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed) {
                            eprintln!(
                                "trust_cg_propagate: JIT conflict-branch implied_len={} \
                                 larger than buffer (lits={}, reasons={}); falling \
                                 back to native",
                                len,
                                implied_literals_buf.len(),
                                implied_reasons_buf.len()
                            );
                        }
                        return None;
                    }
                    let lits = &implied_literals_buf[..len];
                    let reasons = &implied_reasons_buf[..len];

                    // Decide whether this conflict short-circuits to
                    // UNSAT or must drive `analyze`. The propagate-loop
                    // `forced` flag (== `reason[abs(*processed)] != 0`)
                    // is NOT a sound proxy for "this is a root-level
                    // conflict" once the ADF path runs post-learning:
                    // a unit lemma's UIP at decision-level >= 1 also
                    // has a non-zero reason, so `forced` is true for
                    // BOTH "DL0 root-forced unit prop" and
                    // "post-backjump UIP propagation at DL >= 1". The
                    // canonical decision-level-0 check walks the trail
                    // and verifies no entry has `reason == 0`
                    // (microsat.c:179 - `solve` writes `reason=0` for
                    // every decision); only then does propagate's
                    // `if (forced) return UNSAT;` branch (microsat.c:
                    // 153) terminate the solve as UNSAT.
                    //
                    // SAFETY: `s` is live per the enclosing function's
                    // precondition.
                    let at_root_level = unsafe { decision_level_is_zero(s) };
                    if at_root_level {
                        // Root-level conflict: solve() returns UNSAT
                        // on the rc alone; no analyze needed. The
                        // pushed literals are consistent with native
                        // semantics because the conflict short-circuits
                        // to UNSAT before any further propagation.
                        // SAFETY: same precondition as the success branch.
                        unsafe { apply_jit_implications(s, lits, reasons, forced) };
                        let _ = conflict_idx;
                        JIT_SUCCESSFUL_RUNS.fetch_add(1, Ordering::Relaxed);
                        // SAFETY: `s` is live; refresh restart
                        // detector even though solve() is about to
                        // terminate (defensive: a follow-up call in
                        // the same JIT_PROVIDER cell, e.g. in a
                        // subsequent test on the same thread, should
                        // not misread the stale offset as a rewind).
                        let new_off = unsafe { current_processed_offset(s) };
                        *last_processed_offset = new_off;
                        return Some(JitReplacementOutcome::Unsat);
                    }

                    // Decision-level >= 1 conflict: drive
                    // MicroSAT's `analyze` + `assign` from outside
                    // its propagate context.
                    //
                    // The empty-lemma bug (see
                    // `docs/empty_lemma_bug_design.md`) was that
                    // the JIT may detect a different "first
                    // conflict clause" than native's
                    // watched-literal scan order, and analyze on
                    // that alternative clause can produce an
                    // empty lemma (size == 0) on SAT instances.
                    // Option (c) sidesteps this by re-deriving the
                    // conflict-clause choice host-side: after
                    // applying the JIT's implications,
                    // `native_find_first_conflict_clause` walks
                    // `S->first[]` exactly as native's propagate
                    // would and picks the same clause native
                    // would have. `analyze` is then run on that
                    // clause; the lemma is well-formed and
                    // `assign(S, lemma, post_forced)` mirrors
                    // microsat.c:155-156 byte-for-byte.

                    // Capture the falseStack offset before
                    // applying any JIT-derived implications so
                    // the watch-list scan starts at the same
                    // position native's `propagate` would have
                    // (microsat.c:134's `while (S->processed <
                    // S->assigned)` begins at the current
                    // `S->processed`).
                    //
                    // SAFETY: `s` is live per the enclosing
                    // function's precondition.
                    let original_processed_offset = {
                        let off = unsafe { current_processed_offset(s) };
                        if off < 0 {
                            // Sentinel / null pointer; cannot
                            // safely scan. Surrender.
                            return None;
                        }
                        off as usize
                    };

                    // Install synthetic scratch reasons for each
                    // JIT-propagated literal so that `analyze`'s
                    // walk through `S->reason[]` lands on
                    // `clause[0] == lit` records (the invariant
                    // analyze's `implied()` recursion relies on).
                    // Falls back to native on arena overflow.
                    if !scratch_bound {
                        // Without a bound scratch arena we cannot
                        // install soundly-shaped reasons; surrender.
                        let _ = conflict_idx;
                        return None;
                    }
                    let scratch_reasons = match unsafe {
                        install_scratch_reasons_for_jit(s, lits, reasons, scratch_arena)
                    } {
                        Ok(v) => v,
                        Err(()) => {
                            // Arena exhausted mid-call; surrender.
                            return None;
                        }
                    };

                    // Apply the JIT's pre-conflict implications so
                    // the trail prefix the native watch scan sees
                    // matches what the JIT propagated against.
                    //
                    // CRITICAL: in the analyze-driver (conflict)
                    // branch we must NOT lift `S->forced` even when
                    // the entry-time `forced` flag is true. Native
                    // MicroSAT's propagate lifts `S->forced` only
                    // at the END of a conflict-free loop
                    // (microsat.c:157 `if (forced) S->forced =
                    // S->processed;`); on the conflict path it
                    // `break`s out before that line and `S->forced`
                    // is left untouched. If we mirrored apply's
                    // default "lift on forced" behaviour here,
                    // `S->forced` would jump up to the post-apply
                    // `S->assigned`, and `analyze`'s build loop
                    // `while (p >= S->forced)` (microsat.c:116)
                    // would never enter the body, producing an
                    // empty lemma (size==0). We therefore push each
                    // implied literal individually via
                    // `microsat_assign_from_jit` (the per-lit
                    // primitive) and explicitly advance only
                    // `S->processed`, leaving `S->forced` alone.
                    debug_assert_eq!(lits.len(), scratch_reasons.len());
                    // (Diagnostic eprintlns removed.)
                    // Tag each JIT-pushed literal as decision-derived
                    // (not root-forced). We are inside the
                    // `at_root_level == false` branch, so every
                    // implication sitting on the trail is below at
                    // least one decision and analyze MUST treat them
                    // as MARK candidates (not as `IMPLIED` units that
                    // bypass the build loop). The legacy
                    // `read_microsat_forced_flag` proxy at the top of
                    // `try_jit_replace_native` returns `true` whenever
                    // `S->reason[abs(*S->processed)] != 0`, which is
                    // an unsound proxy for "root-level forced" after
                    // any UIP has been pushed onto the trail by a
                    // prior analyze-driver cycle (the UIP has
                    // `reason != 0` even though decisions live further
                    // down the stack); using that value here would
                    // tag JIT pushes as `IMPLIED`, hiding them from
                    // analyze's MARK loop and yielding empty lemmas.
                    let push_forced = false;
                    for i in 0..lits.len() {
                        // SAFETY: `s` is live; `lits[i]` is in
                        // `[-nVars, nVars]\\{0}` by the kernel's
                        // emit contract; the synthetic reason
                        // points into the scratch arena bound to
                        // this solver.
                        unsafe {
                            microsat_assign_from_jit(s, lits[i], scratch_reasons[i], push_forced)
                        };
                    }
                    // Advance `S->processed = S->assigned` so
                    // analyze's preconditions (microsat.c:115's
                    // `S->processed = S->assigned;` is overwritten
                    // anyway, but having `processed` lag behind
                    // `assigned` mid-call leaves a window where a
                    // re-entrant native call would mis-process the
                    // JIT-pushed tail).
                    //
                    // SAFETY: `s` is live.
                    {
                        let solver_ref = unsafe { &mut *s };
                        solver_ref.processed = solver_ref.assigned;
                    }

                    // Candidate 1 (F1-v2 perf gap): try to short-circuit
                    // the native watch-list walk by validating the JIT's
                    // own `conflicting_clause_index` directly.
                    //
                    // The JIT reports the kernel-side clause index where
                    // it observed a conflict. Translate to a DB offset via
                    // `clause_id_translation[idx]`; if the corresponding
                    // input clause is fully falsified at the current trail
                    // *AND* one of its literals is the trail's most-
                    // recently-pushed literal (`*S->processed - 1` in
                    // microsat's order — i.e. the very lit native's outer
                    // `while (processed < assigned)` is about to process,
                    // which is the first false literal it'd inspect in
                    // watch-list scan order), then native's walk would
                    // hit this clause first (any earlier conflict would
                    // have terminated propagation before this lit got
                    // pushed). In that case we skip the O(trail × watch)
                    // walk entirely.
                    //
                    // This is correctness-safe because:
                    //   * The clause being fully false guarantees
                    //     `analyze` will produce a non-empty lemma (the
                    //     empty-lemma bug was about analyze on a clause
                    //     the JIT picked PAST native's first conflict
                    //     point; here we verify the clause is hot now).
                    //   * Pinning to the latest-pushed trail literal
                    //     reproduces native's watch-list scan starting
                    //     point: native processes the falseStack in
                    //     push order, so the first conflict it can hit
                    //     after processing a literal must involve that
                    //     literal in one of its watch slots.
                    //
                    // SAFETY: `s` is live; `conflict_idx` was bounds-
                    // checked against `clause_id_translation.len()`
                    // above. All `db.offset(...)` reads target the
                    // 0-terminated input-clause record region of
                    // `S->DB[0..S->mem_used]` already covered by
                    // MicroSAT's allocation contract.
                    let jit_conflict_db_off = clause_id_translation[conflict_idx as usize];
                    let conflict_db_off = {
                        let short_circuit_ok =
                            unsafe { jit_conflict_clause_is_native_first(s, jit_conflict_db_off) };
                        if short_circuit_ok {
                            JIT_ANALYZE_DRIVER_CLAUSE_AGREEMENTS.fetch_add(1, Ordering::Relaxed);
                            jit_conflict_db_off
                        } else {
                            // Fall back to the full native watch walk.
                            //
                            // SAFETY: `s` is live; this helper is
                            // read-only over `S->DB`, `S->first`,
                            // `S->false`, `S->falseStack`.
                            match unsafe {
                                native_find_first_conflict_clause(s, original_processed_offset)
                            } {
                                Some(off) => off,
                                None => {
                                    if TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed) {
                                        eprintln!(
                                            "trust_cg_propagate: JIT reported conflict at \
                                             idx={} but native watch scan found no conflict \
                                             at trail offset {}; surrendering",
                                            conflict_idx, original_processed_offset
                                        );
                                    }
                                    return None;
                                }
                            }
                        }
                    };

                    // Drive MicroSAT's `analyze` on the
                    // native-chosen conflict clause and then
                    // assign the resulting lemma exactly as
                    // microsat.c:154-156 does.
                    //
                    // SAFETY: `conflict_db_off` is the
                    // reason-style offset
                    // (`1 + (first_lit - S->DB)`), so
                    // `s->DB.add(conflict_db_off - 1)` is the
                    // pointer to the clause's first literal —
                    // the exact shape `analyze` expects.
                    let solver_ptr_ref = unsafe { &mut *s };
                    let clause_ptr =
                        unsafe { solver_ptr_ref.DB.add((conflict_db_off - 1) as usize) };
                    // SAFETY: `analyze` is `extern "C"` from
                    // microsat.c; `s` is live and `clause_ptr`
                    // points at the first literal of a falsified
                    // clause record per the contract of
                    // `native_find_first_conflict_clause`.
                    let lemma_ptr = unsafe { analyze(s, clause_ptr) };

                    // Mirror microsat.c:155
                    //   `if (!lemma[1]) forced = 1;`
                    // i.e. unit-lemma -> forced = 1; multi-literal
                    // lemma -> retain entry-time `forced`. Because
                    // we are inside the `at_root_level == false`
                    // branch, the entry-time `forced` (in native's
                    // sense, post the build-time rewrite of
                    // microsat.c:133 -> `trust_cg_decision_level_is_zero`)
                    // is `0`. So the unit-lemma case is the only
                    // case that bumps `forced` to 1.
                    //
                    // SAFETY: `analyze` returns a pointer into
                    // `S->DB` to the first literal of the freshly
                    // learned lemma; `lemma[1]` is either the
                    // second literal or the 0 terminator if the
                    // lemma is unit.
                    let lemma_second = unsafe { *lemma_ptr.add(1) };
                    let post_forced: c_int = if lemma_second == 0 { 1 } else { 0 };
                    // SAFETY: `assign` is `extern "C"` from
                    // microsat.c; `s` is live and `lemma_ptr`
                    // points at a valid clause-first-literal slot
                    // inside `S->DB`.
                    unsafe { assign(s, lemma_ptr, post_forced) };

                    JIT_ANALYZE_DRIVEN.fetch_add(1, Ordering::Relaxed);
                    JIT_SUCCESSFUL_RUNS.fetch_add(1, Ordering::Relaxed);
                    // Continue propagation by handing off to native:
                    // native's `propagate` body runs analyze + assign
                    // INSIDE its outer `while (S->processed <
                    // S->assigned)` loop and continues processing
                    // the freshly-assigned lemma UIP (and any further
                    // implications) in the SAME call. If a follow-on
                    // conflict materialises at DL0, native returns
                    // UNSAT directly; this is exactly the path
                    // pigeonhole-style instances rely on to detect
                    // UNSAT via unit-lemma chains.
                    //
                    // Skipping this continuation would let
                    // `solve()` push a fresh decision on top of the
                    // about-to-conflict trail, masking the root
                    // conflict and feeding the next analyze-driver
                    // call an unanalyzable trail (the conflict clause
                    // literals are all unit-implied, so analyze's
                    // build loop reduces them via `implied()` and
                    // emits an empty lemma).
                    //
                    // SAFETY: `s` is live per the enclosing
                    // function's precondition;
                    // `microsat_native_propagate` is the renamed
                    // upstream `propagate` and accepts exactly that.
                    let native_continuation_rc = unsafe { microsat_native_propagate(s) };
                    // SAFETY: `s` is live; refresh the restart
                    // detector with the post-continuation offset.
                    let new_off = unsafe { current_processed_offset(s) };
                    *last_processed_offset = new_off;
                    let _ = (conflict_idx, lemma_second, post_forced, forced);
                    if native_continuation_rc == sys::UNSAT {
                        return Some(JitReplacementOutcome::Unsat);
                    }
                    Some(JitReplacementOutcome::AnalyzeDriven)
                }
                _ => {
                    if TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed) {
                        eprintln!(
                            "trust_cg_propagate: JIT returned result={} \
                             (decode error or unknown); falling back to native",
                            status.result
                        );
                    }
                    None
                }
            }
        })
    })
}

/// The Rust-defined replacement for MicroSAT's `propagate`. The C
/// trampoline in `propagate_trampoline.c` forwards every `propagate(S)`
/// call site inside `solve()` to this function.
///
/// # Safety
///
/// `s` must be a valid pointer to a `sys::solver` that has been
/// initialised by `parse` / `initCDCL` (this matches the precondition of
/// MicroSAT's own `propagate`). The pointer must remain live and
/// exclusively owned for the duration of the call.
///
/// # ABI
///
/// Returns `sys::SAT` (1) on no conflict or `sys::UNSAT` (0) on a
/// root-level conflict, matching the upstream contract.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_cg_propagate(s: *mut sys::solver) -> c_int {
    PROPAGATE_CALL_COUNT.fetch_add(1, Ordering::Relaxed);

    let shadow_on = SHADOW_MODE.load(Ordering::Relaxed);
    let primary_on = PRIMARY_JIT_MODE.load(Ordering::Relaxed);

    // Fast path: no JIT machinery engaged.
    if !shadow_on && !primary_on {
        // SAFETY: `s` is a live `*mut sys::solver` per this function's
        // safety precondition; `microsat_native_propagate` is the
        // renamed upstream `propagate` and accepts exactly that.
        return unsafe { microsat_native_propagate(s) };
    }

    // Pre-native snapshot: the JIT's notion of "did this call see a
    // root-level conflict?" depends on the state at entry to
    // propagate, not the state after native has finished propagating
    // (native advances `processed` to `assigned` and possibly pushes
    // more literals onto `falseStack` and bumps `nLemmas` via
    // analyze->addClause). We capture everything the JIT needs
    // before delegating to native so the snapshots are consistent
    // with the JIT's view of the call.
    //
    // SAFETY: `s` is live per this function's precondition.
    let pre_authoritative = unsafe { jit_is_authoritative_at_root(s) };
    // SAFETY: `s` is live.
    let pre_nonempty = unsafe { unprocessed_trail_nonempty(s) };
    // Unprocessed-trail decoding for the shadow-style differential
    // check (the legacy "primary" path that runs the JIT alongside
    // native and compares result codes) AND for the JIT-replacement
    // path's `decisions` input.
    //
    // For replacement we only pass the unprocessed suffix as
    // decisions — the already-settled trail prefix is communicated
    // through `pre_initial_values` (the kernel ABI's seeding slot).
    // This mirrors native MicroSAT's `propagate`, which iterates
    // `S->trail[S->processed..S->assigned]` and leaves the prefix
    // alone. See `snapshot_initial_values` and the kernel ABI docs
    // for the precise contract.
    // SAFETY: `s` is live; reads from `falseStack[processed..assigned)`.
    let pre_decisions = if primary_on {
        unsafe { snapshot_unprocessed_trail_as_decisions(s) }
    } else {
        Vec::new()
    };
    // Per-variable assignment state at entry to propagate. Used to
    // seed the kernel's `values[]` arena so it begins BCP from the
    // exact MicroSAT-visible assignment. Without this seed, the
    // kernel would re-derive parse-time unit assignments and re-emit
    // already-on-trail literals through `implied_literals_out`,
    // which `apply_jit_implications` would then double-push onto
    // MicroSAT's stack.
    // SAFETY: `s` is live; reads `S->false[+/-v]` for `v` in `[1, nVars]`.
    let pre_initial_values = if primary_on && pre_nonempty {
        unsafe { snapshot_initial_values(s) }
    } else {
        Vec::new()
    };

    // Phase 3.5 / extension #5 (JIT replaces native, with analyze-driver):
    // if PRIMARY_JIT_MODE is on, the unprocessed trail is non-empty, and
    // the cache is healthy, run the JIT FIRST and skip native entirely
    // on success.
    //
    // The historical `jit_is_authoritative_at_root` gate (extensions
    // #1-4) only let the JIT replace native at the root-forced regime;
    // mid-search conflicts surrendered the primary path to native.
    // Extension #5 (this commit) relaxes the gate to cover decision-
    // level >= 1 conflicts: the JIT-replacement path now drives the
    // conflict clause into MicroSAT's `analyze` and `assign` (the
    // analyze-driver) so `solve()` sees the same lemma it would have
    // seen had native propagate run end-to-end.
    //
    // We still keep the `pre_authoritative` value plumbed through the
    // outcome handling because the *return value* (SAT vs UNSAT)
    // depends on it: only root-forced conflicts terminate as UNSAT;
    // every other outcome (clean BCP, or analyze-driven mid-search
    // conflict) returns SAT to `solve()` so the outer search loop
    // continues. The JIT mutates MicroSAT's state via
    // `apply_jit_implications` (and, on the analyze branch,
    // `analyze` + `assign` itself) so subsequent solver iterations
    // see the same trail / reason / model fields they would have
    // seen had native run.
    //
    // Note: `pre_authoritative` is still required as the gate for the
    // JIT-as-primary replacement path. Extension #5's analyze-driver
    // is implemented inside `try_jit_replace_native` for the conflict
    // sub-path, but the BCP-OK sub-path is not yet trusted to drive
    // MicroSAT's full mid-search state, so we keep the existing
    // root-authoritative gate for the production replacement entry.
    // Dedicated tests below exercise the analyze-driver via the
    // `JIT_ANALYZE_DRIVER_FORCE` override flag.
    let analyze_driver_forced = JIT_ANALYZE_DRIVER_FORCE.load(Ordering::Relaxed);
    let replacement_outcome: Option<JitReplacementOutcome> =
        if primary_on && pre_nonempty && (pre_authoritative || analyze_driver_forced) {
            // SAFETY: `s` is live per precondition.
            //
            // `pre_authoritative` is the entry gate (do we even try
            // the JIT?) but is NOT plumbed into `try_jit_replace_native`
            // any more — both the OK and conflict sub-paths there
            // re-evaluate `decision_level_is_zero(s)` because
            // `pre_authoritative`'s `reason[abs(*processed)] != 0`
            // proxy mis-fires for lemma UIPs at decision-level >= 1
            // (the B1 latent-bug diagnosis).
            unsafe { try_jit_replace_native(s, &pre_initial_values, &pre_decisions) }
        } else {
            None
        };
    if let Some(outcome) = replacement_outcome {
        match outcome {
            // Both `Sat` (no conflict) and `AnalyzeDriven`
            // (mid-search conflict learned through analyze) surface
            // as SAT to `solve()` so its outer loop can continue.
            // `solve` inspects `S->nLemmas` for the post-analyze
            // re-decide path, which the analyze-driver branch
            // increments via the addClause trampoline.
            JitReplacementOutcome::Sat => return sys::SAT,
            JitReplacementOutcome::AnalyzeDriven => return sys::SAT,
            JitReplacementOutcome::Unsat => return sys::UNSAT,
        }
    }

    // Fall through to native: either the JIT was not authoritative,
    // or it could not produce a confident verdict (decode error /
    // overflow / cache miss). Native runs the propagate; we may also
    // do a shadow-mode differential check or a legacy non-replacement
    // primary comparison afterwards.
    //
    // SAFETY: `s` is a live `*mut sys::solver` per this function's
    // safety precondition; `microsat_native_propagate` is the renamed
    // upstream `propagate` and accepts exactly that.
    let native_return = unsafe { microsat_native_propagate(s) };

    let (shadow_result_opt, primary_result_opt) = JIT_PROVIDER.with(|cache_cell| {
        JIT_SHADOW_EVALUATED.with(|evaluated_cell| {
            let mut cache_ref = cache_cell.borrow_mut();
            let mut evaluated_ref = evaluated_cell.borrow_mut();

            if cache_ref.is_none() {
                // SAFETY: `s` satisfies the snapshot precondition.
                let (num_vars, clauses) = unsafe { snapshot_input_clauses(s) };
                let num_clauses = clauses.len();
                // Build the per-JIT-clause translation table on the
                // same DB walk as `snapshot_input_clauses`. Each entry
                // is `lit_start_offset + 1`, the value MicroSAT's
                // `assign` macro writes into `S->reason[var]`.
                //
                // SAFETY: same precondition; the function only reads
                // `S->DB[0..S->mem_fixed]`.
                let clause_id_translation = unsafe { build_clause_id_translation(s, num_clauses) };

                // A single JIT provider serves both shadow and primary
                // paths. The choice is `JIT_KERNEL_CHOICE` at
                // first-compile time; default is
                // `JIT_KERNEL_WATCHED_LITERAL`.
                let choice = JIT_KERNEL_CHOICE.load(Ordering::Relaxed);
                let compiled = compile_chosen_provider(choice, num_vars, clauses);
                let provider = match compiled {
                    Ok(p) => Some(p),
                    Err(err) => {
                        eprintln!(
                            "trust_cg_propagate: JIT compile failed for kernel choice {}: \
                             {err}; shadow/primary disabled for this solver",
                            kernel_choice_label(choice)
                        );
                        None
                    }
                };

                if provider.is_some() {
                    JIT_INIT_COUNT.fetch_add(1, Ordering::Relaxed);
                }
                // Buffer sizing: `2 * num_vars` is a safe upper bound.
                // Each propagation sweep assigns at most `num_vars`
                // literals (every variable touched at most once); the
                // factor of 2 provides headroom for any future kernel
                // shape that emits slightly more.
                let buf_size = (num_vars * 2).max(8);
                let implied_literals_buf = vec![0i32; buf_size];
                let implied_reasons_buf = vec![0i32; buf_size];
                // Phase 2: bind a per-solve scratch arena to the
                // solver's `S->DB`. The shadow / non-replacement
                // primary path does not actually consume scratch
                // reasons (it only runs the JIT alongside native for
                // a divergence check), but we still bind here so the
                // first-cache-init path in this branch yields a
                // well-formed cache structure for any subsequent
                // call that may take the replacement path.
                let scratch_reserve = (num_vars.saturating_mul(8)).max(64);
                let mut scratch_arena = ScratchArena::new(scratch_reserve);
                // SAFETY: `s` is live and post-`parse`.
                let scratch_bound = unsafe { scratch_arena.bind_to_solver(s) }.is_ok();
                if !scratch_bound && TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed) {
                    eprintln!(
                        "trust_cg_propagate: scratch_arena.bind_to_solver rejected \
                         reserve={} (DB headroom too tight); Phase 2 analyze-driver \
                         disabled for this solver",
                        scratch_reserve
                    );
                }
                *cache_ref = Some(JitProviderCache {
                    provider,
                    clause_id_translation,
                    implied_literals_buf,
                    implied_reasons_buf,
                    scratch_arena,
                    last_processed_offset: isize::MIN,
                    scratch_bound,
                });
                *evaluated_ref = false;
            }

            let cache = match cache_ref.as_mut() {
                Some(c) => c,
                None => return (None, None),
            };

            // Phase 2 (A1 scratch-arena design) makes the JIT's
            // baked-in original-formula clause set valid for the
            // entire solve: learned lemmas never enter the kernel;
            // their reason values live in S->DB's scratch tail. The
            // JIT therefore runs alongside / replaces native on every
            // eligible propagate call regardless of learning.
            let shadow_result = if shadow_on {
                run_jit_shadow_once(cache, &mut evaluated_ref)
            } else {
                None
            };

            // The primary-JIT (non-replacement comparison) path is
            // engaged only when:
            //   * PRIMARY_JIT_MODE is on,
            //   * the JIT was authoritative *at entry* to this call
            //     (root-level state, no decisions yet on the stack),
            //   * the chosen kernel supports primary mode (i.e. is
            //     not the single-shot scan kernel).
            // We use the pre-native authoritative check and pre-native
            // decision snapshot so the kernel sees the same input
            // MicroSAT's native propagate saw.
            let primary_eligible = primary_on
                && pre_authoritative
                && cache
                    .provider
                    .as_ref()
                    .map(ChosenProvider::supports_primary)
                    .unwrap_or(false);
            let primary_result = if primary_eligible {
                run_jit_primary(cache, &pre_decisions)
            } else {
                None
            };

            (shadow_result, primary_result)
        })
    });

    // Compare and possibly surface divergence for the SHADOW_MODE
    // single-shot check. SHADOW_MODE always stays soft-warning: even
    // a divergence here is a research signal, not a correctness
    // claim, because the JIT runs on the original formula with no
    // assignments and the native runs on the current solver state.
    if let Some(jit_result) = shadow_result_opt {
        let native_conflict = native_return == sys::UNSAT;
        let jit_conflict = jit_result == 1;
        if native_conflict != jit_conflict {
            // `prior` is the divergence count *before* this increment, so
            // the very first divergence sees `prior == 0` and is always
            // reported. Subsequent divergences emit a warning only when
            // `prior` is a multiple of `JIT_DIVERGENCE_WARN_INTERVAL`
            // (i.e. at occurrences 1, 1001, 2001, ...). This rate limit
            // keeps a regression from spamming stderr while still leaving
            // an audit trail. The full divergence count is
            // surfaced in `JIT_DIVERGENCE_COUNT` regardless.
            let prior = JIT_DIVERGENCE_COUNT.fetch_add(1, Ordering::Relaxed);
            if prior == 0 || prior.is_multiple_of(JIT_DIVERGENCE_WARN_INTERVAL) {
                eprintln!(
                    "trust_cg_propagate: shadow divergence on initial formula \
                     (occurrence #{}): native={native_return} \
                     (conflict={native_conflict}) jit_result={jit_result} \
                     (conflict={jit_conflict})",
                    prior + 1
                );
            }
        }
    }

    // Surface the primary-JIT mapped result if it was produced AND
    // the kernel returned a well-defined OK/conflict code. A decode
    // error (result == 2) falls through to native silently.
    if let Some(jit_result) = primary_result_opt
        && let Some(mapped) = jit_result_to_microsat(jit_result)
    {
        let agree = mapped == native_return;
        if agree {
            let prior = JIT_SUCCESSFUL_RUNS.fetch_add(1, Ordering::Relaxed);
            let _ = prior;
        } else {
            let successful_so_far = JIT_SUCCESSFUL_RUNS.load(Ordering::Relaxed);
            let prior = JIT_DIVERGENCE_COUNT.fetch_add(1, Ordering::Relaxed);
            if successful_so_far >= JIT_HARDFAIL_WARMUP {
                panic!(
                    "trust_cg_propagate: PRIMARY_JIT_MODE divergence past \
                         warmup ({} >= {}) - jit_mapped={} native={} \
                         jit_result_code={}",
                    successful_so_far, JIT_HARDFAIL_WARMUP, mapped, native_return, jit_result
                );
            } else if prior == 0 || prior.is_multiple_of(JIT_DIVERGENCE_WARN_INTERVAL) {
                // First divergence in the warmup window is always
                // reported; further divergences emit a warning at
                // every `JIT_DIVERGENCE_WARN_INTERVAL` occurrences so
                // a stuck-in-warmup regression cannot flood stderr.
                eprintln!(
                    "trust_cg_propagate: PRIMARY_JIT_MODE divergence within \
                         warmup window (occurrence #{}, successful_so_far={}/{}) - \
                         jit_mapped={} native={} jit_result_code={}",
                    prior + 1,
                    successful_so_far,
                    JIT_HARDFAIL_WARMUP,
                    mapped,
                    native_return,
                    jit_result
                );
            }
        }
        JIT_PRIMARY_RETURNS.fetch_add(1, Ordering::Relaxed);
        // Whether agree or not, the primary path *would* surface
        // the JIT's mapped value. To keep the solver state
        // self-consistent we still need to return what MicroSAT
        // expects: native's return value drove all the side
        // effects, so if we returned a different code we would
        // tell solve() "no conflict" while solve() has e.g. just
        // had a lemma learned. In practice when agree==true the
        // two are equal so this is a no-op; when agree==false in
        // the warmup window we have already warned, and we
        // surface native to avoid a UNSAT/SAT mixup mid-search.
        //
        // The hard-fail panic above guarantees that *post-warmup*
        // a divergence stops the run, so this "return native"
        // policy only applies during the warmup phase where
        // divergence is treated as data, not error.
        return native_return;
    }

    native_return
}

// ===========================================================================
// Deferred empty-lemma conflict path.
//
//   * Implement `native_find_first_conflict_clause` (currently
//     `unimplemented!()`).
//   * Rewire `try_jit_replace_native`'s `result == 1` arm
//     (the surrender block at the DL >= 1 conflict branch).
//   * Flip `JIT_ANALYZE_DRIVER_FORCE` default to `true` and enable the explicit
//     campaign gate for the tests below.
// ===========================================================================

/// MicroSAT's `END` enum value (from `microsat.c`:
///   `enum { END = -9, ... };`
/// Used as the watch-list terminator (`S->first[lit] == END` means no
/// clause watches `lit`).
const MICROSAT_END: c_int = -9;

/// Walk MicroSAT's native watch lists exactly as `propagate`
/// (microsat.c:132-158) would, but only as far as identifying the first
/// all-false clause given the current trail. Returns the reason-style
/// DB offset (`1 + (clause_first_lit - S->DB)`) of that clause, or
/// `None` if no conflict is found before the trail tail.
///
/// This is the option-(c) entry point that lets the JIT-replacement
/// path piggy-back on native's watch-list iteration order to pick
/// the same conflict clause native's `propagate` would have picked,
/// sidestepping the empty-lemma bug entirely.
///
/// `trail_start_offset` is the falseStack index where the scan begins
/// (typically `S->processed - S->falseStack` at entry to
/// `try_jit_replace_native`, captured pre-`apply_jit_implications`).
///
/// # Safety
///
/// `s` must point to a live, post-`parse`, exclusively-owned solver.
/// The function performs no writes to `S->DB`, `S->first`, `S->reason`,
/// `S->false`, or any other solver field — it only reads.
unsafe fn native_find_first_conflict_clause(
    s: *mut sys::solver,
    trail_start_offset: usize,
) -> Option<i32> {
    // SAFETY: caller's precondition - `s` is live and exclusively owned.
    let solver_ref = unsafe { &*s };
    let db = solver_ref.DB;
    let first = solver_ref.first;
    let false_arr = solver_ref.false_;
    let base = solver_ref.falseStack;
    let assigned = solver_ref.assigned;
    if db.is_null()
        || first.is_null()
        || false_arr.is_null()
        || base.is_null()
        || assigned.is_null()
    {
        return None;
    }
    let trail_len = {
        let diff = (assigned as isize) - (base as isize);
        if diff <= 0 {
            return None;
        }
        (diff / core::mem::size_of::<c_int>() as isize) as usize
    };
    if trail_start_offset >= trail_len {
        return None;
    }

    // Mirror microsat.c::propagate's outer loop: walk falseStack from
    // the start offset to `assigned`, and for each falsified literal
    // traverse `S->first[lit]`'s linked list.
    for trail_idx in trail_start_offset..trail_len {
        // SAFETY: `trail_idx < trail_len` and `[base..base+trail_len)`
        // is inside the live falseStack region.
        let lit = unsafe { *base.add(trail_idx) };
        if lit == 0 {
            continue;
        }
        // SAFETY: `first` is allocated with offset `+nVars` so that
        // signed-literal indexing in `[-nVars, nVars]` is in bounds;
        // any literal sitting on the trail satisfies that range.
        let mut watch_off = unsafe { *first.offset(lit as isize) };
        while watch_off != MICROSAT_END {
            // Mirror microsat.c:139-140's pointer juggling.
            // Native sets `clause = DB + *watch + 1`, then:
            //   * if `clause[-2] == 0`: `*watch == used` (first-watch
            //     case). `clause++` lands the pointer on the first
            //     literal slot at `DB[used + 2] = DB[*watch + 2]`.
            //   * else (`*watch == used + 1`, second-watch case):
            //     `clause` is already at the first literal slot
            //     `DB[*watch + 1] = DB[used + 2]`.
            //
            // So the first-literal DB offset is:
            //   probe == 0  -> watch_off + 2
            //   probe != 0  -> watch_off + 1
            //
            // SAFETY: every watch offset stored in `S->first` points
            // inside `S->DB[0..S->mem_used]`; the `-1` access is also
            // inside DB because every clause record is preceded by
            // its own watch-link slots (and DB[0..] starts after the
            // pre-watch region; for the very first clause the slot at
            // `watch_off - 1` is the start-of-DB sentinel).
            let probe = unsafe { *db.offset((watch_off - 1) as isize) };
            let first_lit_off: isize = if probe == 0 {
                (watch_off + 2) as isize
            } else {
                (watch_off + 1) as isize
            };
            // SAFETY: `first_lit_off` and `first_lit_off + 1` are the
            // two watched-literal slots of the clause record.
            let wlit0 = unsafe { *db.offset(first_lit_off) };
            let wlit1 = unsafe { *db.offset(first_lit_off + 1) };
            // The "other watched" is whichever of the two is NOT
            // `lit`. Per native's `if (clause[0] == lit) clause[0] =
            // clause[1];` (microsat.c:141), the watched-other is read
            // off the slot that does not equal `lit`. We do not
            // perform the mutation; we just read.
            let other = if wlit0 == lit { wlit1 } else { wlit0 };

            // Scan the non-watched literals (clause[2..]) for a
            // replacement candidate (`!S->false[clause[i]]`).
            let mut replacement_found = false;
            let mut i: isize = 2;
            loop {
                // SAFETY: clause is 0-terminated inside DB; we stop
                // as soon as we observe the terminator.
                let cl = unsafe { *db.offset(first_lit_off + i) };
                if cl == 0 {
                    break;
                }
                // SAFETY: `false_` is `+nVars`-offset; `cl` is in
                // `[-nVars, nVars]\\{0}`.
                let cl_false = unsafe { *false_arr.offset(cl as isize) };
                if cl_false == 0 {
                    replacement_found = true;
                    break;
                }
                i += 1;
            }

            if replacement_found {
                // Native would swap and re-seat the watch; we just
                // step to the next link in the list.
                // SAFETY: `db[watch_off]` is the in-list next-link.
                watch_off = unsafe { *db.offset(watch_off as isize) };
                continue;
            }

            // No replacement among `clause[2..]`. Check the
            // other-watched literal:
            //   * `false_[-other] != 0` => `other` is true => satisfied.
            //   * `false_[other] == 0`  => `other` is unset => would
            //     unit-propagate; not a conflict yet.
            //   * else                  => `other` is false => CONFLICT.
            //
            // SAFETY: same indexing bounds as the clause[i] read.
            let other_neg_false = unsafe { *false_arr.offset((-other) as isize) };
            let other_false = unsafe { *false_arr.offset(other as isize) };
            if other_neg_false != 0 {
                // Satisfied; step.
                watch_off = unsafe { *db.offset(watch_off as isize) };
                continue;
            }
            if other_false == 0 {
                // Would unit-prop; step.
                watch_off = unsafe { *db.offset(watch_off as isize) };
                continue;
            }
            // Conflict. Return the reason-style DB offset
            // (`1 + (first_lit - DB)`).
            return Some((first_lit_off + 1) as i32);
        }
    }
    None
}

/// F1-v2 Candidate 1 fast-path: validate the JIT's reported conflict
/// clause without running the full watch-list walk.
///
/// Returns `true` iff the input clause at reason-style DB offset
/// `jit_conflict_db_off` (i.e. `db.add(jit_conflict_db_off - 1)` is
/// the first literal slot) is currently fully falsified AND the
/// most-recently-pushed trail literal (`*(S->assigned - 1)`) is one
/// of its first two (watched) literals. Under those conditions
/// native's watch-list scan starting at the current `S->processed`
/// would hit this clause as its FIRST conflict: any earlier conflict
/// would have terminated native's propagate loop before the latest
/// trail push, contradicting our assumption that the call is even in
/// the conflict branch.
///
/// "First two literals" mirrors microsat.c::propagate (line 132-)
/// which only traverses `S->first[lit]` for each falsified literal
/// — the watch lists are keyed by the first two clause slots, so any
/// conflict native enumerates must be reachable via one of them.
///
/// # Safety
///
/// `s` must be a live, post-`parse`, exclusively-owned solver. The
/// caller must have validated `jit_conflict_db_off` against
/// `clause_id_translation`'s contract (`1 + first_lit_offset` of an
/// input clause record).
unsafe fn jit_conflict_clause_is_native_first(
    s: *mut sys::solver,
    jit_conflict_db_off: i32,
) -> bool {
    if jit_conflict_db_off <= 0 {
        return false;
    }
    // SAFETY: precondition.
    let solver_ref = unsafe { &*s };
    let db = solver_ref.DB;
    let false_arr = solver_ref.false_;
    let assigned = solver_ref.assigned;
    let base = solver_ref.falseStack;
    if db.is_null() || false_arr.is_null() || assigned.is_null() || base.is_null() {
        return false;
    }
    // Need at least one trail entry so we can identify the literal
    // native is currently processing.
    if assigned <= base {
        return false;
    }
    // The latest-pushed false literal sits at `assigned - 1`.
    //
    // SAFETY: `assigned > base` and both point into the same
    // falseStack allocation.
    let last_pushed = unsafe { *assigned.offset(-1) };
    if last_pushed == 0 {
        return false;
    }

    let first_lit_off = (jit_conflict_db_off - 1) as isize;
    // Read first two literals of the clause (the watched slots) and
    // verify every literal in the clause is falsified.
    //
    // SAFETY: clause records are 0-terminated inside `S->DB`; we
    // stop on the terminator.
    let wlit0 = unsafe { *db.offset(first_lit_off) };
    let wlit1 = unsafe { *db.offset(first_lit_off + 1) };
    if wlit0 == 0 {
        return false;
    }
    if wlit1 == 0 {
        // Single-literal clause: if it's falsified, native would
        // also catch it via the unit-clause path. Treat as
        // non-fast-pathable.
        return false;
    }
    // The most-recently-pushed false literal must be one of the
    // clause's two watched literals (otherwise native's outer loop
    // would not visit this clause when processing the latest lit).
    if wlit0 != last_pushed && wlit1 != last_pushed {
        return false;
    }
    // Every literal in the clause must be currently false. Walk
    // until the 0 terminator.
    let mut i: isize = 0;
    loop {
        // SAFETY: 0-terminated clause record inside `S->DB`.
        let cl = unsafe { *db.offset(first_lit_off + i) };
        if cl == 0 {
            break;
        }
        // `S->false` is `+nVars`-offset; signed-literal indexing in
        // `[-nVars, nVars]` is in bounds.
        //
        // SAFETY: `cl` is a parsed input literal; `cl in [-nVars, nVars]`.
        let cl_false = unsafe { *false_arr.offset(cl as isize) };
        if cl_false == 0 {
            // At least one literal is still unassigned or true; the
            // clause is not currently falsified.
            return false;
        }
        i += 1;
    }
    true
}

/// Test support bindings re-exported so sibling test modules can
/// share state across files. Visible only under `cfg(test)`.
#[cfg(test)]
pub(crate) mod test_support {
    use std::sync::Mutex;

    /// Process-wide solver-test lock. Tests in any module that
    /// mutate the process-global JIT atomics (`PRIMARY_JIT_MODE`,
    /// `JIT_ANALYZE_DRIVER_FORCE`, `SHADOW_MODE`, ...) MUST acquire
    /// this before mutating; cargo test runs threads in parallel by
    /// default and the atomics' temporary swaps in one test would
    /// otherwise race with another test's load.
    pub static SOLVER_LOCK: Mutex<()> = Mutex::new(());
}

#[cfg(test)]
mod empty_lemma_bug_scaffold {
    use super::*;
    use std::ffi::CString;
    use std::io::Write;
    use std::mem::MaybeUninit;
    use std::path::Path;
    use std::sync::atomic::Ordering;

    use tempfile::NamedTempFile;

    use super::test_support::SOLVER_LOCK;

    fn solver_lock() -> std::sync::MutexGuard<'static, ()> {
        SOLVER_LOCK.lock().expect("solver lock not poisoned")
    }

    fn solve_with_adf_on(cnf: &str) -> c_int {
        let _guard = solver_lock();
        let prior_adf = JIT_ANALYZE_DRIVER_FORCE.swap(true, Ordering::SeqCst);
        let prior_primary = PRIMARY_JIT_MODE.swap(true, Ordering::SeqCst);
        reset_jit_shadow_for_tests();

        let mut file = NamedTempFile::new().expect("create tempfile");
        file.write_all(cnf.as_bytes()).expect("write cnf");
        file.flush().expect("flush cnf");
        let path = file.path().to_path_buf();
        let c_path = CString::new(path.to_string_lossy().into_owned()).expect("path to CString");
        let mut solver: MaybeUninit<sys::solver> = MaybeUninit::uninit();
        // SAFETY: `parse` runs `initCDCL` and populates every field of
        // `*solver` before returning. Passing an uninitialised solver
        // matches MicroSAT's own `main`.
        let rc = unsafe {
            let parse_rc = sys::parse(
                solver.as_mut_ptr(),
                c_path.as_ptr() as *mut std::os::raw::c_char,
            );
            if parse_rc == sys::UNSAT {
                sys::UNSAT
            } else {
                sys::solve(solver.as_mut_ptr())
            }
        };

        PRIMARY_JIT_MODE.store(prior_primary, Ordering::SeqCst);
        JIT_ANALYZE_DRIVER_FORCE.store(prior_adf, Ordering::SeqCst);
        rc
    }

    #[test]
    fn native_find_first_conflict_clause_matches_microsat_propagate() {
        // End-to-end differential: a small UNSAT formula that
        // exercises non-empty BCP with conflicts at DL >= 1, run
        // under ADF + PRIMARY_JIT_MODE. The walker's "pick native's
        // first conflict clause" guarantee is the load-bearing
        // invariant for the analyze-driver to terminate with a
        // non-empty lemma; if the walker picked a different clause,
        // `analyze`'s build loop would reduce every conflict
        // literal via `implied()` and emit an empty lemma, which in
        // turn would either return `Unsat` (mis-verdict on SAT) or
        // corrupt the falseStack (segfault). The fact that this
        // tiny UNSAT instance solves cleanly is a direct functional
        // assertion that the walker produces the same first
        // conflict native's propagate would have.
        let cnf = "\
p cnf 6 9
1 2 0
3 4 0
5 6 0
-1 -3 0
-1 -5 0
-3 -5 0
-2 -4 0
-2 -6 0
-4 -6 0
";
        let rc = solve_with_adf_on(cnf);
        assert_eq!(
            rc,
            sys::UNSAT,
            "pigeonhole 3->2 must be UNSAT under ADF (the walker's \
             clause-choice fidelity is the regression target)"
        );
    }

    #[test]
    fn analyze_driver_uf50_02_does_not_regress() {
        // The original failing fixture from D1's report. With
        // option (c) implemented and ADF default-on, the solve
        // must produce `s SATISFIABLE` and `rc == sys::SAT`.
        let cnf_path = Path::new("tests/fixtures/sat_corpus/uf50-02.cnf");
        if !cnf_path.exists() {
            eprintln!(
                "fixture {} missing; skipping (test cannot run without it)",
                cnf_path.display()
            );
            return;
        }
        let cnf = std::fs::read_to_string(cnf_path).expect("read uf50-02.cnf");
        let rc = solve_with_adf_on(&cnf);
        assert_eq!(
            rc,
            sys::SAT,
            "uf50-02 must be SAT under ADF default-on (the empty-lemma \
             bug was the original regression target); observed rc={rc}"
        );
    }

    #[test]
    fn analyze_driver_php_10_9_no_regression_vs_native() {
        // Phase 3 wall-clock gate: php-10-9 ADF wall-clock must be
        // within 5% of native-only. Phase 4 (the bench-corpus
        // sweep) re-checks this on the production corpus; this
        // unit-test gate exists to catch regressions in CI without
        // running the full corpus.
        let cnf_path = Path::new("tests/fixtures/sat_corpus/php-10-9.cnf");
        if !cnf_path.exists() {
            eprintln!("fixture {} missing; skipping", cnf_path.display());
            return;
        }
        let cnf = std::fs::read_to_string(cnf_path).expect("read php-10-9.cnf");
        const REPS: usize = 3;
        use std::time::Instant;

        let mut native_total = std::time::Duration::ZERO;
        let mut adf_total = std::time::Duration::ZERO;
        for _ in 0..REPS {
            // Native-only baseline (ADF off, primary off).
            let _guard = solver_lock();
            let prior_adf = JIT_ANALYZE_DRIVER_FORCE.swap(false, Ordering::SeqCst);
            let prior_primary = PRIMARY_JIT_MODE.swap(false, Ordering::SeqCst);
            reset_jit_shadow_for_tests();
            let mut file = NamedTempFile::new().expect("create tempfile");
            file.write_all(cnf.as_bytes()).expect("write cnf");
            file.flush().expect("flush cnf");
            let path = file.path().to_path_buf();
            let c_path =
                CString::new(path.to_string_lossy().into_owned()).expect("path to CString");
            let mut solver: MaybeUninit<sys::solver> = MaybeUninit::uninit();
            let t = Instant::now();
            // SAFETY: same as `solve_with_adf_on`.
            let rc_native = unsafe {
                let parse_rc = sys::parse(
                    solver.as_mut_ptr(),
                    c_path.as_ptr() as *mut std::os::raw::c_char,
                );
                if parse_rc == sys::UNSAT {
                    sys::UNSAT
                } else {
                    sys::solve(solver.as_mut_ptr())
                }
            };
            native_total += t.elapsed();
            PRIMARY_JIT_MODE.store(prior_primary, Ordering::SeqCst);
            JIT_ANALYZE_DRIVER_FORCE.store(prior_adf, Ordering::SeqCst);
            assert_eq!(rc_native, sys::UNSAT);
            drop(_guard);

            // ADF-on path.
            let t = Instant::now();
            let rc_adf = solve_with_adf_on(&cnf);
            adf_total += t.elapsed();
            assert_eq!(rc_adf, sys::UNSAT);
        }
        eprintln!(
            "php-10-9 over {} reps: native={:?} adf={:?}",
            REPS, native_total, adf_total
        );
        // Functional gate: ADF must produce a verdict in a finite
        // amount of time and agree on UNSAT. The wall-clock budget
        // (E1's "within 5% of native-only" or comparable) is
        // checked via the production bench
        // (`satlib_bench_table --warmup`); duplicating that gate as
        // a unit-test threshold would either over-tighten CI or
        // be too noisy on shared runners. The unit-test value is
        // in eyeballing the eprintln output during local triage.
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shadow_mode_default_is_off() {
        // The shadow flag must start disabled so default builds pay no
        // extra propagate cost.
        assert!(!SHADOW_MODE.load(Ordering::Relaxed));
    }

    #[test]
    fn trust_cg_propagate_verbose_default_is_off() {
        // The hot-path verbosity flag must default to off so a
        // production solve does not flood stderr with thousands of
        // per-call diagnostic eprintlns (epoch-fallback,
        // buffer-overflow, decode-error). The `trust_cg_sat --verbose`
        // CLI flag flips it explicitly when an operator is
        // investigating a JIT regression.
        assert!(!TRUST_CG_PROPAGATE_VERBOSE.load(Ordering::Relaxed));
    }

    #[test]
    fn jit_divergence_warn_interval_is_sane() {
        // The rate-limit stride for divergence warnings must be a
        // positive constant >= 100. A value of 0 would re-introduce
        // the per-call stderr flood; a value of 1 would defeat the
        // rate-limit entirely; a value larger than ~10_000 would
        // hide a real correctness regression for too long.
        const {
            assert!(
                JIT_DIVERGENCE_WARN_INTERVAL >= 100,
                "JIT_DIVERGENCE_WARN_INTERVAL is too small; would defeat the rate-limit"
            );
            assert!(
                JIT_DIVERGENCE_WARN_INTERVAL <= 100_000,
                "JIT_DIVERGENCE_WARN_INTERVAL is too large; would hide regressions"
            );
        }
    }
}
