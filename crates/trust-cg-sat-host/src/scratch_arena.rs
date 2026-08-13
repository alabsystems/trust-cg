// trust-cg-sat-host - per-solve scratch arena for JIT-emitted synthetic
// reason clauses.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates - License: Apache-2.0
//
// This module implements the DB-arena split described in
// `docs/db_arena_split_design.md`. It began life as a Phase-1 scaffold
// (type shape + public API with placeholder bodies). Every ScratchArena API
// body in this module is now implemented; there is no live placeholder body
// here. The crate's integration tests exercise arena binding, allocation, and
// solver/JIT interactions.
//
// Design summary (see the design doc for the full rationale):
//
// MicroSAT's `analyze` walks the implication graph via
// `S->reason[var]` and dereferences `S->DB + reason - 1`. The walk
// requires `clause[0] == propagated_literal` for every reason clause.
// Native propagate maintains this via in-place swaps as it advances
// watches; the JIT-replacement path runs on a private arena and
// cannot mutate `S->DB` (the watch lists are rooted there). We work
// around this by allocating synthetic reason clauses inside a
// reserved tail region of `S->DB` itself, between
// `S->mem_max - reserve_words` and `S->mem_max`. Reason values in
// this range are ordinary DB offsets, so `analyze` and `implied`
// dereference them with no source changes; the watch-list invariant
// is preserved because `getMemory` never advances into the reserved
// region.

use core::ffi::c_int;

use crate::sys;

/// Default per-clause overhead in `c_int` units for synthetic reason
/// clauses: one slot for `clause[0]` (the propagated literal), `k`
/// slots for the antecedents, and one slot for the 0 terminator. We
/// pad by 2 ints per clause for safety.
pub const SYNTHETIC_CLAUSE_OVERHEAD: usize = 2;

/// Safety floor: minimum gap (in `c_int` units) between `S->mem_used`
/// and the scratch base. Bind-time check refuses to attach the arena
/// if the live DB is closer than this to the scratch region.
pub const SCRATCH_BIND_MARGIN: usize = 1024;

/// Pre-allocation guard threshold (in `c_int` units): if `S->mem_used`
/// grows to within this many ints of the scratch base mid-solve, the
/// hot path stops calling `allocate_synthetic_clause` and falls back
/// to native for the remainder of the solve.
pub const SCRATCH_NEAR_OVERFLOW_MARGIN: usize = 256;

/// Error returned by [`ScratchArena::allocate_synthetic_clause`] when
/// the requested clause does not fit in the remaining reservation.
/// The JIT-replacement path treats this exactly like an
/// implied-literals buffer overflow: log under
/// `TRUST_CG_PROPAGATE_VERBOSE`, fall back to native propagate for
/// the rest of the solve, increment a telemetry counter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScratchOverflow {
    /// `c_int` slots that were requested by the failed allocation.
    pub requested_words: usize,
    /// `c_int` slots that were available in the arena at the time of
    /// the call.
    pub available_words: usize,
}

/// Per-solve scratch storage for JIT-emitted synthetic reason clauses.
///
/// The arena occupies a reserved tail region of `S->DB`, so any
/// reason value it returns is a valid DB offset (in the high range)
/// that MicroSAT's `analyze` and `implied` walks dereference without
/// modification. The watch-list invariant is preserved because
/// `getMemory` never advances into the reserved region (see the
/// design doc for the full argument).
///
/// # Lifecycle
///
///   1. [`ScratchArena::new`] - construct, with reservation size.
///   2. [`ScratchArena::bind_to_solver`] - capture `S->DB` and choose
///      `scratch_base_offset`. Called once per solve.
///   3. [`ScratchArena::allocate_synthetic_clause`] - bump-allocate a
///      synthetic clause and return its reason value. Called many
///      times per solve, once per JIT-emitted implication.
///   4. [`ScratchArena::reset`] - zero the cursor. Called at restart,
///      reduceDB, and epoch-recompile boundaries.
///   5. [`ScratchArena::lookup_reason`] - diagnostic helper; not on
///      the hot path.
///
/// The arena does **not** own any heap memory of its own - the
/// backing storage lives inside `S->DB`, which MicroSAT (or the
/// host's drop guard) frees with its own allocation.
pub struct ScratchArena {
    /// Raw base pointer into `S->DB`. Captured by `bind_to_solver`;
    /// stable for the life of the MicroSAT solver allocation.
    /// `core::ptr::null_mut()` until binding.
    #[allow(dead_code)]
    db_base: *mut c_int,
    /// Offset (in `c_int` units) from `db_base` where the scratch
    /// arena starts. Chosen as `S->mem_max - reserve_words` at
    /// bind-time.
    #[allow(dead_code)]
    scratch_base_offset: usize,
    /// Reservation size in `c_int` units. Set by `new` and consulted
    /// by `bind_to_solver` when computing `scratch_base_offset`.
    #[allow(dead_code)]
    reserve_words: usize,
    /// Bump cursor (in `c_int` units, relative to
    /// `scratch_base_offset`). Reset to 0 by [`Self::reset`].
    #[allow(dead_code)]
    cursor: usize,
    /// Cached `S->mem_max` (read once at bind time). Used by the
    /// near-overflow guard to test
    /// `s.mem_used + SCRATCH_NEAR_OVERFLOW_MARGIN < scratch_base_offset`
    /// without re-reading the solver.
    #[allow(dead_code)]
    db_mem_max: usize,
    /// True once `bind_to_solver` has succeeded. Methods that require
    /// binding will assert this in debug builds.
    #[allow(dead_code)]
    bound: bool,
}

impl ScratchArena {
    /// Construct a new unbound scratch arena with the requested
    /// reservation size. The arena is inert until
    /// [`Self::bind_to_solver`] is called.
    ///
    /// `reserve_words` must be sized to fit
    /// `num_vars * (max_clause_len + SYNTHETIC_CLAUSE_OVERHEAD)`
    /// `c_int` slots. Callers can compute this from the JIT-compiled
    /// formula's worst-case clause length.
    ///
    /// # Implementation contract (Phase 1)
    ///
    /// Initialise every field but do not touch any external memory.
    /// The arena is unusable until `bind_to_solver` runs.
    pub fn new(reserve_words: usize) -> Self {
        Self {
            db_base: core::ptr::null_mut(),
            scratch_base_offset: 0,
            reserve_words,
            cursor: 0,
            db_mem_max: 0,
            bound: false,
        }
    }

    /// Attach the arena to a live MicroSAT solver. Captures
    /// `S->DB` and `S->mem_max`, computes `scratch_base_offset =
    /// S->mem_max - reserve_words`, and asserts that the live DB
    /// (`S->mem_used + SCRATCH_BIND_MARGIN`) does not collide with
    /// the reserved region. Returns `Err` with a descriptive value
    /// if the collision check fails.
    ///
    /// # Safety
    ///
    /// `s` must point to a fully initialised `sys::solver`
    /// (post-`parse`). The function reads `S->DB`, `S->mem_used`, and
    /// `S->mem_max`. No writes are performed.
    ///
    /// # Implementation contract (Phase 1)
    ///
    ///   * Read `S->DB`, `S->mem_max`, `S->mem_used`.
    ///   * Verify `S->mem_used + SCRATCH_BIND_MARGIN < S->mem_max -
    ///     self.reserve_words` (i.e., the reservation does not
    ///     collide with the live DB).
    ///   * Store the captured pointer and offsets; set `bound = true`.
    ///   * On collision return `Err(ScratchOverflow{...})` with
    ///     `requested = reserve_words` and `available =
    ///     mem_max - mem_used - SCRATCH_BIND_MARGIN`.
    pub unsafe fn bind_to_solver(&mut self, s: *mut sys::solver) -> Result<(), ScratchOverflow> {
        debug_assert!(!s.is_null(), "bind_to_solver requires a non-null solver");
        // SAFETY: caller guarantees `s` points to a fully initialised
        // `sys::solver` (post-`parse`); we read three plain `int` fields
        // and a `*mut c_int` pointer. No writes are performed.
        let (db_base, mem_used, mem_max) =
            unsafe { ((*s).DB, (*s).mem_used as usize, (*s).mem_max as usize) };

        // Verify the reservation fits inside `S->mem_max` with enough
        // headroom for the live DB plus the bind-time safety floor.
        // Using checked arithmetic to make oversized `reserve_words`
        // requests fail loudly rather than wrap around.
        let scratch_base_offset = match mem_max.checked_sub(self.reserve_words) {
            Some(v) => v,
            None => {
                return Err(ScratchOverflow {
                    requested_words: self.reserve_words,
                    available_words: 0,
                });
            }
        };

        let min_required = match mem_used.checked_add(SCRATCH_BIND_MARGIN) {
            Some(v) => v,
            None => {
                return Err(ScratchOverflow {
                    requested_words: self.reserve_words,
                    available_words: 0,
                });
            }
        };

        if min_required >= scratch_base_offset {
            // The live DB + safety floor collides with the reservation.
            let available = mem_max
                .saturating_sub(mem_used)
                .saturating_sub(SCRATCH_BIND_MARGIN);
            return Err(ScratchOverflow {
                requested_words: self.reserve_words,
                available_words: available,
            });
        }

        self.db_base = db_base;
        self.scratch_base_offset = scratch_base_offset;
        self.db_mem_max = mem_max;
        self.cursor = 0;
        self.bound = true;
        Ok(())
    }

    /// Bump-allocate a synthetic reason clause for a single
    /// JIT-emitted implication.
    ///
    /// `propagated_lit` is the DIMACS-signed literal the JIT just
    /// assigned. `antecedents` is the list of trail literals whose
    /// joint truth makes the JIT's input clause unit on
    /// `propagated_lit` - i.e., for an input clause
    /// `C = (propagated_lit OR not_a OR not_b OR ...)` where each
    /// `not_x` is currently false, this slice is `[a, b, ...]`.
    ///
    /// The returned value is the DB-offset reason that the caller
    /// stamps into `S->reason[abs(propagated_lit)]`, matching
    /// MicroSAT's own `assign` formula `1 + (clause - S->DB)`. The
    /// underlying scratch slot run is laid out as:
    ///
    /// ```text
    /// scratch[cursor + 0] = propagated_lit
    /// scratch[cursor + 1] = antecedents[0]
    /// ...
    /// scratch[cursor + k] = antecedents[k-1]
    /// scratch[cursor + k + 1] = 0  (terminator)
    /// ```
    ///
    /// Returns `Err(ScratchOverflow)` if the clause does not fit in
    /// the remaining reservation.
    ///
    /// # Implementation contract (Phase 1)
    ///
    ///   * Debug-assert `self.bound`.
    ///   * Compute `needed = 1 + antecedents.len() + 1`.
    ///   * If `self.cursor + needed > self.reserve_words`, return
    ///     `Err(ScratchOverflow{ requested: needed, available:
    ///     self.reserve_words - self.cursor })`.
    ///   * Compute `slot_offset = self.scratch_base_offset +
    ///     self.cursor`.
    ///   * Write `propagated_lit` at `db_base[slot_offset]`,
    ///     antecedents at `db_base[slot_offset + 1..]`, and 0 at the
    ///     terminator.
    ///   * Advance `self.cursor` by `needed`.
    ///   * Return `Ok((slot_offset + 1) as c_int)` (the
    ///     "1 + (clause - S->DB)" reason value, with `clause` =
    ///     `db_base + slot_offset`, the first literal slot - the
    ///     reason convention is that the value points one PAST
    ///     `clause[0]` so `S->DB + reason - 1 == &clause[0]`).
    pub fn allocate_synthetic_clause(
        &mut self,
        propagated_lit: c_int,
        antecedents: &[c_int],
    ) -> Result<c_int, ScratchOverflow> {
        debug_assert!(
            self.bound,
            "allocate_synthetic_clause called on an unbound ScratchArena"
        );
        debug_assert!(
            !self.db_base.is_null(),
            "ScratchArena bound but db_base is null"
        );

        // Layout: [propagated_lit, antecedents..., 0_terminator].
        let needed = 1usize + antecedents.len() + 1usize;
        let available = self.reserve_words - self.cursor;
        if needed > available {
            return Err(ScratchOverflow {
                requested_words: needed,
                available_words: available,
            });
        }

        let slot_offset = self.scratch_base_offset + self.cursor;

        // SAFETY: `db_base + slot_offset .. + needed` lies inside the
        // exclusive scratch region `[scratch_base_offset,
        // scratch_base_offset + reserve_words)` of `S->DB`. The bind
        // check verified `scratch_base_offset + reserve_words <=
        // mem_max`, and the overflow guard above ensured
        // `cursor + needed <= reserve_words`. No other party writes to
        // this region (MicroSAT's `getMemory` allocates from
        // `mem_used` upward and never crosses `mem_max -
        // reserve_words`; nothing else touches `S->DB`'s tail).
        unsafe {
            let mut slot = self.db_base.add(slot_offset);
            *slot = propagated_lit;
            for &lit in antecedents {
                slot = slot.add(1);
                *slot = lit;
            }
            slot = slot.add(1);
            *slot = 0;
        }

        self.cursor += needed;

        // Reason convention: `S->DB + reason - 1 == &clause[0]`, so the
        // reason value is `slot_offset + 1`.
        let reason = slot_offset + 1;
        Ok(reason as c_int)
    }

    /// Look up the slot range backing a previously-allocated
    /// synthetic clause by its reason value. Returns `Some(ptr)`
    /// where `ptr` is a pointer to the clause's `clause[0]` slot
    /// (equivalently, `S->DB + reason - 1`) if the reason lies inside
    /// the scratch range, else `None`.
    ///
    /// Used by the analyze-driver test harness (Phase 3 / Phase 4) to
    /// verify a reason value indeed lives in scratch and not in the
    /// live DB. NOT used by the JIT-replacement hot path - MicroSAT's
    /// `analyze` dereferences reason values directly through `S->DB`
    /// without consulting this helper.
    ///
    /// # Implementation contract (Phase 1)
    ///
    ///   * If unbound, return `None`.
    ///   * If `reason_val <= 0`, return `None` (reasons are always
    ///     positive).
    ///   * Let `offset = (reason_val - 1) as usize`. If
    ///     `offset < self.scratch_base_offset || offset >=
    ///     self.scratch_base_offset + self.cursor`, return `None`.
    ///   * Return `Some(self.db_base.add(offset))` as `*const c_int`.
    pub fn lookup_reason(&self, reason_val: c_int) -> Option<*const c_int> {
        if !self.bound {
            return None;
        }
        if reason_val <= 0 {
            return None;
        }
        let offset = (reason_val as usize) - 1;
        let live_end = self.scratch_base_offset + self.cursor;
        if offset < self.scratch_base_offset || offset >= live_end {
            return None;
        }
        // SAFETY: `offset` falls inside the bound, allocated scratch
        // region `[scratch_base_offset, scratch_base_offset + cursor)`,
        // which is a strict subrange of the solver's `S->DB`
        // allocation.
        let ptr = unsafe { self.db_base.add(offset) };
        Some(ptr as *const c_int)
    }

    /// Reset the cursor to zero. Does NOT free any memory and does
    /// NOT zero the slot run - subsequent allocations overwrite
    /// slot-by-slot. Called at restart, reduceDB, and
    /// epoch-recompile boundaries.
    ///
    /// # Implementation contract (Phase 1)
    ///
    ///   * Set `self.cursor = 0`.
    ///   * Do not touch `db_base`, `scratch_base_offset`,
    ///     `reserve_words`, or `bound`.
    pub fn reset(&mut self) {
        self.cursor = 0;
    }

    /// Returns `true` iff the arena is currently bound to a live
    /// solver and `S->mem_used` is within `SCRATCH_NEAR_OVERFLOW_MARGIN`
    /// of `scratch_base_offset`. The JIT-replacement hot path
    /// consults this before every allocation so it can fall back to
    /// native if the live DB has grown into the safety buffer.
    ///
    /// # Safety
    ///
    /// `s` must point to a live, post-bind solver.
    ///
    /// # Implementation contract (Phase 1)
    ///
    ///   * If `!self.bound`, return `false` (defensively).
    ///   * Read `S->mem_used`.
    ///   * Return `(mem_used + SCRATCH_NEAR_OVERFLOW_MARGIN) >=
    ///     self.scratch_base_offset`.
    pub unsafe fn is_near_overflow(&self, s: *mut sys::solver) -> bool {
        if !self.bound {
            return false;
        }
        debug_assert!(!s.is_null(), "is_near_overflow requires a non-null solver");
        // SAFETY: caller guarantees `s` points to a live solver. We
        // only read the plain `int` field `mem_used`.
        let mem_used = unsafe { (*s).mem_used as usize };
        mem_used.saturating_add(SCRATCH_NEAR_OVERFLOW_MARGIN) >= self.scratch_base_offset
    }

    /// Number of `c_int` slots currently consumed by allocated
    /// synthetic clauses. Exposed for telemetry and tests.
    pub fn cursor(&self) -> usize {
        self.cursor
    }

    /// Reservation size set at construction. Exposed for tests.
    pub fn reserve_words(&self) -> usize {
        self.reserve_words
    }

    /// Offset where the scratch region begins in `S->DB`. Defined
    /// only after `bind_to_solver` has been called; returns `None`
    /// otherwise. Exposed for tests and telemetry.
    pub fn scratch_base_offset(&self) -> Option<usize> {
        if self.bound {
            Some(self.scratch_base_offset)
        } else {
            None
        }
    }
}

// SAFETY:
// `ScratchArena` holds a raw `*mut c_int` pointing into a MicroSAT
// solver's `S->DB`. The arena does not give safe API consumers any
// way to dereference the pointer except via `lookup_reason` (which
// returns a `*const c_int` the caller must handle unsafely).
// MicroSAT is single-threaded inside this crate and the arena lives
// on the same thread as the solver it is bound to. We intentionally
// do NOT implement `Send` / `Sync` so the borrow checker enforces
// thread-locality.
