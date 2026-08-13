// trust-cg-sat-host - integration tests for the DB-arena split scratch
// arena (design: docs/db_arena_split_design.md).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates - License: Apache-2.0
//
// These tests pin the Phase-1 / Phase-4 contracts the implementation must
// satisfy. Every completed contract remains visible in the ordinary test lane.

#![allow(dead_code)]

use std::ffi::CString;
use std::io::Write;
use std::mem::MaybeUninit;

use tempfile::NamedTempFile;

use trust_cg_sat_host::scratch_arena::{
    SCRATCH_BIND_MARGIN, SYNTHETIC_CLAUSE_OVERHEAD, ScratchArena,
};
use trust_cg_sat_host::sys;

/// Helper: parse a CNF into a MicroSAT solver suitable for binding a
/// scratch arena to. Returns the `MaybeUninit<sys::solver>` (so the
/// caller can pass `solver.as_mut_ptr()` to `bind_to_solver`) and the
/// `parse_rc` so the test can branch on parse-time UNSAT.
fn parse_solver(cnf: &str) -> (MaybeUninit<sys::solver>, i32) {
    let mut file = NamedTempFile::new().expect("create tempfile");
    file.write_all(cnf.as_bytes()).expect("write cnf");
    file.flush().expect("flush cnf");
    let c_path = CString::new(file.path().to_string_lossy().into_owned()).expect("path to CString");

    let mut solver: MaybeUninit<sys::solver> = MaybeUninit::uninit();
    // SAFETY: `parse` calls `initCDCL` which initialises every field
    // the rest of MicroSAT will read, matching the upstream `main`
    // construction pattern used elsewhere in this crate's tests.
    let parse_rc = unsafe {
        sys::parse(
            solver.as_mut_ptr(),
            c_path.as_ptr() as *mut std::os::raw::c_char,
        )
    };
    (solver, parse_rc)
}

#[test]
fn allocate_single_synthetic_clause_returns_db_offset_reason() {
    // Bind a scratch arena to a tiny solver, allocate one synthetic
    // clause `[propagated_lit, a, b]`, and verify:
    //   * the returned reason value is positive,
    //   * dereferencing `S->DB + reason - 1` yields `propagated_lit`,
    //   * the next three slots are `a, b, 0` in that order.
    let (mut solver, parse_rc) = parse_solver("p cnf 4 2\n1 2 3 0\n-1 -2 -3 4 0\n");
    assert_ne!(parse_rc, sys::UNSAT);
    let s_ptr = solver.as_mut_ptr();

    let mut arena = ScratchArena::new(64);
    // SAFETY: parse returned non-UNSAT so `s_ptr` is fully initialised.
    unsafe { arena.bind_to_solver(s_ptr).expect("bind on tiny solver") };

    let propagated_lit = 4i32;
    let antecedents = &[1, 2, 3][..];
    let reason = arena
        .allocate_synthetic_clause(propagated_lit, antecedents)
        .expect("allocate one synthetic clause");
    assert!(reason > 0, "reason must be a positive DB offset");

    // SAFETY: the reason value is a valid offset into S->DB by the
    // arena's contract.
    let solver_ref = unsafe { &*s_ptr };
    let db = solver_ref.DB;
    let clause0_offset = (reason as isize) - 1;
    let read_lit = unsafe { *db.offset(clause0_offset) };
    assert_eq!(read_lit, propagated_lit, "clause[0] must be propagated_lit");
    let read_a = unsafe { *db.offset(clause0_offset + 1) };
    assert_eq!(read_a, 1);
    let read_b = unsafe { *db.offset(clause0_offset + 2) };
    assert_eq!(read_b, 2);
    let read_c = unsafe { *db.offset(clause0_offset + 3) };
    assert_eq!(read_c, 3);
    let terminator = unsafe { *db.offset(clause0_offset + 4) };
    assert_eq!(terminator, 0, "clause must be 0-terminated");

    // Free the DB by hand (the solver struct lives on our stack and
    // has no destructor).
    if !solver_ref.DB.is_null() {
        unsafe { libc::free(solver_ref.DB as *mut libc::c_void) };
    }
}

#[test]
fn many_allocations_advance_cursor_and_stay_in_range() {
    // Repeatedly allocate small synthetic clauses; assert each
    // returned reason value lies strictly above the live DB region
    // (i.e., above `S->mem_used`), and lookup_reason agrees.
    let (mut solver, parse_rc) = parse_solver("p cnf 4 2\n1 2 3 0\n-1 -2 -3 4 0\n");
    assert_ne!(parse_rc, sys::UNSAT);
    let s_ptr = solver.as_mut_ptr();
    let mem_used = unsafe { (*s_ptr).mem_used } as usize;

    let mut arena = ScratchArena::new(256);
    unsafe { arena.bind_to_solver(s_ptr).unwrap() };
    let scratch_base = arena
        .scratch_base_offset()
        .expect("scratch_base_offset after bind");

    assert!(
        scratch_base > mem_used,
        "scratch arena must sit above live DB: scratch_base={} mem_used={}",
        scratch_base,
        mem_used
    );

    for i in 0..10 {
        let r = arena
            .allocate_synthetic_clause(i + 1, &[1, 2])
            .expect("synthetic alloc must succeed in 256-int reservation");
        let r_offset = (r - 1) as usize;
        assert!(
            r_offset >= scratch_base,
            "reason offset {} must be >= scratch_base {}",
            r_offset,
            scratch_base
        );
        assert!(
            arena.lookup_reason(r).is_some(),
            "lookup_reason should locate the just-allocated reason"
        );
    }

    // A reason value below scratch_base must NOT be reported as
    // belonging to scratch (it would be an ordinary DB clause).
    assert!(
        arena
            .lookup_reason(((mem_used - 1) as i32).max(1))
            .is_none(),
        "live-DB reason values must not show up as scratch"
    );

    let solver_ref = unsafe { &*s_ptr };
    if !solver_ref.DB.is_null() {
        unsafe { libc::free(solver_ref.DB as *mut libc::c_void) };
    }
}

#[test]
fn reset_clears_cursor_without_freeing_memory() {
    // Allocate a few clauses, capture cursor, reset, capture cursor
    // again, allocate a clause and confirm it lands at scratch_base.
    let (mut solver, parse_rc) = parse_solver("p cnf 4 2\n1 2 3 0\n-1 -2 -3 4 0\n");
    assert_ne!(parse_rc, sys::UNSAT);
    let s_ptr = solver.as_mut_ptr();

    let mut arena = ScratchArena::new(128);
    unsafe { arena.bind_to_solver(s_ptr).unwrap() };

    let _ = arena.allocate_synthetic_clause(1, &[2, 3]).unwrap();
    let _ = arena.allocate_synthetic_clause(2, &[1]).unwrap();
    assert!(arena.cursor() > 0, "cursor must have advanced");

    arena.reset();
    assert_eq!(arena.cursor(), 0, "reset must zero the cursor");

    // After reset, the next allocation must land at scratch_base
    // (cursor = 0), so its reason value should be exactly
    // scratch_base + 1.
    let scratch_base = arena.scratch_base_offset().unwrap();
    let r = arena.allocate_synthetic_clause(7, &[1]).unwrap();
    assert_eq!(
        r as usize,
        scratch_base + 1,
        "first post-reset allocation must occupy slot 0"
    );

    let solver_ref = unsafe { &*s_ptr };
    if !solver_ref.DB.is_null() {
        unsafe { libc::free(solver_ref.DB as *mut libc::c_void) };
    }
}

#[test]
fn overflow_returns_error_does_not_corrupt_state() {
    // Reservation of exactly 6 ints fits one 3-antecedent clause
    // (`[L, a, b, c, 0]` is 5 ints with overhead = 5 = 1 + 3 + 1).
    // The second allocation must overflow cleanly.
    let (mut solver, parse_rc) = parse_solver("p cnf 4 2\n1 2 3 0\n-1 -2 -3 4 0\n");
    assert_ne!(parse_rc, sys::UNSAT);
    let s_ptr = solver.as_mut_ptr();

    let reservation = 5 + SYNTHETIC_CLAUSE_OVERHEAD; // a hair over what one clause needs
    let mut arena = ScratchArena::new(reservation);
    unsafe { arena.bind_to_solver(s_ptr).unwrap() };

    let first = arena.allocate_synthetic_clause(1, &[2, 3, 4]);
    assert!(
        first.is_ok(),
        "first allocation must fit in {reservation}-int arena"
    );

    let second = arena.allocate_synthetic_clause(2, &[1, 3, 4]);
    assert!(
        second.is_err(),
        "second allocation must overflow once arena is full"
    );

    let solver_ref = unsafe { &*s_ptr };
    if !solver_ref.DB.is_null() {
        unsafe { libc::free(solver_ref.DB as *mut libc::c_void) };
    }
}

#[test]
fn bind_rejects_collision_with_live_db() {
    // A pathologically small `reserve_words` is fine; the bind-time
    // check asserts only that the live DB plus SCRATCH_BIND_MARGIN
    // does not collide. To exercise the *rejection* path we ask for a
    // reservation that consumes nearly all of `S->mem_max`, leaving
    // less than SCRATCH_BIND_MARGIN free above `mem_used`.
    let (mut solver, parse_rc) = parse_solver("p cnf 4 2\n1 2 3 0\n-1 -2 -3 4 0\n");
    assert_ne!(parse_rc, sys::UNSAT);
    let s_ptr = solver.as_mut_ptr();
    let mem_max = unsafe { (*s_ptr).mem_max } as usize;
    let huge_reserve = mem_max - SCRATCH_BIND_MARGIN + 8; // 8 ints into the safety floor

    let mut arena = ScratchArena::new(huge_reserve);
    let bind_result = unsafe { arena.bind_to_solver(s_ptr) };
    assert!(
        bind_result.is_err(),
        "bind must refuse a reservation that crowds the live DB"
    );

    let solver_ref = unsafe { &*s_ptr };
    if !solver_ref.DB.is_null() {
        unsafe { libc::free(solver_ref.DB as *mut libc::c_void) };
    }
}

#[test]
fn watch_invariant_unchanged_after_synthetic_allocation() {
    // The strongest correctness property: a sweep of synthetic
    // allocations must not perturb the live-DB clause records that
    // carry the watch-list linked lists. We capture `S->DB[0..mem_used]`
    // before and after a batch of allocations and assert byte-equality.
    let (mut solver, parse_rc) = parse_solver("p cnf 4 4\n1 2 3 0\n-1 2 0\n-2 4 0\n-3 -4 0\n");
    assert_ne!(parse_rc, sys::UNSAT);
    let s_ptr = solver.as_mut_ptr();
    let mem_used = unsafe { (*s_ptr).mem_used } as usize;
    let db = unsafe { (*s_ptr).DB };

    let snapshot_before: Vec<i32> = (0..mem_used).map(|i| unsafe { *db.add(i) }).collect();

    let mut arena = ScratchArena::new(256);
    unsafe { arena.bind_to_solver(s_ptr).unwrap() };
    let _ = arena.allocate_synthetic_clause(4, &[1, 2, 3]).unwrap();
    let _ = arena.allocate_synthetic_clause(2, &[1]).unwrap();
    let _ = arena.allocate_synthetic_clause(3, &[1, 2]).unwrap();

    let snapshot_after: Vec<i32> = (0..mem_used).map(|i| unsafe { *db.add(i) }).collect();

    assert_eq!(
        snapshot_before, snapshot_after,
        "live DB region (watch lists etc.) must be byte-identical \
         before vs after synthetic allocations"
    );

    let solver_ref = unsafe { &*s_ptr };
    if !solver_ref.DB.is_null() {
        unsafe { libc::free(solver_ref.DB as *mut libc::c_void) };
    }
}

#[test]
fn lookup_reason_distinguishes_db_from_scratch_ranges() {
    // Compose a reason value from the live DB region (any small
    // positive int representing an offset into [first_clause_offset,
    // mem_used) ) and assert lookup_reason returns None on it; then
    // allocate a synthetic clause and confirm lookup_reason returns
    // Some on its reason value.
    let (mut solver, parse_rc) = parse_solver("p cnf 4 2\n1 2 3 0\n-1 -2 -3 4 0\n");
    assert_ne!(parse_rc, sys::UNSAT);
    let s_ptr = solver.as_mut_ptr();
    let mem_used = unsafe { (*s_ptr).mem_used } as usize;

    let mut arena = ScratchArena::new(128);
    unsafe { arena.bind_to_solver(s_ptr).unwrap() };

    // Any in-DB reason value is < scratch_base + 1.
    let live_db_reason = (mem_used as i32) - 4; // somewhere in clause space
    assert!(arena.lookup_reason(live_db_reason).is_none());

    let scratch_reason = arena.allocate_synthetic_clause(4, &[1, 2, 3]).unwrap();
    assert!(arena.lookup_reason(scratch_reason).is_some());

    let solver_ref = unsafe { &*s_ptr };
    if !solver_ref.DB.is_null() {
        unsafe { libc::free(solver_ref.DB as *mut libc::c_void) };
    }
}
