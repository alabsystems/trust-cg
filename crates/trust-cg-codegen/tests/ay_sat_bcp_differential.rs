// trust-cg-codegen/tests/ay_sat_bcp_differential.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use proptest::prelude::*;
use std::collections::VecDeque;

const MAX_VAR: usize = 16;
const MAX_CLAUSE_LITS: usize = 8;
const MAX_CLAUSES: usize = 32;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(i32)]
enum BcpStatus {
    Ok = 0,
    Unit = 1,
    Conflict = 2,
    Bounds = 3,
    StaleGeneration = 4,
    UnsupportedShape = 5,
    VerifierFailure = 6,
    Timeout = 7,
    InternalError = 8,
}

impl BcpStatus {
    fn promotes_native(self) -> bool {
        false
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Assignment {
    Unknown,
    False,
    True,
}

impl Assignment {
    fn for_literal(self, lit: i32) -> Option<bool> {
        match (self, lit.is_positive()) {
            (Self::Unknown, _) => None,
            (Self::True, true) | (Self::False, false) => Some(true),
            (Self::True, false) | (Self::False, true) => Some(false),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Clause {
    lits: Vec<i32>,
}

impl Clause {
    fn new(lits: impl Into<Vec<i32>>) -> Self {
        Self { lits: lits.into() }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct WatchEntry {
    clause: usize,
    watch_slot: usize,
}

#[derive(Clone, Debug)]
struct BcpInput {
    clauses: Vec<Clause>,
    assignment: Vec<Assignment>,
    pending: Vec<i32>,
    context_generation: u64,
    expected_generation: u64,
    watch_generation: u64,
    assignment_generation: u64,
    clause_arena_len: usize,
    watch_head_count: usize,
    watch_entry_count: usize,
    trail_capacity: usize,
    pending_capacity: usize,
    result_capacity: usize,
    force_internal_error: bool,
    verifier_accepts: bool,
    timeout_budget_steps: usize,
}

impl BcpInput {
    fn new(clauses: Vec<Clause>, assignment_len: usize, pending: Vec<i32>) -> Self {
        let watch_entries = clauses
            .iter()
            .map(|clause| clause.lits.len().min(2))
            .sum::<usize>();
        Self {
            clause_arena_len: clauses.iter().map(|clause| clause.lits.len()).sum(),
            watch_head_count: assignment_len.saturating_mul(2).saturating_add(1),
            watch_entry_count: watch_entries,
            trail_capacity: assignment_len,
            pending_capacity: assignment_len.saturating_add(pending.len()),
            result_capacity: 1,
            force_internal_error: false,
            clauses,
            assignment: vec![Assignment::Unknown; assignment_len + 1],
            pending,
            context_generation: 7,
            expected_generation: 7,
            watch_generation: 7,
            assignment_generation: 7,
            verifier_accepts: true,
            timeout_budget_steps: 10_000,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct BcpTelemetry {
    clauses_scanned: u64,
    literals_tested: u64,
    propagations: u64,
    conflicts: u64,
    deopts_bounds: u64,
    deopts_stale_generation: u64,
    deopts_unsupported_shape: u64,
    deopts_verifier_failure: u64,
    deopts_timeout: u64,
    deopts_internal_error: u64,
    stale_generation_rejects: u64,
    validation_time_ns: u64,
    cache_key_placeholder: u64,
    proof_placeholder: u64,
    useful_native_count: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct BcpOutput {
    status: BcpStatus,
    assignment: Vec<Assignment>,
    trail: Vec<i32>,
    conflict_clause: Option<usize>,
    unit_literal: Option<i32>,
    watches: Vec<[usize; 2]>,
    telemetry: BcpTelemetry,
}

impl BcpOutput {
    fn rejected(status: BcpStatus, mut telemetry: BcpTelemetry) -> Self {
        match status {
            BcpStatus::Bounds => telemetry.deopts_bounds += 1,
            BcpStatus::StaleGeneration => {
                telemetry.deopts_stale_generation += 1;
                telemetry.stale_generation_rejects += 1;
            }
            BcpStatus::UnsupportedShape => telemetry.deopts_unsupported_shape += 1,
            BcpStatus::VerifierFailure => telemetry.deopts_verifier_failure += 1,
            BcpStatus::Timeout => telemetry.deopts_timeout += 1,
            BcpStatus::InternalError => telemetry.deopts_internal_error += 1,
            BcpStatus::Ok | BcpStatus::Unit | BcpStatus::Conflict => {}
        }
        Self {
            status,
            assignment: Vec::new(),
            trail: Vec::new(),
            conflict_clause: None,
            unit_literal: None,
            watches: Vec::new(),
            telemetry,
        }
    }
}

fn lit_index(lit: i32, assignment_len: usize) -> Option<usize> {
    let var = lit.unsigned_abs() as usize;
    if var == 0 || var >= assignment_len {
        return None;
    }
    Some((var - 1) * 2 + usize::from(lit.is_negative()))
}

#[allow(clippy::result_large_err)] // The rejected value is the complete telemetry fixture.
fn validate_input(input: &BcpInput) -> Result<BcpTelemetry, BcpOutput> {
    let mut telemetry = BcpTelemetry {
        validation_time_ns: 1,
        cache_key_placeholder: 0x0005_a4bc_u64,
        proof_placeholder: 0x660,
        ..BcpTelemetry::default()
    };

    if input.context_generation != input.expected_generation
        || input.watch_generation != input.expected_generation
        || input.assignment_generation != input.expected_generation
    {
        return Err(BcpOutput::rejected(BcpStatus::StaleGeneration, telemetry));
    }
    if !input.verifier_accepts {
        return Err(BcpOutput::rejected(BcpStatus::VerifierFailure, telemetry));
    }
    if input.timeout_budget_steps == 0 {
        return Err(BcpOutput::rejected(BcpStatus::Timeout, telemetry));
    }
    if input.clauses.len() > MAX_CLAUSES {
        return Err(BcpOutput::rejected(BcpStatus::UnsupportedShape, telemetry));
    }
    let arena_lits = input
        .clauses
        .iter()
        .map(|clause| clause.lits.len())
        .sum::<usize>();
    let needed_watch_entries = input
        .clauses
        .iter()
        .map(|clause| clause.lits.len().min(2))
        .sum::<usize>();
    if input.clause_arena_len < arena_lits
        || input.watch_head_count < input.assignment.len().saturating_sub(1) * 2
        || input.watch_entry_count < needed_watch_entries
        || input.pending_capacity < input.pending.len()
        || input.result_capacity == 0
    {
        return Err(BcpOutput::rejected(BcpStatus::Bounds, telemetry));
    }
    for clause in &input.clauses {
        if clause.lits.is_empty() || clause.lits.len() > MAX_CLAUSE_LITS {
            return Err(BcpOutput::rejected(BcpStatus::UnsupportedShape, telemetry));
        }
        for &lit in &clause.lits {
            if lit_index(lit, input.assignment.len()).is_none()
                || lit.unsigned_abs() as usize > MAX_VAR
            {
                return Err(BcpOutput::rejected(BcpStatus::Bounds, telemetry));
            }
        }
    }
    for &lit in &input.pending {
        if lit_index(lit, input.assignment.len()).is_none() {
            return Err(BcpOutput::rejected(BcpStatus::Bounds, telemetry));
        }
    }
    if input.force_internal_error {
        return Err(BcpOutput::rejected(BcpStatus::InternalError, telemetry));
    }

    telemetry.useful_native_count = 0;
    Ok(telemetry)
}

#[allow(clippy::result_large_err)] // The rejected value is the complete telemetry fixture.
fn push_trail_or_bounds(
    trail: &mut Vec<i32>,
    lit: i32,
    input: &BcpInput,
    telemetry: &BcpTelemetry,
) -> Result<(), BcpOutput> {
    trail.push(lit);
    if trail.len() > input.trail_capacity {
        return Err(BcpOutput::rejected(BcpStatus::Bounds, telemetry.clone()));
    }
    Ok(())
}

#[allow(clippy::result_large_err)] // The rejected value is the complete telemetry fixture.
fn push_pending_or_bounds(
    queue: &mut VecDeque<i32>,
    lit: i32,
    input: &BcpInput,
    telemetry: &BcpTelemetry,
) -> Result<(), BcpOutput> {
    if queue.len().saturating_add(1) > input.pending_capacity {
        return Err(BcpOutput::rejected(BcpStatus::Bounds, telemetry.clone()));
    }
    queue.push_back(lit);
    Ok(())
}

fn apply_literal(assignment: &mut [Assignment], lit: i32) -> bool {
    let var = lit.unsigned_abs() as usize;
    let wanted = if lit.is_positive() {
        Assignment::True
    } else {
        Assignment::False
    };
    match assignment[var] {
        Assignment::Unknown => {
            assignment[var] = wanted;
            true
        }
        current => current == wanted,
    }
}

fn dense_reference_bcp(input: &BcpInput) -> BcpOutput {
    let mut telemetry = match validate_input(input) {
        Ok(telemetry) => telemetry,
        Err(output) => return output,
    };
    let mut assignment = input.assignment.clone();
    let mut trail = Vec::new();
    let mut queue = VecDeque::from(input.pending.clone());

    while let Some(lit) = queue.pop_front() {
        if !apply_literal(&mut assignment, lit) {
            telemetry.conflicts += 1;
            return finish(
                BcpStatus::Conflict,
                assignment,
                trail,
                Some(usize::MAX),
                None,
                initial_watches(&input.clauses),
                telemetry,
            );
        }
        if let Err(output) = push_trail_or_bounds(&mut trail, lit, input, &telemetry) {
            return output;
        }
        let false_lit = -lit;
        let mut pending_unit = None;
        for (clause_idx, clause) in input.clauses.iter().enumerate() {
            if !clause.lits.contains(&false_lit) {
                continue;
            }
            telemetry.clauses_scanned += 1;
            let mut unknown = None;
            let mut false_count = 0;
            let mut satisfied = false;
            for &clause_lit in &clause.lits {
                telemetry.literals_tested += 1;
                match assignment[clause_lit.unsigned_abs() as usize].for_literal(clause_lit) {
                    Some(true) => {
                        satisfied = true;
                        break;
                    }
                    Some(false) => false_count += 1,
                    None => unknown = Some(clause_lit),
                }
            }
            if satisfied {
                continue;
            }
            if false_count == clause.lits.len() {
                telemetry.conflicts += 1;
                return finish(
                    BcpStatus::Conflict,
                    assignment,
                    trail,
                    Some(clause_idx),
                    None,
                    initial_watches(&input.clauses),
                    telemetry,
                );
            }
            if pending_unit.is_none() && false_count + 1 == clause.lits.len() {
                pending_unit = Some(unknown.expect("unit clause has one unknown literal"));
            }
        }
        if let Some(unit) = pending_unit
            && apply_literal(&mut assignment, unit)
        {
            telemetry.propagations += 1;
            if let Err(output) = push_trail_or_bounds(&mut trail, unit, input, &telemetry) {
                return output;
            }
            if let Err(output) = push_pending_or_bounds(&mut queue, unit, input, &telemetry) {
                return output;
            }
            return finish(
                BcpStatus::Unit,
                assignment,
                trail,
                None,
                Some(unit),
                initial_watches(&input.clauses),
                telemetry,
            );
        }
    }

    finish(
        BcpStatus::Ok,
        assignment,
        trail,
        None,
        None,
        initial_watches(&input.clauses),
        telemetry,
    )
}

fn watch_list_bcp(input: &BcpInput) -> BcpOutput {
    let mut telemetry = match validate_input(input) {
        Ok(telemetry) => telemetry,
        Err(output) => return output,
    };
    let mut assignment = input.assignment.clone();
    let mut trail = Vec::new();
    let mut watches = initial_watches(&input.clauses);
    let mut watch_lists = build_watch_lists(input, &watches);
    let mut queue = VecDeque::from(input.pending.clone());

    while let Some(lit) = queue.pop_front() {
        if !apply_literal(&mut assignment, lit) {
            telemetry.conflicts += 1;
            return finish(
                BcpStatus::Conflict,
                assignment,
                trail,
                Some(usize::MAX),
                None,
                watches,
                telemetry,
            );
        }
        if let Err(output) = push_trail_or_bounds(&mut trail, lit, input, &telemetry) {
            return output;
        }

        let false_lit = -lit;
        let Some(list_idx) = lit_index(false_lit, input.assignment.len()) else {
            return BcpOutput::rejected(BcpStatus::Bounds, telemetry);
        };
        let mut entries = std::mem::take(&mut watch_lists[list_idx]);
        let mut pending_unit = None;
        for entry in entries.drain(..) {
            telemetry.clauses_scanned += 1;
            let clause = &input.clauses[entry.clause];
            let other_slot = 1 - entry.watch_slot;
            let other_watch_idx = watches[entry.clause][other_slot];
            let other_lit = clause.lits[other_watch_idx];
            if assignment[other_lit.unsigned_abs() as usize].for_literal(other_lit) == Some(true) {
                watch_lists[list_idx].push(entry);
                continue;
            }

            let mut moved = false;
            for (candidate_idx, &candidate_lit) in clause.lits.iter().enumerate() {
                telemetry.literals_tested += 1;
                if candidate_idx == watches[entry.clause][0]
                    || candidate_idx == watches[entry.clause][1]
                {
                    continue;
                }
                if assignment[candidate_lit.unsigned_abs() as usize].for_literal(candidate_lit)
                    != Some(false)
                {
                    watches[entry.clause][entry.watch_slot] = candidate_idx;
                    let Some(new_list_idx) = lit_index(candidate_lit, input.assignment.len())
                    else {
                        return BcpOutput::rejected(BcpStatus::Bounds, telemetry);
                    };
                    watch_lists[new_list_idx].push(entry);
                    moved = true;
                    break;
                }
            }
            if moved {
                continue;
            }

            match assignment[other_lit.unsigned_abs() as usize].for_literal(other_lit) {
                Some(false) => {
                    telemetry.conflicts += 1;
                    watch_lists[list_idx].push(entry);
                    return finish(
                        BcpStatus::Conflict,
                        assignment,
                        trail,
                        Some(entry.clause),
                        None,
                        watches,
                        telemetry,
                    );
                }
                Some(true) => watch_lists[list_idx].push(entry),
                None => {
                    watch_lists[list_idx].push(entry);
                    if pending_unit.is_none() {
                        pending_unit = Some(other_lit);
                    }
                }
            }
        }
        if let Some(unit) = pending_unit {
            if !apply_literal(&mut assignment, unit) {
                telemetry.conflicts += 1;
                return finish(
                    BcpStatus::Conflict,
                    assignment,
                    trail,
                    Some(usize::MAX),
                    None,
                    watches,
                    telemetry,
                );
            }
            telemetry.propagations += 1;
            if let Err(output) = push_trail_or_bounds(&mut trail, unit, input, &telemetry) {
                return output;
            }
            if let Err(output) = push_pending_or_bounds(&mut queue, unit, input, &telemetry) {
                return output;
            }
            return finish(
                BcpStatus::Unit,
                assignment,
                trail,
                None,
                Some(unit),
                watches,
                telemetry,
            );
        }
    }

    finish(
        BcpStatus::Ok,
        assignment,
        trail,
        None,
        None,
        watches,
        telemetry,
    )
}

fn initial_watches(clauses: &[Clause]) -> Vec<[usize; 2]> {
    clauses
        .iter()
        .map(|clause| match clause.lits.len() {
            0 | 1 => [0, 0],
            _ => [0, 1],
        })
        .collect()
}

fn build_watch_lists(input: &BcpInput, watches: &[[usize; 2]]) -> Vec<Vec<WatchEntry>> {
    let mut watch_lists = vec![Vec::new(); input.assignment.len().saturating_sub(1) * 2];
    for (clause_idx, clause_watches) in watches.iter().enumerate() {
        for (slot, &lit_idx) in clause_watches.iter().enumerate() {
            let lit = input.clauses[clause_idx].lits[lit_idx];
            if let Some(list_idx) = lit_index(lit, input.assignment.len()) {
                watch_lists[list_idx].push(WatchEntry {
                    clause: clause_idx,
                    watch_slot: slot,
                });
            }
        }
    }
    watch_lists
}

fn finish(
    status: BcpStatus,
    assignment: Vec<Assignment>,
    trail: Vec<i32>,
    conflict_clause: Option<usize>,
    unit_literal: Option<i32>,
    watches: Vec<[usize; 2]>,
    telemetry: BcpTelemetry,
) -> BcpOutput {
    BcpOutput {
        status,
        assignment,
        trail,
        conflict_clause,
        unit_literal,
        watches,
        telemetry,
    }
}

fn assert_unit_literal_is_semantically_valid(input: &BcpInput, output: &BcpOutput) {
    let unit = output
        .unit_literal
        .expect("unit result carries the propagated literal");
    assert_eq!(output.trail.last().copied(), Some(unit));

    let mut assignment_before_unit = input.assignment.clone();
    for &lit in &output.trail[..output.trail.len().saturating_sub(1)] {
        assert!(apply_literal(&mut assignment_before_unit, lit));
    }

    assert!(
        input.clauses.iter().any(|clause| {
            let mut saw_unit = false;
            for &lit in &clause.lits {
                if lit == unit {
                    saw_unit = true;
                    continue;
                }
                if assignment_before_unit[lit.unsigned_abs() as usize].for_literal(lit)
                    != Some(false)
                {
                    return false;
                }
            }
            saw_unit
                && assignment_before_unit[unit.unsigned_abs() as usize]
                    .for_literal(unit)
                    .is_none()
        }),
        "unit literal {unit} must be justified by a clause under the pre-unit assignment"
    );
}

fn assert_differential(input: BcpInput) -> BcpOutput {
    let reference = dense_reference_bcp(&input);
    let watched = watch_list_bcp(&input);
    assert_eq!(watched.status, reference.status);
    assert_eq!(
        watched.conflict_clause.is_some(),
        reference.conflict_clause.is_some()
    );
    match watched.status {
        BcpStatus::Unit => {
            assert_unit_literal_is_semantically_valid(&input, &reference);
            assert_unit_literal_is_semantically_valid(&input, &watched);
        }
        BcpStatus::Conflict => {
            assert!(watched.conflict_clause.is_some());
            assert!(reference.conflict_clause.is_some());
        }
        _ => {
            assert_eq!(watched.assignment, reference.assignment);
            assert_eq!(watched.unit_literal, reference.unit_literal);
        }
    }
    assert_eq!(
        watched.telemetry.propagations,
        reference.telemetry.propagations
    );
    assert_eq!(watched.telemetry.conflicts, reference.telemetry.conflicts);
    assert_eq!(watched.telemetry.useful_native_count, 0);
    assert!(!watched.status.promotes_native());
    watched
}

#[test]
fn ay_sat_bcp_watched_clause_movement_matches_dense_reference() {
    let input = BcpInput::new(vec![Clause::new(vec![-1, 2, 3])], 3, vec![1]);

    let watched = assert_differential(input);

    assert_eq!(watched.status, BcpStatus::Ok);
    assert_eq!(watched.watches[0], [2, 1]);
    assert_eq!(watched.telemetry.clauses_scanned, 1);
    assert!(watched.telemetry.literals_tested >= 1);
}

#[test]
fn ay_sat_bcp_unit_propagation_matches_dense_reference() {
    let mut input = BcpInput::new(vec![Clause::new(vec![-1, 2])], 2, vec![1]);
    input.pending_capacity = 2;

    let watched = assert_differential(input);

    assert_eq!(watched.status, BcpStatus::Unit);
    assert_eq!(watched.unit_literal, Some(2));
    assert_eq!(watched.assignment[2], Assignment::True);
    assert_eq!(watched.telemetry.propagations, 1);
}

#[test]
fn ay_sat_bcp_conflict_discovery_matches_dense_reference() {
    let mut input = BcpInput::new(vec![Clause::new(vec![-1, 2])], 2, vec![1]);
    input.assignment[2] = Assignment::False;

    let watched = assert_differential(input);

    assert_eq!(watched.status, BcpStatus::Conflict);
    assert_eq!(watched.conflict_clause, Some(0));
    assert_eq!(watched.telemetry.conflicts, 1);
}

#[test]
fn ay_sat_bcp_conflict_takes_priority_over_unit_on_same_propagation_step() {
    let input = BcpInput::new(
        vec![Clause::new(vec![6, -1, 8]), Clause::new(vec![8])],
        12,
        vec![-9, 1, 1, -8],
    );

    let watched = assert_differential(input);

    assert_eq!(watched.status, BcpStatus::Conflict);
    assert_eq!(watched.conflict_clause, Some(1));
    assert_eq!(watched.telemetry.conflicts, 1);
    assert_eq!(watched.telemetry.propagations, 0);
}

#[test]
fn ay_sat_bcp_conflict_priority_scans_past_earlier_watched_unit() {
    let input = BcpInput::new(
        vec![Clause::new(vec![5, -1]), Clause::new(vec![5])],
        12,
        vec![-5],
    );

    let watched = assert_differential(input);

    assert_eq!(watched.status, BcpStatus::Conflict);
    assert_eq!(watched.conflict_clause, Some(1));
    assert_eq!(watched.telemetry.conflicts, 1);
    assert_eq!(watched.telemetry.propagations, 0);
}

#[test]
fn ay_sat_bcp_empty_watch_lists_are_ok_without_scans() {
    let input = BcpInput::new(Vec::new(), 4, vec![1]);

    let watched = assert_differential(input);

    assert_eq!(watched.status, BcpStatus::Ok);
    assert_eq!(watched.telemetry.clauses_scanned, 0);
    assert_eq!(watched.telemetry.propagations, 0);
    assert_eq!(watched.telemetry.conflicts, 0);
}

#[test]
fn ay_sat_bcp_stale_generations_are_typed_fail_closed_rejects() {
    let mut input = BcpInput::new(vec![Clause::new(vec![-1, 2])], 2, vec![1]);
    input.watch_generation = input.expected_generation + 1;

    let watched = assert_differential(input);

    assert_eq!(watched.status, BcpStatus::StaleGeneration);
    assert_eq!(watched.telemetry.deopts_stale_generation, 1);
    assert_eq!(watched.telemetry.stale_generation_rejects, 1);
}

#[test]
fn ay_sat_bcp_typed_non_promoting_statuses_cover_preflight_rejects() {
    let mut bounds = BcpInput::new(vec![Clause::new(vec![-1, 2])], 2, vec![1]);
    bounds.clause_arena_len = 1;
    assert_eq!(assert_differential(bounds).status, BcpStatus::Bounds);

    let unsupported = BcpInput::new(vec![Clause::new(vec![1; MAX_CLAUSE_LITS + 1])], 2, vec![]);
    assert_eq!(
        assert_differential(unsupported).status,
        BcpStatus::UnsupportedShape
    );

    let mut verifier = BcpInput::new(vec![Clause::new(vec![1])], 1, vec![]);
    verifier.verifier_accepts = false;
    assert_eq!(
        assert_differential(verifier).status,
        BcpStatus::VerifierFailure
    );

    let mut timeout = BcpInput::new(vec![Clause::new(vec![1])], 1, vec![]);
    timeout.timeout_budget_steps = 0;
    assert_eq!(assert_differential(timeout).status, BcpStatus::Timeout);

    let mut internal = BcpInput::new(vec![Clause::new(vec![1])], 1, vec![]);
    internal.force_internal_error = true;
    assert_eq!(
        assert_differential(internal).status,
        BcpStatus::InternalError
    );
}

#[test]
fn ay_sat_bcp_bounds_cover_all_manifest_buffers() {
    let base = BcpInput::new(vec![Clause::new(vec![-1, 2])], 2, vec![1]);

    let mut clause_arena = base.clone();
    clause_arena.clause_arena_len = 1;
    assert_eq!(assert_differential(clause_arena).status, BcpStatus::Bounds);

    let mut watch_heads = base.clone();
    watch_heads.watch_head_count = 1;
    assert_eq!(assert_differential(watch_heads).status, BcpStatus::Bounds);

    let mut watch_entries = base.clone();
    watch_entries.watch_entry_count = 1;
    assert_eq!(assert_differential(watch_entries).status, BcpStatus::Bounds);

    let mut assignment = base.clone();
    assignment.pending = vec![3];
    assert_eq!(assert_differential(assignment).status, BcpStatus::Bounds);

    let mut trail = base.clone();
    trail.trail_capacity = 0;
    assert_eq!(assert_differential(trail).status, BcpStatus::Bounds);

    let mut pending_queue = base.clone();
    pending_queue.pending_capacity = 0;
    assert_eq!(assert_differential(pending_queue).status, BcpStatus::Bounds);

    let mut result = base;
    result.result_capacity = 0;
    assert_eq!(assert_differential(result).status, BcpStatus::Bounds);
}

#[test]
fn ay_sat_bcp_trail_capacity_bounds_pending_and_unit_writes() {
    let mut pending_overflow = BcpInput::new(Vec::new(), 1, vec![1]);
    pending_overflow.trail_capacity = 0;
    let watched = assert_differential(pending_overflow);
    assert_eq!(watched.status, BcpStatus::Bounds);
    assert_eq!(watched.telemetry.deopts_bounds, 1);

    let mut unit_overflow = BcpInput::new(vec![Clause::new(vec![-1, 2])], 2, vec![1]);
    unit_overflow.trail_capacity = 1;
    let watched = assert_differential(unit_overflow);
    assert_eq!(watched.status, BcpStatus::Bounds);
    assert_eq!(watched.telemetry.deopts_bounds, 1);
}

#[test]
fn ay_sat_bcp_result_capacity_bounds_unit_and_conflict_buffers() {
    let mut unit = BcpInput::new(vec![Clause::new(vec![-1, 2])], 2, vec![1]);
    unit.result_capacity = 0;
    assert_eq!(assert_differential(unit).status, BcpStatus::Bounds);

    let mut conflict = BcpInput::new(vec![Clause::new(vec![-1, 2])], 2, vec![1]);
    conflict.assignment[2] = Assignment::False;
    conflict.result_capacity = 0;
    assert_eq!(assert_differential(conflict).status, BcpStatus::Bounds);
}

fn random_clause_strategy() -> impl Strategy<Value = Clause> {
    prop::collection::vec(1i32..=12, 1..=MAX_CLAUSE_LITS).prop_map(|vars| {
        let lits = vars
            .into_iter()
            .enumerate()
            .map(|(idx, var)| if idx % 2 == 0 { var } else { -var })
            .collect::<Vec<_>>();
        Clause::new(lits)
    })
}

proptest! {
    #[test]
    fn ay_sat_bcp_randomized_cnf_shapes_match_dense_reference(
        clauses in prop::collection::vec(random_clause_strategy(), 0..=12),
        pending_vars in prop::collection::vec(1i32..=12, 0..=8),
    ) {
        let pending = pending_vars
            .into_iter()
            .enumerate()
            .map(|(idx, var)| if idx % 3 == 0 { -var } else { var })
            .collect::<Vec<_>>();
        let input = BcpInput::new(clauses, 12, pending);

        let watched = assert_differential(input);

        prop_assert!(matches!(
            watched.status,
            BcpStatus::Ok | BcpStatus::Unit | BcpStatus::Conflict
        ));
        prop_assert_eq!(watched.telemetry.useful_native_count, 0);
        prop_assert!(!watched.status.promotes_native());
    }
}
