// trust-cg-codegen/tests/ay_sat_helper_replacement_differential.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use proptest::prelude::*;

use trust_cg_codegen::ay_sat_helper_replacement_contract::{
    AY_SAT_MINIMIZE_CLASSIFY_CHECK, AY_SAT_MINIMIZE_CLASSIFY_DROP, AY_SAT_MINIMIZE_CLASSIFY_KEEP,
    AY_SAT_MINIMIZE_MIN_KEEP_FLAG, AY_SAT_MINIMIZE_MIN_POISON_FLAG,
    AY_SAT_MINIMIZE_MIN_REMOVABLE_FLAG, AY_SAT_THEORY_DISPATCH_FLAG_COND_ASSIGNED,
    AY_SAT_THEORY_DISPATCH_FLAG_COND_VALUE, AY_SAT_THEORY_DISPATCH_FLAG_ITE_GUARDED,
    AY_SAT_THEORY_DISPATCH_FLAG_THEN_BRANCH, AY_SAT_THEORY_DISPATCH_NO_ITE_COND_VAR,
    AY_SAT_THEORY_DISPATCH_RESULT_STATUS_MASK, AY_SAT_THEORY_DISPATCH_RESULT_TERM_SHIFT,
    AY_SAT_THEORY_DISPATCH_RESULT_VALUE_BIT, AY_SAT_THEORY_DISPATCH_STATUS_ASSERT,
    AY_SAT_THEORY_DISPATCH_STATUS_DEFER_ITE, AY_SAT_THEORY_DISPATCH_STATUS_SKIP,
};

const LANES: usize = 4;
const MAX_CLAUSE_LEN: usize = 64;
const SENTINEL: i32 = i32::MIN;
const NO_REASON: u32 = u32::MAX;
const NO_ITE_COND_VAR: u32 = AY_SAT_THEORY_DISPATCH_NO_ITE_COND_VAR as u32;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TheoryAtomEntry {
    term_id: u32,
    ite_cond_var: u32,
    is_then_branch: bool,
}

impl TheoryAtomEntry {
    fn unguarded(term_id: u32) -> Self {
        Self {
            term_id,
            ite_cond_var: NO_ITE_COND_VAR,
            is_then_branch: false,
        }
    }

    fn guarded(term_id: u32, ite_cond_var: u32, is_then_branch: bool) -> Self {
        Self {
            term_id,
            ite_cond_var,
            is_then_branch,
        }
    }

    fn is_ite_guarded(self) -> bool {
        self.ite_cond_var != NO_ITE_COND_VAR
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TheoryDispatchResult {
    Assert { term_id: u32, value: bool },
    DeferIte { term_id: u32, value: bool },
    Skip,
}

impl TheoryDispatchResult {
    fn status(self) -> i32 {
        match self {
            Self::Skip => AY_SAT_THEORY_DISPATCH_STATUS_SKIP,
            Self::Assert { .. } => AY_SAT_THEORY_DISPATCH_STATUS_ASSERT,
            Self::DeferIte { .. } => AY_SAT_THEORY_DISPATCH_STATUS_DEFER_ITE,
        }
    }

    fn term_id(self) -> u32 {
        match self {
            Self::Assert { term_id, .. } | Self::DeferIte { term_id, .. } => term_id,
            Self::Skip => 0,
        }
    }

    fn value(self) -> bool {
        match self {
            Self::Assert { value, .. } | Self::DeferIte { value, .. } => value,
            Self::Skip => false,
        }
    }

    fn packed(self) -> i64 {
        let status = self.status() as u64;
        let value = if self.value() {
            AY_SAT_THEORY_DISPATCH_RESULT_VALUE_BIT
        } else {
            0
        };
        let term = u64::from(self.term_id()) << AY_SAT_THEORY_DISPATCH_RESULT_TERM_SHIFT;
        (status | value | term) as i64
    }
}

fn unpack_theory_dispatch_result(packed: i64) -> (i32, u32, bool) {
    let packed = packed as u64;
    let status = (packed & AY_SAT_THEORY_DISPATCH_RESULT_STATUS_MASK) as i32;
    let term_id = (packed >> AY_SAT_THEORY_DISPATCH_RESULT_TERM_SHIFT) as u32;
    let value = packed & AY_SAT_THEORY_DISPATCH_RESULT_VALUE_BIT != 0;
    (status, term_id, value)
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PaddedChunk {
    lanes: [i32; LANES],
    valid_mask: i32,
}

fn contains4_masked_reference(lanes: [i32; LANES], literal: i32, valid_mask: i32) -> i32 {
    let mut mask = 0i32;
    for (lane, value) in lanes.iter().enumerate() {
        let lane_bit = 1i32 << lane;
        if valid_mask & lane_bit != 0 && *value == literal {
            mask |= lane_bit;
        }
    }
    mask
}

fn contains4_masked_candidate(lanes: [i32; LANES], literal: i32, valid_mask: i32) -> i32 {
    let lane0 = if lanes[0] == literal { 1 } else { 0 } & valid_mask;
    let lane1 = if lanes[1] == literal { 2 } else { 0 } & valid_mask;
    let lane2 = if lanes[2] == literal { 4 } else { 0 } & valid_mask;
    let lane3 = if lanes[3] == literal { 8 } else { 0 } & valid_mask;
    lane0 | lane1 | lane2 | lane3
}

fn padded_chunks(clause: &[i32]) -> Vec<PaddedChunk> {
    if clause.is_empty() {
        return vec![PaddedChunk {
            lanes: [SENTINEL; LANES],
            valid_mask: 0,
        }];
    }

    clause
        .chunks(LANES)
        .map(|chunk| {
            let mut lanes = [SENTINEL; LANES];
            let mut valid_mask = 0i32;
            for (lane, literal) in chunk.iter().enumerate() {
                lanes[lane] = *literal;
                valid_mask |= 1 << lane;
            }
            PaddedChunk { lanes, valid_mask }
        })
        .collect()
}

fn contains_literal_reference(clause: &[i32], literal: i32) -> bool {
    clause.contains(&literal)
}

fn contains_literal_via_contains4(clause: &[i32], literal: i32) -> bool {
    padded_chunks(clause)
        .iter()
        .any(|chunk| contains4_masked_candidate(chunk.lanes, literal, chunk.valid_mask) != 0)
}

fn minimize_keep_drop_reference(
    var_level: u32,
    trail_pos: u32,
    reason: u32,
    min_flags: u8,
    level_seen_count: u32,
    level_seen_trail: u32,
    decision_level: u32,
) -> i32 {
    if var_level == 0 {
        return AY_SAT_MINIMIZE_CLASSIFY_DROP;
    }
    if min_flags & ((AY_SAT_MINIMIZE_MIN_REMOVABLE_FLAG | AY_SAT_MINIMIZE_MIN_KEEP_FLAG) as u8) != 0
    {
        return AY_SAT_MINIMIZE_CLASSIFY_DROP;
    }
    if min_flags & AY_SAT_MINIMIZE_MIN_POISON_FLAG as u8 != 0 {
        return AY_SAT_MINIMIZE_CLASSIFY_KEEP;
    }
    if var_level == decision_level {
        return AY_SAT_MINIMIZE_CLASSIFY_KEEP;
    }
    if reason == NO_REASON {
        return AY_SAT_MINIMIZE_CLASSIFY_KEEP;
    }
    if level_seen_count < 2 {
        return AY_SAT_MINIMIZE_CLASSIFY_KEEP;
    }
    if trail_pos <= level_seen_trail {
        return AY_SAT_MINIMIZE_CLASSIFY_KEEP;
    }
    AY_SAT_MINIMIZE_CLASSIFY_CHECK
}

fn minimize_keep_drop_candidate(
    var_level: u32,
    trail_pos: u32,
    reason: u32,
    min_flags: u8,
    level_seen_count: u32,
    level_seen_trail: u32,
    decision_level: u32,
) -> i32 {
    let cached_drop = min_flags
        & ((AY_SAT_MINIMIZE_MIN_REMOVABLE_FLAG | AY_SAT_MINIMIZE_MIN_KEEP_FLAG) as u8)
        != 0;
    let keep_abort = min_flags & AY_SAT_MINIMIZE_MIN_POISON_FLAG as u8 != 0
        || var_level == decision_level
        || reason == NO_REASON
        || level_seen_count < 2
        || trail_pos <= level_seen_trail;

    if var_level == 0 || cached_drop {
        AY_SAT_MINIMIZE_CLASSIFY_DROP
    } else if keep_abort {
        AY_SAT_MINIMIZE_CLASSIFY_KEEP
    } else {
        AY_SAT_MINIMIZE_CLASSIFY_CHECK
    }
}

fn theory_dispatch_reference(
    table: &[Option<TheoryAtomEntry>],
    var_id: u32,
    value: bool,
    cond_assignment: Option<(u32, bool)>,
    decision_level: u32,
) -> TheoryDispatchResult {
    let Some(Some(entry)) = table.get(var_id as usize) else {
        return TheoryDispatchResult::Skip;
    };

    if entry.is_ite_guarded() && decision_level > 0 {
        let cond_value = cond_assignment.and_then(|(cond_var, cond_value)| {
            (cond_var == entry.ite_cond_var).then_some(cond_value)
        });
        if let Some(cond_value) = cond_value
            && cond_value != entry.is_then_branch
        {
            return TheoryDispatchResult::DeferIte {
                term_id: entry.term_id,
                value,
            };
        }
    }

    TheoryDispatchResult::Assert {
        term_id: entry.term_id,
        value,
    }
}

fn theory_dispatch_candidate(
    var_id: u32,
    table_len: u32,
    entry: Option<TheoryAtomEntry>,
    value: bool,
    cond_assignment: Option<(u32, bool)>,
    decision_level: u32,
) -> TheoryDispatchResult {
    if var_id >= table_len {
        return TheoryDispatchResult::Skip;
    }
    let Some(entry) = entry else {
        return TheoryDispatchResult::Skip;
    };
    if entry.is_ite_guarded() && decision_level > 0 {
        let cond_value = cond_assignment.and_then(|(cond_var, cond_value)| {
            (cond_var == entry.ite_cond_var).then_some(cond_value)
        });
        if cond_value.is_some_and(|cond_value| cond_value != entry.is_then_branch) {
            return TheoryDispatchResult::DeferIte {
                term_id: entry.term_id,
                value,
            };
        }
    }
    TheoryDispatchResult::Assert {
        term_id: entry.term_id,
        value,
    }
}

fn theory_dispatch_entry_from_contract_args(
    entry_present: i32,
    term_id: i32,
    guard_flags: i32,
) -> Option<TheoryAtomEntry> {
    (entry_present != 0).then_some(TheoryAtomEntry {
        term_id: term_id as u32,
        ite_cond_var: if guard_flags & AY_SAT_THEORY_DISPATCH_FLAG_ITE_GUARDED != 0 {
            0
        } else {
            NO_ITE_COND_VAR
        },
        is_then_branch: guard_flags & AY_SAT_THEORY_DISPATCH_FLAG_THEN_BRANCH != 0,
    })
}

fn theory_dispatch_guard_flags(
    guarded: bool,
    is_then_branch: bool,
    cond_assigned: bool,
    cond_value: bool,
) -> i32 {
    let mut flags = 0;
    if guarded {
        flags |= AY_SAT_THEORY_DISPATCH_FLAG_ITE_GUARDED;
    }
    if is_then_branch {
        flags |= AY_SAT_THEORY_DISPATCH_FLAG_THEN_BRANCH;
    }
    if cond_assigned {
        flags |= AY_SAT_THEORY_DISPATCH_FLAG_COND_ASSIGNED;
    }
    if cond_value {
        flags |= AY_SAT_THEORY_DISPATCH_FLAG_COND_VALUE;
    }
    flags
}

fn theory_dispatch_candidate_from_contract_args(
    var_id: i32,
    table_len: i32,
    entry_present: i32,
    term_id: i32,
    assignment_value: i32,
    guard_flags: i32,
    decision_level: i32,
) -> i64 {
    let entry = theory_dispatch_entry_from_contract_args(entry_present, term_id, guard_flags);
    let cond_assignment = (guard_flags & AY_SAT_THEORY_DISPATCH_FLAG_COND_ASSIGNED != 0)
        .then_some((0, guard_flags & AY_SAT_THEORY_DISPATCH_FLAG_COND_VALUE != 0));
    theory_dispatch_candidate(
        var_id as u32,
        table_len as u32,
        entry,
        assignment_value != 0,
        cond_assignment,
        decision_level as u32,
    )
    .packed()
}

#[test]
fn contains4_masked_matches_reference_for_fixture_edge_cases() {
    let cases = [
        ([1, 2, 3, 4], 3, 0b1111, 0b0100),
        ([9, 9, 9, 9], 9, 0b0101, 0b0101),
        ([7, 8, 7, 8], 7, 0b1010, 0),
        ([SENTINEL, 42, SENTINEL, 42], SENTINEL, 0b1010, 0),
        ([SENTINEL, 42, SENTINEL, 42], SENTINEL, 0b0101, 0b0101),
        ([-1, -2, -3, -4], -2, 0b1111_0010, 0b0010),
        ([i32::MIN, i32::MAX, 0, -0x400], i32::MAX, 0b1111, 0b0010),
    ];

    for (lanes, literal, valid_mask, expected) in cases {
        assert_eq!(
            contains4_masked_reference(lanes, literal, valid_mask),
            expected
        );
        assert_eq!(
            contains4_masked_candidate(lanes, literal, valid_mask),
            expected
        );
        assert_eq!(
            contains4_masked_candidate(lanes, literal, valid_mask) & !0b1111,
            0
        );
    }
}

#[test]
fn contains_literal_fold_ignores_padded_lanes() {
    let clause = [11, 17, 23, 29, 31, 37];
    assert!(contains_literal_reference(&clause, 31));
    assert!(contains_literal_via_contains4(&clause, 31));
    assert!(!contains_literal_reference(&clause, SENTINEL));
    assert!(!contains_literal_via_contains4(&clause, SENTINEL));

    let padded = padded_chunks(&clause);
    assert_eq!(padded.len(), 2);
    assert_eq!(padded[1].valid_mask, 0b0011);
    assert_eq!(
        contains4_masked_candidate(padded[1].lanes, SENTINEL, padded[1].valid_mask),
        0
    );
}

#[test]
fn minimize_keep_drop_classification_matches_reference_for_fixture_edge_cases() {
    let cases = [
        (0, 0, 42, 0, 0, u32::MAX, 5, AY_SAT_MINIMIZE_CLASSIFY_DROP),
        (
            3,
            10,
            100,
            AY_SAT_MINIMIZE_MIN_REMOVABLE_FLAG as u8,
            0,
            u32::MAX,
            5,
            AY_SAT_MINIMIZE_CLASSIFY_DROP,
        ),
        (
            3,
            10,
            100,
            AY_SAT_MINIMIZE_MIN_KEEP_FLAG as u8,
            0,
            u32::MAX,
            5,
            AY_SAT_MINIMIZE_CLASSIFY_DROP,
        ),
        (
            3,
            10,
            100,
            AY_SAT_MINIMIZE_MIN_POISON_FLAG as u8,
            5,
            0,
            5,
            AY_SAT_MINIMIZE_CLASSIFY_KEEP,
        ),
        (5, 10, 100, 0, 5, 0, 5, AY_SAT_MINIMIZE_CLASSIFY_KEEP),
        (3, 10, NO_REASON, 0, 5, 0, 5, AY_SAT_MINIMIZE_CLASSIFY_KEEP),
        (3, 10, 100, 0, 1, 0, 5, AY_SAT_MINIMIZE_CLASSIFY_KEEP),
        (3, 10, 100, 0, 5, 10, 5, AY_SAT_MINIMIZE_CLASSIFY_KEEP),
        (3, 11, 100, 0, 5, 10, 5, AY_SAT_MINIMIZE_CLASSIFY_CHECK),
    ];

    for (
        var_level,
        trail_pos,
        reason,
        min_flags,
        level_seen_count,
        level_seen_trail,
        decision_level,
        expected,
    ) in cases
    {
        assert_eq!(
            minimize_keep_drop_reference(
                var_level,
                trail_pos,
                reason,
                min_flags,
                level_seen_count,
                level_seen_trail,
                decision_level,
            ),
            expected
        );
        assert_eq!(
            minimize_keep_drop_candidate(
                var_level,
                trail_pos,
                reason,
                min_flags,
                level_seen_count,
                level_seen_trail,
                decision_level,
            ),
            expected
        );
    }
}

#[test]
fn theory_dispatch_assignment_matches_local_private_reference_edge_cases() {
    let mut table = vec![None; 16];
    table[3] = Some(TheoryAtomEntry::unguarded(30));
    table[4] = Some(TheoryAtomEntry::guarded(40, 1, true));
    table[5] = Some(TheoryAtomEntry::guarded(50, 1, false));

    let cases = [
        (0, true, None, 1, TheoryDispatchResult::Skip),
        (20, true, None, 1, TheoryDispatchResult::Skip),
        (
            3,
            true,
            None,
            1,
            TheoryDispatchResult::Assert {
                term_id: 30,
                value: true,
            },
        ),
        (
            3,
            false,
            Some((1, false)),
            1,
            TheoryDispatchResult::Assert {
                term_id: 30,
                value: false,
            },
        ),
        (
            4,
            true,
            Some((1, false)),
            1,
            TheoryDispatchResult::DeferIte {
                term_id: 40,
                value: true,
            },
        ),
        (
            4,
            true,
            Some((1, true)),
            1,
            TheoryDispatchResult::Assert {
                term_id: 40,
                value: true,
            },
        ),
        (
            4,
            true,
            None,
            1,
            TheoryDispatchResult::Assert {
                term_id: 40,
                value: true,
            },
        ),
        (
            4,
            true,
            Some((1, false)),
            0,
            TheoryDispatchResult::Assert {
                term_id: 40,
                value: true,
            },
        ),
        (
            5,
            false,
            Some((1, true)),
            3,
            TheoryDispatchResult::DeferIte {
                term_id: 50,
                value: false,
            },
        ),
    ];

    for (var_id, value, cond_assignment, decision_level, expected) in cases {
        let reference =
            theory_dispatch_reference(&table, var_id, value, cond_assignment, decision_level);
        let candidate = theory_dispatch_candidate(
            var_id,
            table.len() as u32,
            table.get(var_id as usize).copied().flatten(),
            value,
            cond_assignment,
            decision_level,
        );
        assert_eq!(reference, expected);
        assert_eq!(candidate, expected);
        assert_eq!(
            unpack_theory_dispatch_result(candidate.packed()).0,
            expected.status()
        );
        assert_eq!(
            unpack_theory_dispatch_result(candidate.packed()),
            (expected.status(), expected.term_id(), expected.value())
        );
    }
}

#[test]
fn theory_dispatch_contract_arg_candidate_uses_ay_sentinel_and_bool_normalization() {
    let no_guard = theory_dispatch_candidate_from_contract_args(7, 8, 1, 123, 99, 0, 4);
    assert_eq!(
        unpack_theory_dispatch_result(no_guard),
        (AY_SAT_THEORY_DISPATCH_STATUS_ASSERT, 123, true)
    );

    let defer_flags = theory_dispatch_guard_flags(true, true, true, false);
    let defer_inactive =
        theory_dispatch_candidate_from_contract_args(2, 8, 1, 77, 0, defer_flags, 4);
    assert_eq!(
        unpack_theory_dispatch_result(defer_inactive),
        (AY_SAT_THEORY_DISPATCH_STATUS_DEFER_ITE, 77, false)
    );

    let out_of_bounds =
        theory_dispatch_candidate_from_contract_args(9, 8, 1, 77, 1, defer_flags, 4);
    assert_eq!(
        unpack_theory_dispatch_result(out_of_bounds),
        (AY_SAT_THEORY_DISPATCH_STATUS_SKIP, 0, false)
    );
}

proptest! {
    #[test]
    fn contains4_candidate_matches_reference_for_all_lane_masks(
        lanes in prop::array::uniform4(-2048i32..=2048),
        literal in -2048i32..=2048,
        valid_mask in any::<i32>(),
    ) {
        let expected = contains4_masked_reference(lanes, literal, valid_mask);
        let actual = contains4_masked_candidate(lanes, literal, valid_mask);
        prop_assert_eq!(actual, expected);
        prop_assert_eq!(actual & !0b1111, 0);
    }

    #[test]
    fn contains_literal_fold_matches_scalar_reference(
        clause in prop::collection::vec(-4096i32..=4096, 0..=MAX_CLAUSE_LEN),
        literal in -4096i32..=4096,
    ) {
        prop_assert_eq!(
            contains_literal_via_contains4(&clause, literal),
            contains_literal_reference(&clause, literal)
        );
    }

    #[test]
    fn minimize_keep_drop_candidate_matches_reference(
        var_level in 0u32..=128,
        trail_pos in 0u32..=4096,
        reason in prop_oneof![Just(NO_REASON), 0u32..=4096],
        min_flags in any::<u8>(),
        level_seen_count in 0u32..=8,
        level_seen_trail in 0u32..=4096,
        decision_level in 0u32..=128,
    ) {
        let expected = minimize_keep_drop_reference(
            var_level,
            trail_pos,
            reason,
            min_flags,
            level_seen_count,
            level_seen_trail,
            decision_level,
        );
        let actual = minimize_keep_drop_candidate(
            var_level,
            trail_pos,
            reason,
            min_flags,
            level_seen_count,
            level_seen_trail,
            decision_level,
        );
        prop_assert_eq!(actual, expected);
        prop_assert!((AY_SAT_MINIMIZE_CLASSIFY_DROP..=AY_SAT_MINIMIZE_CLASSIFY_CHECK)
            .contains(&actual));
    }

    #[test]
    fn theory_dispatch_candidate_matches_local_private_reference(
        table_len in 0u32..=32,
        var_id in 0u32..=40,
        entry_present in any::<bool>(),
        term_id in any::<u32>(),
        value in any::<bool>(),
        guarded in any::<bool>(),
        cond_var in 0u32..=40,
        is_then_branch in any::<bool>(),
        cond_assigned in any::<bool>(),
        cond_value in any::<bool>(),
        cond_matches_guard in any::<bool>(),
        decision_level in 0u32..=8,
    ) {
        let table_len = table_len as usize;
        let mut table = vec![None; table_len];
        let entry = entry_present.then_some(if guarded {
            TheoryAtomEntry::guarded(term_id, cond_var, is_then_branch)
        } else {
            TheoryAtomEntry::unguarded(term_id)
        });
        if (var_id as usize) < table_len {
            table[var_id as usize] = entry;
        }

        let cond_assignment = cond_assigned.then_some((
            if cond_matches_guard { cond_var } else { cond_var.saturating_add(1) },
            cond_value,
        ));
        let expected =
            theory_dispatch_reference(&table, var_id, value, cond_assignment, decision_level);
        let actual = theory_dispatch_candidate(
            var_id,
            table_len as u32,
            entry,
            value,
            cond_assignment,
            decision_level,
        );

        prop_assert_eq!(actual, expected);
        prop_assert_eq!(
            unpack_theory_dispatch_result(actual.packed()),
            (expected.status(), expected.term_id(), expected.value())
        );
    }
}
