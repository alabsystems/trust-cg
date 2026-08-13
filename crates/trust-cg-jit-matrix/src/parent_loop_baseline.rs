// trust-cg-jit-matrix/src/parent_loop_baseline.rs - Native Rust parent-loop
// state enumerator baseline for TY-JIT'd TLA+ workloads.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::HashSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct State(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Action {
    pub guard_mask: u64,
    pub guard_value: u64,
    pub set_mask: u64,
    pub set_value: u64,
}

#[derive(Clone, Debug)]
pub struct TransitionSystem {
    pub init: State,
    pub actions: Vec<Action>,
    pub invariant_mask: u64,
    pub invariant_value: u64,
}

#[derive(Clone, Debug)]
pub struct ParentLoopState {
    pub frontier: Vec<State>,
    pub visited: HashSet<State>,
    pub parent_count: u64,
    pub generated_count: u64,
    pub parent_digest: u64,
    pub fingerprint: u64,
    pub invariant_violations: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StepResult {
    Continued,
    FrontierEmpty,
    InvariantViolation(State),
}

impl ParentLoopState {
    pub fn new(system: &TransitionSystem) -> Self {
        let mut visited = HashSet::new();
        visited.insert(system.init);
        Self {
            frontier: vec![system.init],
            visited,
            parent_count: 0,
            generated_count: 0,
            parent_digest: 0,
            fingerprint: 0,
            invariant_violations: 0,
        }
    }
}

// Mixing formula: state.wrapping_mul(0x9e3779b97f4a7c15).rotate_left(13)
// matches TY's wire-format hash, enabling direct
// comparison against TY's emitted telemetry slots.
fn mix(state: u64) -> u64 {
    state.wrapping_mul(0x9e3779b97f4a7c15).rotate_left(13)
}

fn action_enabled(state: u64, action: &Action) -> bool {
    (state & action.guard_mask) == action.guard_value
}

fn apply_action(state: u64, action: &Action) -> u64 {
    (state & !action.set_mask) | action.set_value
}

fn invariant_holds(state: u64, system: &TransitionSystem) -> bool {
    (state & system.invariant_mask) == system.invariant_value
}

pub fn explore_one_step(state: &mut ParentLoopState, system: &TransitionSystem) -> StepResult {
    let parent = match state.frontier.pop() {
        Some(p) => p,
        None => return StepResult::FrontierEmpty,
    };

    state.parent_count += 1;
    state.parent_digest = state.parent_digest.wrapping_add(mix(parent.0));

    for action in &system.actions {
        if !action_enabled(parent.0, action) {
            continue;
        }
        let succ_raw = apply_action(parent.0, action);
        let succ = State(succ_raw);
        state.generated_count += 1;
        state.fingerprint = state.fingerprint.wrapping_add(mix(succ_raw));

        if !invariant_holds(succ_raw, system) {
            state.invariant_violations += 1;
            return StepResult::InvariantViolation(succ);
        }

        if state.visited.insert(succ) {
            state.frontier.push(succ);
        }
    }

    StepResult::Continued
}

pub fn random_transition_system(num_vars: u32, num_actions: usize, seed: u64) -> TransitionSystem {
    assert!(num_vars <= 64);
    let var_mask: u64 = if num_vars == 64 {
        u64::MAX
    } else {
        (1u64 << num_vars) - 1
    };

    let mut rng = if seed == 0 {
        0x9E37_79B9_7F4A_7C15
    } else {
        seed
    };

    let init = State(xorshift64(&mut rng) & var_mask);

    let mut actions = Vec::with_capacity(num_actions);
    for _ in 0..num_actions {
        let guard_mask = xorshift64(&mut rng) & var_mask;
        let guard_value = xorshift64(&mut rng) & guard_mask;
        let set_mask = xorshift64(&mut rng) & var_mask;
        let set_value = xorshift64(&mut rng) & set_mask;
        actions.push(Action {
            guard_mask,
            guard_value,
            set_mask,
            set_value,
        });
    }

    let invariant_mask = xorshift64(&mut rng) & var_mask;
    let invariant_value = xorshift64(&mut rng) & invariant_mask;

    TransitionSystem {
        init,
        actions,
        invariant_mask,
        invariant_value,
    }
}

fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_enabled_actions_yields_continued_then_empty() {
        let system = TransitionSystem {
            init: State(0),
            actions: vec![Action {
                guard_mask: 0x1,
                guard_value: 0x1,
                set_mask: 0x2,
                set_value: 0x2,
            }],
            invariant_mask: 0,
            invariant_value: 0,
        };
        let mut state = ParentLoopState::new(&system);
        let r1 = explore_one_step(&mut state, &system);
        assert_eq!(r1, StepResult::Continued);
        let r2 = explore_one_step(&mut state, &system);
        assert_eq!(r2, StepResult::FrontierEmpty);
        assert_eq!(state.parent_count, 1);
        assert_eq!(state.generated_count, 0);
    }

    #[test]
    fn two_state_cycle_visits_two_states() {
        let toggle = Action {
            guard_mask: 0,
            guard_value: 0,
            set_mask: 0x1,
            set_value: 0x1,
        };
        let untoggle = Action {
            guard_mask: 0x1,
            guard_value: 0x1,
            set_mask: 0x1,
            set_value: 0x0,
        };
        let system = TransitionSystem {
            init: State(0),
            actions: vec![toggle, untoggle],
            invariant_mask: 0,
            invariant_value: 0,
        };
        let mut state = ParentLoopState::new(&system);
        loop {
            match explore_one_step(&mut state, &system) {
                StepResult::Continued => continue,
                StepResult::FrontierEmpty => break,
                StepResult::InvariantViolation(_) => panic!("unexpected violation"),
            }
        }
        assert_eq!(state.visited.len(), 2);
        assert!(state.visited.contains(&State(0)));
        assert!(state.visited.contains(&State(1)));
    }

    #[test]
    fn invariant_violation_detected() {
        let bad = Action {
            guard_mask: 0,
            guard_value: 0,
            set_mask: 0x1,
            set_value: 0x1,
        };
        let system = TransitionSystem {
            init: State(0),
            actions: vec![bad],
            invariant_mask: 0x1,
            invariant_value: 0x0,
        };
        let mut state = ParentLoopState::new(&system);
        let result = explore_one_step(&mut state, &system);
        match result {
            StepResult::InvariantViolation(s) => assert_eq!(s, State(1)),
            other => panic!("expected violation, got {:?}", other),
        }
        assert_eq!(state.invariant_violations, 1);
    }

    #[test]
    fn determinism_same_seed_same_telemetry() {
        let system = random_transition_system(8, 16, 0xDEAD_BEEF);
        let mut a = ParentLoopState::new(&system);
        let mut b = ParentLoopState::new(&system);

        for _ in 0..200 {
            let ra = explore_one_step(&mut a, &system);
            let rb = explore_one_step(&mut b, &system);
            assert_eq!(ra, rb);
            assert_eq!(a.parent_digest, b.parent_digest);
            assert_eq!(a.fingerprint, b.fingerprint);
            assert_eq!(a.parent_count, b.parent_count);
            assert_eq!(a.generated_count, b.generated_count);
            if matches!(ra, StepResult::FrontierEmpty) {
                break;
            }
        }
    }

    #[test]
    fn counters_increment_correctly() {
        let a1 = Action {
            guard_mask: 0,
            guard_value: 0,
            set_mask: 0x1,
            set_value: 0x1,
        };
        let a2 = Action {
            guard_mask: 0,
            guard_value: 0,
            set_mask: 0x2,
            set_value: 0x2,
        };
        let system = TransitionSystem {
            init: State(0),
            actions: vec![a1, a2],
            invariant_mask: 0,
            invariant_value: 0,
        };
        let mut state = ParentLoopState::new(&system);
        let r = explore_one_step(&mut state, &system);
        assert_eq!(r, StepResult::Continued);
        assert_eq!(state.parent_count, 1);
        assert_eq!(state.generated_count, 2);

        let _ = explore_one_step(&mut state, &system);
        assert_eq!(state.parent_count, 2);
        assert!(state.generated_count >= 4);
    }
}
