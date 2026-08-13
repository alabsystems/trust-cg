// Symbolic execution: use-after-free detector
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Symbolic execution: use-after-free detector (Phase 1d).
//!
//! This evaluator-only checker is the UAF companion to [`crate::fsym_null`],
//! [`crate::fsym_arith`], and [`crate::fsym_bounds`]. It tracks a small event
//! stream over concrete object identifiers and reports statically analyzable
//! loads, stores, generic uses, and double-frees after a known free. Symbolic
//! object identities intentionally remain [`FsymVerdict::Unknown`] for future
//! SMT/provenance escalation.

use crate::fsym_null::{FsymVerdict, PathContext, guards_hold};
use crate::smt::{EvalResult, SmtExpr};
use std::collections::{HashMap, HashSet};

/// Memory/lifetime event kind understood by the fast UAF evaluator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UafEventKind {
    /// Read from an object.
    Load,
    /// Write to an object.
    Store,
    /// Free an object. A second free of the same known object is UB.
    Free,
    /// Generic non-load/store use of an object or pointer-derived value.
    Use,
}

/// One lifetime/memory event in program order.
#[derive(Debug, Clone)]
pub struct UafEvent {
    /// Human-friendly label, e.g. "bb3/inst12 load".
    pub label: String,
    /// Event kind.
    pub kind: UafEventKind,
    /// Object identity expression. Only concrete, env-independent bitvector
    /// identities are handled by this evaluator slice.
    pub object: SmtExpr,
}

/// A labeled event stream to scan under one path context.
#[derive(Debug, Clone)]
pub struct UafTrace {
    /// Human-friendly trace label.
    pub label: String,
    /// Events in program order.
    pub events: Vec<UafEvent>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ObjectId {
    value: u128,
    width: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TraceOutcome {
    Safe,
    Ub,
    Unknown,
}

fn no_witness_found() -> FsymVerdict {
    FsymVerdict::Unknown {
        reason: "no witness found in evaluator; escalate to SMT".to_string(),
    }
}

fn concrete_object(expr: &SmtExpr) -> Option<ObjectId> {
    if !expr.free_vars().is_empty() {
        return None;
    }

    let width = expr.try_bv_width().ok()?;
    if width == 0 || width > 128 {
        return None;
    }

    let empty_env = HashMap::new();
    match expr.try_eval(&empty_env).ok()? {
        EvalResult::Bv(value) => Some(ObjectId {
            value: value as u128,
            width,
        }),
        EvalResult::Bv128(value) => Some(ObjectId { value, width }),
        // Poison (a trapping-op result) has no defined object id; fail closed.
        EvalResult::Bool(_)
        | EvalResult::Float(_)
        | EvalResult::Array { .. }
        | EvalResult::Poison => None,
    }
}

fn analyze_events(events: &[UafEvent]) -> TraceOutcome {
    let mut freed = HashSet::new();
    let mut saw_unknown_object = false;

    for event in events {
        let Some(object) = concrete_object(&event.object) else {
            saw_unknown_object = true;
            continue;
        };

        match event.kind {
            UafEventKind::Free => {
                if freed.contains(&object) {
                    return TraceOutcome::Ub;
                }
                freed.insert(object);
            }
            UafEventKind::Load | UafEventKind::Store | UafEventKind::Use => {
                if freed.contains(&object) {
                    return TraceOutcome::Ub;
                }
            }
        }
    }

    if saw_unknown_object {
        TraceOutcome::Unknown
    } else {
        TraceOutcome::Safe
    }
}

fn no_free_concrete_events(events: &[UafEvent]) -> bool {
    events
        .iter()
        .all(|event| event.kind != UafEventKind::Free && concrete_object(&event.object).is_some())
}

/// Check one event stream against its path context.
///
/// The fast evaluator reports:
/// - [`FsymVerdict::Safe`] when all reachable events reference concrete objects
///   and no use/double-free occurs after a known free.
/// - [`FsymVerdict::Ub`] when a candidate environment satisfies the path guards
///   and the concrete event stream contains load/store/use/free after free.
/// - [`FsymVerdict::Unknown`] when the path is unreached by the supplied
///   witnesses, object identity is symbolic/unknown, or no evaluator witness is
///   found and SMT/provenance reasoning would be needed.
///
/// Concrete objects are assumed live on entry. A `Free` event marks the object
/// freed for subsequent events in the same trace.
pub fn check_uaf_ub(events: &[UafEvent], ctx: &PathContext) -> FsymVerdict {
    if no_free_concrete_events(events) {
        return FsymVerdict::Safe;
    }

    let empty_env = HashMap::new();
    let candidates: &[HashMap<String, u64>] = if ctx.witness_candidates.is_empty() {
        std::slice::from_ref(&empty_env)
    } else {
        ctx.witness_candidates.as_slice()
    };

    let mut saw_reachable_candidate = false;
    let mut saw_unknown_object = false;

    for env in candidates {
        if !guards_hold(&ctx.guards, env) {
            continue;
        }

        saw_reachable_candidate = true;
        match analyze_events(events) {
            TraceOutcome::Ub => {
                return FsymVerdict::Ub {
                    witness: env.clone(),
                };
            }
            TraceOutcome::Unknown => saw_unknown_object = true,
            TraceOutcome::Safe => {}
        }
    }

    if saw_reachable_candidate && !saw_unknown_object {
        FsymVerdict::Safe
    } else {
        no_witness_found()
    }
}

/// Scan a collection of UAF traces sharing one path context; return each
/// verdict tagged with its trace label.
#[cfg(feature = "fsym")]
pub fn run_uaf_scan(traces: &[UafTrace], ctx: &PathContext) -> Vec<(String, FsymVerdict)> {
    traces
        .iter()
        .map(|trace| (trace.label.clone(), check_uaf_ub(&trace.events, ctx)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{UafEvent, UafEventKind, check_uaf_ub};
    use crate::fsym_null::{FsymVerdict, PathContext};
    use crate::smt::SmtExpr;
    use std::collections::HashMap;

    fn event(kind: UafEventKind, object: SmtExpr) -> UafEvent {
        UafEvent {
            label: "uaf-event".to_string(),
            kind,
            object,
        }
    }

    fn obj(value: u64) -> SmtExpr {
        SmtExpr::bv_const(value, 64)
    }

    fn ctx(guards: Vec<SmtExpr>, witness_candidates: Vec<HashMap<String, u64>>) -> PathContext {
        PathContext {
            guards,
            witness_candidates,
        }
    }

    fn unknown() -> FsymVerdict {
        FsymVerdict::Unknown {
            reason: "no witness found in evaluator; escalate to SMT".to_string(),
        }
    }

    #[test]
    fn concrete_safe_use_before_free_is_safe() {
        let events = vec![
            event(UafEventKind::Load, obj(1)),
            event(UafEventKind::Store, obj(1)),
            event(UafEventKind::Use, obj(1)),
            event(UafEventKind::Free, obj(1)),
        ];

        assert_eq!(
            check_uaf_ub(&events, &ctx(vec![], vec![])),
            FsymVerdict::Safe
        );
    }

    #[test]
    fn concrete_load_after_free_is_ub() {
        let events = vec![
            event(UafEventKind::Free, obj(1)),
            event(UafEventKind::Load, obj(1)),
        ];

        assert_eq!(
            check_uaf_ub(&events, &ctx(vec![], vec![])),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn concrete_store_after_free_is_ub() {
        let events = vec![
            event(UafEventKind::Free, obj(1)),
            event(UafEventKind::Store, obj(1)),
        ];

        assert_eq!(
            check_uaf_ub(&events, &ctx(vec![], vec![])),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn concrete_generic_use_after_free_is_ub() {
        let events = vec![
            event(UafEventKind::Free, obj(1)),
            event(UafEventKind::Use, obj(1)),
        ];

        assert_eq!(
            check_uaf_ub(&events, &ctx(vec![], vec![])),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn concrete_double_free_is_ub() {
        let events = vec![
            event(UafEventKind::Free, obj(1)),
            event(UafEventKind::Free, obj(1)),
        ];

        assert_eq!(
            check_uaf_ub(&events, &ctx(vec![], vec![])),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn false_guard_blocks_concrete_uaf() {
        let events = vec![
            event(UafEventKind::Free, obj(1)),
            event(UafEventKind::Load, obj(1)),
        ];

        assert_eq!(
            check_uaf_ub(&events, &ctx(vec![SmtExpr::bool_const(false)], vec![])),
            unknown()
        );
    }

    #[test]
    fn concrete_no_free_trace_with_symbolic_guard_is_safe() {
        let events = vec![
            event(UafEventKind::Load, obj(1)),
            event(UafEventKind::Store, obj(1)),
            event(UafEventKind::Use, obj(1)),
        ];

        assert_eq!(
            check_uaf_ub(&events, &ctx(vec![SmtExpr::var("g", 1)], vec![])),
            FsymVerdict::Safe
        );
    }

    #[test]
    fn no_free_symbolic_object_remains_unknown() {
        let events = vec![event(UafEventKind::Load, SmtExpr::var("p", 64))];

        assert_eq!(check_uaf_ub(&events, &ctx(vec![], vec![])), unknown());
    }

    #[test]
    fn i1_bitvector_guard_allows_uaf_witness() {
        let events = vec![
            event(UafEventKind::Free, obj(1)),
            event(UafEventKind::Load, obj(1)),
        ];
        let guard = SmtExpr::var("g", 1);
        let witness = HashMap::from([(String::from("g"), 1_u64)]);

        assert_eq!(
            check_uaf_ub(&events, &ctx(vec![guard], vec![witness.clone()])),
            FsymVerdict::Ub { witness }
        );
    }

    #[test]
    fn fork_branch_i1_else_path_allows_uaf_witness() {
        let events = vec![
            event(UafEventKind::Free, obj(1)),
            event(UafEventKind::Store, obj(1)),
        ];
        let witness = HashMap::from([(String::from("g"), 0_u64)]);
        let fork = ctx(vec![], vec![witness.clone()]).fork_branch(SmtExpr::var("g", 1));

        assert_eq!(check_uaf_ub(&events, &fork.then_ctx), unknown());
        assert_eq!(
            check_uaf_ub(&events, &fork.else_ctx),
            FsymVerdict::Ub { witness }
        );
    }

    #[test]
    fn symbolic_object_cases_remain_unknown() {
        let events = vec![
            event(UafEventKind::Free, SmtExpr::var("p", 64)),
            event(UafEventKind::Load, SmtExpr::var("p", 64)),
        ];
        let witness = HashMap::from([(String::from("p"), 1_u64)]);

        assert_eq!(
            check_uaf_ub(&events, &ctx(vec![], vec![witness])),
            unknown()
        );
    }

    #[cfg(feature = "fsym")]
    #[test]
    fn run_uaf_scan_tags_labels() {
        let traces = vec![super::UafTrace {
            label: "trace0".to_string(),
            events: vec![
                event(UafEventKind::Free, obj(1)),
                event(UafEventKind::Load, obj(1)),
            ],
        }];

        assert_eq!(
            super::run_uaf_scan(&traces, &ctx(vec![], vec![])),
            vec![(
                "trace0".to_string(),
                FsymVerdict::Ub {
                    witness: HashMap::new(),
                }
            )]
        );
    }
}
