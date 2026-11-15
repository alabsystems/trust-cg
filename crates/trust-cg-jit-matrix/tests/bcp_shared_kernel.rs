// trust-cg-jit-matrix/tests/bcp_shared_kernel.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The `bind_shared_kernel` constructors: every BCP kernel is compiled once per
// process and each formula gets only its own arena. These tests hold that to
// three things: the providers really share one code buffer, a provider built
// that way answers exactly as a freshly compiled one does (and, for the
// watched-literal kernel, as the native `BcpState` reference does), and
// providers sharing the code keep independent arenas, interleaved and across
// threads.

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use trust_cg_jit_matrix::bcp_baseline::{BcpState, Value};
use trust_cg_jit_matrix::bcp_kernel::BcpKernelProvider;
use trust_cg_jit_matrix::bcp_module_builder::{BCP_RESULT_CONFLICT, BCP_RESULT_OK};
use trust_cg_jit_matrix::jit_bcp_kernel::{
    JitBcpKernelProvider, JitBcpWatchedLiteralChunkedKernelProvider,
    JitBcpWatchedLiteralKernelProvider, JitBcpWithDecisionsProvider,
};
use trust_cg_jit_matrix::solver_kernel_abi::{KernelStatus, SolverKernelHandle};

/// One BCP problem: variable count, clauses, and decision literals in the
/// kernels' `(var << 1) | negated` input encoding.
struct Problem {
    num_vars: usize,
    clauses: Vec<Vec<i32>>,
    decisions: Vec<u32>,
}

fn problems() -> Vec<Problem> {
    let dec = |lit: i32| BcpKernelProvider::encode_literal(lit.unsigned_abs(), lit < 0);
    vec![
        // Nothing to propagate.
        Problem {
            num_vars: 3,
            clauses: vec![vec![1, 2], vec![-2, 3]],
            decisions: vec![],
        },
        // A unit clause.
        Problem {
            num_vars: 3,
            clauses: vec![vec![3]],
            decisions: vec![],
        },
        // Root-level conflict.
        Problem {
            num_vars: 3,
            clauses: vec![vec![1, 2, 3], vec![-1], vec![-2], vec![-3]],
            decisions: vec![],
        },
        // An implication chain started by a decision.
        Problem {
            num_vars: 6,
            clauses: vec![
                vec![-1, 2],
                vec![-2, 3],
                vec![-3, 4],
                vec![-4, 5],
                vec![-5, 6],
            ],
            decisions: vec![dec(1)],
        },
        // A decision whose implications falsify a clause.
        Problem {
            num_vars: 4,
            clauses: vec![vec![-1, 2], vec![-1, 3], vec![-2, -3, 4], vec![-4, -1]],
            decisions: vec![dec(1)],
        },
        // Two decisions on independent implication chains. (The kernel
        // assigns every decision before it propagates, while the reference
        // propagates after each one, so decisions that an earlier decision
        // implies or refutes would make the two disagree by construction.)
        Problem {
            num_vars: 6,
            clauses: vec![vec![-1, 2], vec![-2, 3], vec![-4, 5], vec![-5, 6]],
            decisions: vec![dec(1), dec(4)],
        },
    ]
}

/// The kernel's status plus the assignment it left, for variables 1..=n.
type Outcome = (KernelStatus, Vec<i8>);

fn values(arena: &[i8], num_vars: usize) -> Vec<i8> {
    (1..=num_vars).map(|v| arena[v]).collect()
}

fn run_scan(p: &JitBcpKernelProvider, num_vars: usize) -> Outcome {
    // The scan kernel has no decision input: its arena's trail holds only
    // the root assignments, so it is always called with none.
    let status = SolverKernelHandle::from_provider(p).call(&[]);
    (status, values(&p.arena_values(), num_vars))
}

fn run_with_decisions(p: &JitBcpWithDecisionsProvider, pr: &Problem) -> Outcome {
    p.reset_arena();
    let status = SolverKernelHandle::from_provider(p).call(&pr.decisions);
    (status, values(&p.arena_values(), pr.num_vars))
}

fn run_watched(p: &JitBcpWatchedLiteralKernelProvider, pr: &Problem) -> Outcome {
    p.reset_arena();
    let status = SolverKernelHandle::from_provider(p).call(&pr.decisions);
    (status, values(&p.arena_values(), pr.num_vars))
}

fn run_chunked(p: &JitBcpWatchedLiteralChunkedKernelProvider, pr: &Problem) -> Outcome {
    p.reset_arena();
    let status = SolverKernelHandle::from_provider(p).call(&pr.decisions);
    (status, values(&p.arena_values(), pr.num_vars))
}

fn watched(pr: &Problem) -> JitBcpWatchedLiteralKernelProvider {
    JitBcpWatchedLiteralKernelProvider::bind_shared_kernel(
        pr.num_vars,
        pr.clauses.clone(),
        pr.decisions.len(),
    )
    .expect("bind the shared watched-literal kernel")
}

/// The native watched-literal reference's `(result, assignment)`, computed the
/// way `bcp_watched_literal_trust_ir.rs` computes it.
fn reference(pr: &Problem) -> (u32, Vec<i8>) {
    let mut state = BcpState::new(pr.num_vars, pr.clauses.clone());
    let mut result = BCP_RESULT_OK;
    if state.propagate().is_some() {
        result = BCP_RESULT_CONFLICT;
    } else {
        for &enc in &pr.decisions {
            let var = (enc >> 1) as i32;
            state.assign(if enc & 1 == 0 { var } else { -var });
            if state.propagate().is_some() {
                result = BCP_RESULT_CONFLICT;
                break;
            }
        }
    }
    let vals = (1..=pr.num_vars)
        .map(|v| match state.value_of_lit(v as i32) {
            Value::Unassigned => 0,
            Value::True => 1,
            Value::False => -1,
        })
        .collect();
    (result, vals)
}

/// A kernel outcome against the native reference: the result code always, and
/// the assignment when there was no conflict (at a conflict the two
/// implementations may stop after different prefixes of the same propagation).
fn assert_as_reference(got: &Outcome, want: &(u32, Vec<i8>), what: &str) {
    assert_eq!(got.0.result, want.0, "{what}: result");
    if want.0 == BCP_RESULT_OK {
        assert_eq!(got.1, want.1, "{what}: assignment");
    }
}

#[test]
fn each_kernel_is_compiled_once_and_serves_every_formula() {
    let ps = problems();
    let (a, b) = (&ps[0], &ps[3]);

    let scan_a =
        JitBcpKernelProvider::bind_shared_kernel(a.num_vars, a.clauses.clone()).expect("bind scan");
    let scan_b =
        JitBcpKernelProvider::bind_shared_kernel(b.num_vars, b.clauses.clone()).expect("bind scan");
    assert!(std::ptr::eq(scan_a.buffer(), scan_b.buffer()));

    let dec_a = JitBcpWithDecisionsProvider::bind_shared_kernel(a.num_vars, a.clauses.clone(), 0)
        .expect("bind with-decisions");
    let dec_b = JitBcpWithDecisionsProvider::bind_shared_kernel(b.num_vars, b.clauses.clone(), 1)
        .expect("bind with-decisions");
    assert!(std::ptr::eq(dec_a.buffer(), dec_b.buffer()));
    assert_eq!(dec_a.entry_fn() as usize, dec_b.entry_fn() as usize);

    let (wa, wb) = (watched(a), watched(b));
    assert!(std::ptr::eq(wa.buffer(), wb.buffer()));
    assert_eq!(wa.entry_fn() as usize, wb.entry_fn() as usize);

    let ch_a = JitBcpWatchedLiteralChunkedKernelProvider::bind_shared_kernel(
        a.num_vars,
        a.clauses.clone(),
        0,
    )
    .expect("bind chunked");
    let ch_b = JitBcpWatchedLiteralChunkedKernelProvider::bind_shared_kernel(
        b.num_vars,
        b.clauses.clone(),
        1,
    )
    .expect("bind chunked");
    assert!(std::ptr::eq(ch_a.buffer(), ch_b.buffer()));
    assert_eq!(ch_a.entry_fn() as usize, ch_b.entry_fn() as usize);

    // `compile` is still a real compile: its code is its own.
    let compiled = JitBcpWatchedLiteralKernelProvider::compile(a.num_vars, a.clauses.clone(), 0)
        .expect("compile watched-literal");
    assert!(!std::ptr::eq(compiled.buffer(), wa.buffer()));
}

#[test]
fn shared_kernel_answers_as_a_fresh_compile_does() {
    for (i, pr) in problems().iter().enumerate() {
        let hint = pr.decisions.len();

        let shared = JitBcpKernelProvider::bind_shared_kernel(pr.num_vars, pr.clauses.clone())
            .expect("bind scan");
        let fresh =
            JitBcpKernelProvider::compile(pr.num_vars, pr.clauses.clone()).expect("compile scan");
        assert_eq!(
            run_scan(&shared, pr.num_vars),
            run_scan(&fresh, pr.num_vars),
            "scan, problem {i}"
        );

        let shared =
            JitBcpWithDecisionsProvider::bind_shared_kernel(pr.num_vars, pr.clauses.clone(), hint)
                .expect("bind with-decisions");
        let fresh = JitBcpWithDecisionsProvider::compile(pr.num_vars, pr.clauses.clone(), hint)
            .expect("compile with-decisions");
        assert_eq!(
            run_with_decisions(&shared, pr),
            run_with_decisions(&fresh, pr),
            "with-decisions, problem {i}"
        );

        let shared = watched(pr);
        let fresh =
            JitBcpWatchedLiteralKernelProvider::compile(pr.num_vars, pr.clauses.clone(), hint)
                .expect("compile watched-literal");
        let got = run_watched(&shared, pr);
        assert_eq!(got, run_watched(&fresh, pr), "watched-literal, problem {i}");
        assert_as_reference(
            &got,
            &reference(pr),
            &format!("watched-literal vs the native reference, problem {i}"),
        );

        let shared = JitBcpWatchedLiteralChunkedKernelProvider::bind_shared_kernel(
            pr.num_vars,
            pr.clauses.clone(),
            hint,
        )
        .expect("bind chunked");
        let fresh = JitBcpWatchedLiteralChunkedKernelProvider::compile(
            pr.num_vars,
            pr.clauses.clone(),
            hint,
        )
        .expect("compile chunked");
        assert_eq!(
            run_chunked(&shared, pr),
            run_chunked(&fresh, pr),
            "chunked watched-literal, problem {i}"
        );
    }
}

#[test]
fn providers_sharing_a_kernel_keep_their_own_arenas() {
    let ps = problems();
    let (pa, pb) = (&ps[3], &ps[4]);
    let (a, b) = (watched(pa), watched(pb));
    let (want_a, want_b) = (reference(pa), reference(pb));
    // Interleave the two formulas' calls, resetting only the one being run,
    // so a leak of either arena into the other shows up as a wrong answer.
    for round in 0..3 {
        let got_a = run_watched(&a, pa);
        let got_b = run_watched(&b, pb);
        assert_as_reference(&got_a, &want_a, &format!("formula a, round {round}"));
        assert_as_reference(&got_b, &want_b, &format!("formula b, round {round}"));
    }
}

#[test]
fn shared_kernel_is_correct_under_concurrent_use() {
    let ps = problems();
    let code_addresses: Vec<usize> = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..8)
            .map(|t| {
                let pr = &ps[t % ps.len()];
                scope.spawn(move || {
                    let provider = watched(pr);
                    let want = reference(pr);
                    for iteration in 0..200 {
                        let got = run_watched(&provider, pr);
                        assert_as_reference(
                            &got,
                            &want,
                            &format!("thread {t}, iteration {iteration}"),
                        );
                    }
                    provider.buffer().code_slice().as_ptr() as usize
                })
            })
            .collect();
        workers
            .into_iter()
            .map(|w| w.join().expect("worker thread"))
            .collect()
    });
    assert!(
        code_addresses.windows(2).all(|w| w[0] == w[1]),
        "every thread must run the one shared kernel: {code_addresses:x?}"
    );
}
