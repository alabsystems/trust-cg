// trust-cg-verify/tests/wasm_local_tv.rs - the wasm local emission validator
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`trust_cg_verify::wasm_local_tv::validate`] on hand-built function
//! bodies: the rewrites the lane's local emission pass makes (colouring,
//! self-copy deletion, reordering, constant rematerialization, single-use
//! stackify, `local.tee`, dead-definition removal, narrow-mask elimination,
//! memarg offset folding, small-copy expansion) are accepted, and each
//! deliberately wrong rewrite — two locals swapped, a live-out value dropped,
//! an effect reordered, a non-constant rematerialized, a moved relocation, a
//! changed control skeleton, a float evaluation whose NaN result may differ
//! duplicated, a definition stackified across a trap or a store, a folded
//! offset that may wrap, a false claimed fact, a mask removed after a
//! non-canonical producer, an overlapping or misordered small copy, a
//! global's value sent to another operand or slot — is refused with its
//! class; so are stacks the validator's model cannot type and operations on
//! a memory other than 0. The last section folds a GEP's address addition
//! under the no-wrap premise `wasm_nowrap_premise::check_nowrap_premises`
//! re-derives (`validate_with_premises`), with the checker's refusals and
//! the validator's own negative controls; both entries are provisional
//! surfaces (docs/wasm32_perf_roadmap.md, "Pending owner sign-off").

use trust_cg_verify::wasm_cfg_proofs::{FuncSig, ValKind};
use trust_cg_verify::wasm_local_tv::{
    LocalFacts, LocalImage, ResidualPolicy, TvBody, TvFailureKind, TvReloc, TvReport, TvRequest,
    TvTypes, validate,
};

const GET: u8 = 0x20;
const SET: u8 = 0x21;
const TEE: u8 = 0x22;
const I32_CONST: u8 = 0x41;
const I32_ADD: u8 = 0x6a;
const I32_SUB: u8 = 0x6b;
const I32_OR: u8 = 0x72;
const I32_STORE: u8 = 0x36;
const DROP: u8 = 0x1a;
const BLOCK: u8 = 0x02;
const LOOP: u8 = 0x03;
const END: u8 = 0x0b;
const BR_IF: u8 = 0x0d;
const CALL: u8 = 0x10;
const VOID: u8 = 0x40;

use ValKind::I32;

/// Function 0 is `(i32) -> (i32)` and globals 0 and 1 are `i32`; nothing
/// else has a type.
struct OneCallee;

impl TvTypes for OneCallee {
    fn func(&self, index: u32) -> Option<FuncSig> {
        (index == 0).then(|| FuncSig {
            params: vec![I32],
            results: vec![I32],
        })
    }
    fn type_at(&self, _: u32) -> Option<FuncSig> {
        None
    }
    fn global(&self, index: u32) -> Option<ValKind> {
        (index < 2).then_some(I32)
    }
}

struct Case<'a> {
    params: &'a [ValKind],
    pre_locals: &'a [ValKind],
    pre: &'a [u8],
    pre_relocs: &'a [TvReloc],
    post_locals: &'a [ValKind],
    post: &'a [u8],
    post_relocs: &'a [TvReloc],
    image: &'a [LocalImage],
    facts: &'a [LocalFacts],
    residual: ResidualPolicy,
    max_work: usize,
}

impl Default for Case<'_> {
    fn default() -> Self {
        Case {
            params: &[I32],
            pre_locals: &[],
            pre: &[],
            pre_relocs: &[],
            post_locals: &[],
            post: &[],
            post_relocs: &[],
            image: &[],
            facts: &[],
            residual: ResidualPolicy::Refuse,
            max_work: 1 << 20,
        }
    }
}

fn run(c: Case<'_>) -> Result<TvReport, trust_cg_verify::wasm_local_tv::TvFailure> {
    validate(&TvRequest {
        params: c.params,
        pre: TvBody {
            locals: c.pre_locals,
            code: c.pre,
            relocs: c.pre_relocs,
        },
        post: TvBody {
            locals: c.post_locals,
            code: c.post,
            relocs: c.post_relocs,
        },
        image: c.image,
        facts: c.facts,
        types: &OneCallee,
        residual: c.residual,
        max_work: c.max_work,
    })
}

fn l(i: u32) -> LocalImage {
    LocalImage::Local(i)
}

fn refused(c: Case<'_>, kind: TvFailureKind) {
    match run(c) {
        Ok(r) => panic!("the rewrite was accepted ({r:?}); expected {kind:?}"),
        Err(f) => assert_eq!(f.kind, kind, "refused for another reason: {f}"),
    }
}

/// `acc = 0; loop { t = acc + n; acc = t; n -= 1; br_if n } return acc`.
const SUM_LOOP: &[u8] = &[
    I32_CONST, 0, SET, 1, LOOP, VOID, GET, 1, GET, 0, I32_ADD, SET, 2, GET, 2, SET, 1, GET, 0,
    I32_CONST, 1, I32_SUB, TEE, 0, BR_IF, 0, END, GET, 1,
];

#[test]
fn an_unchanged_body_is_accepted() {
    let image = [l(0), l(1), l(2)];
    let r = run(Case {
        pre_locals: &[I32, I32],
        pre: SUM_LOOP,
        post_locals: &[I32, I32],
        post: SUM_LOOP,
        image: &image,
        ..Case::default()
    })
    .expect("accepted");
    // Four segments: before the loop, its body up to `br_if`, between `br_if`
    // and `end`, and after `end`.
    assert_eq!(r.segments, 4);
    assert_eq!(r.residuals_proven, 0);
}

#[test]
fn a_coalesced_copy_chain_with_its_self_copies_deleted_is_accepted() {
    // n -> a -> b -> c, each a copy: everything is parameter 0.
    let pre = [GET, 0, SET, 1, GET, 1, SET, 2, GET, 2, SET, 3, GET, 3];
    let image = [l(0), l(0), l(0), l(0)];
    run(Case {
        pre_locals: &[I32, I32, I32],
        pre: &pre,
        post: &[GET, 0],
        image: &image,
        ..Case::default()
    })
    .expect("accepted");
}

#[test]
fn a_loop_carried_copy_coalesced_into_its_phi_is_accepted() {
    // `t` and `acc` share local 1; `t = acc + n; acc = t` becomes one write.
    let post = [
        I32_CONST, 0, SET, 1, LOOP, VOID, GET, 1, GET, 0, I32_ADD, SET, 1, GET, 0, I32_CONST, 1,
        I32_SUB, TEE, 0, BR_IF, 0, END, GET, 1,
    ];
    let image = [l(0), l(1), l(1)];
    run(Case {
        pre_locals: &[I32, I32],
        pre: SUM_LOOP,
        post_locals: &[I32],
        post: &post,
        image: &image,
        ..Case::default()
    })
    .expect("accepted");
}

#[test]
fn a_reordered_local_space_is_accepted() {
    // Locals 1 and 2 trade indices consistently.
    let post = [
        I32_CONST, 0, SET, 2, LOOP, VOID, GET, 2, GET, 0, I32_ADD, SET, 1, GET, 1, SET, 2, GET, 0,
        I32_CONST, 1, I32_SUB, TEE, 0, BR_IF, 0, END, GET, 2,
    ];
    let image = [l(0), l(2), l(1)];
    run(Case {
        pre_locals: &[I32, I32],
        pre: SUM_LOOP,
        post_locals: &[I32, I32],
        post: &post,
        image: &image,
        ..Case::default()
    })
    .expect("accepted");
}

#[test]
fn a_set_then_get_turned_into_a_tee_is_accepted() {
    // Not a rewrite the pass makes, but the same values on every boundary.
    let pre = [GET, 0, CALL, 0, SET, 1, GET, 1, GET, 1, I32_ADD];
    let post = [GET, 0, CALL, 0, TEE, 1, GET, 1, I32_ADD];
    let image = [l(0), l(1)];
    run(Case {
        pre_locals: &[I32],
        pre: &pre,
        post_locals: &[I32],
        post: &post,
        image: &image,
        ..Case::default()
    })
    .expect("accepted");
}

/// `a = n; b = n + 1; block {} return a - b`: both live across the block.
const TWO_LIVE: &[u8] = &[
    GET, 0, SET, 1, GET, 0, I32_CONST, 1, I32_ADD, SET, 2, BLOCK, VOID, END, GET, 1, GET, 2,
    I32_SUB,
];

#[test]
fn two_swapped_locals_are_refused() {
    // The body is unchanged but the image swaps the two locals: at the block
    // boundary local 1 holds `n` while its claimed image holds `n + 1`.
    let image = [l(0), l(2), l(1)];
    refused(
        Case {
            pre_locals: &[I32, I32],
            pre: TWO_LIVE,
            post_locals: &[I32, I32],
            post: TWO_LIVE,
            image: &image,
            ..Case::default()
        },
        TvFailureKind::LiveOutMismatch,
    );
    // Swapping only the reads after the boundary (a renaming applied to half
    // the body) computes `b - a`.
    let post = [
        GET, 0, SET, 1, GET, 0, I32_CONST, 1, I32_ADD, SET, 2, BLOCK, VOID, END, GET, 2, GET, 1,
        I32_SUB,
    ];
    let image = [l(0), l(1), l(2)];
    refused(
        Case {
            pre_locals: &[I32, I32],
            pre: TWO_LIVE,
            post_locals: &[I32, I32],
            post: &post,
            image: &image,
            ..Case::default()
        },
        TvFailureKind::StackMismatch,
    );
}

#[test]
fn merging_two_simultaneously_live_locals_drops_a_live_out_and_is_refused() {
    let post = [
        GET, 0, SET, 1, GET, 0, I32_CONST, 1, I32_ADD, SET, 1, BLOCK, VOID, END, GET, 1, GET, 1,
        I32_SUB,
    ];
    let image = [l(0), l(1), l(1)];
    refused(
        Case {
            pre_locals: &[I32, I32],
            pre: TWO_LIVE,
            post_locals: &[I32],
            post: &post,
            image: &image,
            ..Case::default()
        },
        TvFailureKind::LiveOutMismatch,
    );
    // A live local with no image at all.
    let image = [l(0), LocalImage::Unused, l(2)];
    refused(
        Case {
            pre_locals: &[I32, I32],
            pre: TWO_LIVE,
            post_locals: &[I32, I32],
            post: TWO_LIVE,
            image: &image,
            ..Case::default()
        },
        TvFailureKind::LiveOutMismatch,
    );
}

#[test]
fn a_reordered_effect_is_refused() {
    // store [n] = 1; store [n + 4] = 2  vs the two stores swapped.
    let first = [GET, 0, I32_CONST, 1, I32_STORE, 2, 0];
    let second = [GET, 0, I32_CONST, 2, I32_STORE, 2, 4];
    let pre: Vec<u8> = first.iter().chain(&second).copied().collect();
    let post: Vec<u8> = second.iter().chain(&first).copied().collect();
    refused(
        Case {
            pre: &pre,
            post: &post,
            image: &[l(0)],
            ..Case::default()
        },
        TvFailureKind::EffectMismatch,
    );
}

#[test]
fn a_rematerialized_non_constant_is_refused() {
    // `a = n; block {} return a` with `a` claimed to be the constant 5.
    let pre = [GET, 0, SET, 1, BLOCK, VOID, END, GET, 1];
    let post = [BLOCK, VOID, END, I32_CONST, 5];
    let image = [l(0), LocalImage::Const(vec![I32_CONST, 5])];
    refused(
        Case {
            pre_locals: &[I32],
            pre: &pre,
            post: &post,
            image: &image,
            ..Case::default()
        },
        TvFailureKind::LiveOutMismatch,
    );
}

const FADD: u8 = 0x92;
/// `i32.reinterpret_f32`.
const BITS: u8 = 0xbc;

/// `t = x + y` (f32), then `bits(t) - bits(t)`: always 0, because the one
/// evaluation of `x + y` is read twice.
const NAN_ONCE: &[u8] = &[
    GET, 0, GET, 1, FADD, SET, 2, GET, 2, BITS, GET, 2, BITS, I32_SUB,
];

/// `bits(x + y) - bits(x + y)`: two evaluations, whose NaN results may differ
/// in sign and payload, so the difference is not always 0.
const NAN_TWICE: &[u8] = &[
    GET, 0, GET, 1, FADD, BITS, GET, 0, GET, 1, FADD, BITS, I32_SUB,
];

#[test]
fn a_duplicated_nan_producing_evaluation_is_refused() {
    let image = [l(0), l(1), LocalImage::Unused];
    let case = |residual| Case {
        params: &[ValKind::F32, ValKind::F32],
        pre_locals: &[ValKind::F32],
        pre: NAN_ONCE,
        post: NAN_TWICE,
        image: &image,
        residual,
        ..Case::default()
    };
    refused(case(ResidualPolicy::Refuse), TvFailureKind::StackMismatch);
    // The residual is outside the integer fragment, so the solver is never
    // asked.
    refused(
        case(ResidualPolicy::Solver {
            timeout_ms: 1_000,
            max_queries: 4,
        }),
        TvFailureKind::ResidualUnproven,
    );
}

#[test]
fn nan_producing_evaluations_match_one_for_one() {
    // One evaluation kept in a local, re-read through a `tee`: accepted.
    let tee = [GET, 0, GET, 1, FADD, TEE, 2, BITS, GET, 2, BITS, I32_SUB];
    let image = [l(0), l(1), l(2)];
    run(Case {
        params: &[ValKind::F32, ValKind::F32],
        pre_locals: &[ValKind::F32],
        pre: NAN_ONCE,
        post_locals: &[ValKind::F32],
        post: &tee,
        image: &image,
        ..Case::default()
    })
    .expect("the same single evaluation is accepted");
    // Two evaluations on both sides, in the same order: accepted.
    run(Case {
        params: &[ValKind::F32, ValKind::F32],
        pre: NAN_TWICE,
        post: NAN_TWICE,
        image: &[l(0), l(1)],
        ..Case::default()
    })
    .expect("the same two evaluations are accepted");
    // One evaluation where the pre body has two: refused too (the check is
    // one-for-one, not a refinement order).
    refused(
        Case {
            params: &[ValKind::F32, ValKind::F32],
            pre: NAN_TWICE,
            post_locals: &[ValKind::F32],
            post: NAN_ONCE,
            image: &[l(0), l(1)],
            ..Case::default()
        },
        TvFailureKind::StackMismatch,
    );
}

/// `loop { store [n] = a; a = K; br_if n }` — `a` is read as its initial
/// zero on the first iteration.
fn reads_before_write(k: u8) -> (Vec<u8>, Vec<u8>) {
    let pre = vec![
        LOOP, VOID, GET, 0, GET, 1, I32_STORE, 2, 0, I32_CONST, k, SET, 1, GET, 0, BR_IF, 0, END,
    ];
    let post = vec![
        LOOP, VOID, GET, 0, I32_CONST, k, I32_STORE, 2, 0, GET, 0, BR_IF, 0, END,
    ];
    (pre, post)
}

#[test]
fn a_value_only_dropped_need_not_survive() {
    // `loop { drop a; a = 5; br_if n }`: `a` is read only to be dropped, so
    // it is not live (strong liveness) and the rewrite that claims it is
    // always 5 changes nothing observable.
    let pre = [
        LOOP, VOID, GET, 1, DROP, I32_CONST, 5, SET, 1, GET, 0, BR_IF, 0, END,
    ];
    let post = [LOOP, VOID, GET, 0, BR_IF, 0, END];
    run(Case {
        pre_locals: &[I32],
        pre: &pre,
        post: &post,
        image: &[l(0), LocalImage::Unused],
        ..Case::default()
    })
    .expect("accepted");
}

#[test]
fn a_constant_read_before_its_write_is_rematerialized_only_when_zero() {
    let (pre, post) = reads_before_write(0);
    let image = [l(0), LocalImage::Const(vec![I32_CONST, 0])];
    run(Case {
        pre_locals: &[I32],
        pre: &pre,
        post: &post,
        image: &image,
        ..Case::default()
    })
    .expect("a zero constant equals the initial value");
    let (pre, post) = reads_before_write(5);
    let image = [l(0), LocalImage::Const(vec![I32_CONST, 5])];
    refused(
        Case {
            pre_locals: &[I32],
            pre: &pre,
            post: &post,
            image: &image,
            ..Case::default()
        },
        TvFailureKind::LiveOutMismatch,
    );
}

#[test]
fn a_declared_local_read_as_zero_is_not_a_parameter() {
    // `return a` where `a` was never written (zero), imaged to parameter 0.
    refused(
        Case {
            pre_locals: &[I32],
            pre: &[GET, 1],
            post: &[GET, 0],
            image: &[l(0), l(0)],
            ..Case::default()
        },
        TvFailureKind::StackMismatch,
    );
}

#[test]
fn a_changed_control_skeleton_is_refused() {
    refused(
        Case {
            pre: &[GET, 0],
            post: &[BLOCK, VOID, END, GET, 0],
            image: &[l(0)],
            ..Case::default()
        },
        TvFailureKind::StructureMismatch,
    );
}

#[test]
fn a_relocation_must_move_with_its_instruction() {
    // `call 0` with a padded index and its relocation.
    let code = [GET, 0, CALL, 0x80, 0x80, 0x80, 0x80, 0x00];
    let reloc = |offset| TvReloc {
        offset,
        kind: 0,
        target: 7,
        addend: 0,
    };
    let pre_relocs = [reloc(3)];
    run(Case {
        pre: &code,
        pre_relocs: &pre_relocs,
        post: &code,
        post_relocs: &pre_relocs,
        image: &[l(0)],
        ..Case::default()
    })
    .expect("the same relocation on the same instruction");
    refused(
        Case {
            pre: &code,
            pre_relocs: &pre_relocs,
            post: &code,
            post_relocs: &[],
            image: &[l(0)],
            ..Case::default()
        },
        TvFailureKind::EffectMismatch,
    );
    let other = [TvReloc {
        target: 8,
        ..reloc(3)
    }];
    refused(
        Case {
            pre: &code,
            pre_relocs: &pre_relocs,
            post: &code,
            post_relocs: &other,
            image: &[l(0)],
            ..Case::default()
        },
        TvFailureKind::EffectMismatch,
    );
    // A relocation on a local index is never attached.
    refused(
        Case {
            pre: &code,
            pre_relocs: &pre_relocs,
            post: &code,
            post_relocs: &[reloc(1)],
            image: &[l(0)],
            ..Case::default()
        },
        TvFailureKind::RelocUnsupported,
    );
}

#[test]
fn malformed_images_and_unread_bodies_are_refused() {
    refused(
        Case {
            pre_locals: &[I32],
            pre: &[GET, 1],
            post_locals: &[ValKind::I64],
            post: &[GET, 1],
            image: &[l(0), l(1)],
            ..Case::default()
        },
        TvFailureKind::ImageInvalid,
    );
    refused(
        Case {
            pre: &[GET, 0],
            post: &[GET, 0],
            image: &[],
            ..Case::default()
        },
        TvFailureKind::ImageInvalid,
    );
    // A 0xfe-prefixed (atomic) instruction has no decoding rule.
    refused(
        Case {
            pre: &[GET, 0, 0xfe, 0x10, 2, 0],
            post: &[GET, 0, 0xfe, 0x10, 2, 0],
            image: &[l(0)],
            ..Case::default()
        },
        TvFailureKind::Undecodable,
    );
    // A call with no known signature.
    refused(
        Case {
            pre: &[GET, 0, CALL, 1],
            post: &[GET, 0, CALL, 1],
            image: &[l(0)],
            ..Case::default()
        },
        TvFailureKind::Unsupported,
    );
}

#[test]
fn the_work_budget_is_enforced() {
    let image = [l(0), l(1), l(2)];
    refused(
        Case {
            pre_locals: &[I32, I32],
            pre: SUM_LOOP,
            post_locals: &[I32, I32],
            post: SUM_LOOP,
            image: &image,
            max_work: 4,
            ..Case::default()
        },
        TvFailureKind::Budget,
    );
}

#[test]
fn a_residual_is_refused_without_the_solver() {
    // `n | 0` is `n`, but not syntactically (the validator builds `x + 0` as
    // `x`, and nothing for `or`).
    refused(
        Case {
            pre: &[GET, 0, I32_CONST, 0, I32_OR],
            post: &[GET, 0],
            image: &[l(0)],
            ..Case::default()
        },
        TvFailureKind::StackMismatch,
    );
}

/// With the solver, a TRUE residual is accepted only with a certified proof,
/// and a FALSE one is never accepted.
#[test]
fn a_residual_is_accepted_only_on_a_certified_proof() {
    let solver = ResidualPolicy::Solver {
        timeout_ms: 30_000,
        max_queries: 2,
    };
    match run(Case {
        pre: &[GET, 0, I32_CONST, 0, I32_OR],
        post: &[GET, 0],
        image: &[l(0)],
        residual: solver,
        ..Case::default()
    }) {
        Ok(r) => assert_eq!(r.residuals_proven, 1),
        Err(f) => {
            eprintln!("the true residual was not certified on this host: {f}");
            assert_eq!(f.kind, TvFailureKind::ResidualUnproven, "{f}");
        }
    }
    // A counterexample reports the difference; an unavailable or undecided
    // solver reports the residual as unproven. Neither accepts.
    match run(Case {
        pre: &[GET, 0, I32_CONST, 1, I32_ADD],
        post: &[GET, 0],
        image: &[l(0)],
        residual: solver,
        ..Case::default()
    }) {
        Ok(r) => panic!("a false residual was accepted: {r:?}"),
        Err(f) => assert!(
            matches!(
                f.kind,
                TvFailureKind::StackMismatch | TvFailureKind::ResidualUnproven
            ),
            "{f}"
        ),
    }
    // A float residual never reaches the solver.
    refused(
        Case {
            params: &[ValKind::F32],
            pre: &[GET, 0, 0x8c],
            post: &[GET, 0, 0x8c, 0x8c, 0x8c],
            image: &[l(0)],
            residual: solver,
            ..Case::default()
        },
        TvFailureKind::ResidualUnproven,
    );
}

// ---- Stage B: stackify, masks, folding, small copies ----

const I32_MUL: u8 = 0x6c;
const I32_AND: u8 = 0x71;
const I32_DIV_S: u8 = 0x6d;
const I32_LOAD: u8 = 0x28;
const I64_LOAD: u8 = 0x29;
const I32_LOAD8_U: u8 = 0x2d;
const I32_LOAD8_S: u8 = 0x2c;
const I32_LOAD16_U: u8 = 0x2f;
const I64_STORE: u8 = 0x37;
const I32_STORE8: u8 = 0x3a;
const EXTEND8_S: u8 = 0xc0;
const IF: u8 = 0x04;
const UNREACHABLE: u8 = 0x00;
const GLOBAL_GET: u8 = 0x23;
const GLOBAL_SET: u8 = 0x24;
const MEMORY_COPY: [u8; 4] = [0xfc, 0x0a, 0x00, 0x00];
use ValKind::I64;

#[test]
fn a_single_use_definition_moved_to_its_use_is_accepted() {
    // t = n + 1; store [n] = 7; return t * 4  ->  the pure `n + 1` moves past
    // the store to its use, and `t` is gone.
    let pre = [
        GET, 0, I32_CONST, 1, I32_ADD, SET, 1, GET, 0, I32_CONST, 7, I32_STORE, 2, 0, GET, 1,
        I32_CONST, 4, I32_MUL,
    ];
    let post = [
        GET, 0, I32_CONST, 7, I32_STORE, 2, 0, GET, 0, I32_CONST, 1, I32_ADD, I32_CONST, 4, I32_MUL,
    ];
    run(Case {
        pre_locals: &[I32],
        pre: &pre,
        post: &post,
        image: &[l(0), LocalImage::Unused],
        ..Case::default()
    })
    .expect("accepted");
    // The same value read twice: a tee at the first read.
    let pre = [
        GET, 0, GET, 0, I32_MUL, SET, 1, GET, 0, I32_CONST, 7, I32_STORE, 2, 0, GET, 1, GET, 1,
        I32_ADD,
    ];
    let post = [
        GET, 0, I32_CONST, 7, I32_STORE, 2, 0, GET, 0, GET, 0, I32_MUL, TEE, 1, GET, 1, I32_ADD,
    ];
    run(Case {
        pre_locals: &[I32],
        pre: &pre,
        post_locals: &[I32],
        post: &post,
        image: &[l(0), l(1)],
        ..Case::default()
    })
    .expect("accepted");
}

#[test]
fn a_definition_stackified_across_a_trap_or_a_store_is_refused() {
    // t = n / n (traps when n == 0); store [n] = 7; return t. Moving the
    // division after the store changes which effect happens first.
    let pre = [
        GET, 0, GET, 0, I32_DIV_S, SET, 1, GET, 0, I32_CONST, 7, I32_STORE, 2, 0, GET, 1,
    ];
    let post = [
        GET, 0, I32_CONST, 7, I32_STORE, 2, 0, GET, 0, GET, 0, I32_DIV_S,
    ];
    refused(
        Case {
            pre_locals: &[I32],
            pre: &pre,
            post: &post,
            image: &[l(0), LocalImage::Unused],
            ..Case::default()
        },
        TvFailureKind::EffectMismatch,
    );
    // t = load [n]; store [n] = 7; return t: the load moved past the store
    // would read the 7.
    let pre = [
        GET, 0, I32_LOAD, 2, 0, SET, 1, GET, 0, I32_CONST, 7, I32_STORE, 2, 0, GET, 1,
    ];
    let post = [
        GET, 0, I32_CONST, 7, I32_STORE, 2, 0, GET, 0, I32_LOAD, 2, 0,
    ];
    refused(
        Case {
            pre_locals: &[I32],
            pre: &pre,
            post: &post,
            image: &[l(0), LocalImage::Unused],
            ..Case::default()
        },
        TvFailureKind::EffectMismatch,
    );
}

#[test]
fn a_mask_is_removed_only_after_a_canonical_producer() {
    let ok: [(&[u8], &[u8]); 3] = [
        (
            &[GET, 0, I32_LOAD8_U, 0, 0, I32_CONST, 0xff, 0x01, I32_AND],
            &[GET, 0, I32_LOAD8_U, 0, 0],
        ),
        (
            &[GET, 0, I32_LOAD8_S, 0, 0, EXTEND8_S],
            &[GET, 0, I32_LOAD8_S, 0, 0],
        ),
        (
            &[GET, 0, I32_CONST, 3, 0x46, I32_CONST, 1, I32_AND],
            &[GET, 0, I32_CONST, 3, 0x46],
        ),
    ];
    for (pre, post) in ok {
        run(Case {
            pre,
            post,
            image: &[l(0)],
            ..Case::default()
        })
        .unwrap_or_else(|f| panic!("{pre:02x?}: {f}"));
    }
    // A 16-bit load masked to 8 bits, and an `i32.load` sign-extended from 8
    // bits: the operation changes the value, so removing it is refused.
    let bad: [(&[u8], &[u8]); 2] = [
        (
            &[GET, 0, I32_LOAD16_U, 1, 0, I32_CONST, 0xff, 0x01, I32_AND],
            &[GET, 0, I32_LOAD16_U, 1, 0],
        ),
        (
            &[GET, 0, I32_LOAD, 2, 0, EXTEND8_S],
            &[GET, 0, I32_LOAD, 2, 0],
        ),
    ];
    for (pre, post) in bad {
        refused(
            Case {
                pre,
                post,
                image: &[l(0)],
                ..Case::default()
            },
            TvFailureKind::StackMismatch,
        );
    }
}

#[test]
fn an_offset_is_folded_only_when_the_address_cannot_wrap() {
    // (n & 0xff) + 8 never wraps: the 8 may move into the memarg.
    run(Case {
        pre: &[
            GET, 0, I32_CONST, 0xff, 0x01, I32_AND, I32_CONST, 8, I32_ADD, I32_LOAD, 2, 4,
        ],
        post: &[GET, 0, I32_CONST, 0xff, 0x01, I32_AND, I32_LOAD, 2, 12],
        image: &[l(0)],
        ..Case::default()
    })
    .expect("accepted");
    // n + 8 for an arbitrary n may wrap to a low address the folded access
    // (33-bit, so out of bounds) would not reach.
    refused(
        Case {
            pre: &[GET, 0, I32_CONST, 8, I32_ADD, I32_LOAD, 2, 4],
            post: &[GET, 0, I32_LOAD, 2, 12],
            image: &[l(0)],
            ..Case::default()
        },
        TvFailureKind::EffectMismatch,
    );
    // A claimed bound the body does not establish: `a = n` claimed below 100
    // so that `a + 8` would fold.
    let pre = [
        GET, 0, SET, 1, BLOCK, VOID, END, GET, 1, I32_CONST, 8, I32_ADD, I32_LOAD, 2, 0,
    ];
    let post = [GET, 0, SET, 1, BLOCK, VOID, END, GET, 1, I32_LOAD, 2, 8];
    let claimed = [LocalFacts::NONE, LocalFacts { max: 100, sext: 32 }];
    refused(
        Case {
            pre_locals: &[I32],
            pre: &pre,
            post_locals: &[I32],
            post: &post,
            image: &[l(0), l(1)],
            facts: &claimed,
            ..Case::default()
        },
        TvFailureKind::FactUnproven,
    );
}

/// `sp = global 0; base = sp - 32; global 0 = base; if (base <u 1024 |
/// base >u sp) unreachable; a = base + 16; block {} store [a + 8] = n`.
fn guarded_frame(add: &[u8], store: &[u8]) -> Vec<u8> {
    let mut code = vec![
        GLOBAL_GET,
        0,
        SET,
        1,
        GET,
        1,
        I32_CONST,
        32,
        I32_SUB,
        TEE,
        2,
        GLOBAL_SET,
        0,
        GET,
        2,
        I32_CONST,
        0x80,
        0x08,
        0x49,
        GET,
        2,
        GET,
        1,
        0x4b,
        I32_OR,
        IF,
        VOID,
        UNREACHABLE,
        END,
        GET,
        2,
        I32_CONST,
        16,
        I32_ADD,
        SET,
        3,
        BLOCK,
        VOID,
        END,
        GET,
        3,
    ];
    code.extend_from_slice(add);
    code.push(GET);
    code.push(0);
    code.extend_from_slice(store);
    code
}

#[test]
fn a_frame_offset_folds_under_the_stack_guard_bound() {
    let pre = guarded_frame(&[I32_CONST, 8, I32_ADD], &[I32_STORE, 2, 0]);
    let post = guarded_frame(&[], &[I32_STORE, 2, 8]);
    let image = [l(0), l(1), l(2), l(3)];
    let base = LocalFacts {
        max: u64::from(u32::MAX) - 32,
        sext: 32,
    };
    let a = LocalFacts {
        max: u64::from(u32::MAX) - 16,
        sext: 32,
    };
    let claims = [LocalFacts::NONE, LocalFacts::NONE, base, a];
    let r = run(Case {
        pre_locals: &[I32, I32, I32],
        pre: &pre,
        post_locals: &[I32, I32, I32],
        post: &post,
        image: &image,
        facts: &claims,
        ..Case::default()
    })
    .expect("accepted");
    assert_eq!(r.offsets_folded, 1);
    assert!(r.facts_checked >= 2);
    // Without the guard (its `if` removed from both bodies) the base's bound
    // is not established.
    let strip = |c: &[u8]| -> Vec<u8> {
        let at = c
            .windows(4)
            .position(|w| w == [IF, VOID, UNREACHABLE, END])
            .expect("guard");
        let mut v = c[..at].to_vec();
        v.push(DROP);
        v.extend_from_slice(&c[at + 4..]);
        v
    };
    refused(
        Case {
            pre_locals: &[I32, I32, I32],
            pre: &strip(&pre),
            post_locals: &[I32, I32, I32],
            post: &strip(&post),
            image: &image,
            facts: &claims,
            ..Case::default()
        },
        TvFailureKind::FactUnproven,
    );
    // A frame claimed larger than the carve (64 bytes for 32).
    let wide = [
        LocalFacts::NONE,
        LocalFacts::NONE,
        LocalFacts {
            max: u64::from(u32::MAX) - 64,
            sext: 32,
        },
        LocalFacts::NONE,
    ];
    refused(
        Case {
            pre_locals: &[I32, I32, I32],
            pre: &pre,
            post_locals: &[I32, I32, I32],
            post: &pre,
            image: &image,
            facts: &wide,
            ..Case::default()
        },
        TvFailureKind::FactUnproven,
    );
}

/// `memory.copy(d = local 0, s = local 1, 16)`.
fn copy16() -> Vec<u8> {
    let mut v = vec![GET, 0, GET, 1, I32_CONST, 16];
    v.extend(MEMORY_COPY);
    v
}

const COPY_IMAGE: &[LocalImage] = &[LocalImage::Local(0), LocalImage::Local(1)];

/// One i64 scratch local (index 2) after the two pointer parameters.
fn copy_case<'a>(post: &'a [u8], pre: &'a [u8]) -> Case<'a> {
    Case {
        params: &[I32, I32],
        pre,
        post_locals: &[I64],
        post,
        image: COPY_IMAGE,
        ..Case::default()
    }
}

#[test]
fn a_small_copy_expanded_into_loads_then_stores_is_accepted() {
    // Load [s+8] (kept on the stack over d), load [s] into the scratch, store
    // [d+8] first, then [d].
    let post = [
        GET, 0, GET, 1, I64_LOAD, 0, 8, GET, 1, I64_LOAD, 0, 0, SET, 2, I64_STORE, 0, 8, GET, 0,
        GET, 2, I64_STORE, 0, 0,
    ];
    let pre = copy16();
    let r = run(copy_case(&post, &pre)).expect("accepted");
    assert_eq!(r.copies_expanded, 1);
    // Three bytes: a 16-bit chunk and an 8-bit one, through i32 loads.
    let mut pre3 = vec![GET, 0, GET, 1, I32_CONST, 3];
    pre3.extend(MEMORY_COPY);
    let post3 = [
        GET,
        0,
        GET,
        1,
        I32_LOAD8_U,
        0,
        2,
        GET,
        1,
        I32_LOAD16_U,
        0,
        0,
        SET,
        2,
        I32_STORE8,
        0,
        2,
        GET,
        0,
        GET,
        2,
        0x3b,
        0,
        0,
    ];
    run(Case {
        params: &[I32, I32],
        pre: &pre3,
        post_locals: &[I32],
        post: &post3,
        image: &[l(0), l(1)],
        ..Case::default()
    })
    .expect("accepted");
}

#[test]
fn an_overlapping_or_misordered_small_copy_is_refused() {
    let pre = copy16();
    let cases: [(&str, &[u8]); 5] = [
        (
            // Each chunk stored right after it is loaded: a destination that
            // overlaps the source above it reads bytes already overwritten.
            "interleaved",
            &[
                GET, 0, GET, 1, I64_LOAD, 0, 8, I64_STORE, 0, 8, GET, 0, GET, 1, I64_LOAD, 0, 0,
                I64_STORE, 0, 0,
            ],
        ),
        (
            // The low chunk stored first: a destination end past the memory
            // traps after the low bytes were written.
            "low chunk first",
            &[
                GET, 0, GET, 1, I64_LOAD, 0, 0, GET, 1, I64_LOAD, 0, 8, SET, 2, I64_STORE, 0, 0,
                GET, 0, GET, 2, I64_STORE, 0, 8,
            ],
        ),
        (
            // The two values stored at each other's offsets.
            "swapped",
            &[
                GET, 0, GET, 1, I64_LOAD, 0, 8, GET, 1, I64_LOAD, 0, 0, SET, 2, I64_STORE, 0, 0,
                GET, 0, GET, 2, I64_STORE, 0, 8,
            ],
        ),
        (
            // Only 8 of the 16 bytes.
            "short",
            &[GET, 0, GET, 1, I64_LOAD, 0, 8, I64_STORE, 0, 8],
        ),
        (
            // The second chunk read from the destination, not the source.
            "wrong source",
            &[
                GET, 0, GET, 1, I64_LOAD, 0, 8, GET, 0, I64_LOAD, 0, 0, SET, 2, I64_STORE, 0, 8,
                GET, 0, GET, 2, I64_STORE, 0, 0,
            ],
        ),
    ];
    for (what, post) in cases {
        match run(copy_case(post, &pre)) {
            Ok(r) => panic!("{what}: accepted ({r:?})"),
            Err(f) => assert_eq!(f.kind, TvFailureKind::EffectMismatch, "{what}: {f}"),
        }
    }
}

const I32_XOR: u8 = 0x73;
const I32_SHL: u8 = 0x74;
const I32_RESULT: u8 = 0x7f;

/// A `global.get` result is a term of its own: a rewrite that sends a
/// global's value to another operand or slot is refused, which is exactly
/// the stack-pointer protocol (`sp - size`, the saved `sp`).
#[test]
fn a_global_value_sent_elsewhere_is_refused() {
    let cases: [(&str, &[u8], &[u8]); 3] = [
        (
            "sp - 32 against 32 - sp",
            &[
                GLOBAL_GET, 0, I32_CONST, 32, I32_SUB, TEE, 3, GET, 3, GLOBAL_SET, 0, GET, 3,
            ],
            &[
                I32_CONST, 32, GLOBAL_GET, 0, I32_SUB, TEE, 3, GET, 3, GLOBAL_SET, 0, GET, 3,
            ],
        ),
        (
            "shl operands swapped",
            &[
                GLOBAL_GET, 0, I32_CONST, 16, I32_SHL, GLOBAL_SET, 0, I32_CONST, 1,
            ],
            &[
                I32_CONST, 16, GLOBAL_GET, 0, I32_SHL, GLOBAL_SET, 0, I32_CONST, 1,
            ],
        ),
        (
            "global.get moved across a drop",
            &[
                GET, 0, GET, 0, I32_XOR, DROP, GLOBAL_GET, 1, EXTEND8_S, GLOBAL_SET, 1,
            ],
            &[
                GET, 0, GET, 0, I32_XOR, GLOBAL_GET, 1, DROP, EXTEND8_S, GLOBAL_SET, 1,
            ],
        ),
    ];
    for (what, pre, post) in cases {
        let image = [l(0), l(1), l(2), l(3)];
        let case = |post: &'static [u8]| Case {
            pre_locals: &[I32, I32, I32],
            pre,
            post_locals: &[I32, I32, I32],
            post,
            image: &image,
            ..Case::default()
        };
        // The unchanged body is accepted, so the refusal is the rewrite's.
        run(case(pre)).unwrap_or_else(|f| panic!("{what}: identity refused: {f}"));
        match run(case(post)) {
            Ok(r) => panic!("{what}: accepted ({r:?})"),
            Err(f) => assert_eq!(f.kind, TvFailureKind::EffectMismatch, "{what}: {f}"),
        }
    }
    // A global with no known type is not modelled.
    let unknown = [GLOBAL_GET, 7, DROP];
    refused(
        Case {
            pre: &unknown,
            post: &unknown,
            image: &[l(0)],
            ..Case::default()
        },
        TvFailureKind::Unsupported,
    );
}

/// The validator's stack accounting is re-checked against WebAssembly's
/// typing: a segment that takes a value its frame does not hold (here at
/// function entry and at the start of a block), or a frame that ends with
/// another count than its results, is refused even when both bodies agree.
#[test]
fn a_stack_the_model_cannot_type_is_refused() {
    let bodies: [&[u8]; 3] = [
        &[I32_CONST, 1, I32_ADD],
        &[BLOCK, VOID, DROP, END],
        &[BLOCK, I32_RESULT, END, DROP],
    ];
    for code in bodies {
        refused(
            Case {
                pre: code,
                post: code,
                image: &[l(0)],
                ..Case::default()
            },
            TvFailureKind::Unsupported,
        );
    }
    // A block's result is consumed after its `end`, and a branch makes the
    // rest of its frame polymorphic: both type.
    let ok = [
        BLOCK,
        I32_RESULT,
        GET,
        0,
        END,
        GET,
        0,
        BLOCK,
        VOID,
        UNREACHABLE,
        DROP,
        END,
        I32_ADD,
    ];
    run(Case {
        pre: &ok,
        post: &ok,
        image: &[l(0)],
        ..Case::default()
    })
    .expect("accepted");
}

/// Only memory 0 is modelled: a bulk operation or memarg naming another
/// memory is refused, not compared as if it named memory 0.
#[test]
fn an_operation_on_another_memory_is_refused() {
    let copy1 = [GET, 0, GET, 0, I32_CONST, 4, 0xfc, 0x0a, 0x00, 0x01];
    let fill1 = [GET, 0, I32_CONST, 0, I32_CONST, 4, 0xfc, 0x0b, 0x01];
    let load1 = [GET, 0, I32_LOAD, 0x42, 0x01, 0x00, DROP];
    for code in [&copy1[..], &fill1[..], &load1[..]] {
        refused(
            Case {
                pre: code,
                post: code,
                image: &[l(0)],
                ..Case::default()
            },
            TvFailureKind::Unsupported,
        );
    }
}

// ---- No-wrap premises of GEP additions (round 14 stage B) ----
//
// `validate_with_premises` and `wasm_nowrap_premise::check_nowrap_premises`
// are provisional surfaces (docs/wasm32_perf_roadmap.md, "Pending owner
// sign-off"); these tests follow them if they change.

use trust_cg_verify::wasm_local_tv::validate_with_premises;
use trust_cg_verify::wasm_nowrap_premise::{
    NoWrapCheck, NoWrapClaim, NoWrapPremise, NoWrapRefusal, check_nowrap_premises,
};
use trust_ir::ValueId;

const MEMORY_FILL: [u8; 3] = [0xfc, 0x0b, 0x00];

/// `c` under `premises`, as the function [`gep_module`] names (`f`).
fn run_premised(
    c: Case<'_>,
    premises: &[NoWrapPremise],
) -> Result<TvReport, trust_cg_verify::wasm_local_tv::TvFailure> {
    run_premised_as(c, "f", premises)
}

fn run_premised_as(
    c: Case<'_>,
    function: &str,
    premises: &[NoWrapPremise],
) -> Result<TvReport, trust_cg_verify::wasm_local_tv::TvFailure> {
    validate_with_premises(
        &TvRequest {
            params: c.params,
            pre: TvBody {
                locals: c.pre_locals,
                code: c.pre,
                relocs: c.pre_relocs,
            },
            post: TvBody {
                locals: c.post_locals,
                code: c.post,
                relocs: c.post_relocs,
            },
            image: c.image,
            facts: c.facts,
            types: &OneCallee,
            residual: c.residual,
            max_work: c.max_work,
        },
        function,
        premises,
    )
}

/// `f(%0: ptr) -> u32 { %1 = const usize 8; %2 = gep u8, ptr %0, %1;
/// %3 = load u32, ptr %2; ret %3 }` on wasm32, with the `GEP` replaced by
/// `gep_line` (one line defining `%2`).
fn gep_module(target: &str, gep_line: &str) -> trust_ir::Module {
    let text = format!(
        "module \"nowrap\"\ntarget {target}\n\nfuncty.0 = (ptr) -> (u32)\n\n\
         fn @f(functy.0) {{\nbb0(%0: ptr):\n    %1 = const usize 8\n    {gep_line}\n    \
         %3 = load u32, ptr %2\n    ret %3\n}}\n"
    );
    trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("{e}\n{text}"))
}

const WASM32: &str = "\"wasm32-unknown-unknown\" 4 little";
const GEP_U8: &str = "%2 = gep u8, ptr %0, %1";

/// The lane's map for [`gep_module`]: `%n` in local `n`.
fn slots() -> Vec<(ValueId, u32)> {
    (0..4).map(|n| (ValueId::new(n), n)).collect()
}

/// The lowering of [`gep_module`]: `%1` into local 1, the GEP's addition
/// (at byte 8) into local 2, the load into local 3.
const GEP_PRE: &[u8] = &[
    I32_CONST, 8, SET, 1, GET, 0, GET, 1, I32_ADD, SET, 2, GET, 2, I32_LOAD, 2, 0, SET, 3, GET, 3,
];
const GEP_ADD_AT: u32 = 8;
const GEP_LOCALS: &[ValKind] = &[I32, I32, I32];
/// `f` with the load's address folded: `i32.load offset=8 (local 0)`.
const GEP_FOLDED: &[u8] = &[GET, 0, I32_LOAD, 2, 8];
const GEP_IMAGE: &[LocalImage] = &[
    LocalImage::Local(0),
    LocalImage::Unused,
    LocalImage::Unused,
    LocalImage::Unused,
];

fn check(module: &trust_ir::Module, pre: &[u8], claims: &[NoWrapClaim]) -> NoWrapCheck {
    let f = &module.functions[0];
    check_nowrap_premises(
        module,
        f,
        &slots(),
        &[I32],
        &TvBody {
            locals: GEP_LOCALS,
            code: pre,
            relocs: &[],
        },
        claims,
    )
}

fn claim(value: u32, add_offset: u32) -> NoWrapClaim {
    NoWrapClaim {
        value: ValueId::new(value),
        add_offset,
    }
}

/// The premise [`gep_module`]'s GEP carries on [`GEP_PRE`].
fn gep_premise() -> NoWrapPremise {
    let c = check(
        &gep_module(WASM32, GEP_U8),
        GEP_PRE,
        &[claim(2, GEP_ADD_AT)],
    );
    assert_eq!(c.refused, vec![], "{c:?}");
    let [p] = c.premises.as_slice() else {
        panic!("{c:?}")
    };
    assert_eq!(
        (p.result(), p.base(), p.index(), p.scale(), p.multiplied()),
        (2, 0, 1, 1, false)
    );
    *p
}

/// The premise [`gep_module`]'s GEP carries on `pre`, a lowering with the
/// GEP's addition at [`GEP_ADD_AT`].
fn premise_on(pre: &[u8]) -> NoWrapPremise {
    let c = check(&gep_module(WASM32, GEP_U8), pre, &[claim(2, GEP_ADD_AT)]);
    let [p] = c.premises.as_slice() else {
        panic!("{c:?}")
    };
    *p
}

fn gep_case<'a>(pre: &'a [u8], post: &'a [u8]) -> Case<'a> {
    Case {
        pre_locals: GEP_LOCALS,
        pre,
        post,
        image: GEP_IMAGE,
        ..Case::default()
    }
}

/// The checker admits the lane's claim on a single-index GEP, and under the
/// premise the validator accepts `i32.load (x + 8)` folded to `i32.load
/// offset=8 (x)` for an `x` nothing bounds; without it the fold is refused.
#[test]
fn a_gep_premise_lets_an_unbounded_base_fold() {
    let p = gep_premise();
    refused(gep_case(GEP_PRE, GEP_FOLDED), TvFailureKind::EffectMismatch);
    let r = run_premised(gep_case(GEP_PRE, GEP_FOLDED), &[p]).expect("accepted");
    assert_eq!((r.offsets_folded, r.premised_folds), (1, 1));
    // The unfolded body needs no premise and uses none.
    let same = Case {
        post_locals: GEP_LOCALS,
        image: &[l(0), l(1), l(2), l(3)],
        ..gep_case(GEP_PRE, GEP_PRE)
    };
    let r = run_premised(same, &[p]).expect("accepted");
    assert_eq!((r.offsets_folded, r.premised_folds), (0, 0));
}

/// Claims the checker refuses, each by its reason: an integer address chain
/// (`ptrtoint`/`add`/`inttoptr`, which wraps at the target width), a claim on
/// another instruction, a multi-index GEP, a 64-bit target, a shared or
/// missing local, a second write of the GEP's local, and a lowering whose
/// scale is not the element size.
#[test]
fn the_premise_checker_refuses_claims_it_cannot_re_derive() {
    let refusal = |module: &trust_ir::Module, pre: &[u8], c: NoWrapClaim| -> NoWrapRefusal {
        let got = check(module, pre, &[c]);
        assert!(got.premises.is_empty(), "admitted: {got:?}");
        got.refused[0].1
    };
    // `%2` is an integer sum turned into a pointer: no premise, whichever of
    // its values is claimed.
    let chain = trust_ir::parser::parse_module(&format!(
        "module \"nowrap\"\ntarget {WASM32}\n\nfuncty.0 = (ptr) -> (u32)\n\n\
         fn @f(functy.0) {{\nbb0(%0: ptr):\n    %1 = const i32 8\n    \
         %4 = ptrtoint ptr %0 to i32\n    %5 = add i32 %4, %1\n    %2 = inttoptr i32 %5 to ptr\n    \
         %3 = load u32, ptr %2\n    ret %3\n}}\n"
    ))
    .expect("parses");
    for v in [2, 5] {
        assert_eq!(
            refusal(&chain, GEP_PRE, claim(v, GEP_ADD_AT)),
            NoWrapRefusal::NotGep
        );
    }
    let module = gep_module(WASM32, GEP_U8);
    // The load's value, and the GEP claimed at another instruction.
    assert_eq!(
        refusal(&module, GEP_PRE, claim(3, GEP_ADD_AT)),
        NoWrapRefusal::NotGep
    );
    assert_eq!(
        refusal(&module, GEP_PRE, claim(2, GEP_ADD_AT - 2)),
        NoWrapRefusal::Shape
    );
    assert_eq!(
        refusal(&module, GEP_PRE, claim(2, GEP_ADD_AT + 1)),
        NoWrapRefusal::Shape
    );
    assert_eq!(
        refusal(&module, GEP_PRE, claim(2, 1000)),
        NoWrapRefusal::Offset
    );
    // The addition reads another local than the GEP's index.
    let other = [
        I32_CONST, 8, SET, 1, GET, 0, GET, 3, I32_ADD, SET, 2, GET, 2, I32_LOAD, 2, 0, SET, 3, GET,
        3,
    ];
    assert_eq!(
        refusal(&module, &other, claim(2, GEP_ADD_AT)),
        NoWrapRefusal::Shape
    );
    // The GEP's local written a second time.
    let twice = [
        I32_CONST, 8, SET, 1, GET, 0, GET, 1, I32_ADD, SET, 2, GET, 0, SET, 2, GET, 2, I32_LOAD, 2,
        0, SET, 3, GET, 3,
    ];
    assert_eq!(
        refusal(&module, &twice, claim(2, GEP_ADD_AT)),
        NoWrapRefusal::Writes
    );
    // Two indices.
    let two = gep_module(WASM32, "%2 = gep u8, ptr %0, %1, %1");
    assert_eq!(
        refusal(&two, GEP_PRE, claim(2, GEP_ADD_AT)),
        NoWrapRefusal::IndexCount
    );
    // A 64-bit target: WS2.16's bound is 2^64 - 1 there, not a wasm32
    // address.
    let wide = gep_module("\"x86_64-unknown-linux-gnu\" 8 little", GEP_U8);
    assert_eq!(
        refusal(&wide, GEP_PRE, claim(2, GEP_ADD_AT)),
        NoWrapRefusal::Target
    );
    // A `u32` element lowered with a scale of 8.
    let u32_gep = gep_module(WASM32, "%2 = gep u32, ptr %0, %1");
    let scaled = |k: u8| {
        vec![
            I32_CONST, 8, SET, 1, GET, 0, GET, 1, I32_CONST, k, I32_MUL, I32_ADD, SET, 2, GET, 2,
            I32_LOAD, 2, 0, SET, 3, GET, 3,
        ]
    };
    assert_eq!(
        refusal(&u32_gep, &scaled(8), claim(2, 11)),
        NoWrapRefusal::Shape
    );
    let ok = check(&u32_gep, &scaled(4), &[claim(2, 11)]);
    assert_eq!(ok.premises.len(), 1, "{ok:?}");
    assert!(ok.premises[0].multiplied() && ok.premises[0].scale() == 4);
    // The unscaled form claims a one-byte element only.
    assert_eq!(
        refusal(&u32_gep, GEP_PRE, claim(2, GEP_ADD_AT)),
        NoWrapRefusal::Shape
    );
    // A local the lane maps two values to.
    let mut shared = slots();
    shared.push((ValueId::new(9), 1));
    let got = check_nowrap_premises(
        &module,
        &module.functions[0],
        &shared,
        &[I32],
        &TvBody {
            locals: GEP_LOCALS,
            code: GEP_PRE,
            relocs: &[],
        },
        &[claim(2, GEP_ADD_AT)],
    );
    assert_eq!(
        got.refused,
        vec![(claim(2, GEP_ADD_AT), NoWrapRefusal::Local)]
    );
    // A value the lane's map lists twice (`%1` in locals 1 and 3): the map
    // is not a function, so nothing is admitted, whichever entry is later.
    for dup in [3, 1] {
        let mut repeated = slots();
        repeated.push((ValueId::new(1), dup));
        let got = check_nowrap_premises(
            &module,
            &module.functions[0],
            &repeated,
            &[I32],
            &TvBody {
                locals: GEP_LOCALS,
                code: GEP_PRE,
                relocs: &[],
            },
            &[claim(2, GEP_ADD_AT)],
        );
        assert_eq!(
            got.refused,
            vec![(claim(2, GEP_ADD_AT), NoWrapRefusal::Local)],
            "{got:?}"
        );
    }
}

/// A premise is bound to the function and body it was derived on: applied
/// to another body (a write of `x + 12` where the index holds 8, or the
/// local written twice) or under another function name, it licenses
/// nothing. (The validator's re-check of the sum and the write count on a
/// body the premise IS bound to is unit-tested in `wasm_local_tv`, since
/// the checker refuses both bodies.)
#[test]
fn a_premise_on_another_body_licenses_nothing() {
    let p = gep_premise();
    let e = run_premised_as(gep_case(GEP_PRE, GEP_FOLDED), "g", &[p]).expect_err("refused");
    assert_eq!(e.kind, TvFailureKind::EffectMismatch, "{e}");
    let other_sum = [
        I32_CONST, 8, SET, 1, GET, 0, I32_CONST, 12, I32_ADD, SET, 2, GET, 2, I32_LOAD, 2, 0, SET,
        3, GET, 3,
    ];
    let folded12 = [GET, 0, I32_LOAD, 2, 12];
    refused(
        gep_case(&other_sum, &folded12),
        TvFailureKind::EffectMismatch,
    );
    let e = run_premised(gep_case(&other_sum, &folded12), &[p]).expect_err("refused");
    assert_eq!(e.kind, TvFailureKind::EffectMismatch, "{e}");
    let twice = [
        I32_CONST, 8, SET, 1, GET, 0, GET, 1, I32_ADD, SET, 2, GET, 2, SET, 2, GET, 2, I32_LOAD, 2,
        0, SET, 3, GET, 3,
    ];
    let e = run_premised(gep_case(&twice, GEP_FOLDED), &[p]).expect_err("refused");
    assert_eq!(e.kind, TvFailureKind::EffectMismatch, "{e}");
}

/// The fold must address what the GEP did: after the base local is
/// redefined, `offset=8` from its new value is another address.
#[test]
fn a_fold_across_a_redefinition_of_the_base_is_refused() {
    let pre = [
        I32_CONST, 8, SET, 1, GET, 0, GET, 1, I32_ADD, SET, 2, I32_CONST, 64, SET, 0, GET, 2,
        I32_LOAD, 2, 0, SET, 3, GET, 3,
    ];
    let p = premise_on(&pre);
    let post = [I32_CONST, 64, SET, 0, GET, 0, I32_LOAD, 2, 8];
    let e = run_premised(gep_case(&pre, &post), &[p]).expect_err("refused");
    assert_eq!(e.kind, TvFailureKind::EffectMismatch, "{e}");
    // Folded from the base's value before the redefinition, it is accepted.
    let kept = [GET, 0, I32_CONST, 64, SET, 0, I32_LOAD, 2, 8];
    run_premised(gep_case(&pre, &kept), &[p]).expect("accepted");
}

/// A premise holds from the GEP on: an access to the same address BEFORE
/// it (an effect the GEP may never be reached after) is not folded on it.
#[test]
fn a_premise_does_not_reach_back_before_its_gep() {
    let pre = [
        GET, 0, I32_CONST, 8, I32_ADD, I32_LOAD, 2, 0, DROP, I32_CONST, 8, SET, 1, GET, 0, GET, 1,
        I32_ADD, SET, 2, GET, 2, I32_LOAD, 2, 0, SET, 3, GET, 3,
    ];
    let add_at = 17;
    let module = gep_module(WASM32, GEP_U8);
    let c = check(&module, &pre, &[claim(2, add_at)]);
    let [p] = c.premises.as_slice() else {
        panic!("{c:?}")
    };
    let both = [GET, 0, I32_LOAD, 2, 8, DROP, GET, 0, I32_LOAD, 2, 8];
    let e = run_premised(gep_case(&pre, &both), &[*p]).expect_err("refused");
    assert_eq!(e.kind, TvFailureKind::EffectMismatch, "{e}");
    let second = [
        GET, 0, I32_CONST, 8, I32_ADD, I32_LOAD, 2, 0, DROP, GET, 0, I32_LOAD, 2, 8,
    ];
    let r = run_premised(gep_case(&pre, &second), &[*p]).expect("accepted");
    assert_eq!(r.premised_folds, 1);
}

/// A memarg offset is a `u32`: a pre access at `offset=0xFFFF_FFF8` through
/// the premised sum reaches `x + 2^32`, which a folded offset cannot encode
/// (the wrapped offset 0 is another address); the unfolded post is
/// accepted.
#[test]
fn a_fold_past_the_memarg_range_is_refused() {
    let high = [0xf8, 0xff, 0xff, 0xff, 0x0f];
    let mut pre = vec![
        I32_CONST, 8, SET, 1, GET, 0, GET, 1, I32_ADD, SET, 2, GET, 2, I32_LOAD, 2,
    ];
    pre.extend(high);
    pre.extend([SET, 3, GET, 3]);
    let p = premise_on(&pre);
    let wrapped = [GET, 0, I32_LOAD, 2, 0];
    let e = run_premised(gep_case(&pre, &wrapped), &[p]).expect_err("refused");
    assert_eq!(e.kind, TvFailureKind::EffectMismatch, "{e}");
    let mut kept = vec![GET, 0, I32_CONST, 8, I32_ADD, I32_LOAD, 2];
    kept.extend(high);
    run_premised(gep_case(&pre, &kept), &[p]).expect("accepted");
}

/// Bulk memory has no memarg: `memory.fill` through the premised sum may
/// not drop the addend; with it kept, the addresses compare equal. An atomic
/// access is outside both models: the checker admits no premise on its
/// body and the validator refuses it whatever the premise.
#[test]
fn bulk_and_atomic_accesses_are_not_folded() {
    let pre = [
        I32_CONST,
        8,
        SET,
        1,
        GET,
        0,
        GET,
        1,
        I32_ADD,
        SET,
        2,
        GET,
        2,
        I32_CONST,
        0,
        I32_CONST,
        4,
        MEMORY_FILL[0],
        MEMORY_FILL[1],
        MEMORY_FILL[2],
        I32_CONST,
        0,
    ];
    let p = premise_on(&pre);
    let dropped = [
        GET,
        0,
        I32_CONST,
        0,
        I32_CONST,
        4,
        MEMORY_FILL[0],
        MEMORY_FILL[1],
        MEMORY_FILL[2],
        I32_CONST,
        0,
    ];
    let e = run_premised(gep_case(&pre, &dropped), &[p]).expect_err("refused");
    assert_eq!(e.kind, TvFailureKind::EffectMismatch, "{e}");
    let kept = [
        GET,
        0,
        I32_CONST,
        8,
        I32_ADD,
        I32_CONST,
        0,
        I32_CONST,
        4,
        MEMORY_FILL[0],
        MEMORY_FILL[1],
        MEMORY_FILL[2],
        I32_CONST,
        0,
    ];
    run_premised(gep_case(&pre, &kept), &[p]).expect("accepted");
    // `i32.atomic.load offset=0` through the sum, and folded.
    let atomic_pre = [
        I32_CONST, 8, SET, 1, GET, 0, GET, 1, I32_ADD, SET, 2, GET, 2, 0xfe, 0x10, 2, 0, SET, 3,
        GET, 3,
    ];
    let atomic_post = [GET, 0, 0xfe, 0x10, 2, 8];
    // The checker's decoder has no atomics: no premise is admitted on such
    // a body, and none bound to another body applies.
    let c = check(
        &gep_module(WASM32, GEP_U8),
        &atomic_pre,
        &[claim(2, GEP_ADD_AT)],
    );
    assert_eq!(
        c.refused,
        vec![(claim(2, GEP_ADD_AT), NoWrapRefusal::Offset)],
        "{c:?}"
    );
    assert!(run_premised(gep_case(&atomic_pre, &atomic_post), &[p]).is_err());
    assert!(run_premised(gep_case(&atomic_pre, &atomic_pre), &[p]).is_err());
}

/// A scaled constant index (`u32` element, index 2) is admitted by the
/// checker, but its addend is a product the validator does not evaluate:
/// no fold is accepted for it.
#[test]
fn a_scaled_constant_index_is_not_folded() {
    let module = gep_module(WASM32, "%2 = gep u32, ptr %0, %1");
    let pre = [
        I32_CONST, 2, SET, 1, GET, 0, GET, 1, I32_CONST, 4, I32_MUL, I32_ADD, SET, 2, GET, 2,
        I32_LOAD, 2, 0, SET, 3, GET, 3,
    ];
    let c = check(&module, &pre, &[claim(2, 11)]);
    let [p] = c.premises.as_slice() else {
        panic!("{c:?}")
    };
    let e = run_premised(gep_case(&pre, GEP_FOLDED), &[*p]).expect_err("refused");
    assert_eq!(e.kind, TvFailureKind::EffectMismatch, "{e}");
}
