// Trust-toolchain slice — the production trust-ir `edge_bounds`
// (trust-ir/crates/trust-ir/src/alloc_bound.rs:427) lowered VERBATIM over the
// real `ICmpOp` enum.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (2nd batch, fn #2).
//
// `edge_bounds(op, k)` is the per-comparison reasoning core of the trust-ir
// ALLOCATION-BOUNDS analyzer's guard pass (`guard_count_bound`, alloc_bound.rs:374
// calls it directly): given a comparison `count <op> K`, it returns the
// (then-edge, else-edge) UPPER BOUNDS on `count` implied by taking each branch.
// This is a genuine SOUNDNESS predicate — it is the arithmetic that decides
// whether a dominating guard proves an allocation count is bounded; a wrong
// edge bound here is a missed (or unsound) bounds proof.
//
// It is PURE, deterministic, closure-free, self-contained:
//   * an early-return on `k == None` and on `k < 0` (the negative-count case),
//   * a `k as u128` cast + `saturating_sub(1)` (real arithmetic, exercises the
//     k=0 saturation edge),
//   * a WIDE match over all 10 `ICmpOp` arms, each returning a distinct
//     `(Option<u128>, Option<u128>)` shape,
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O, NO rustc internals.
//
// TRANSCRIBED VERBATIM:
//   * `edge_bounds` (alloc_bound.rs:427-447) — THE EMIT ROOT, byte-for-byte.
//   * `ICmpOp` enum (inst.rs:75-86) — every variant in order (the match reads
//     the discriminant; layout/order must match the production enum).

#![allow(dead_code)]

// ── ICmpOp (inst.rs:73-86) — VERBATIM variant set & order (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ICmpOp {
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

/// For `count <cmp> K`, the (then-edge, else-edge) upper bounds on `count`.
/// Signed and unsigned compares are treated alike for a non-negative `K` — a
/// negative count is a separate allocation UB, so for an upper bound the
/// distinction is immaterial. `None` means that edge implies no upper bound.
fn edge_bounds(op: ICmpOp, k: Option<i128>) -> (Option<u128>, Option<u128>) {
    let Some(k) = k else { return (None, None) };
    if k < 0 {
        return (None, None);
    }
    let k = k as u128;
    let km1 = k.saturating_sub(1);
    match op {
        // count < K : then count ≤ K-1 ; else count ≥ K (unbounded)
        ICmpOp::Ult | ICmpOp::Slt => (Some(km1), None),
        // count ≤ K : then K ; else unbounded
        ICmpOp::Ule | ICmpOp::Sle => (Some(k), None),
        // count > K : then unbounded ; else count ≤ K
        ICmpOp::Ugt | ICmpOp::Sgt => (None, Some(k)),
        // count ≥ K : then unbounded ; else count ≤ K-1
        ICmpOp::Uge | ICmpOp::Sge => (None, Some(km1)),
        // count == K : then exactly K ; else unbounded
        ICmpOp::Eq => (Some(k), None),
        ICmpOp::Ne => (None, Some(k)),
    }
}

/// Map a small tag to an `ICmpOp` (covers every arm of `edge_bounds`).
fn op_for_tag(tag: u32) -> ICmpOp {
    match tag {
        0 => ICmpOp::Eq,
        1 => ICmpOp::Ne,
        2 => ICmpOp::Ult,
        3 => ICmpOp::Ule,
        4 => ICmpOp::Ugt,
        5 => ICmpOp::Uge,
        6 => ICmpOp::Slt,
        7 => ICmpOp::Sle,
        8 => ICmpOp::Sgt,
        _ => ICmpOp::Sge,
    }
}

// ── Pick ONE edge of the `(Option<u128>, Option<u128>)` result, returning a
//    single `Option<u128>`. This calls the REAL `edge_bounds` and SELECTS one
//    component — keeping the wrapper from ever materializing the whole 4×i128
//    tuple on its own stack (the full-tuple block-copy is what an earlier
//    `let (then, else) = edge_bounds(..)` wrapper tripped over in trust-cg ISel;
//    a single-Option returner is cleaner — see the run notes). The selection is
//    OUTSIDE the verified body. NOTE: this STILL exercises the full `edge_bounds`
//    body every call — it just picks one half of its tuple result.
fn edge_bound_pick(op: ICmpOp, k: Option<i128>, want_then: bool) -> Option<u128> {
    let edges = edge_bounds(op, k);
    if want_then {
        edges.0
    } else {
        edges.1
    }
}

// ── C-ABI entrypoint. The verified body is `edge_bounds`; this wrapper only
//    reconstructs the `Option<i128> k` from a presence flag + two i64 halves,
//    selects the `ICmpOp` from a tag, calls `edge_bound_pick` (which calls the
//    REAL fn and selects ONE `Option<u128>` edge), then flattens that single
//    Option to one scalar. The reconstruction + flatten are OUTSIDE the verified
//    body.
//
//    `which` selects:
//      0 -> then-edge present? (1/0)
//      1 -> then-edge value low 64 bits (0 if None)
//      2 -> then-edge value high 64 bits (0 if None)
//      3 -> else-edge present? (1/0)
//      4 -> else-edge value low 64 bits (0 if None)
//      5 -> else-edge value high 64 bits (0 if None)
#[no_mangle]
pub extern "C" fn edge_bounds_entry(
    op_tag: u32,
    k_present: u32,
    k_hi: i64,
    k_lo: u64,
    which: u32,
) -> u64 {
    let k: Option<i128> = if k_present != 0 {
        Some(((k_hi as i128) << 64) | (k_lo as i128))
    } else {
        None
    };
    let op = op_for_tag(op_tag);
    let want_then = which < 3;
    let edge = edge_bound_pick(op, k, want_then);
    // Extraction WITHOUT closures (so no `{closure#0}` mono-item shadows the
    // `edge_bounds` emit root and so the wrapper stays inside the verified surface).
    match which {
        0 | 3 => match edge {
            Some(_) => 1,
            None => 0,
        },
        1 | 4 => match edge {
            Some(v) => v as u64,
            None => 0,
        },
        _ => match edge {
            Some(v) => (v >> 64) as u64,
            None => 0,
        },
    }
}

fn main() {
    // Smoke: count < 10 -> then ≤ 9, else unbounded.
    println!("{}", edge_bounds_entry(2, 1, 0, 10, 0)); // then present? 1
    println!("{}", edge_bounds_entry(2, 1, 0, 10, 1)); // then low = 9
    println!("{}", edge_bounds_entry(2, 1, 0, 10, 3)); // else present? 0
    println!("{}", edge_bounds_entry(0, 0, 0, 0, 0)); // k=None -> then present? 0
}
