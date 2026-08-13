// Trust-toolchain slice — the production trust-ir `swap_cmp`
// (trust-ir/crates/trust-ir/src/alloc_bound.rs:450) lowered VERBATIM over the
// real `ICmpOp` enum.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (2nd batch, fn #3).
//
// `swap_cmp(op)` is the operand-swap law of comparisons: the `c` such that
// `K op count` ≡ `count c K`. The trust-ir ALLOCATION-BOUNDS guard pass uses it
// (`guard_count_bound`, alloc_bound.rs:402) to normalize a guard written
// `K <op> count` into the `count <swap_cmp(op)> K` form `edge_bounds` expects.
// A wrong swap here would invert a bound direction — an unsound bounds proof.
//
// It is PURE, deterministic, closure-free, self-contained:
//   * a TOTAL match over all 10 `ICmpOp` arms, each returning a (possibly
//     different) `ICmpOp` — the strict/order-reversing pairs swap (Ult<->Ugt,
//     Slt<->Sgt, etc.) while Eq/Ne are fixed points,
//   * it returns an ENUM VALUE (exercises niche-encoded discriminant emission on
//     the RESULT, a different surface from the predicates that return bool/int),
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O, NO rustc internals.
//
// TRANSCRIBED VERBATIM:
//   * `swap_cmp` (alloc_bound.rs:449-463) — THE EMIT ROOT, byte-for-byte.
//   * `ICmpOp` enum (inst.rs:75-86) — every variant in order.

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

/// The comparison `c` such that `K op count` ≡ `count c K` (operand swap).
fn swap_cmp(op: ICmpOp) -> ICmpOp {
    match op {
        ICmpOp::Ult => ICmpOp::Ugt,
        ICmpOp::Ule => ICmpOp::Uge,
        ICmpOp::Ugt => ICmpOp::Ult,
        ICmpOp::Uge => ICmpOp::Ule,
        ICmpOp::Slt => ICmpOp::Sgt,
        ICmpOp::Sle => ICmpOp::Sge,
        ICmpOp::Sgt => ICmpOp::Slt,
        ICmpOp::Sge => ICmpOp::Sle,
        ICmpOp::Eq => ICmpOp::Eq,
        ICmpOp::Ne => ICmpOp::Ne,
    }
}

/// Map a small tag to an `ICmpOp`.
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

/// Map an `ICmpOp` back to its tag (inverse of `op_for_tag`).
fn tag_for_op(op: ICmpOp) -> u32 {
    match op {
        ICmpOp::Eq => 0,
        ICmpOp::Ne => 1,
        ICmpOp::Ult => 2,
        ICmpOp::Ule => 3,
        ICmpOp::Ugt => 4,
        ICmpOp::Uge => 5,
        ICmpOp::Slt => 6,
        ICmpOp::Sle => 7,
        ICmpOp::Sgt => 8,
        ICmpOp::Sge => 9,
    }
}

// ── C-ABI entrypoint. The verified body is `swap_cmp`; this wrapper only selects
//    the `ICmpOp` from a tag, calls the REAL fn, and maps the result ENUM back to
//    a tag (both maps are OUTSIDE the verified body). ──
#[no_mangle]
pub extern "C" fn swap_cmp_entry(op_tag: u32) -> u32 {
    let op = op_for_tag(op_tag);
    tag_for_op(swap_cmp(op))
}

fn main() {
    // Smoke: swap_cmp(Ult) = Ugt (tag 2 -> 4); Eq fixed (0 -> 0).
    println!("{}", swap_cmp_entry(2)); // 4
    println!("{}", swap_cmp_entry(4)); // 2
    println!("{}", swap_cmp_entry(0)); // 0
    println!("{}", swap_cmp_entry(6)); // Slt -> Sgt = 8
}
