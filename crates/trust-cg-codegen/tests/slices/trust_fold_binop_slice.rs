// Trust-toolchain slice — the production trust-ir `fold_binop`
// (trust-ir/crates/trust-ir/src/alloc_bound.rs:247) lowered VERBATIM over the
// real `BinOp` enum, restricted to its CLOSURE-FREE arms.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF, targeting the
// Option<i128> (16-byte discriminant tag) CLASS that the frontend width-16
// addition unblocks.
//
// `fold_binop(op, lhs, rhs)` is the constant-folding core of the trust-ir
// ALLOCATION-BOUNDS analyzer (`alloc_bound.rs`): given a binary op and two
// already-folded `Option<i128>` operands, it returns the folded constant or
// `None` (operand unknown, or arithmetic OVERFLOW). This is a genuine SOUNDNESS
// computation — a wrong fold here is a wrong byte-budget verdict.
//
// It is PURE, deterministic, self-contained, and — for the arms transcribed
// here — closure-free:
//   * the `let (a, b) = (lhs?, rhs?)` early-return on either operand `None`
//     (the `?` on Option<i128> — a 16-byte-tag discriminant READ),
//   * a match over `BinOp` returning `Option<i128>` (a 16-byte-tag CONSTRUCT),
//   * real `checked_add`/`checked_sub`/`checked_mul` i128 arithmetic that
//     returns `None` on OVERFLOW (the Some(v)/None boundary the test exercises),
//   * bitwise `&`/`|`/`^` arms returning `Some(a OP b)`,
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O, NO rustc internals.
//
// The production `fold_binop` additionally has a `Shl` arm
// (`1i128.checked_shl(b as u32).and_then(|m| a.checked_mul(m))`) whose
// `Option::and_then(closure)` constructs a `{closure#0}` aggregate the frontend
// deliberately does not lower (RUNG 4). It is REPLACED here by the same
// `_ => None` catch-all the production fn already uses for every other BinOp
// variant (UDiv/SDiv/shifts/floats), so the emit root stays inside the verified
// surface WITHOUT changing the semantics of any arm that IS present. This is the
// `fold_binop` of the closure-free op set — faithful for those arms byte-for-byte.
//
// TRANSCRIBED VERBATIM:
//   * `BinOp` enum (inst.rs:11-35) — every variant in order (the match reads the
//     discriminant; layout/order must match the production enum).
//   * `fold_binop` (alloc_bound.rs:247-265) — THE EMIT ROOT; every arm present is
//     byte-for-byte the production arm (only the `Shl` arm is folded into the
//     existing `_ => None`, see above).

#![allow(dead_code)]

// ── BinOp (inst.rs:11-35) — VERBATIM variant set & order (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    FAdd,
    FSub,
    FMul,
    FDiv,
    FRem,
    FMin,
    FMax,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
}

// ── fold_binop (alloc_bound.rs:247-265) — THE EMIT ROOT. Every arm present is the
//    production arm verbatim; the closure-bearing `Shl` arm is folded into the
//    existing production `_ => None` catch-all (see header). ──
fn fold_binop(op: BinOp, lhs: Option<i128>, rhs: Option<i128>) -> Option<i128> {
    let (a, b) = (lhs?, rhs?);
    match op {
        BinOp::Add => a.checked_add(b),
        BinOp::Sub => a.checked_sub(b),
        BinOp::Mul => a.checked_mul(b),
        BinOp::And => Some(a & b),
        BinOp::Or => Some(a | b),
        BinOp::Xor => Some(a ^ b),
        _ => None,
    }
}

/// Map a small tag to a `BinOp` (covers every arm of this `fold_binop`).
fn op_for_tag(tag: u32) -> BinOp {
    match tag {
        0 => BinOp::Add,
        1 => BinOp::Sub,
        2 => BinOp::Mul,
        3 => BinOp::And,
        4 => BinOp::Or,
        5 => BinOp::Xor,
        // A non-folded arm hits the `_ => None` catch-all.
        _ => BinOp::UDiv,
    }
}

// ── C-ABI entrypoint. The verified body is `fold_binop`; this wrapper only
//    reconstructs the two `Option<i128>` operands from presence flags + i64
//    halves, selects the `BinOp` from a tag, calls the REAL fn, then EXTRACTS one
//    scalar component of the `Option<i128>` result according to `which`. The
//    reconstruction + extraction are OUTSIDE the verified body (no closures, so no
//    `{closure#0}` mono-item shadows the `fold_binop` emit root).
//
//    `which` selects:
//      0 -> result present? (1/0)
//      1 -> result value low 64 bits (0 if None)
//      2 -> result value high 64 bits (0 if None)
#[no_mangle]
pub extern "C" fn fold_binop_entry(
    op_tag: u32,
    lhs_present: u32,
    lhs_hi: i64,
    lhs_lo: u64,
    rhs_present: u32,
    rhs_hi: i64,
    rhs_lo: u64,
    which: u32,
) -> u64 {
    let lhs: Option<i128> = if lhs_present != 0 {
        Some(((lhs_hi as i128) << 64) | (lhs_lo as i128))
    } else {
        None
    };
    let rhs: Option<i128> = if rhs_present != 0 {
        Some(((rhs_hi as i128) << 64) | (rhs_lo as i128))
    } else {
        None
    };
    let op = op_for_tag(op_tag);
    let result = fold_binop(op, lhs, rhs);
    match which {
        0 => match result {
            Some(_) => 1,
            None => 0,
        },
        1 => match result {
            Some(v) => v as u64,
            None => 0,
        },
        _ => match result {
            Some(v) => (v >> 64) as u64,
            None => 0,
        },
    }
}

fn split(value: i128) -> (i64, u64) {
    ((value >> 64) as i64, value as u64)
}

fn main() {
    // Smoke: 2 + 3 = Some(5).
    let (ah, al) = split(2);
    let (bh, bl) = split(3);
    println!("{}", fold_binop_entry(0, 1, ah, al, 1, bh, bl, 0)); // present? 1
    println!("{}", fold_binop_entry(0, 1, ah, al, 1, bh, bl, 1)); // low = 5
    // i128::MAX + 1 -> checked_add overflow -> None.
    let (mh, ml) = split(i128::MAX);
    let (oh, ol) = split(1);
    println!("{}", fold_binop_entry(0, 1, mh, ml, 1, oh, ol, 0)); // present? 0
    // lhs = None -> None.
    println!("{}", fold_binop_entry(0, 0, 0, 0, 1, bh, bl, 0)); // present? 0
}
