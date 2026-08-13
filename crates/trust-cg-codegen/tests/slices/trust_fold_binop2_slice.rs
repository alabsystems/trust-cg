// SELF-CONTAINED trust-ir `fold_binop` slice — the REAL constant-folder the
// ALLOCATION-BOUND analysis uses, copied VERBATIM from
// trust-ir/crates/trust-ir/src/alloc_bound.rs:247 (`fold_binop`) plus the `BinOp`
// enum (inst.rs:11) it dispatches on.
//
// WHY SOUNDNESS-CRITICAL: `fold_binop` folds integer arithmetic on KNOWN constants
// while bounding the size of an allocation. Every arm is overflow-AWARE: it returns
// `None` (give up / no static bound) rather than a WRONG (wrapped) value, because a
// wrapped fold would under-estimate an allocation's size and produce an out-of-bounds
// access — a memory-safety miscompile. The `Shl` arm is the subtle one: it folds
// `a << b` as `a * 2^b` precisely so `checked_mul` catches value overflow, and it
// range-checks `0..128` on the shift amount first. A trust-cg miscompile of the
// checked-arith chain (`checked_add`/`sub`/`mul`, `checked_shl().and_then(checked_mul)`)
// or the `Option<i128>` plumbing (`lhs?`/`rhs?`) is a real soundness bug.
//
// Faithfulness: `BinOp` is the VERBATIM production variant SET + ORDER (a fieldless
// C-like enum -> 1-byte discriminant), so the emitted `switch` over the op matches
// the native value. `fold_binop` is byte-for-byte the production body. The
// `Option<i128>` ABI is rustc's (no niche -> a 32-byte `(disc, i128)`). A bail here
// is a REAL frontend gap on REAL Trust analysis code.

#![allow(dead_code)]
#![allow(clippy::all)]

// ---- the production `BinOp` enum, VERBATIM variant SET + ORDER (inst.rs:11-40) ----
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

// alloc_bound.rs:247-265, transcribed with ONE faithful rewrite: the production
// Shl-arm range guard `if !(0..128).contains(&b)` becomes the SEMANTICALLY-IDENTICAL
// `if b < 0 || b >= 128`. Reason: the stage1 MIR frontend cannot lower the
// `Range<i128>` const aggregate `Range::contains` builds (`constant value not a
// single scalar` — a real frontend gap, reported separately); the comparison form
// is provably equivalent (`(0..128).contains(&b)` IS `0 <= b && b < 128`). Every
// arm's ARITHMETIC — `checked_add/sub/mul`, the bitwise `& | ^`, and the Shl
// `1i128.checked_shl(b as u32).and_then(|m| a.checked_mul(m))` overflow chain — is
// BYTE-IDENTICAL to production, as is the `?`-operator `Option<i128>` plumbing and
// the `BinOp` switch.
fn fold_binop(op: BinOp, lhs: Option<i128>, rhs: Option<i128>) -> Option<i128> {
    let (a, b) = (lhs?, rhs?);
    match op {
        BinOp::Add => a.checked_add(b),
        BinOp::Sub => a.checked_sub(b),
        BinOp::Mul => a.checked_mul(b),
        BinOp::And => Some(a & b),
        BinOp::Or => Some(a | b),
        BinOp::Xor => Some(a ^ b),
        BinOp::Shl => {
            // Fold via `a * 2^b` so value overflow is caught by `checked_mul`.
            // (`(0..128).contains(&b)` rewritten to the equivalent comparisons.)
            if b < 0 || b >= 128 {
                return None;
            }
            1i128.checked_shl(b as u32).and_then(|m| a.checked_mul(m))
        }
        _ => None,
    }
}

// A `#[no_mangle]` mono ROOT. The `Option<i128>` args/result are sentinel-encoded for
// the FFI boundary: `lhs_present`/`rhs_present` flags gate the values, and the result
// is `(present: bool, value: i128)` packed into the two out-params via a tiny struct.
// `fold_binop` ITSELF stays VERBATIM.
#[repr(C)]
pub struct FoldOut {
    pub present: u8,
    pub value: i128,
}

// `op` crosses the FFI boundary as a `u8` (then mapped to the in-module `BinOp`,
// whose 20 fieldless variants rustc lays out as a u8 discriminant — same byte) so
// the root is FFI-safe WITHOUT putting a `#[repr]` on `BinOp` (which must keep the
// production no-repr-hint layout the emitted `switch` decodes).
fn binop_from_u8(b: u8) -> BinOp {
    match b {
        0 => BinOp::Add,
        1 => BinOp::Sub,
        2 => BinOp::Mul,
        3 => BinOp::UDiv,
        4 => BinOp::SDiv,
        5 => BinOp::URem,
        6 => BinOp::SRem,
        7 => BinOp::FAdd,
        8 => BinOp::FSub,
        9 => BinOp::FMul,
        10 => BinOp::FDiv,
        11 => BinOp::FRem,
        12 => BinOp::FMin,
        13 => BinOp::FMax,
        14 => BinOp::And,
        15 => BinOp::Or,
        16 => BinOp::Xor,
        17 => BinOp::Shl,
        18 => BinOp::LShr,
        _ => BinOp::AShr,
    }
}

#[no_mangle]
pub extern "C" fn fold_binop_root(
    op: u8,
    lhs_present: bool,
    lhs: i128,
    rhs_present: bool,
    rhs: i128,
) -> FoldOut {
    let l = if lhs_present { Some(lhs) } else { None };
    let r = if rhs_present { Some(rhs) } else { None };
    match fold_binop(binop_from_u8(op), l, r) {
        Some(v) => FoldOut { present: 1, value: v },
        None => FoldOut { present: 0, value: 0 },
    }
}

fn main() {}
