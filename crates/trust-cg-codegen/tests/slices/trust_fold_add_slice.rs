// Trust-toolchain slice — `fold_add`, the `BinOp::Add` arm of the production
// trust-ir `fold_binop` (alloc_bound.rs:247,250) lifted to its own root.
//
// `fold_add(lhs, rhs) -> Option<i128>` is the constant-folding ADD of the
// allocation-bounds analyzer: it returns the folded i128 sum, or `None` on
// integer OVERFLOW (`checked_add`) or if either operand is unknown. This is the
// EXACT arithmetic `fold_binop(BinOp::Add, ..)` performs — the single-`Option<i128>`
// returner the width-16 (16-byte discriminant tag) class targets.
//
// It uses explicit `match` on the operand Options (rather than the `?` operator)
// so the emit stays free of the `Try::branch`/`from_residual` closure stubs; the
// ARITHMETIC is byte-identical to the production `a.checked_add(b)`. `checked_add`
// on i128 is a `core` intrinsic the frontend lowers to an empty leaf body — the
// SAME documented shim discipline as `total_bits`'s u32 `checked_add` and
// `type_max`'s `sub.overflow` (here `add.overflow i128`).
//
//   * the operand match is a 16-byte-tag Option<i128> READ,
//   * the `Option<i128>` result is a 16-byte-tag CONSTRUCT,
//   * `checked_add` returns `None` on overflow (the Some/None boundary),
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O.

#![allow(dead_code)]

fn fold_add(lhs: Option<i128>, rhs: Option<i128>) -> Option<i128> {
    match (lhs, rhs) {
        (Some(a), Some(b)) => a.checked_add(b),
        _ => None,
    }
}

#[no_mangle]
pub extern "C" fn fold_add_entry(
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
    let r = fold_add(lhs, rhs);
    match which {
        0 => match r { Some(_) => 1, None => 0 },
        1 => match r { Some(v) => v as u64, None => 0 },
        _ => match r { Some(v) => (v >> 64) as u64, None => 0 },
    }
}

fn split(value: i128) -> (i64, u64) {
    ((value >> 64) as i64, value as u64)
}

fn main() {
    let (ah, al) = split(2);
    let (bh, bl) = split(3);
    println!("{}", fold_add_entry(1, ah, al, 1, bh, bl, 1)); // 5
    let (mh, ml) = split(i128::MAX);
    let (oh, ol) = split(1);
    println!("{}", fold_add_entry(1, mh, ml, 1, oh, ol, 0)); // overflow -> 0
}
