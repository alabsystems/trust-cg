// A `for` loop over a range whose Range struct rustc CONST-FOLDS, so the
// `IntoIterator::into_iter` argument arrives as `Operand::Constant` and there
// is no source place to copy the iterator state from:
//
//   -O1, literal bound:   into_iter(const Range::<usize> {{ start: 0, end: 64 }})
//   any opt, const item:  into_iter(const R)
//
// Both shapes declined with "Range::into_iter argument is not a place" — a
// hard compile error, since the bridge has no per-function fallback. The
// literal-bound form is ordinary Rust and hit four programs in this corpus at
// -O1 alone. RangeInclusive has the same lowering and the same gap; only the
// const-ITEM form reaches it, because `a..=b` otherwise goes through
// `RangeInclusive::new(start, end)` and arrives as a place.
use std::hint::black_box as bb;

const R: std::ops::Range<u64> = 0..16;
const RI: std::ops::RangeInclusive<u64> = 0..=15;

fn main() {
    let mut acc: u64 = 0;
    // Literal bound: const-folded to an aggregate constant at -O1.
    for i in 0..64usize {
        acc = acc.wrapping_mul(31).wrapping_add(i as u64);
    }
    // Const ITEM, Range and RangeInclusive: `const R` at every opt level.
    for i in R {
        acc = acc.wrapping_mul(3).wrapping_add(i);
    }
    for i in RI {
        acc = acc.wrapping_add(i.wrapping_mul(7));
    }
    // A dynamic bound still arrives as a place — keep the original path covered.
    let n = bb(24u64);
    for i in 0..n {
        acc = acc.wrapping_add(i);
    }
    for i in 0..=n {
        acc = acc.wrapping_add(i.wrapping_mul(5));
    }
    std::process::exit((bb(acc) % 126) as i32);
}
