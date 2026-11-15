// CORPUS FIXTURE — `impl Sum<Local> for u64` runs its OWN body.
//
// The accumulator is a PRIMITIVE `u64`, so an accumulator-only check would call this
// core's integer `Sum` — but the impl is the USER's (`Sum<M>` with a local `M`
// satisfies the orphan rule), which is exactly why `std_sum_product_arith` also
// requires the item to be `S` or `&S`. Measured on the unpatched base: LLVM
// `1000 5000`, the bridge `6 5007` (a bare add). Now the interception steps aside to
// the real `Iterator::sum`, which calls this impl.
//
// HOW IT FAILS IF THE ITEM CONJUNCT IS REMOVED: it COMPILES and DIVERGES from LLVM
// (mutation-measured: `6 5007`) — a hard failure.
use std::iter::Sum;
#[derive(Clone, Copy)]
struct M(u64);
impl Sum<M> for u64 {
    fn sum<I: Iterator<Item = M>>(it: I) -> u64 {
        let mut best = 1000;
        for m in it {
            if m.0 > best {
                best = m.0;
            }
        }
        best
    }
}
#[inline(never)]
fn f(v: &[u64]) -> u64 {
    v.iter().map(|&x| M(x)).sum::<u64>()
}
fn main() {
    println!("{} {}", f(&[1, 2, 3]), f(&[5000, 7]));
}
