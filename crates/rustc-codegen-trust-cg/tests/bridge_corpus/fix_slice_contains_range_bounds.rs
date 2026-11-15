// CORPUS FIXTURE — core's provided `RangeBounds::contains`, for a user
// `impl RangeBounds<Lim> for [u32]`, answers from the user's bounds.
//
// WHAT IT PINS. The slice `contains` interception recognized
// `<[T]>::contains` by a crate test on the callee, the name and a `&[T]`
// receiver. `RangeBounds::contains` is a provided method of a core trait with
// the same `(&[u32], &u32)` arguments, so it was replaced by an element scan:
// with both bounds `Unbounded` every value is contained, but the scan answered
// `false` for a value absent from the slice. Measured on 6b108b81d: the
// `absent` check diverged from LLVM at -O0..-O3 (exit 5). The callee must now
// be core's own inherent `<[T]>::contains`.
//
// HOW IT FAILS IF THE FIX IS REVERTED. It compiles and DIVERGES from LLVM: the
// exit code carries one bit per wrong answer.

use std::cmp::Ordering;
use std::hint::black_box as bb;
use std::ops::{Bound, RangeBounds};

pub struct Lim(pub u32);

impl PartialEq<u32> for Lim {
    fn eq(&self, o: &u32) -> bool {
        self.0 == *o
    }
}

impl PartialOrd<u32> for Lim {
    fn partial_cmp(&self, o: &u32) -> Option<Ordering> {
        self.0.partial_cmp(o)
    }
}

impl PartialEq<Lim> for u32 {
    fn eq(&self, o: &Lim) -> bool {
        *self == o.0
    }
}

impl PartialOrd<Lim> for u32 {
    fn partial_cmp(&self, o: &Lim) -> Option<Ordering> {
        self.partial_cmp(&o.0)
    }
}

impl RangeBounds<Lim> for [u32] {
    fn start_bound(&self) -> Bound<&Lim> {
        Bound::Unbounded
    }
    fn end_bound(&self) -> Bound<&Lim> {
        Bound::Unbounded
    }
}

#[inline(never)]
fn in_bounds(s: &[u32], x: &u32) -> bool {
    RangeBounds::<Lim>::contains(s, x)
}

fn main() {
    let s = [bb(1u32), 2, 3];
    let (present, absent) = (bb(2u32), bb(9u32));
    let mut code = 0;
    if !in_bounds(&s, &present) {
        code |= 1;
    }
    if !in_bounds(&s, &absent) {
        code |= 2;
    }
    std::process::exit(code + 3);
}
