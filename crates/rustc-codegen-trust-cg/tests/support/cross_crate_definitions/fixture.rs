// Library half of the cross-crate local-copy regression. Each item gives rustc
// a function that it copies into EVERY crate that uses it, as an `Internal`
// mono item under one mangled name that names no instantiating crate:
// `<u64 as From<u16>>::from` (reified as a fn pointer) and `<i128>::wrapping_mul`
// at O0/O1, and the vtable method `<TA as Tr>::t`, which rustc makes
// cross-crate-inlinable from O2.
use std::hint::black_box as bb;

pub trait Tr {
    fn t(&self) -> u64;
}

pub struct TA(pub u64);

impl Tr for TA {
    fn t(&self) -> u64 {
        self.0.wrapping_mul(3) + 1
    }
}

#[inline(never)]
pub fn use_dyn(d: &dyn Tr) -> u64 {
    d.t()
}

#[inline(never)]
pub fn mk(k: u64) -> u64 {
    let ta = TA(k);
    let d: &dyn Tr = &ta;
    use_dyn(d)
}

#[inline(never)]
pub fn widen(g: u16) -> u64 {
    let f: fn(u16) -> u64 = u64::from;
    bb(f)(g)
}

#[inline(never)]
pub fn wide(h: i128) -> u64 {
    let x = h.wrapping_mul(3).wrapping_add(0x11);
    (x as u64) ^ ((x >> 64) as u64)
}
