// Four modules, each calling the same `#[inline]` core items: rustc gives
// every CGU that uses `<u64 as PartialOrd>::le`/`lt` and `<i64 as From<i8>>::from`
// its own `Internal` copy, all under one mangled name.
use std::hint::black_box as bb;
mod a { #[inline(never)] pub fn f(x: u64, y: u64) -> bool { PartialOrd::le(&x, &y) && PartialOrd::lt(&x, &(y + 1)) } }
mod b { #[inline(never)] pub fn g(x: u64, y: u64) -> bool { PartialOrd::le(&y, &x) || PartialOrd::lt(&y, &x) } }
mod c { #[inline(never)] pub fn h(x: i8) -> i64 { i64::from(x) * 3 } }
mod d { #[inline(never)] pub fn k(x: i8) -> i64 { i64::from(x) + 7 } }
fn main() { println!("{} {} {} {}", a::f(bb(3), bb(5)), b::g(bb(3), bb(5)), c::h(bb(-4)), d::k(bb(5))); }
