// (d) `select_unpredictable` over a FAT pointer (`&str` / `&[u8]`) and an
// aggregate (`String`): the discriminant lane's intrinsic fallback-body redirect
// (and the dedicated `Select` arm at -O0) admitted them and returned wrong
// values (`47 47` / `401 401` for `3 2` / `306 0`). Now gated on rustc's
// `BackendRepr::Scalar` for `T`: this program is REFUSED (fail-closed) at every
// opt level; the scalar selects stay covered by the lane corpus.
#![feature(core_intrinsics)]
#![allow(internal_features, dead_code)]
use core::hint::select_unpredictable as sel;
#[inline(never)] fn s_u8(c: bool, a: u8, b: u8) -> u8 { sel(c, a, b) }
#[inline(never)] fn s_str(c: bool, a: &str, b: &str) -> usize { sel(c, a, b).len() }
#[inline(never)] fn s_slice(c: bool, a: &[u8], b: &[u8]) -> u64 { let s = sel(c, a, b); s.iter().map(|x| *x as u64).sum::<u64>() + s.len() as u64 * 100 }
#[inline(never)] fn s_string(c: bool, a: String, b: String) -> usize { sel(c, a, b).len() }
fn main() {
    println!("u8 {} {}", s_u8(true, 255, 1), s_u8(false, 255, 1));
    println!("str {} {} slice {} {}", s_str(true, "abc", "de"), s_str(false, "abc", "de"), s_slice(true, &[1, 2, 3], &[]), s_slice(false, &[1, 2, 3], &[]));
    println!("string {} {}", s_string(true, String::from("hello"), String::from("hi")), s_string(false, String::from("hello"), String::from("hi")));
}
