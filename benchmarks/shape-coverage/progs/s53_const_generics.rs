// const-generic functions and arrays (fn f<const N: usize>) — the value N drives
// loop bounds and array sizes across monomorphizations.
use std::hint::black_box as bb;
fn dot<const N: usize>(a: &[u64; N], b: &[u64; N]) -> u64 {
    let mut s = 0u64; for i in 0..N { s = s.wrapping_add(a[i].wrapping_mul(b[i])); } s
}
fn sum_sq<const N: usize>(xs: [u64; N]) -> u64 { let mut s=0u64; for i in 0..N { s=s.wrapping_add(xs[i].wrapping_mul(xs[i])); } s }
fn main() {
    let mut acc: u64 = 0;
    acc = acc.wrapping_add(dot(&[bb(1u64),bb(2),bb(3)], &[bb(4u64),bb(5),bb(6)]));
    acc = acc.wrapping_add(dot(&[bb(7u64),bb(8)], &[bb(9u64),bb(10)]));
    acc = acc.wrapping_add(sum_sq([bb(2u64),bb(3),bb(4),bb(5)]));
    std::process::exit((acc % 251) as i32);
}
