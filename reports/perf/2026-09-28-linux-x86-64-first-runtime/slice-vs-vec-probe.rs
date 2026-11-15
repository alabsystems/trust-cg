use std::hint::black_box as bb;
fn done(code: u64) -> ! { std::process::exit((code % 126) as i32) }
#[inline(never)]
fn sum_slice(s: &[u64]) -> u64 {
    let mut acc = 0u64; let mut k = 0usize;
    while k < s.len() { acc = acc.wrapping_add(s[k]); k += 1; }
    acc
}
#[inline(never)]
fn sum_vec(v: &Vec<u64>) -> u64 {
    let mut acc = 0u64; let mut k = 0usize;
    while k < v.len() { acc = acc.wrapping_add(v[k]); k += 1; }
    acc
}
fn main() {
    let n = bb(1000usize);
    let mut v: Vec<u64> = Vec::new();
    let mut i = 0usize;
    while i < n { v.push(bb(i as u64)); i += 1; }
    done(sum_slice(&v).wrapping_add(sum_vec(&v)))
}
