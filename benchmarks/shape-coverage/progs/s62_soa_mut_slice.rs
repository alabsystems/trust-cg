// struct-of-arrays processing: a helper taking &[T], &[T], &mut [T]; index-writes
// into the mut slice, then fold. Common data-parallel shape.
use std::hint::black_box as bb;
fn process(xs: &[u64], ys: &[u64], out: &mut [u64]) {
    for i in 0..out.len() { out[i] = xs[i].wrapping_mul(2).wrapping_add(ys[i].wrapping_sub(1)); }
}
fn main() {
    let n = bb(64usize);
    let xs: Vec<u64> = (0..n as u64).collect();
    let ys: Vec<u64> = (0..n as u64).map(|i| i.wrapping_mul(7)).collect();
    let mut out = vec![0u64; n];
    process(&xs, &ys, &mut out);
    let acc = out.iter().fold(0u64, |p, &v| p.wrapping_mul(31).wrapping_add(v));
    std::process::exit((acc % 239) as i32);
}
