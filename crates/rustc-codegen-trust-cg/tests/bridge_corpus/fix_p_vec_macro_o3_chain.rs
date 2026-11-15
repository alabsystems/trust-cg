// `vec![a, b, c]` at -O2/-O3: rustc inlines the whole desugar into a box
// allocation, an Unsize and a `from_raw_parts_in` repackaging chain. The exit
// code folds every element and the length.
#[inline(never)]
fn sum_len(n: u64) -> u64 {
    let v = vec![n, n + 1, n + 2];
    let mut s = 0;
    let mut i = 0;
    while i < v.len() {
        s += v[i] * (i as u64 + 1);
        i += 1;
    }
    s * 10 + v.len() as u64
}
#[inline(never)]
fn mixed(n: u64) -> u64 {
    let v = vec![n.wrapping_mul(3), n ^ 0x55, n, n + 9];
    v[3] * 1000 + v[2] * 100 + v[1] * 10 + v[0] + v.len() as u64
}
fn main() {
    let n = std::hint::black_box(7u64);
    let a = mixed(n);
    let b = sum_len(n);
    std::process::exit(((a * 31 + b) % 251) as i32);
}
