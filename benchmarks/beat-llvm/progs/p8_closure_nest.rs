use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
fn main() {
    let k = bb(17u64);
    let step = |x: u64, y: u64| -> u64 { x.wrapping_mul(k | 1).wrapping_add(y ^ (x >> 9)) };
    let n = bb(20_000u64);
    let m = bb(10_000u64);
    let mut acc: u64 = bb(5u64);
    let mut i = 0u64;
    while i < n {
        let mut j = 0u64;
        while j < m {
            acc = step(acc, i.wrapping_mul(j));
            j += 1;
        }
        i += 1;
    }
    done(acc);
}
