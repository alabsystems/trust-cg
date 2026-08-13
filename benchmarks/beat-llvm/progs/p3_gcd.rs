use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 { let t = a % b; a = b; b = t; }
    a
}
fn main() {
    let mut s: u64 = bb(0x9E3779B97F4A7C15u64);
    let mut acc: u64 = 0;
    let n = bb(4_000_000u64);
    let mut i = 0u64;
    while i < n {
        s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let a = (s >> 16) | 1;
        s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let b = (s >> 16) | 1;
        acc = acc.wrapping_add(gcd(a, b));
        i += 1;
    }
    done(acc);
}
