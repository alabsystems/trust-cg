// heap: growth-heavy Vec — push to 6M elements with interleaved data-dependent
// index reads (realloc/memcpy pressure), then one final sum pass. Exits without
// dropping the Vec (std::process::exit).
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
fn main() {
    let n = bb(6_000_000usize);
    let mut x: u64 = bb(88172645463325252u64);
    let mut v: Vec<u64> = Vec::new();
    let mut acc: u64 = 0;
    while v.len() < n {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        v.push(x);
        if v.len() & 1023 == 0 {
            acc ^= v[(x as usize) % v.len()];
        }
    }
    let mut k = 0usize;
    while k < v.len() {
        acc = acc.wrapping_add(v[k]);
        k += 1;
    }
    done(acc);
}
