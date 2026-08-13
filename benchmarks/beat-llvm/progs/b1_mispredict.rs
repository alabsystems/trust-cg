// branch: mispredict-shaped — data-dependent unpredictable branches from an RNG
// stream, each arm doing DIFFERENT work including stores to different scratch
// slots (defeats full if-conversion/cmov), plus a nested unpredictable branch.
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
fn main() {
    let n = bb(60_000_000u64);
    let mut s: u64 = bb(0x9E3779B97F4A7C15u64);
    let mut t = [0u64; 16];
    let mut acc: u64 = 0;
    let mut i = 0u64;
    while i < n {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        if s & 1 == 0 {
            acc = acc.wrapping_add(s >> 3);
            let j = ((s >> 4) & 15) as usize;
            t[j] ^= s;
        } else {
            acc ^= s.wrapping_mul(0x2545F4914F6CDD1D);
            let j = ((s >> 8) & 15) as usize;
            t[j] = t[j].wrapping_add(acc);
        }
        if s & 6 == 2 {
            acc = acc.rotate_left(7);
        }
        i += 1;
    }
    let mut k = 0usize;
    while k < 16 {
        acc = acc.wrapping_add(t[k]);
        k += 1;
    }
    done(acc);
}
