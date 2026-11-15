// b1 with MINIMAL arms: same unpredictable branch, far less work per arm. If the bridge's
// gap is wrong-path work, it must shrink here; if it is the branch itself, it must not.
use std::hint::black_box as bb;
fn done(code: u64) -> ! { std::process::exit((code % 126) as i32) }
fn main() {
    let n = bb(60_000_000u64);
    let mut s: u64 = bb(0x9E3779B97F4A7C15u64);
    let mut acc: u64 = 0;
    let mut i = 0u64;
    while i < n {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        if s & 1 == 0 { acc = acc.wrapping_add(s); } else { acc ^= s; }
        i += 1;
    }
    done(acc)
}
