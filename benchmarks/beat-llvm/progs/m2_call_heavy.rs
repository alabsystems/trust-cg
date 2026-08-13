// multifn: call-heavy hot loop — #[inline(never)] callees so BOTH lanes pay real
// calls (~80M calls). Measures call ABI + prologue/epilogue + regalloc-around-call
// quality rather than inlining.
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
#[inline(never)]
fn step(mut s: u64) -> u64 {
    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
    s
}
#[inline(never)]
fn mix(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b | 1) ^ (a >> 11)
}
fn main() {
    let n = bb(40_000_000u64);
    let mut s: u64 = bb(0x243F6A8885A308D3u64);
    let mut acc: u64 = bb(7u64);
    let mut i = 0u64;
    while i < n {
        s = step(s);
        acc = mix(acc, s);
        i += 1;
    }
    done(acc);
}
