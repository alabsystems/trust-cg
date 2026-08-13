use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
fn main() {
    let mut x: u64 = bb(0x243F6A8885A308D3u64);
    let mut acc: u64 = 0;
    let n = bb(400_000_000u64);
    let mut i = 0u64;
    while i < n {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        acc = acc.wrapping_add(x);
        i += 1;
    }
    done(acc);
}
