// vectorizable: byte-array popcount loop (LLVM vectorizes via psadbw/table tricks;
// the bridge emits proven width-32 popcnt). One byte mutates per rep so the
// computation carries a cross-rep dependence (no closed-form folding).
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
const N: usize = 4096;
fn main() {
    let mut x: u64 = bb(0x243F6A8885A308D3u64);
    let mut a = [0u8; N];
    let mut i = 0usize;
    while i < N {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        a[i] = (x & 0xFF) as u8;
        i += 1;
    }
    let reps = bb(60_000u32);
    let mut acc: u64 = 0;
    let mut r = 0u32;
    while r < reps {
        let mut i = 0usize;
        while i < N {
            acc = acc.wrapping_add((a[i] as u32).count_ones() as u64);
            i += 1;
        }
        a[r as usize % N] = (acc & 0xFF) as u8;
        r += 1;
    }
    done(acc);
}
