// vectorizable: i32 saxpy-like kernel — a[i] = a[i]*k + b[i] over a fixed array,
// repeated; the audited 7-9x auto-vectorization-loss class (contract G1b band).
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
const N: usize = 4096;
fn main() {
    let k = bb(3i32);
    let mut a = [0i32; N];
    let mut b = [0i32; N];
    let mut i = 0usize;
    while i < N {
        a[i] = (i as i32).wrapping_mul(7).wrapping_add(1);
        b[i] = (i as i32).wrapping_mul(13).wrapping_sub(5);
        i += 1;
    }
    let reps = bb(200_000u32);
    let mut acc: u64 = 0;
    let mut r = 0u32;
    while r < reps {
        let mut i = 0usize;
        while i < N {
            a[i] = a[i].wrapping_mul(k).wrapping_add(b[i]);
            i += 1;
        }
        acc = acc.wrapping_add(a[(r as usize).wrapping_mul(61) % N] as u32 as u64);
        r += 1;
    }
    done(acc);
}
