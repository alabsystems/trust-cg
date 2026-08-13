// GOAL-3 perf baseline benchmark.
// Float kernel: dot product of two fixed f64 vectors, repeated.
// The float result is folded into an integer checksum via bit operations on
// a scaled, truncated value so the exit code stays a stable byte.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

const N: usize = 512;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0f64; N];
    let mut b = [0f64; N];
    let mut i = 0;
    while i < N {
        a[i] = ((i % 17) as f64) * 0.5 + 1.0;
        b[i] = ((i % 13) as f64) * 0.25 + 0.5;
        i += 1;
    }
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 45000 {
        let mut dot: f64 = 0.0;
        let mut k = 0;
        while k < N {
            dot += a[k] * b[k];
            k += 1;
        }
        // scale + truncate to a deterministic integer, fold into acc
        let scaled = (dot * 0.000001) as i64 as u64;
        acc = acc.wrapping_add(scaled).wrapping_add(rep as u64);
        rep += 1;
    }
    (acc & 0xff) as i32
}
