// CORPUS FIXTURE — large `[v; N]` array-repeat lowered as ONE call to the
// verified `__trustcg_array_fill_iN` helper loop (N >= 16, fixed-width integer
// element) instead of `N` unrolled stores, and the helper's byte variant
// vectorized by the runtime byte-fill slice (`x86_vectorize`).
//
// Boundaries pinned here:
//   * N = 15 (below the threshold — unrolled path) vs 16/17 (helper path,
//     exactly one packed iteration + 0/1 tail) vs 100/1024 (tail 4 / 0);
//   * a RUNTIME fill value that VARIES per loop entry (the packed broadcast
//     must be rebuilt every entry — a stale broadcast diverges immediately);
//   * fill immediately partially overwritten (helper-call/store ordering);
//   * first/last/middle element reads + a full checksum;
//   * wider elements (u16/i32/u64) through the scalar helper variants,
//     including sign bits through the I64 helper lane.
//
// Exit code (the folded checksum mod 126) must agree with LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let z = bb(0usize);
    let mut acc: u64 = 0;
    macro_rules! case {
        ($n:expr, $v:expr) => {{
            let a = [$v; $n];
            acc = acc.wrapping_mul(31).wrapping_add(a[z] as u64);
            acc = acc.wrapping_mul(31).wrapping_add(a[z + $n - 1] as u64);
            acc = acc.wrapping_mul(31).wrapping_add(a[z + $n / 2] as u64);
            let mut s: u64 = 0;
            let mut i = z;
            while i < $n {
                s = s.wrapping_add(a[i] as u64);
                i += 1;
            }
            acc = acc.wrapping_mul(31).wrapping_add(s);
        }};
    }
    // u8 threshold + packed-lane boundaries.
    case!(15, 0xA5u8);
    case!(16, 0x5Au8);
    case!(17, 0x11u8);
    case!(100, 0x42u8);
    case!(1024, 7u8);
    // Wider elements (scalar helper variants), sign bits included.
    case!(33, 0xBEEFu16);
    case!(20, -123456789i32);
    case!(16, 0xFEDC_BA98_7654_3210u64);

    // Runtime value varying per entry + partial overwrite after the fill.
    let reps = bb(50u32);
    let mut r = 0u32;
    while r < reps {
        let v = (r as u8).wrapping_mul(37);
        let mut a = [v; 300];
        a[z] = a[z].wrapping_add(1);
        a[z + 299] = a[z + 299].wrapping_add(2);
        let mut s: u64 = 0;
        let mut i = z;
        while i < 300 {
            s = s.wrapping_add(a[i] as u64);
            i += 1;
        }
        acc = acc.wrapping_mul(31).wrapping_add(s);
        r += 1;
    }
    (acc % 126) as i32
}
