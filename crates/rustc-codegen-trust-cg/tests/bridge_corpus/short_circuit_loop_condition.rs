// CORPUS FIXTURE — a loop whose body branches on a SHORT-CIRCUIT CONDITION.
//
// This is the exact shape of `core::str::pattern::TwoWaySearcher::maximal_suffix`
// (the last failed root of `library/core` in the trust-ir-cg census), which is
// what `vc_short_circuit_shape` in `src/lib.rs` exists for:
//
//     while let Some(&a) = arr.get(i) {
//         let b = arr[j];
//         if (a < b && !flag) || (a > b && flag) { .. }
//         else if a == b { .. }
//         else { .. }
//     }
//
// MIR lowers `(a < b && !flag) || (a > b && flag)` to a CHAIN of bool
// `SwitchInt`s converging on two blocks. Without the short-circuit recognizer the
// back-edge walker sees the second link as "an arm that ends in a switch with two
// in-loop targets", refuses it, and the loop-completeness check fails closed
// ([TCG-SSA-071]) — so this fixture does not compile at all on a backend whose
// recognizer is disabled. That refusal is the pin.
//
// THE TRAP: the loop's every branch mutates a DIFFERENT subset of the four
// loop-carried locals (`left`, `right`, `offset`, `period`), so a wrong
// reaching-condition, a hoisted-out-of-guard link, or a clobbered link temp
// produces a plausible-looking `(left, period)` pair rather than a trap. Every
// result is printed and compared with LLVM byte-for-byte, over inputs that drive
// all three branches (both `flag` polarities, runs of equal bytes, a strictly
// increasing and a strictly decreasing string, and a periodic string).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
#[no_mangle]
pub extern "C" fn rust_eh_personality() {}
use core::hint::black_box as bb;

unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, n: usize) -> isize;
}

fn put(v: u32) {
    let mut b = [0u8; 12];
    let mut i = 11usize;
    b[11] = b'\n';
    let mut x = v;
    loop {
        i -= 1;
        b[i] = b'0' + (x % 10) as u8;
        x /= 10;
        if x == 0 {
            break;
        }
    }
    unsafe {
        write(1, b.as_ptr().wrapping_add(i), 12 - i);
    }
}

/// `TwoWaySearcher::maximal_suffix`, verbatim in shape: the critical
/// factorization of `arr` under the order selected by `order_greater`.
#[inline(never)]
fn maximal_suffix(arr: &[u8], order_greater: bool) -> (usize, usize) {
    let mut left = 0; // i in the paper
    let mut right = 1; // j in the paper
    let mut offset = 0; // k in the paper, but starting at 0
    let mut period = 1; // p in the paper
    while let Some(&a) = arr.get(right + offset) {
        let b = arr[left + offset];
        if (a < b && !order_greater) || (a > b && order_greater) {
            // Suffix is smaller, period is entire prefix so far.
            right += offset + 1;
            offset = 0;
            period = right - left;
        } else if a == b {
            // Advance through repetition of the current period.
            if offset + 1 == period {
                right += offset + 1;
                offset = 0;
            } else {
                offset += 1;
            }
        } else {
            // Suffix is larger, start over from current location.
            left = right;
            right += 1;
            offset = 0;
            period = 1;
        }
    }
    (left, period)
}

#[inline(never)]
fn run(s: &[u8], checksum: u32) -> u32 {
    let (l0, p0) = maximal_suffix(s, bb(false));
    let (l1, p1) = maximal_suffix(s, bb(true));
    put(l0 as u32);
    put(p0 as u32);
    put(l1 as u32);
    put(p1 as u32);
    checksum
        .wrapping_mul(31)
        .wrapping_add((l0 + 7 * p0 + 13 * l1 + 17 * p1) as u32)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // One call per input rather than a static table of `&[u8]` indexed at
    // runtime: a fat-pointer element read through `Index` is a different
    // lane's shape and must not be what this fixture refuses on.
    let mut c = 0u32;
    c = run(bb(b"abcabcab"), c);
    c = run(bb(b"aaaaaa"), c);
    c = run(bb(b"abcdefg"), c);
    c = run(bb(b"gfedcba"), c);
    c = run(bb(b"banana"), c);
    c = run(bb(b"abaabaaabaaaab"), c);
    c = run(bb(b"x"), c);
    c = run(bb(b""), c);
    put(c);
    (c % 100) as i32
}
