// CORPUS FIXTURE — [TCG-SSA-071] cell retry: loops whose back-edge threading is
// CORRECT but trips the structural anti-swap sub-check, and which the semantic
// back-edge VC cannot model. (1) core's `overflowing_pow` (u64 / u128 / i128 —
// the `library/core` census roots): `overflow' = J_overflow | t(base)` where the
// in-loop join param breaks the derivation, so the arg "belongs" to `base` only.
// (2) `TwoWaySearcher::maximal_suffix` (the census root, copied — the type is
// private): the `left = right` rotation and the `period = right - left` fresh
// update. (3) a diamond-then-combine accumulator. Each is admitted by re-lowering
// the flagged slots in memory cells with every gate re-run; the order-sensitive
// checksum must equal LLVM at O0/O2/O3. Correct exit = LLVM oracle (58 at O0/O2/O3).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;

#[inline(never)]
fn maximal_suffix(arr: &[u8], order_greater: bool) -> (usize, usize) {
    let mut left = 0;
    let mut right = 1;
    let mut offset = 0;
    let mut period = 1;
    while let Some(&a) = arr.get(right + offset) {
        let b = arr[left + offset];
        if (a < b && !order_greater) || (a > b && order_greater) {
            right += offset + 1;
            offset = 0;
            period = right - left;
        } else if a == b {
            if offset + 1 == period {
                right += offset + 1;
                offset = 0;
            } else {
                offset += 1;
            }
        } else {
            left = right;
            right += 1;
            offset = 0;
            period = 1;
        }
    }
    (left, period)
}

#[inline(never)]
fn combine(mut n: u32, mut a: u64, mut b: u64) -> u64 {
    while n > 0 {
        if n & 1 == 1 {
            a = a.wrapping_add(3);
        }
        a = a.wrapping_add(b);
        b = b.wrapping_add(1);
        n -= 1;
    }
    a
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut s: u64 = 0;
    let mut i = 0u32;
    while i < 12 {
        let (a, o) = bb(3 + i as u64 * 1000).overflowing_pow(bb(i * 3));
        let (b, p) = bb(3 + i as u128 * 100_000).overflowing_pow(bb(i * 5));
        let (c, q) = bb(-7 - i as i128 * 1000).overflowing_pow(bb(i * 4 + 1));
        s = s.wrapping_mul(31).wrapping_add(a).wrapping_add(o as u64);
        s = s.wrapping_mul(31).wrapping_add(b as u64 ^ (b >> 64) as u64).wrapping_add(p as u64);
        s = s.wrapping_mul(31).wrapping_add(c as u64 ^ (c >> 64) as u64).wrapping_add(q as u64 * 2);
        i += 1;
    }
    let inputs: [&[u8]; 4] = [b"abcabcabd", b"zyxzyxzz", b"aaaaab", b"mississippi"];
    let mut k = 0;
    while k < 4 {
        let (l, per) = maximal_suffix(bb(inputs[k]), false);
        let (l2, per2) = maximal_suffix(bb(inputs[k]), true);
        s = s.wrapping_mul(31).wrapping_add((l * 7 + per) as u64).wrapping_add((l2 * 13 + per2) as u64);
        k += 1;
    }
    s = s.wrapping_add(combine(bb(7), bb(1), bb(2)));
    (s % 113) as i32
}
