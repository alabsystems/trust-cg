// wide-numerics fixture: SIGNED `carrying_mul_add` (i8/i32/i64/i128), which the inline
// lowering refuses ("on a signed type is not modeled") and the design routes to the
// intrinsic's fallback body (`core::intrinsics::fallback::CarryingMulAdd`). MIN/MAX corners.
// CORPUS FIXTURE. Correct exit = LLVM oracle (139 at O0/O2).
#![no_std]
#![no_main]
#![feature(signed_bigint_helpers)]
use core::hint::black_box;
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[inline(never)]
fn fold(x: u128) -> u64 { (x as u64) ^ ((x >> 64) as u64).rotate_left(7) }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut s: u64 = 0;
    let (l, h) = black_box(i128::MIN).carrying_mul_add(black_box(i128::MIN), black_box(i128::MAX), black_box(i128::MAX));
    s = s.wrapping_mul(31) ^ fold(l) ^ fold(h as u128).wrapping_mul(3);
    let (l, h) = black_box(-5i128).carrying_mul_add(black_box(7), black_box(-1), black_box(3));
    s = s.wrapping_mul(31) ^ fold(l) ^ fold(h as u128).wrapping_mul(3);
    let (l, h) = black_box(i64::MIN).carrying_mul_add(black_box(-3), black_box(i64::MIN), black_box(i64::MAX));
    s = s.wrapping_mul(31) ^ l ^ (h as u64).wrapping_mul(5);
    let (l, h) = black_box(1_000_000_000i32).carrying_mul_add(black_box(-10), black_box(10), black_box(10));
    s = s.wrapping_mul(31) ^ (l as u64) ^ ((h as i64) as u64).wrapping_mul(7);
    let (l, h) = black_box(i8::MIN).carrying_mul_add(black_box(i8::MIN), black_box(i8::MIN), black_box(-1));
    s = s.wrapping_mul(31) ^ (l as u64) ^ ((h as i64) as u64).wrapping_mul(11);
    (s % 251) as i32
}
