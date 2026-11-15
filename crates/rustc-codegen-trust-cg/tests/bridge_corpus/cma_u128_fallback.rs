// wide-numerics fixture: `u128::carrying_mul_add` (the `[carrying_mul_add width 128]` root)
// routed to the intrinsic's FALLBACK BODY, plus the unchanged inline widths (u64 via U128,
// u32/u8 via I64) as controls. Corners: MAX*MAX+MAX+MAX = (MAX, MAX) and mixed operands.
// CORPUS FIXTURE. Correct exit = LLVM oracle (66 at O0/O2).
#![no_std]
#![no_main]
use core::hint::black_box;
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[inline(never)]
fn fold(x: u128) -> u64 { (x as u64) ^ ((x >> 64) as u64).rotate_left(7) }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let m = black_box(u128::MAX);
    let (lo, hi) = m.carrying_mul_add(black_box(u128::MAX), black_box(u128::MAX), black_box(u128::MAX));
    let mut s = fold(lo).wrapping_mul(31) ^ fold(hi);
    let (lo2, hi2) = black_box(0x1234_5678_9abc_def0_0fed_cba9_8765_4321u128).carrying_mul_add(
        black_box(0xdead_beef_cafe_babe_1111_2222_3333_4444u128),
        black_box(7),
        black_box(1u128 << 127),
    );
    s = s.wrapping_mul(1_000_003) ^ fold(lo2).wrapping_add(fold(hi2).wrapping_mul(17));
    let (lo3, hi3) = black_box(3u128).carrying_mul_add(black_box(5), black_box(0), black_box(0));
    s = s.wrapping_add(fold(lo3) * 3 + fold(hi3));
    // Controls: the inline-lowered widths must be unchanged.
    let (a, b) = black_box(u64::MAX).carrying_mul_add(black_box(u64::MAX), black_box(u64::MAX), black_box(3));
    s = s.wrapping_mul(31) ^ a ^ b.rotate_left(9);
    let (c, d) = black_box(0xdead_beefu32).carrying_mul_add(black_box(0x1234_5678), black_box(9), black_box(u32::MAX));
    s = s.wrapping_mul(31) ^ (c as u64) ^ ((d as u64) << 32);
    let (e, f) = black_box(200u8).carrying_mul_add(black_box(201), black_box(255), black_box(254));
    s = s.wrapping_mul(31) ^ (e as u64) ^ ((f as u64) << 8);
    (s % 251) as i32
}
