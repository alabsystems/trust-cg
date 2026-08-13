// CORPUS FIXTURE — i128/u128 count_ones via per-limb popcount.
// 0xF0F0..F0F0 has 4 set bits per byte x 16 bytes = 64; 64 % 250 = 64.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let v: u128 = black_box(0xF0F0_F0F0_F0F0_F0F0_F0F0_F0F0_F0F0_F0F0u128);
    (v.count_ones() % 250) as i32
}
