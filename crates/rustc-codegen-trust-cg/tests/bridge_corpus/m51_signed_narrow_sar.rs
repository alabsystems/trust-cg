// CORPUS FIXTURE — bug #51: signed-narrow SAR from a narrowing cast. The narrow
// carrier is zero-extended by select_trunc; a signed SAR must sign-extend it
// first. Regression anchor: simplest WrongValue shape, known sign.
// -100 >> 1 = -50; (-50i8 as u8) = 206. Zero-extended carrier gives 78.
// Correct exit: 206.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let x: i8 = black_box(-100i32) as i8;
    let r: i8 = x >> 1;
    (r as u8) as i32
}
