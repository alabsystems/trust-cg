// CORPUS FIXTURE — unsigned i128 saturating_add / saturating_sub.
// a = u128::MAX-0x10 ; a.saturating_add(0x20) saturates to u128::MAX (all ones);
// low byte 0xFF=255 ; 255 % 250 = 5.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a: u128 = black_box(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFF0u128);
    let s = a.saturating_add(black_box(0x20u128));
    let lo = (s & black_box(0xffu128)) as u8;
    (lo % 250) as i32
}
