#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let v: u128 = black_box(5u128);
    let n = v.wrapping_neg();
    let lo = (n & black_box(0xffu128)) as u8;
    (lo % 250) as i32
}
