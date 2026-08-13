// signed i128 saturating_add: overflow clamps to i128::MAX; non-overflow returns
// the sum.  (i128::MAX-5).saturating_add(100) -> i128::MAX (low byte 0xFF=255);
// 10.saturating_add(20) -> 30. (255 + 30) % 250 = 35.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a: i128 = black_box(i128::MAX - 5);
    let s = a.saturating_add(black_box(100i128));
    let c: i128 = black_box(10i128);
    let d = c.saturating_add(black_box(20i128));
    let lo_s = (s & black_box(0xffi128)) as u8;
    let lo_d = (d & black_box(0xffi128)) as u8;
    ((lo_s as u32 + lo_d as u32) % 250) as i32
}
