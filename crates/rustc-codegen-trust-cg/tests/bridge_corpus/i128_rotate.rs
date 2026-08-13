// i128 rotate_left/right (via the funnel-shift fallback synthesized at n==128).
//   0xF.rotate_left(4)=0xF0 (240); (bit127).rotate_left(1)=1 (wrap);
//   0xF0.rotate_right(4)=0x0F (15). (240+1+15)%250 = 6.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a: u128 = black_box(0xFu128);
    let ra = (a.rotate_left(black_box(4)) & black_box(0xffu128)) as u8;
    let b: u128 = black_box(0x8000_0000_0000_0000_0000_0000_0000_0000u128);
    let rb = (b.rotate_left(black_box(1)) & black_box(0xffu128)) as u8;
    let c: u128 = black_box(0xF0u128);
    let rc = (c.rotate_right(black_box(4)) & black_box(0xffu128)) as u8;
    ((ra as u32 + rb as u32 + rc as u32) % 250) as i32
}
