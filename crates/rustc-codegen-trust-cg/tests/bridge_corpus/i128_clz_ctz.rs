// i128 leading_zeros / trailing_zeros via per-limb clz/ctz + zero-limb select.
//   v = 0x0000_0000_0000_00FF_1234_5678_9ABC_DEF0 : hi limb nonzero (0xFF),
//       leading_zeros = clz(hi) = 56.
//   w = 0x8000_0000_..._0000 : lo limb == 0, only bit 127 set,
//       trailing_zeros = 64 + ctz(hi) = 127.
//   (56 + 127) % 250 = 183.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let v: u128 = black_box(0x0000_0000_0000_00FF_1234_5678_9ABC_DEF0u128);
    let w: u128 = black_box(0x8000_0000_0000_0000_0000_0000_0000_0000u128);
    let lz = v.leading_zeros();
    let tz = w.trailing_zeros();
    ((lz + tz) % 250) as i32
}
