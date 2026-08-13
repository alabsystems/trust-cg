// i128 swap_bytes / reverse_bits via per-limb op + limb-swap recombine.
//   v = 0x0102_0304_..._0F10 ; swap_bytes(v) reverses the 16 bytes ->
//       0x100F_..._0201 ; its low byte 0x01 -> observe 0x01.
//   reverse_bits(v) low byte = bit-reverse of v's TOP byte (0x01 -> 0x80).
//   (0x01 + 0x80) % 250 = 129.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let v: u128 = black_box(0x0102_0304_0506_0708_090A_0B0C_0D0E_0F10u128);
    let sb = (v.swap_bytes() & black_box(0xffu128)) as u8;     // 0x01
    let rb = (v.reverse_bits() & black_box(0xffu128)) as u8;   // bit-rev of 0x01 (top byte) = 0x80
    ((sb as u32 + rb as u32) % 250) as i32
}
