// CORPUS FIXTURE — integer <-> `[u8; N]` byte conversions (`to_le_bytes`,
// `to_be_bytes`, `from_le_bytes`, `from_be_bytes`). Each lowers to a
// `Transmute` between the integer and a `[u8; N]` array, which failed closed
// because a by-value `[u8; N]` array (from / into a transmute) had no scalar
// trust-ir type ("Ty::[u8; 4]").
//
// The integer and the array share the same bytes, so the transmute is a store /
// load through the array's memory slot: `int -> [u8;N]` stores the integer (a
// proven Store of the int width — on little-endian x86 the slot bytes ARE
// `to_le_bytes`); `[u8;N] -> int` loads the integer (a proven Load). The array is
// memory-backed by a dedicated `compute_memory_backed_locals` case. `to_be_bytes`/
// `from_be_bytes` reuse the same transmute — their MIR pre-`bswap`s the integer.
//
// Checks the byte ORDER (LE vs BE), signed bytes, and a round-trip. All correct
// -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) little-endian byte order: 0x04030201 -> [01, 02, 03, 04].
    let le = black_box(0x04030201u32).to_le_bytes();
    let ok_le = le[0] == 1 && le[1] == 2 && le[2] == 3 && le[3] == 4;

    // (b) big-endian byte order: 0x04030201 -> [04, 03, 02, 01].
    let be = black_box(0x04030201u32).to_be_bytes();
    let ok_be = be[0] == 4 && be[1] == 3 && be[2] == 2 && be[3] == 1;

    // (c) signed all-ones bytes, and a u64 width.
    let neg = black_box(-1i32).to_le_bytes();
    let wide = black_box(0x0807060504030201u64).to_le_bytes();
    let ok_w = neg[0] == 0xff && neg[3] == 0xff && wide[0] == 1 && wide[7] == 8;

    // (d) round-trip both endiannesses.
    let x = black_box(0xDEAD_BEEFu32);
    let ok_rt = u32::from_le_bytes(x.to_le_bytes()) == x
        && u32::from_be_bytes(x.to_be_bytes()) == x;

    if ok_le && ok_be && ok_w && ok_rt {
        7
    } else {
        13
    }
}
