// CORPUS FIXTURE — i128 memory store/load round-trip preserves all 128 bits.
//
// `*slot = v` then read `*slot` back, through a &mut u128, must preserve the full
// 128 bits. Before the two-limb store/load fix, an I128 store/load was a single
// 64-bit MOV (high limb dropped/untracked). Observed via an i128 equality compare
// (uses BOTH limbs), now that u128 literals + i128 call-arg pairs + i128 compare
// all lower on a fresh dylib.
//
// got == v -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[inline(never)]
fn roundtrip(slot: &mut u128, v: u128) -> u128 {
    *slot = v; // i128 store (two limbs)
    black_box(*slot) // i128 load (two limbs)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let v: u128 = black_box(0xAAAA_BBBB_CCCC_DDDD_1111_2222_3333_4444u128);
    let mut slot: u128 = black_box(0u128);
    let got = roundtrip(&mut slot, v);
    if got == v {
        7
    } else {
        13
    }
}
