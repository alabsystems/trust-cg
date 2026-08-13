// CORPUS FIXTURE — i128 memory round-trip preserves the full 128 bits.
//
// `*r = v` then `*r` (read back through a &mut u128) must preserve all 128 bits.
// Before the fix, select_memory_store/select_memory_load lowered an I128 access
// to a SINGLE 64-bit MovMR/MovRM, dropping the high eightbyte on store and
// leaving it untracked on load. The fix lowers each to a (lo@[base+0],
// hi@[base+8]) pair.
//
// Everything is inlined into `main` to avoid the surrounding i128 fail-closed
// edges (128-bit literals, raw-pointer casts, by-value i128 call args). The
// test value is built from supported ops (u64 zero-extend + u128 multiply); the
// high bits are observed via an i128 equality compare (uses both limbs).
//
// Correct (LLVM, and trust-cg after the fix): got == v -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let seed: u64 = black_box(0xDEAD_BEEF_CAFE_1234);
    let a: u128 = seed as u128; // zero-extend u64 -> u128 (high limb = 0)
    let v: u128 = a.wrapping_mul(a); // u128 mul -> large non-zero high limb
    let mut slot: u128 = a.wrapping_sub(a); // = 0, no 128-bit literal
    let r: &mut u128 = black_box(&mut slot);
    *r = v; // i128 store (inline, no call)
    let got: u128 = black_box(*r); // i128 load
    if got == v {
        7
    } else {
        13
    }
}
