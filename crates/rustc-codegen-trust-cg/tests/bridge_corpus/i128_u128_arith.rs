// CORPUS FIXTURE — u128 arithmetic via methods (wrapping_mul / wrapping_add).
//
// Re-checks the REAL i128 surface against a fresh dylib: u128 wrapping_mul at O0
// may lower to a call carrying i128 register-pair args (the shared lower_call_inner
// ArgLoc::I128Pair path). The earlier "i128 call argument not yet implemented; see
// WS2b" failure was an artifact of a STALE dylib.
//
// a = 2^64 - 1, b = 3 ; a.wrapping_mul(b) = 3*2^64 - 3 = 0x2_FFFF_FFFF_FFFF_FFFD,
// low byte 0xFD = 253 ; 253 % 250 = 3. Observed via i128 AND + truncation.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a: u128 = black_box(0xFFFF_FFFF_FFFF_FFFFu64) as u128;
    let b: u128 = black_box(3u64) as u128;
    let prod = a.wrapping_mul(b);
    let low = (prod & black_box(0xffu128)) as u8;
    (low % 250) as i32
}
