// CORPUS FIXTURE — a u128 literal with the HIGH BIT SET must lower.
//
// Before the fix, const_to_scalar_i128 range-checked unsigned consts via
// `i128::try_from(bits)`, which returns None for any u128 > i128::MAX (high bit
// set), so const_to_trust_ir_constant fell through to a fail-closed
// "ConstValue::Scalar(..)" — a u128 literal could not even be materialized.
// Now the raw 128 bits are reinterpreted as i128 (a bit pattern) and the isel
// materializes the two 64-bit limbs (Iconst128).
//
// Observed via i128 bitwise-AND + truncation (both supported), avoiding `>> 64`
// / raw-ptr / by-value i128 call args (all fail closed). Low byte of
// 0xAAAA_BBBB_CCCC_DDDD_1111_2222_3333_4444 is 0x44 = 68; 68 % 250 = 68.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let v: u128 = black_box(0xAAAA_BBBB_CCCC_DDDD_1111_2222_3333_4444u128);
    let low_byte = (v & black_box(0xff_u128)) as u8;
    (low_byte % 250) as i32
}
