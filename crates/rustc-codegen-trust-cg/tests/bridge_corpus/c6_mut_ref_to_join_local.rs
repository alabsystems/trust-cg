// CORPUS FIXTURE — class c6: &mut to a local live across a control-flow join.
// An if/else where both arms write through the same &mut of an address-taken
// local; the mutation must be observed after the join. The bug dropped the write
// on one arm. O0-specific class.
// Correct exit: 40 & 0xff = 40.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[inline(never)]
fn bump(p: &mut i64, by: i64) { *p += by; }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: i64 = black_box(0);
    let cond = black_box(1i64);
    let r = &mut acc;
    if cond > 0 {
        bump(r, black_box(40));
    } else {
        bump(r, black_box(2));
    }
    (acc & 0xff) as i32
}
