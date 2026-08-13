// CORPUS FIXTURE — bug #72: nested-closure wrapping_shl. A closure inside a
// closure whose body does a wrapping shift; the inner shift count carrier and
// the nested environment lowering interacted to drop a wrap.
// wrapping_shl masks the shift to 0..63; 3 << 4 = 48. Correct exit: 48.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let base = black_box(3u64);
    let outer = |shift: u32| {
        let inner = |v: u64| v.wrapping_shl(shift);
        inner(base)
    };
    (outer(black_box(4u32)) & 0xff) as i32
}
