// CORPUS FIXTURE — `.filter_map(..).take(n).sum()` (Take WRAPPING an unmodeled adapter).
//
// FOUND BY FUZZ-2 differential sweep. `FilterMap` is unmodeled and `Take` wraps it,
// so the `.sum()` terminal cannot drive the chain; the general path reached the
// TRAPPED `<Take<..> as Iterator>::try_fold` ud2 stub at runtime -> SIGILL. Now the
// sum/fold/count terminal fails CLOSED at compile time on any unmodeled chain.
//
// LLVM: evens 0,2,4,6,8 -> take 3 -> 0+2+4 = 6.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = [bb(0i64), 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let s: i64 = a.iter().filter_map(|&x| if x % 2 == 0 { Some(x) } else { None }).take(3).sum();
    (s & 0xff) as i32
}
