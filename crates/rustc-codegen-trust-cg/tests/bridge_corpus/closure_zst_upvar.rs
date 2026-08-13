// CORPUS FIXTURE — a closure whose only capture is ZERO-SIZED (a captured fn item,
// the phantom capture of a non-capturing `|x| ..`, `PhantomData`, …). Before this
// fix the closure TYPE didn't convert ("closure upvar 0 is not memory-scalar:
// Unit"): the upvar tuple required every field to be a memory scalar, and a ZST
// upvar (Unit) is neither a scalar nor a pointer.
//
// A ZST upvar carries no data, so it is kept in the closure's upvar tuple (which
// preserves the `(*env).N` field indices the body reads) but is no longer required
// to be a memory scalar — nothing is ever read out of a ZST capture. This makes a
// closure that calls a free function type and lower.
//
// (a) a closure capturing a fn item, called directly; (b) a second such closure
// reused twice (a `Cell`-free accumulator via plain calls). Both correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[inline(never)]
fn one() -> i32 {
    black_box(1)
}

#[inline(never)]
fn two() -> i32 {
    black_box(2)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) closure capturing the ZST fn item `one`, called directly.
    let add_one = |x: i32| x + one();
    let a = add_one(black_box(3)); // 4

    // (b) closure capturing the ZST fn item `two`, called twice.
    let add_two = |x: i32| x + two();
    let b = add_two(add_two(black_box(-1))); // -1 +2 +2 = 3

    if a == 4 && b == 3 {
        7
    } else {
        13
    }
}
