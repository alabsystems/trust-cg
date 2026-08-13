// CORPUS FIXTURE — reverse range iteration `for k in (a..b).rev()` at O0.
//
// FRONTEND COMPLETENESS: the bridge intercepts `.rev()` at the ctor/consumer, but
// rustc's mono-collector still emits the libcore `<Rev<Range<i32>> as Iterator>::next`
// body (`_2 = &mut ((*self).0: Range)` then `next_back(_2)`), which the backend must
// compile. That failed closed on the `&mut Range` sub-aggregate ref (a reference to a
// nested-aggregate FIELD) and on passing `&mut Rev<Range>` (a nested-aggregate thin
// pointer) as a call argument. Both are now compiled: the real libcore reverse
// iterator drives the loop, so `for k in (a..b).rev()` runs end->start correctly.
//
// ORDER-SENSITIVE: the digit-building accumulations (`acc = acc*10 + k`) make the
// iteration ORDER observable — a wrong reversed-Range `next` (off-by-one on the
// endpoints, or forward order) produces a different value, not just a wrong sum.
//   (1..5).rev() -> 4,3,2,1  => 4321
//   (0..10).rev() sum        => 45
//   (0..4).rev() over a[..]  => a[3],a[2],a[1],a[0] = 8,6,4,2 => 8642
//   total = (4321 + 45 + 8642) & 0xff = 13008 & 0xff = 208
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: i64 = 0;
    for k in (bb(1i64)..bb(5i64)).rev() {
        acc = acc * 10 + k;
    }
    let mut s: i64 = 0;
    for k in (0..bb(10i64)).rev() {
        s += k;
    }
    let a = [bb(2i64), bb(4), bb(6), bb(8)];
    let mut w: i64 = 0;
    for i in (0..bb(4usize)).rev() {
        w = w * 10 + a[i];
    }
    ((acc + s + w) & 0xff) as i32
}
