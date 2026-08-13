// CORPUS FIXTURE — `.rev().enumerate().map().sum()` order sensitivity.
//
// FOUND BY FUZZ-2 differential sweep. At -Copt-level=2/3 rustc specializes
// `x.iter().rev().enumerate().map(g).sum()` into
// `<slice::Iter as DoubleEndedIterator>::rfold(0, enumerate(map_fold(sum)))` — the
// `.rev()` is realized as `rfold`. The bridge's rfold "commutative reduction" fast
// path drove the FORWARD chain (valid for an order-INSENSITIVE map/copied sum), but
// the peel silently appended an ORDER-SENSITIVE `Enumerate` adapter, so the forward
// walk paired index 0 with the FIRST element instead of the LAST — computing the
// un-reversed 55 instead of 35 (a SILENT WRONG VALUE). Now the fast path rejects a
// peeled enumerate/take/skip/step_by adapter and fails closed at O2/O3; O0 (which
// builds the whole chain via `resolve_iter_chain`) drives it correctly.
//
// ORDER-SENSITIVE: `(i+1)*x` over rev=[5,4,3,2,1] = 5+8+9+8+5 = 35; the wrong
// forward pairing gives 1+4+9+16+25 = 55 (a different value, not just a wrong sum).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = [bb(1i64), bb(2), bb(3), bb(4), bb(5)];
    let s: i64 = a.iter().rev().enumerate().map(|(i, &x)| (i as i64 + 1) * x).sum();
    (s & 0xff) as i32
}
