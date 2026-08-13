// CORPUS FIXTURE — FUZZ-5: a call to a FOREIGN function declared in an
// `extern "C" { ... }` block (here libc `abs`/`labs`). Such a foreign item is
// `is_local()` (declared in this crate) but has NO MIR body; the direct-call
// interception probes used to call `tcx.instance_mir` on it, triggering
// `mir_built` -> typeck of a body-less foreign fn, which ICE'd
// ("can't type-check body of ..."). The fix guards those probes with
// `is_foreign_item`, routing foreign calls straight to the generic external-symbol
// emission. Exit is a deterministic checksum of the two libc results.
// Correct exit: (42 + 100) & 0x7f = 142 & 0x7f = 14.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
extern "C" {
    fn abs(x: i32) -> i32;
    fn labs(x: i64) -> i64;
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = unsafe { abs(black_box(-42)) };
    let b = unsafe { labs(black_box(-100i64)) };
    ((a as i64 + b) & 0x7f) as i32
}
