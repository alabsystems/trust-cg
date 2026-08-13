// CORPUS FIXTURE — fail-closed TRIPWIRE (NOT a differential). An i128 by-value
// extern "C" parameter. The bridge fails closed on the i128 scalar ABI today
// (see crates/trust-cg-test/src/cmd/rustc.rs UI_FIXTURES
// `extern-c-i128-scalar-abi-fail-closed`). Kept in the corpus as
// `CompileExpectation::MayFailClosed` so the day it SILENTLY starts compiling,
// the harness flags that it must be promoted to a differential MustCompile entry
// rather than shipping an unverified i128 ABI.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[no_mangle]
pub extern "C" fn takes_i128(v: i128) -> i128 { v.wrapping_add(1) }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    takes_i128(0) as i32
}
