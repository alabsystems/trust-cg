// OPT-12-FILL positive: constant fill a[i] = K over ONE distinct, write-only
// local [i32;N] array. No loads -> no dependence; a single distinct StackSlot
// -> no alias. The x86 SSE2 vectorizer builds [K,K,K,K] once (four covered i32
// stores into a fresh 16-byte scratch slot + one covered MOVDQU load) and then
// issues MOVDQU stores for floor(N/4) iters + a scalar remainder. No broadcast
// (PSHUFD/MOVD) is used, so the transform stays within the proof-covered op set.
// Must equal LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 65; // not a multiple of 4 -> exercises the scalar remainder
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let mut i = 0usize;
    while i < N { a[i] = 0x1234_5678; i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(a[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
