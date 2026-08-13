// OPT-12-REDUCE positive: integer sum-reduction s += a[i] over a local [i32;N]
// array with a loop-carried Gpr32 accumulator. The x86 SSE2 vectorizer rewrites
// it to a PADDD-accumulate loop (four independent i32 lane-partials in a loop-
// carried XMM) + a COVERED horizontal reduce (MOVDQU spill of the accumulator to
// a fresh scratch slot + four scalar MOVRM32 loads + AddRRs, no PHADDD/PSHUFD)
// + the unchanged scalar remainder. Integer wrapping add is associative AND
// commutative, so summing four interleaved lanes then combining == the
// sequential sum, bit-for-bit. N is not a multiple of 4 -> exercises the tail.
// Must equal LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 66;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i32).wrapping_mul(3).wrapping_add(1); i += 1; }
    let mut s: i32 = bb(0);
    let mut i = 0usize;
    while i < N { s = s.wrapping_add(a[i]); i += 1; }
    ((s as u32 as u64) % 126) as i32
}
