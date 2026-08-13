// OPT-12-REDUCE positive: integer dot-product d += a[i]*b[i] over two distinct
// local [i32;N] arrays with a loop-carried Gpr32 accumulator. The x86 SSE2
// vectorizer rewrites it to a PMULLD + PADDD-accumulate loop (four independent
// i32 lane-partials in a loop-carried XMM) + a COVERED horizontal reduce (MOVDQU
// spill + four scalar loads/adds, no PHADDD/PSHUFD) + the unchanged scalar
// remainder. PMULLD's low-dword product == the scalar i32 wrapping_mul per lane,
// and integer add is associative+commutative, so lane-partials + combine == the
// sequential sum, bit-for-bit. N is not a multiple of 4 -> exercises the tail.
// Must equal LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 130;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let mut b = [0i32; N];
    let s = bb(5i32);
    let mut i = 0usize;
    while i < N { a[i] = (i as i32).wrapping_mul(7).wrapping_add(s); i += 1; }
    let mut i = 0usize;
    while i < N { b[i] = (i as i32).wrapping_mul(3).wrapping_sub(s); i += 1; }
    let mut d: i32 = bb(0);
    let mut i = 0usize;
    while i < N { d = d.wrapping_add(a[i].wrapping_mul(b[i])); i += 1; }
    ((d as u32 as u64) % 126) as i32
}
