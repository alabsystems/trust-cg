// OPT-12 reg-arg REDUCE positive: an i64 sum reduction over a slice whose
// (ptr, len) arrive in REGISTERS (a `&[i64]` argument to `#[inline(never)] g`,
// not a fixed-size local array). The x86 SSE2 vectorizer's register-argument
// tier (recognize_regarg_sumq_loop) rewrites `for i in 0..s.len() { t += s[i] }`
// to a PADDQ-accumulate loop (two i64 lane-partials in a loop-carried XMM) + a
// COVERED horizontal reduce (MOVDQU spill + two scalar loads/adds) + the
// unchanged scalar remainder, behind a runtime `vN = len & !1` gate.
// Legality by construction: the header bound and the per-element bounds guard
// are the SAME loop-invariant length register (own-length identity), the loop
// has no stores (pure reduction => no aliasing), and i64 wrapping add is
// associative+commutative so lane-partials + fold == the sequential sum,
// bit-for-bit. N is odd -> exercises the scalar tail. Must equal LLVM O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
#[inline(never)]
fn g(s: &[i64]) -> i64 {
    let mut t = 0i64;
    let mut i = 0usize;
    while i < s.len() {
        t = t.wrapping_add(s[i]);
        i += 1;
    }
    t
}
const N: usize = 133;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i64; N];
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i64).wrapping_mul(3).wrapping_sub(7); i += 1; }
    let r = g(bb(&a[..]));
    ((r as u64) % 126) as i32
}
