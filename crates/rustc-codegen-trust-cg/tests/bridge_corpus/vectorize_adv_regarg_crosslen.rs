// OPT-12 reg-arg REDUCE adversarial: the loop trip count (`k`) is a DIFFERENT
// value than the slice length that bounds each element access. The header test
// is `i <u k` but every `s[i]` bounds-check guard is `i <u s.len()` — two
// distinct registers. The register-argument reduction recognizer requires the
// own-length identity (header bound register == every guard bound register); it
// canonicalizes the two bounds, sees they differ, and REFUSES to vectorize
// (fail-safe to the scalar loop). Called with k == s.len() so the scalar result
// is well-defined; the point is that it stays SCALAR and equals LLVM O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
#[inline(never)]
fn h(s: &[i64], k: usize) -> i64 {
    let mut t = 0i64;
    let mut i = 0usize;
    while i < k {
        t = t.wrapping_add(s[i]);
        i += 1;
    }
    t
}
const N: usize = 100;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i64; N];
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i64).wrapping_mul(5).wrapping_add(1); i += 1; }
    let s = bb(&a[..]);
    let r = h(s, bb(s.len()));
    ((r as u64) % 126) as i32
}
