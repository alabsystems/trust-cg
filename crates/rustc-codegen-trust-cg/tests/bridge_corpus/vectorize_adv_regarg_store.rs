// OPT-12 reg-arg adversarial: an in-place map `s[i] = s[i]*2 + 1` over a
// register-argument `&mut [i64]`. The loop CONTAINS a store, so the pure-
// reduction register tier (which admits NO stores, to keep aliasing impossible
// and invariant reloads sound) refuses it, and the stack-slot map/fill
// recognizers do not match a register-held base either. It stays SCALAR and
// correct == LLVM O0/O2/O3 (a store-bearing register-slice loop is out of the
// first-cut scope; fail-safe covers it).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
#[inline(never)]
fn m(s: &mut [i64]) {
    let mut i = 0usize;
    while i < s.len() {
        s[i] = s[i].wrapping_mul(2).wrapping_add(1);
        i += 1;
    }
}
const N: usize = 101;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i64; N];
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i64); i += 1; }
    m(bb(&mut a[..]));
    let mut acc = 0i64;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(a[i]); i += 1; }
    ((acc as u64) % 126) as i32
}
