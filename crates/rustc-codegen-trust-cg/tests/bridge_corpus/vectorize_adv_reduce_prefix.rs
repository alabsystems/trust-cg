// OPT-12-REDUCE adversarial: the running partial sum ESCAPES to memory each
// iteration (a prefix-sum: c[i] = s after s += a[i]). Reordering the additions
// would change the intermediate `s` written into c[i], so this MUST stay scalar.
// The recognizer rejects it: the reduction requires ZERO stores in the loop (the
// accumulator lives only in a register), and here `s` is both stored and read
// mid-loop. Stays scalar+correct == LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 66;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let mut c = [0i32; N];
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i32).wrapping_mul(2).wrapping_add(1); i += 1; }
    let mut s: i32 = bb(0);
    let mut i = 0usize;
    while i < N {
        s = s.wrapping_add(a[i]);
        c[i] = s; // the running accumulator escapes to memory: NOT a pure reduction
        i += 1;
    }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(c[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
