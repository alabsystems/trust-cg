// OPT-12 adversarial: offset source index c[i] = a[i+1] + b[i]. The source read
// is at a different index than the destination write, so it is NOT the
// same-index element-wise map; the ElemAddr(index==iv) guard rejects it. Stays
// scalar+correct == LLVM.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 64;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let mut b = [0i32; N];
    let mut c = [0i32; N];
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i32).wrapping_mul(7); b[i] = bb(i as i32).wrapping_mul(3); i += 1; }
    let mut i = 0usize;
    while i + 1 < N { c[i] = a[i + 1].wrapping_add(b[i]); i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(c[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
