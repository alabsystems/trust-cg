// CORPUS FIXTURE — 3/5/6/7-byte arrays returned through `black_box` (a System V
// PARTIAL eightbyte, moved as width-exact pieces) and read back as slices. Before:
// the lane ASSEMBLY used `MOV r8/r16, [mem]`, which leaves the register's upper
// bits stale, and ORed the shifted pieces over them (3 and 7 bytes read back
// garbage, nondeterministically); the call RESULT was stored with one `lane.ty`
// store (4 bytes for a 3-byte lane), one byte past the object. Correct exit =
// LLVM oracle (53 at O0/O2/O3).
#![no_std]
#![no_main]
use core::hint::black_box;
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[inline(never)]
fn fold(s: &[u8]) -> u32 {
    let mut acc: u32 = 0;
    let mut i = 0;
    while i < s.len() {
        acc = acc.wrapping_mul(31).wrapping_add(s[i] as u32);
        i += 1;
    }
    acc
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a3 = black_box([11u8, 12, 13]);
    let a5 = black_box([21u8, 22, 23, 24, 25]);
    let a6 = black_box([31u8, 32, 33, 34, 35, 36]);
    let a7 = black_box([41u8, 42, 43, 44, 45, 46, 47]);
    let a11 = black_box([1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]);
    let guard = black_box([0xAAu8; 4]);
    let acc = fold(&a3) ^ fold(&a5) ^ fold(&a6) ^ fold(&a7) ^ fold(&a11) ^ fold(&guard);
    (acc % 251) as i32
}
