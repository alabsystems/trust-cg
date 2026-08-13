// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// A by-value #[derive(Copy)] struct of four u8 passed into a fn, read back
// through `&s as *const S as *const u8` + `.add(i)` byte walk (the historical
// 1-byte-stride struct-ptr-field-by-value SIGSEGV class). Agree O0/O2/O3 -> 100.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    #[derive(Clone, Copy)]
    struct S { a: u8, b: u8, c: u8, d: u8 }
    #[inline(never)]
    fn get(s: S) -> u32 {
        let p = &s as *const S as *const u8;
        unsafe { *p as u32 + *p.add(1) as u32 + *p.add(2) as u32 + *p.add(3) as u32 }
    }
    let s = S { a: black_box(10), b: black_box(20), c: black_box(30), d: black_box(40) };
    (get(s) & 0xff) as i32
}
