// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// mem::transmute of a dense #[repr(C)] struct { u32, u32 } to a u64 then
// field-wise recovery (aggregate-slot store/load transmute). Agree O0/O2/O3 -> 153.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    #[derive(Clone, Copy)] #[repr(C)]
    struct Two { a: u32, b: u32 }
    let t = Two { a: black_box(0xAABBCCDD), b: black_box(0x11223344) };
    let n: u64 = unsafe { core::mem::transmute(t) };
    let r = (n & 0xff) ^ ((n >> 32) & 0xff);
    (r & 0xff) as i32
}
