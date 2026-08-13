// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// Nested #[repr(C)] { Inner{u16,u16}, u32, Inner{u16,u16} } — read the middle u32
// through `(&o as *const _ as *const u8).add(4) as *const u32` (layout-offset raw
// read of a nested aggregate). Agree O0/O2/O3 -> 237.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    #[repr(C)] #[derive(Clone, Copy)]
    struct Inner { a: u16, b: u16 }
    #[repr(C)] #[derive(Clone, Copy)]
    struct Outer { x: Inner, y: u32, z: Inner }
    let o = Outer {
        x: Inner { a: black_box(1), b: black_box(2) },
        y: black_box(1000),
        z: Inner { a: black_box(3), b: black_box(4) },
    };
    let base = &o as *const Outer as *const u8;
    let y = unsafe { *(base.add(4) as *const u32) };
    let r = y + o.x.a as u32 + o.z.b as u32;
    (r & 0xff) as i32
}
