// CONTROL for `pointee_lanes_simd_overaligned.rs`: a FIELD read through the
// over-aligned pointee's shell (`(*r).0[1]`, not an address-preserving cast)
// has no lane the shell can address, so it must REFUSE — never a value.
#![no_std]
#![no_main]

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

use core::hint::black_box as bb;

#[repr(C, align(32))]
struct A32([i64; 4]);

#[inline(never)]
fn read_field(r: &A32) -> i64 {
    r.0[1]
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut buf = [0u64; 12];
    let base = buf.as_mut_ptr() as usize;
    let p32 = ((base + 31) & !31) as *mut A32;
    unsafe { (p32 as *mut i64).add(1).write(bb(7)) };
    let r: &A32 = unsafe { &*p32 };
    read_field(r) as i32
}
