// CORPUS FIXTURE — a pointer<->integer round-trip preserves the address, and a
// raw deref reads the pointee. `addr_of!(x)` is a projection-free `Rvalue::RawPtr`
// of a scalar local; `p as usize` is `CastKind::PointerExposeProvenance`; `a as
// *const T` is `CastKind::PointerWithExposedProvenance`. All three were failing
// closed before the raw-pointer slice landed (the two cast kinds fell through to
// "CastKind::{..}" unsupported; the `RawPtr` to "Rvalue::RawPtr"). Each is a
// bit-preserving 64-bit reinterpret mapped to the proven `PtrToInt`/`IntToPtr`
// cast ops, so the round-tripped pointer derefs back to the original value.
//
// `*(((addr_of!(x)) as usize) as *const u64) == x` -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let x: u64 = black_box(0xABCD_1234_5678_9F00u64);
    let p = core::ptr::addr_of!(x); // Rvalue::RawPtr (projection-free)
    let a = p as usize; // PointerExposeProvenance (ptr -> int)
    let q = a as *const u64; // PointerWithExposedProvenance (int -> ptr)
    if unsafe { *q } == x {
        7
    } else {
        13
    }
}
