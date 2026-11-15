// CORPUS FIXTURE — a CLOSURE whose parameter is a SLICE / `str` FAT POINTER
// (`|s: &[u8]| ..`, `|t: &str| ..`), called at O0 so the call is a real
// `Fn::call` with a tupled `(&[u8],)` argument. The closure body declares the
// parameter as the 16-byte `{ data, len }` slot every fat-pointer parameter
// gets; the closure call site used to push ONE 8-byte value for the element
// (the data-only `Ptr` mapping of a `&[T]`), so the body read `{ data, len }`
// out of whatever the data pointer addressed — measured 2026-09-22: SIGSEGV at
// O0 where LLVM exits normally (the minimal probe exits 17; this fixture 43);
// O2 agreed only because the call inlined. The call
// site now passes the ADDRESS of the element's `{ data, len }` pair inside the
// memory-backed tupled-args slot, exactly as a direct call passes a slice.
#![no_std]
#![no_main]

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

use core::hint::black_box as bb;

#[inline(never)]
fn apply_slice(f: impl Fn(&[u8]) -> usize, s: &[u8]) -> usize {
    f(s)
}

#[inline(never)]
fn apply_str(f: impl Fn(&str, u32) -> usize, t: &str, k: u32) -> usize {
    f(t, k)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let arr = [1u8, 2, 3];
    let f = |s: &[u8]| s.len() + s[0] as usize * 10;
    let s: &[u8] = bb(&arr[..]);
    let a = f(s); // 3 + 10 = 13
    let b = apply_slice(|s: &[u8]| s.len() * 100 + s[2] as usize, s); // 300 + 3 = 303
    let t: &str = bb("hello");
    let c = apply_str(
        |t: &str, k: u32| t.len() * k as usize + t.as_bytes()[1] as usize,
        t,
        bb(2),
    ); // 10 + 101 = 111
    ((a + b + c) & 0x7f) as i32 // 427 & 0x7f = 43
}
