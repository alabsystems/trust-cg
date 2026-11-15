// CORPUS FIXTURE — an OVER-ALIGNED (32- / 64-byte) struct POINTEE: core_arch's
// `__m256i` / `__m512d` `as_array` are `&*(self as *const Self as *const [T; N])`
// on a `#[repr(simd)]` struct whose alignment exceeds the 16-byte stack
// alignment the memory model's slot lanes cover. Only `&Self` / `*const Self`
// need a pointee type — the cast preserves the address and the `&[T; N]`
// result flattens as an ordinary array reference — so such a pointee is typed
// as a 16-byte-lane SHELL (`Array(I128, size / 16)`): an ABI/thin-pointer
// spelling only, never a slot (an over-aligned LOCAL keeps refusing, because
// the frame clamps alignment at 16). The objects are obtained by hand-aligning
// a `u64` buffer so no over-aligned local or static is ever needed.
#![no_std]
#![no_main]
#![feature(repr_simd)]
#![allow(non_camel_case_types)]

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

use core::hint::black_box as bb;

#[repr(C, align(32))]
struct A32([i64; 4]);
#[repr(C, align(64))]
struct A64([u16; 32]);
#[repr(simd)]
struct V4([i64; 4]);

impl A32 {
    #[inline(never)]
    fn as_array(&self) -> &[i64; 4] {
        unsafe { &*(self as *const Self as *const [i64; 4]) }
    }
    #[inline(never)]
    fn as_mut_array(&mut self) -> &mut [i64; 4] {
        unsafe { &mut *(self as *mut Self as *mut [i64; 4]) }
    }
}
impl A64 {
    #[inline(never)]
    fn as_array(&self) -> &[u16; 32] {
        unsafe { &*(self as *const Self as *const [u16; 32]) }
    }
}
impl V4 {
    #[inline(never)]
    fn as_array(&self) -> &[i64; 4] {
        unsafe { &*(self as *const Self as *const [i64; 4]) }
    }
}

#[inline(never)]
fn aligned_base(buf: *mut u64, align: usize) -> usize {
    let base = buf as usize;
    (base + align - 1) & !(align - 1)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut buf = [0u64; 24];
    let p32 = bb(aligned_base(buf.as_mut_ptr(), 32) as *mut A32);
    let lanes = p32 as *mut i64;
    for k in 0..4 {
        unsafe { lanes.add(k).write(bb(10 + k as i64 * 3)) };
    }
    let r: &A32 = unsafe { &*p32 };
    let a = r.as_array();
    let acc = a[0] + 3 * a[1] + 5 * a[2] + 7 * a[3]; // 10 + 39 + 80 + 133 = 262
    let same_addr = (a as *const [i64; 4] as usize) == (r as *const A32 as usize);
    let m: &mut A32 = unsafe { &mut *p32 };
    m.as_mut_array()[2] = bb(99);
    let back = unsafe { lanes.add(2).read() }; // 99

    let pv = bb(p32 as *const V4);
    let v: &V4 = unsafe { &*pv };
    let va = v.as_array();
    let vacc = va[0] + va[1] + va[2] + va[3]; // 10 + 13 + 99 + 19 = 141

    let mut buf64 = [0u64; 24];
    let p64 = bb(aligned_base(buf64.as_mut_ptr(), 64) as *mut A64);
    let shorts = p64 as *mut u16;
    for k in 0..32 {
        unsafe { shorts.add(k).write(bb(k as u16 * 2)) };
    }
    let r64: &A64 = unsafe { &*p64 };
    let s = r64.as_array();
    let sacc = s[0] as i64 + s[31] as i64 * 10; // 0 + 620
    let same64 = (s as *const [u16; 32] as usize) == (r64 as *const A64 as usize);

    let total =
        acc + back + vacc + sacc + if same_addr { 1000 } else { 0 } + if same64 { 2000 } else { 0 };
    // 262 + 99 + 141 + 620 + 1000 + 2000 = 4122; 4122 & 0x7f = 26
    (total & 0x7f) as i32
}
