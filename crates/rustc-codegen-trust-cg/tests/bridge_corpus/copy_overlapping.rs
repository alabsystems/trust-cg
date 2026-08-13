// CORPUS FIXTURE — overlapping `core::ptr::copy` / slice `copy_within`.
//
// This is the memmove contract, not memcpy: both overlap directions are legal,
// and `dst > src` is the adversarial case where a naive forward copy corrupts
// later source lanes. The explicit u16 pointer copy also pins count*size_of::<T>
// byte sizing and the intrinsic's (src,dst,count) -> memmove(dst,src,n) reorder.
#![no_std]
#![no_main]

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

use core::hint::black_box as bb;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut right = [bb(10i32), bb(20), bb(30), bb(40), bb(50)];
    right.copy_within(0..3, 2);
    let right_ok = right == [10, 20, 10, 20, 30];

    let mut left = [bb(10i32), bb(20), bb(30), bb(40), bb(50)];
    left.copy_within(2..5, 0);
    let left_ok = left == [30, 40, 50, 40, 50];

    let mut wide = [bb(1u16), bb(2), bb(3), bb(4), bb(5)];
    let count = bb(4usize);
    unsafe {
        core::ptr::copy(wide.as_ptr(), wide.as_mut_ptr().add(1), count);
    }
    let wide_ok = wide == [1, 1, 2, 3, 4];

    if right_ok && left_ok && wide_ok { 110 } else { 13 }
}
