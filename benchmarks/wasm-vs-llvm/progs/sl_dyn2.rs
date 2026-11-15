#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
trait Sh {
    fn area(&self) -> u32;
}
struct Sq(u32);
struct Re(u32, u32);
impl Sh for Sq {
    fn area(&self) -> u32 {
        self.0.wrapping_mul(self.0)
    }
}
impl Sh for Re {
    fn area(&self) -> u32 {
        self.0.wrapping_mul(self.1) + 1
    }
}

#[inline(never)]
fn total(xs: &[&dyn Sh]) -> u32 {
    let mut t = 0u32;
    let mut i = 0;
    while i < xs.len() {
        t = t.wrapping_mul(7).wrapping_add(xs[i].area());
        i += 1;
    }
    t
}
#[no_mangle]
pub extern "C" fn e_dyn_slice(a: u32) -> u32 {
    let s = Sq(a);
    let r = Re(a ^ 5, 3);
    let arr: [&dyn Sh; 3] = [&s, &r, &s];
    total(&arr[(a % 4) as usize..])
}
#[inline(never)]
fn one(x: &dyn Sh) -> u32 {
    x.area()
}
#[no_mangle]
pub extern "C" fn e_dyn_one(a: u32) -> u32 {
    let s = Sq(a);
    let r = Re(a, 9);
    if a & 1 == 0 { one(&s) } else { one(&r) }
}
#[no_mangle]
pub extern "C" fn e_dyn_iter(a: u32) -> u32 {
    let s = Sq(a);
    let r = Re(a ^ 5, 3);
    let arr: [&dyn Sh; 3] = [&s, &r, &s];
    let mut t = 0u32;
    for x in arr.iter() {
        t = t.wrapping_mul(3).wrapping_add(x.area());
    }
    t
}
#[inline(never)]
fn deref_dyn(r: &&dyn Sh) -> u32 {
    let x: &dyn Sh = *r;
    x.area()
}
#[no_mangle]
pub extern "C" fn e_dyn_deref(a: u32) -> u32 {
    let s = Sq(a);
    let d: &dyn Sh = &s;
    deref_dyn(&d)
}
