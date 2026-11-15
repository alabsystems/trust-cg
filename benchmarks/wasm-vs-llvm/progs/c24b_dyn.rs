#![no_std]
#![allow(dead_code)]
#![feature(core_float_math, float_minimum_maximum)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
trait Shape {
    fn area(&self) -> f64;
    fn scale(&mut self, k: f32);
}
struct Sq(f32);
struct Ci {
    r: f64,
    n: u8,
}
impl Shape for Sq {
    fn area(&self) -> f64 {
        (self.0 * self.0) as f64
    }
    fn scale(&mut self, k: f32) {
        self.0 *= k
    }
}
impl Shape for Ci {
    fn area(&self) -> f64 {
        3.25 * self.r * self.r + self.n as f64
    }
    fn scale(&mut self, k: f32) {
        self.r *= k as f64;
        self.n = self.n.wrapping_add(1)
    }
}
#[inline(never)]
fn tot(v: &mut [&mut dyn Shape], k: f32) -> f64 {
    let mut s = 0.0;
    for x in v.iter_mut() {
        x.scale(k);
        s += x.area();
    }
    s
}
fn f1(a: f32, b: f64, c: i64) -> f64 {
    a as f64 * b - c as f64
}
fn f2(a: f32, b: f64, c: i64) -> f64 {
    b / a as f64 + c as f64
}
#[no_mangle]
pub extern "C" fn fnptr(a: f32, b: f64) -> f64 {
    let t: [fn(f32, f64, i64) -> f64; 2] = [f1, f2];
    t[(a.to_bits() & 1) as usize](a, b, 5) + t[1](b as f32, a as f64, -3)
}
fn g32(x: f32) -> f32 {
    x * 0.5
}
fn h32(x: f32) -> f32 {
    -x
}
#[inline(never)]
fn apply(f: fn(f32) -> f32, x: f32, n: u32) -> f32 {
    let mut v = x;
    let mut i = 0;
    while i < n % 8 {
        v = f(v);
        i += 1;
    }
    v
}
#[no_mangle]
pub extern "C" fn fnptr32(x: f32, n: i32) -> f32 {
    apply(if n & 1 == 0 { g32 } else { h32 }, x, n as u32)
}
#[inline(never)]
fn dynfn(f: &dyn Fn(f64) -> f64, x: f64) -> f64 {
    f(f(x))
}
#[no_mangle]
pub extern "C" fn closure_dyn(x: f64, y: f64) -> f64 {
    let k = y * 2.0;
    dynfn(&|t| t * k + 1.0, x)
}
trait Num {
    fn two(self) -> Self;
}
impl Num for f32 {
    fn two(self) -> f32 {
        self + self
    }
}
impl Num for f64 {
    fn two(self) -> f64 {
        self * 2.0
    }
}
#[inline(never)]
fn gen<T: Num + Copy>(x: T) -> T {
    x.two().two()
}
#[no_mangle]
pub extern "C" fn generic(x: f32, y: f64) -> f64 {
    gen(x) as f64 + gen(y)
}
#[inline(never)]
fn tot2(v: &[&dyn Shape]) -> f64 {
    let mut s = 0.0;
    for x in v.iter() {
        s += x.area();
    }
    s
}
#[no_mangle]
pub extern "C" fn dyn_area2(a: f32, b: f64) -> f64 {
    let s = Sq(a);
    let c = Ci { r: b, n: 3 };
    tot2(&[&s, &c, &s])
}
