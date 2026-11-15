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
#[derive(Clone, Copy)]
struct M {
    a: f32,
    b: f64,
    c: u8,
    d: f32,
}
#[inline(never)]
fn mk(x: f32, y: f64) -> M {
    M {
        a: x,
        b: y,
        c: 7,
        d: x * 2.0,
    }
}
#[inline(never)]
fn sum(m: M) -> f64 {
    m.a as f64 + m.b + m.c as f64 + m.d as f64
}
#[no_mangle]
pub extern "C" fn st(x: f32, y: f64) -> f64 {
    let m = mk(x, y);
    let n = M { b: m.b * 3.0, ..m };
    sum(m) - sum(n) * 0.5
}
#[inline(never)]
fn pair(x: f64) -> (f32, f64) {
    (x as f32, x * x)
}
#[no_mangle]
pub extern "C" fn tup(x: f64) -> f64 {
    let (a, b) = pair(x);
    a as f64 + b
}
#[inline(never)]
fn opt(x: f64) -> Option<f64> {
    if x > 0.0 { Some(x.sqrt_approx()) } else { None }
}
trait Sq {
    fn sqrt_approx(self) -> f64;
}
impl Sq for f64 {
    fn sqrt_approx(self) -> f64 {
        core::f64::math::sqrt(self)
    }
}
#[no_mangle]
pub extern "C" fn optf(x: f64) -> f64 {
    opt(x).map(|v| v + 1.0).unwrap_or(-1.0)
}
enum E {
    A(f32),
    B(f64, f32),
    C,
}
#[inline(never)]
fn ev(e: &E) -> f64 {
    match e {
        E::A(a) => *a as f64,
        E::B(b, c) => b - *c as f64,
        E::C => 0.5,
    }
}
#[no_mangle]
pub extern "C" fn en(x: f32, y: f64) -> f64 {
    let v = [E::A(x), E::B(y, x), E::C];
    ev(&v[0]) + ev(&v[1]) * 2.0 + ev(&v[2])
}
#[inline(never)]
fn byref(a: &f64, b: &mut f32) {
    *b = (*a * 2.0) as f32 + *b;
}
#[no_mangle]
pub extern "C" fn refs(x: f64, y: f32) -> f32 {
    let mut z = y;
    byref(&x, &mut z);
    z
}
static mut ACC: f64 = 0.0;
#[no_mangle]
pub extern "C" fn acc(x: f64) -> f64 {
    unsafe {
        ACC = ACC * 0.5 + x;
        ACC
    }
}
static TBL: [f32; 5] = [0.1, -2.5, 1e30, f32::MIN_POSITIVE, 3.0];
#[no_mangle]
pub extern "C" fn tbl(i: u32, x: f32) -> f32 {
    TBL[(i % 5) as usize] * x
}
#[inline(never)]
fn many(a: f32, b: f64, c: f32, d: f64, e: f32, f: f64, g: f32, h: f64, i: f32, j: f64) -> f64 {
    a as f64 - b + c as f64 * d - e as f64 / f + g as f64 - h * i as f64 + j
}
#[no_mangle]
pub extern "C" fn manyargs(x: f32, y: f64) -> f64 {
    many(x, y, x + 1.0, y - 1.0, 2.0, y, -x, 0.5, x, y * y)
}
#[no_mangle]
pub extern "C" fn closure(x: f64, y: f32) -> f64 {
    let k = y as f64;
    let f = |t: f64| t * k + x;
    let g = move |t: f32| f(t as f64) - k;
    g(y) + f(1.0)
}
