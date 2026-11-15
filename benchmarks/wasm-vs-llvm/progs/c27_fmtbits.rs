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
struct Buf {
    b: [u8; 128],
    n: usize,
}
impl core::fmt::Write for Buf {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for &c in s.as_bytes() {
            if self.n == 128 {
                return Err(core::fmt::Error);
            }
            self.b[self.n] = c;
            self.n += 1;
        }
        Ok(())
    }
}
#[inline(never)]
fn h(w: &Buf) -> u32 {
    let mut h = 0u32;
    let mut i = 0;
    while i < w.n {
        h = h.wrapping_mul(31).wrapping_add(w.b[i] as u32);
        i += 1;
    }
    h ^ (w.n as u32) << 24
}
#[no_mangle]
pub extern "C" fn fmtb64(x: u64) -> u32 {
    use core::fmt::Write;
    let mut w = Buf { b: [0; 128], n: 0 };
    let _ = write!(w, "{}", f64::from_bits(x));
    h(&w)
}
#[no_mangle]
pub extern "C" fn fmtb32(x: u32) -> u32 {
    use core::fmt::Write;
    let mut w = Buf { b: [0; 128], n: 0 };
    let _ = write!(w, "{:?}", f32::from_bits(x));
    h(&w)
}
#[no_mangle]
pub extern "C" fn fmtb64e(x: u64) -> u32 {
    use core::fmt::Write;
    let mut w = Buf { b: [0; 128], n: 0 };
    let _ = write!(
        w,
        "{:e}|{:E}",
        f64::from_bits(x),
        f64::from_bits(x.rotate_left(9))
    );
    h(&w)
}
#[no_mangle]
pub extern "C" fn fmtb64p(x: u64, p: u32) -> u32 {
    use core::fmt::Write;
    let mut w = Buf { b: [0; 128], n: 0 };
    let _ = write!(w, "{:.*}", (p % 30) as usize, f64::from_bits(x));
    h(&w)
}
#[no_mangle]
pub extern "C" fn fmtb32w(x: u32, p: u32) -> u32 {
    use core::fmt::Write;
    let mut w = Buf { b: [0; 128], n: 0 };
    let _ = write!(
        w,
        "{:+>1$.2$e}",
        f32::from_bits(x),
        (p % 40) as usize,
        (p >> 8) as usize % 12
    );
    h(&w)
}
