#![no_std]
#![allow(dead_code)]

use core::fmt::Write;

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

impl Write for Buf {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let bytes = s.as_bytes();
        if self.n + bytes.len() > self.b.len() {
            return Err(core::fmt::Error);
        }
        self.b[self.n..self.n + bytes.len()].copy_from_slice(bytes);
        self.n += bytes.len();
        Ok(())
    }
}

#[inline(never)]
fn digest(b: &Buf) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    for &c in &b.b[..b.n] {
        h = (h ^ c as u64).wrapping_mul(0x100000001b3);
    }
    h ^ (b.n as u64) << 56
}

#[derive(Debug, Clone, Copy)]
enum Color {
    Red,
    Rgb(u8, u8, u8),
    Named { idx: u16, dark: bool },
}

#[derive(Debug)]
struct Pt {
    x: i16,
    y: i16,
    c: Color,
}

#[no_mangle]
pub extern "C" fn fmt_ints(a: i32, b: u32) -> u64 {
    let mut w = Buf { b: [0; 128], n: 0 };
    let r = write!(
        w,
        "{} {} {:x} {:X} {:o} {:b} {:08x} {:+} {:>6} {:<6}| {:^7}|",
        a,
        b,
        b,
        a,
        b & 0xfff,
        b & 0xff,
        a,
        a,
        b % 1000,
        a % 100,
        b % 77
    );
    digest(&w) ^ r.is_err() as u64
}
