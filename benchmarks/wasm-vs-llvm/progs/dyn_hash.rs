#![no_std]
#![allow(dead_code)]

use core::hash::Hasher;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

struct Fnv(u64);
impl Hasher for Fnv {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0 ^ b as u64).wrapping_mul(0x100000001b3);
        }
    }
}

struct Crc(u32);
impl Hasher for Crc {
    fn finish(&self) -> u64 {
        !self.0 as u64
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            let mut c = (self.0 ^ b as u32) & 0xff;
            for _ in 0..8 {
                c = if c & 1 != 0 {
                    0xEDB88320 ^ (c >> 1)
                } else {
                    c >> 1
                };
            }
            self.0 = c ^ (self.0 >> 8);
        }
    }
}

#[inline(never)]
fn feed(h: &mut dyn Hasher, data: &[u8], k: u32) -> u64 {
    h.write(data);
    h.write_u32(k);
    h.write_u8(k as u8);
    h.write_u64(k as u64 * 3);
    h.write_usize(data.len());
    h.finish()
}

trait Shape {
    fn area2(&self) -> u64;
    fn scale(&mut self, k: u32);
    fn name_len(&self) -> usize {
        4
    }
}

struct Rect {
    w: u32,
    h: u32,
}
struct Tri {
    b: u16,
    h: u16,
    flip: bool,
}
struct Poly {
    pts: [(i32, i32); 5],
}

impl Shape for Rect {
    fn area2(&self) -> u64 {
        2 * self.w as u64 * self.h as u64
    }
    fn scale(&mut self, k: u32) {
        self.w = self.w.wrapping_mul(k);
        self.h = self.h.wrapping_add(k);
    }
}
impl Shape for Tri {
    fn area2(&self) -> u64 {
        self.b as u64 * self.h as u64 + self.flip as u64
    }
    fn scale(&mut self, k: u32) {
        self.b = self.b.wrapping_mul(k as u16);
        self.flip = !self.flip;
    }
    fn name_len(&self) -> usize {
        3
    }
}
impl Shape for Poly {
    fn area2(&self) -> u64 {
        let mut s = 0i64;
        for i in 0..5 {
            let (x1, y1) = self.pts[i];
            let (x2, y2) = self.pts[(i + 1) % 5];
            s += x1 as i64 * y2 as i64 - x2 as i64 * y1 as i64;
        }
        s.unsigned_abs()
    }
    fn scale(&mut self, k: u32) {
        for p in self.pts.iter_mut() {
            p.0 = p.0.wrapping_mul(k as i32);
        }
    }
    fn name_len(&self) -> usize {
        7
    }
}

#[inline(never)]
fn total(shapes: &mut [&mut dyn Shape], k: u32) -> u64 {
    let mut t = 0u64;
    for s in shapes.iter_mut() {
        s.scale(k);
        t = t.wrapping_add(s.area2()).wrapping_add(s.name_len() as u64);
    }
    t
}

#[inline(never)]
fn apply_all(fs: &[&dyn Fn(i64) -> i64], x: i64) -> i64 {
    let mut v = x;
    for f in fs {
        v = f(v);
    }
    v
}

#[inline(never)]
fn run_mut(f: &mut dyn FnMut(u32) -> bool, n: u32) -> u32 {
    let mut c = 0;
    for i in 0..n {
        if f(i) {
            c += 1;
        }
    }
    c
}

#[inline(never)]
fn generic_sum<I: Iterator<Item = u32>>(it: I) -> u64 {
    let mut s = 0u64;
    for (i, x) in it.enumerate() {
        s = s.wrapping_add((x as u64) << (i % 16));
    }
    s
}

#[no_mangle]
pub extern "C" fn dyn_hash(k: u32, which: u32) -> u64 {
    let data = b"dynamic dispatch over hashers";
    let n = (k as usize) % (data.len() + 1);
    let mut f = Fnv(0xcbf29ce484222325);
    let mut c = Crc(!0);
    let h: &mut dyn Hasher = if which & 1 == 0 { &mut f } else { &mut c };
    feed(h, &data[..n], k)
}
