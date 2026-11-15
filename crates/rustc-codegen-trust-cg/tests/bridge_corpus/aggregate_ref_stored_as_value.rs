// Root (e): a bare `r = &mut buf` / `&agg` of a SCALARIZED aggregate stored AS A VALUE
// into another aggregate — a closure capture (`<wtf8::EncodeWide as Iterator>::next`:
// `_9 = &mut _5; _8 = {closure} { buf: move _9, self: move _10 }`), an ADT field,
// a tuple element and an `Option<&T>` payload. Before, every one failed closed with
// "borrowed aggregate reference used without deref"; with rule (4k) the referent
// is memory-backed and the stored value is its real slot address.
// CORPUS FIXTURE. Correct exit = LLVM oracle (40 at O0/O2).
#![no_std]
#![no_main]
use core::hint::black_box;
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }

pub struct Cp(u32);
impl Cp { fn to_u32(&self) -> u32 { self.0 } }
pub struct Cps<'a> { s: &'a [u32], i: usize }
impl<'a> Iterator for Cps<'a> {
    type Item = Cp;
    fn next(&mut self) -> Option<Cp> {
        if self.i < self.s.len() {
            let c = self.s[self.i];
            self.i += 1;
            Some(Cp(c))
        } else {
            None
        }
    }
}
#[inline(never)]
fn enc(code: u32, dst: &mut [u16]) -> usize {
    if code < 0x10000 {
        dst[0] = code as u16;
        1
    } else {
        let c = code - 0x10000;
        dst[0] = 0xD800 | ((c >> 10) as u16);
        dst[1] = 0xDC00 | ((c as u16) & 0x3FF);
        2
    }
}
// The EncodeWide::next shape (core/src/wtf8.rs:579).
pub struct EW<'a> { code_points: Cps<'a>, extra: u16 }
impl Iterator for EW<'_> {
    type Item = u16;
    fn next(&mut self) -> Option<u16> {
        if self.extra != 0 {
            let tmp = self.extra;
            self.extra = 0;
            return Some(tmp);
        }
        let mut buf = [0; 2];
        self.code_points.next().map(|code_point| {
            let n = enc(code_point.to_u32(), &mut buf);
            if n == 2 {
                self.extra = buf[1];
            }
            buf[0]
        })
    }
}

pub struct P { a: u64, b: u64 }
pub struct H<'a> { r: &'a [u16; 2], k: u64 }
#[inline(never)] fn take_opt(o: Option<&[u16; 2]>) -> u16 { match o { Some(a) => a[0] + a[1], None => 0 } }
#[inline(never)] fn take_h(h: H<'_>) -> u64 { h.r[1] as u64 + h.k }
#[inline(never)] fn take_t(t: (&P, u64)) -> u64 { t.0.a * 3 + t.0.b + t.1 }
#[inline(never)] fn v_opt(x: u16) -> u16 { let buf = [x, 3]; take_opt(Some(&buf)) }
#[inline(never)] fn v_adt(x: u16) -> u64 { let buf = [x, 3]; take_h(H { r: &buf, k: 9 }) }
#[inline(never)] fn v_tup(x: u64) -> u64 { let p = P { a: x, b: 2 }; take_t((&p, 4)) }
// A write through the captured `&mut` must be visible in the referent afterwards.
#[inline(never)] fn v_clo_mut(x: u16) -> u16 {
    let mut buf = [x, 3];
    let mut f = |v: u16| { buf[1] = v; };
    f(black_box(7));
    buf[0] * 10 + buf[1]
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let cps = black_box([0x41u32, 0x1F600, 0x7FF, 0x10437]);
    let mut ew = EW { code_points: Cps { s: &cps, i: 0 }, extra: 0 };
    let mut acc: u32 = 0;
    while let Some(u) = ew.next() {
        acc = acc.wrapping_mul(33).wrapping_add(u as u32);
    }
    acc = acc.wrapping_add(v_opt(black_box(40)) as u32);
    acc = acc.wrapping_add(v_adt(black_box(5)) as u32 * 5);
    acc = acc.wrapping_add(v_tup(black_box(11)) as u32 * 7);
    acc = acc.wrapping_add(v_clo_mut(black_box(6)) as u32 * 11);
    (acc % 251) as i32
}
