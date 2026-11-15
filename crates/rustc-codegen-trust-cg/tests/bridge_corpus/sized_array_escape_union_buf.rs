// CORPUS FIXTURE — SIZED ARRAY value types, the `core::escape` shape: a
// `([T; N], Range<u8>)` TUPLE-CONTAINING-AN-ARRAY returned by value from a
// constructor, stored in a struct beside a scalar field, and indexed element by
// element. This is the shape behind the 4 `library/core` roots that stopped on
// `Ty::[ascii::ascii_char::AsciiChar; 10_usize]`
// (`char::EscapeDebug` / `EscapeDefault` / `EscapeUnicode`, each built from
// `escape_unicode::<N>() -> ([ascii::Char; N], Range<u8>)`).
//
// WHY EVERY ELEMENT IS PRINTED. The failure this lane could introduce is not a
// refusal, it is a WRONG ELEMENT: an array addressed at the register width
// instead of `size_of::<T>()`, or a tuple whose rustc layout REORDERED its
// fields while the lowering assumed declaration order. Both yield a plausible
// number, so a folded checksum alone is not enough — each buffer position is
// written to stdout and compared against LLVM's.
//
// THE FIELD-SHIFT CLASS is pinned by `Frame` below: an array field with a
// SCALAR FIELD AFTER IT. If the array's size were mis-modelled, `tail` would be
// read from inside the buffer (or the buffer's last element from `tail`).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;
use core::ops::Range;

// A `&[T]`-indexing `no_std` binary at `-Copt-level=0` leaves libcore's own
// object referencing `_rust_eh_personality`, which `-Cpanic=abort` does not
// define; the LLVM ORACLE fails to link without this shim, so it is a property
// of the fixture shape, not of either backend. Defined identically for both
// sides of the differential.
#[no_mangle]
pub extern "C" fn rust_eh_personality() {}

unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, n: usize) -> isize;
}

fn put(v: u32) {
    let mut b = [0u8; 12];
    let mut i = 11usize;
    b[11] = b'\n';
    let mut x = v;
    loop {
        i -= 1;
        b[i] = b'0' + (x % 10) as u8;
        x /= 10;
        if x == 0 {
            break;
        }
    }
    unsafe {
        write(1, b.as_ptr().wrapping_add(i), 12 - i);
    }
}

/// The `core::escape::escape_unicode` shape: build a fixed buffer and hand it
/// back together with the live sub-range, as ONE by-value tuple.
#[inline(never)]
fn escape_unicode(c: u32) -> ([u8; 10], Range<u8>) {
    let mut out = [0u8; 10];
    out[0] = b'\\';
    out[1] = b'u';
    out[2] = b'{';
    out[3] = b'0' + ((c >> 6) & 7) as u8;
    out[4] = b'0' + ((c >> 4) & 7) as u8;
    out[5] = b'0' + ((c >> 2) & 7) as u8;
    out[6] = b'0' + (c & 7) as u8;
    out[7] = b'f';
    out[8] = b'7';
    out[9] = b'}';
    (out, 1..9)
}

/// The `EscapeIterInner<N>` shape: the buffer lives in a struct beside a
/// two-field scalar range, and `next()` indexes it.
struct Iter {
    data: [u8; 10],
    alive: Range<u8>,
}

impl Iter {
    #[inline(never)]
    fn new(c: u32) -> Iter {
        let (data, alive) = escape_unicode(c);
        Iter { data, alive }
    }
    fn next(&mut self) -> Option<u8> {
        if self.alive.start >= self.alive.end {
            return None;
        }
        let i = self.alive.start;
        self.alive.start += 1;
        Some(self.data[usize::from(i)])
    }
}

/// THE FIELD-SHIFT CONTROL: an array field with a SCALAR FIELD AFTER IT.
struct Frame {
    head: u16,
    buf: [u8; 10],
    tail: u32,
}

#[inline(never)]
fn mk_frame(k: u8) -> Frame {
    let mut buf = [0u8; 10];
    let mut i = 0usize;
    while i < 10 {
        buf[i] = k.wrapping_add(i as u8).wrapping_mul(3);
        i += 1;
    }
    Frame {
        head: 0xBEEF,
        buf,
        tail: 0xDEAD_0001,
    }
}

#[inline(never)]
fn read_frame(f: &Frame) -> u32 {
    let mut acc = f.head as u32;
    let mut i = bb(0usize);
    while i < 10 {
        put(f.buf[i] as u32);
        acc = acc.wrapping_mul(31).wrapping_add(f.buf[i] as u32);
        i += 1;
    }
    put(f.head as u32);
    put(f.tail % 1000);
    acc.wrapping_mul(31).wrapping_add(f.tail)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u32 = 0;
    // (1) Every element of the returned buffer, read out of the by-value tuple.
    let (buf, r) = escape_unicode(bb(0b11_10_01_00));
    let mut i = bb(0usize);
    while i < 10 {
        put(buf[i] as u32);
        acc = acc.wrapping_mul(33).wrapping_add(buf[i] as u32);
        i += 1;
    }
    put(r.start as u32);
    put(r.end as u32);
    acc = acc.wrapping_mul(33).wrapping_add(r.end as u32);
    // (2) Every element again, this time through the struct's iterator.
    let mut it = Iter::new(bb(0b00_01_10_11));
    while let Some(v) = it.next() {
        put(v as u32);
        acc = acc.wrapping_mul(33).wrapping_add(v as u32);
    }
    // (3) The buffer passed BY VALUE into an `#[inline(never)]` callee and
    //     indexed there — the array crossing an ABI boundary on its own.
    let s = sum_buf(bb(buf));
    put(s % 100000);
    acc = acc.wrapping_mul(33).wrapping_add(s);
    // (4) The field-shift class: array field with a scalar field AFTER it.
    let f = mk_frame(bb(5u8));
    acc = acc.wrapping_mul(33).wrapping_add(read_frame(&f));
    put(acc % 1000);
    (acc % 89) as i32
}

#[inline(never)]
fn sum_buf(b: [u8; 10]) -> u32 {
    let mut s = 0u32;
    let mut i = 0usize;
    while i < 10 {
        s = s.wrapping_mul(7).wrapping_add(b[i] as u32);
        i += 1;
    }
    s
}
