// CORPUS FIXTURE — tuple pointee whose field is a NESTED struct / array
// (`&(Range, i16)`, `&(u16, [u16; 3])`): the exact shape of core's
// `unicode_data::conversions` lookup tables (`L2Lut { singles: &[(Range, i16)],
// multis: &[(u16, [u16; 3])] }`, `Range { start: u16, len: u8, parity: bool }`).
// The flat scalar-field pointee lane cannot represent a tuple with an aggregate
// field; the byte-offset memory lane types the pointee as its rustc-layout slot
// and every `(*r).N` projection walks real offsets. Exercises `get_unchecked`
// (rustc's `Rvalue::RawPtr` rewrite), `binary_search_by` closures taking
// `&(T, U)`, whole-tuple copies out of a memory pointee (`let &(r, d) = ..`), a
// nested array element read, and a `&local_tuple` slot construction.
#![no_std]
#![no_main]

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

use core::cmp::Ordering::{Equal, Greater, Less};
use core::hint::black_box as bb;

#[derive(Copy, Clone)]
struct Range {
    start: u16,
    len: u8,
    parity: bool,
}

const _: () = assert!(core::mem::size_of::<(Range, i16)>() == 6);
const _: () = assert!(core::mem::size_of::<(u16, [u16; 3])>() == 8);

static SINGLES: &[(Range, i16)] = &[
    (
        Range {
            start: 10,
            len: 2,
            parity: false,
        },
        3,
    ),
    (
        Range {
            start: 20,
            len: 0,
            parity: true,
        },
        -7,
    ),
    (
        Range {
            start: 40,
            len: 9,
            parity: true,
        },
        11,
    ),
];

static MULTIS: &[(u16, [u16; 3])] = &[(5, [1, 2, 3]), (9, [4, 5, 6]), (33, [7, 8, 9])];

#[inline(never)]
fn lookup(x: u16) -> i64 {
    match SINGLES.binary_search_by(|(r, _)| {
        if x < r.start {
            Greater
        } else if x > r.start + r.len as u16 {
            Less
        } else {
            Equal
        }
    }) {
        Ok(i) => {
            let &(r, d) = unsafe { SINGLES.get_unchecked(i) };
            (r.parity as i64) * 100 + d as i64 + r.len as i64
        }
        Err(i) => -(i as i64),
    }
}

#[inline(never)]
fn lookup2(x: u16) -> i64 {
    if let Ok(i) = MULTIS.binary_search_by_key(&x, |&(p, _)| p) {
        let &(_, a) = unsafe { MULTIS.get_unchecked(i) };
        a[0] as i64 * 1000 + a[2] as i64
    } else {
        0
    }
}

#[inline(never)]
fn peek(t: &(Range, i16)) -> i64 {
    t.0.start as i64 * 4 + t.0.len as i64 * 2 + t.0.parity as i64 + t.1 as i64
}

#[inline(never)]
fn peek2(t: &(u16, [u16; 3])) -> i64 {
    t.0 as i64 * 10 + t.1[1] as i64
}

#[inline(never)]
fn mix(hash: u64, v: i64) -> u64 {
    (hash ^ (v as u64)).wrapping_mul(0x100000001b3)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut hash: u64 = 0xcbf29ce484222325;
    let n = bb(64u16);
    let mut x = 0u16;
    while x < n {
        hash = mix(hash, lookup(x).wrapping_add(lookup2(x)));
        x += 1;
    }
    let i = bb(2usize);
    hash = mix(hash, peek(&SINGLES[i]));
    let t = (
        Range {
            start: bb(7),
            len: bb(1),
            parity: bb(true),
        },
        bb(9i16),
    );
    hash = mix(hash, peek(&t));
    let m = (bb(3u16), [bb(4u16), bb(5), bb(6)]);
    hash = mix(hash, peek2(&MULTIS[bb(1)]));
    hash = mix(hash, peek2(&m));
    (hash & 0x7f) as i32
}
