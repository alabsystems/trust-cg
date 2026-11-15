// CORPUS FIXTURE — a union (`MaybeUninit<T>`) whose active field holds a FAT
// pointer leaf: `MaybeUninit<Part>` with `enum Part { Zero(usize), Num(u16),
// Copy(&[u8]) }`, the exact shape of core's `flt2dec` formatting buffers
// (`[MaybeUninit<Part>; 4]` filled element by element through
// `&mut [MaybeUninit<Part>]`, then `assume_init_ref`). Exercises the union
// slot layout with a two-lane leaf, `MaybeUninit::new`/`uninit` by value (a
// 24-byte union call result re-stored), whole-element stores through a slice
// fat pointer and directly into a local array, and the read-back through the
// `&[Part]` cast and `assume_init`.
#![no_std]
#![no_main]

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

use core::hint::black_box as bb;
use core::mem::MaybeUninit;

#[derive(Clone, Copy)]
enum Part<'a> {
    Zero(usize),
    Num(u16),
    Copy(&'a [u8]),
}

const _: () = assert!(core::mem::size_of::<Part>() == 24);
const _: () = assert!(core::mem::size_of::<MaybeUninit<Part>>() == 24);

/// A subslice without the range-index panic path (`slice_index_fail` is not a
/// `panic*` symbol, so the harness's abort stubs would not cover it).
#[inline(never)]
fn sub(buf: &[u8], start: usize, len: usize) -> &[u8] {
    unsafe { core::slice::from_raw_parts(buf.as_ptr().add(start), len) }
}

#[inline(never)]
fn fill<'a>(parts: &mut [MaybeUninit<Part<'a>>], buf: &'a [u8]) -> &'a [Part<'a>] {
    parts[0] = MaybeUninit::new(Part::Copy(sub(buf, 0, 2)));
    parts[1] = MaybeUninit::new(Part::Zero(3));
    parts[2] = MaybeUninit::new(Part::Num(41));
    unsafe { core::slice::from_raw_parts(parts.as_ptr() as *const Part<'a>, 3) }
}

/// The array twin: a LOCAL `[MaybeUninit<Part>; 4]` (core's
/// `float_to_decimal_common_exact` shape) written in place at a runtime index
/// and read back element by element. (A store through a `&mut [T; N]`
/// reference to such an array is a different, still-refused path.)
#[inline(never)]
fn fill_array(buf: &[u8], k: usize) -> usize {
    let mut parts = [MaybeUninit::<Part>::uninit(); 4];
    parts[k] = MaybeUninit::new(Part::Copy(sub(buf, k, 5 - k)));
    parts[3] = MaybeUninit::new(Part::Num(7));
    let p: Part = unsafe { parts[k].assume_init() };
    let q: Part = unsafe { parts[3].assume_init() };
    part_value(p) * 100 + part_value(q)
}

#[inline(never)]
fn part_value(p: Part<'_>) -> usize {
    match p {
        Part::Zero(n) => n,
        Part::Num(v) => v as usize,
        Part::Copy(b) => b.len() + b[0] as usize,
    }
}

#[inline(never)]
fn total(ps: &[Part<'_>]) -> usize {
    let mut s = 0;
    for p in ps {
        s += part_value(*p);
    }
    s
}

#[inline(never)]
fn round_trip(p: Part<'_>) -> usize {
    let m = MaybeUninit::new(p);
    let m2 = m;
    part_value(unsafe { m2.assume_init() })
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let buf = bb(b"12345" as &[u8]);
    let mut parts = [MaybeUninit::<Part>::uninit(); 4];
    let a = total(fill(&mut parts, buf)); // (2 + 49) + 3 + 41 = 95
    let b = fill_array(buf, bb(1)); // (4 + 50) * 100 + 7 = 5407
    let c = round_trip(Part::Copy(sub(buf, 3, 2))); // 2 + 52 = 54
    let d = round_trip(Part::Num(bb(9))); // 9
    ((a + b + c + d) & 0x7f) as i32 // 5565 & 0x7f = 61
}
