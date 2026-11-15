// CORPUS FIXTURE — `Vec::extend` from a `Range` and from `TrustedLen` chains,
// for `range_closed_forms_differential.rs`. One CASE per run (`CASE=<name>`,
// read through libc), each printing integers or panicking.
//
// std's `Vec::extend` over a `TrustedLen` iterator is `extend_trusted`: it
// reserves the exact `size_hint` BEFORE pulling anything, so a length past
// `usize::MAX` or the allocation byte bound panics "capacity overflow" before
// any element (and any `map` closure) is evaluated, and an empty range of any
// span appends nothing. A non-`TrustedLen` chain with an exact size hint is
// `extend_desugared`, which pulls one item and then reserves `lower + 1` when
// the Vec is full. Each `map` closure here counts its calls and ends the process
// with exit code 42 on the 1000th, so a missing up-front reservation shows as a
// different ending instead of unbounded memory.
use std::hint::black_box as bb;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static CALLS: AtomicUsize = AtomicUsize::new(0);

#[inline(never)]
fn tick() {
    if CALLS.fetch_add(1, Relaxed) == 999 {
        std::process::exit(42);
    }
}

#[inline(never)]
fn ext_i64(v: &mut Vec<i64>, a: i64, b: i64) {
    v.extend(a..b)
}
#[inline(never)]
fn ext_isize(v: &mut Vec<isize>, a: isize, b: isize) {
    v.extend(a..b)
}
#[inline(never)]
fn ext_u64(v: &mut Vec<u64>, a: u64, b: u64) {
    v.extend(a..b)
}
#[inline(never)]
fn ext_i32(v: &mut Vec<i32>, a: i32, b: i32) {
    v.extend(a..b)
}
#[inline(never)]
fn ext_u8(v: &mut Vec<u8>, a: u8, b: u8) {
    v.extend(a..b)
}
#[inline(never)]
fn ext_map(v: &mut Vec<i64>, a: i64, b: i64) {
    v.extend((a..b).map(|x| {
        tick();
        x
    }))
}
#[inline(never)]
fn ext_map_u8(v: &mut Vec<u8>, a: u64, b: u64) {
    v.extend((a..b).map(|x| {
        tick();
        x as u8
    }))
}
#[inline(never)]
fn ext_map_incl(v: &mut Vec<u64>, a: u64, b: u64) {
    v.extend((a..=b).map(|x| {
        tick();
        x
    }))
}
#[inline(never)]
fn ext_map_u128(v: &mut Vec<u64>, a: u128, b: u128) {
    v.extend((a..b).map(|x| {
        tick();
        x as u64
    }))
}
/// Not `TrustedLen` (`Skip` over a `RangeInclusive`): `extend_desugared`.
#[inline(never)]
fn ext_skip_incl(v: &mut Vec<u64>, a: u64, b: u64, n: usize) {
    v.extend((a..=b).skip(n).map(|x| {
        tick();
        x
    }))
}

/// Contents and capacity, as integers.
#[inline(never)]
fn show_i64(v: &Vec<i64>) {
    for &x in v.iter() {
        print!("{x} ");
    }
    println!("| cap {}", v.capacity());
}
#[inline(never)]
fn show_u64(v: &Vec<u64>) {
    for &x in v.iter() {
        print!("{x} ");
    }
    println!("| cap {}", v.capacity());
}
#[inline(never)]
fn one_i64(a: i64, b: i64) {
    let mut v = vec![1i64];
    ext_i64(&mut v, bb(a), bb(b));
    show_i64(&v);
}
#[inline(never)]
fn one_isize(a: isize, b: isize) {
    let mut v = vec![1isize];
    ext_isize(&mut v, bb(a), bb(b));
    for &x in v.iter() {
        print!("{x} ");
    }
    println!("| cap {}", v.capacity());
}
#[inline(never)]
fn one_u64(a: u64, b: u64) {
    let mut v = vec![1u64];
    ext_u64(&mut v, bb(a), bb(b));
    show_u64(&v);
}

unsafe extern "C" {
    fn getenv(name: *const std::ffi::c_char) -> *const std::ffi::c_char;
}

/// The `CASE` selector, read through libc (no `String` / `OsString` needed).
fn case() -> &'static [u8] {
    let value = unsafe { getenv(c"CASE".as_ptr()) };
    if value.is_null() { b"" } else { unsafe { std::ffi::CStr::from_ptr(value) }.to_bytes() }
}

fn main() {
    match case() {
        b"range_i64" => {
            one_i64(-2, 2);
            one_i64(3, -3);
            one_i64(i64::MAX - 2, i64::MAX);
            one_i64(i64::MAX, i64::MIN);
            one_i64(i64::MAX, i64::MIN + 2);
            one_i64(5_000_000_000_000_000_000, -5_000_000_000_000_000_000);
        }
        b"range_isize" => {
            one_isize(-2, 2);
            one_isize(isize::MAX, isize::MIN);
            one_isize(isize::MAX, isize::MIN + 2);
        }
        b"range_u64" => {
            one_u64(2, 6);
            one_u64(u64::MAX, 0);
            one_u64(u64::MAX - 2, u64::MAX);
            one_u64(9, 3);
        }
        b"range_narrow" => {
            let mut v = vec![1i32];
            ext_i32(&mut v, bb(i32::MAX - 1), bb(i32::MIN));
            ext_i32(&mut v, bb(-3), bb(2));
            for &x in v.iter() {
                print!("{x} ");
            }
            println!("| cap {}", v.capacity());
            let mut v = vec![1u8];
            ext_u8(&mut v, bb(250), bb(255));
            ext_u8(&mut v, bb(255), bb(0));
            for &x in v.iter() {
                print!("{x} ");
            }
            println!("| cap {}", v.capacity());
        }
        // `extend_trusted`'s reservation: capacity overflow before any write.
        b"range_span_2p63" => one_i64(i64::MIN, 0),
        b"range_span_full" => one_i64(i64::MIN, i64::MAX),
        b"range_u64_full" => one_u64(0, u64::MAX),
        b"map_small" => {
            let mut v = vec![7i64];
            ext_map(&mut v, bb(-2), bb(8));
            show_i64(&v);
            let mut v = vec![7u8];
            ext_map_u8(&mut v, bb(250), bb(260));
            for &x in v.iter() {
                print!("{x} ");
            }
            println!("| cap {}", v.capacity());
            let mut v = vec![7u64];
            ext_map_incl(&mut v, bb(u64::MAX - 3), bb(u64::MAX));
            show_u64(&v);
            let mut v = vec![7u64];
            ext_map_u128(&mut v, bb(5), bb(9));
            show_u64(&v);
            let mut v = vec![7u64];
            ext_skip_incl(&mut v, bb(1), bb(9), bb(3));
            show_u64(&v);
            println!("calls {}", CALLS.load(Relaxed));
        }
        // Each panics "capacity overflow" before its closure ever runs.
        b"map_huge" => {
            let mut v = vec![7i64];
            ext_map(&mut v, bb(i64::MIN), bb(0));
            println!("returned {}", CALLS.load(Relaxed));
        }
        b"map_u8_huge" => {
            let mut v = vec![7u8];
            ext_map_u8(&mut v, bb(0), bb(u64::MAX));
            println!("returned {}", CALLS.load(Relaxed));
        }
        b"map_incl_full" => {
            let mut v = Vec::new();
            ext_map_incl(&mut v, bb(0), bb(u64::MAX));
            println!("returned {}", CALLS.load(Relaxed));
        }
        b"map_u128_huge" => {
            let mut v = vec![7u64];
            ext_map_u128(&mut v, bb(0), bb(u128::MAX));
            println!("returned {}", CALLS.load(Relaxed));
        }
        // Not `TrustedLen`: one item is pulled (the closure runs once), then
        // the full Vec reserves `lower + 1` and overflows.
        b"skip_incl_huge" => {
            let mut v = vec![7u64];
            ext_skip_incl(&mut v, bb(0), bb(u64::MAX), bb(1));
            println!("returned {}", CALLS.load(Relaxed));
        }
        _ => std::process::exit(2),
    }
}
