// CORPUS FIXTURE — every std panic shape must run the program's panic HOOK,
// with the Location the real panic entry reports, before `panic=abort` aborts.
// The shape is chosen at run time (`PANIC_SHAPE=a`..`k`) so one binary covers
// them all; the hook exits with a code derived from the reported file / line /
// column, so a skipped hook (SIGABRT) or a wrong Location (a different code)
// both diverge from the LLVM oracle.
use std::hint::black_box;

#[inline(never)]
fn option_unwrap() -> u32 {
    let o: Option<u32> = black_box(None);
    o.unwrap()
}

#[inline(never)]
fn option_expect() -> u32 {
    let o: Option<u32> = black_box(None);
    o.expect("value present")
}

#[inline(never)]
fn result_unwrap() -> u32 {
    let r: Result<u32, i32> = black_box(Err(7));
    r.unwrap()
}

#[inline(never)]
fn panic_literal() -> u32 {
    let v: u32 = black_box(3);
    if v == 3 {
        panic!("boom");
    }
    v
}

#[inline(never)]
fn panic_formatted() -> u32 {
    let v: u32 = black_box(3);
    if v == 3 {
        panic!("boom {v}");
    }
    v
}

#[inline(never)]
fn unreachable_arm() -> u32 {
    match black_box(3u32) {
        0 => 1,
        1 => 2,
        _ => unreachable!(),
    }
}

#[inline(never)]
fn assert_message() -> u32 {
    let v: u32 = black_box(3);
    assert!(v < 2, "too big");
    v
}

#[inline(never)]
fn divide_by_zero() -> u32 {
    let a: u32 = black_box(10);
    let b: u32 = black_box(0);
    a / b
}

#[inline(never)]
fn range_index() -> u32 {
    let a: [u32; 4] = black_box([1, 2, 3, 4]);
    let i: usize = black_box(9);
    let s = &a[1..i];
    s[0]
}

#[inline(never)]
fn split_at() -> u32 {
    let a: [u32; 4] = black_box([1, 2, 3, 4]);
    let i: usize = black_box(9);
    let (l, r) = a.split_at(i);
    l[0] + r.len() as u32
}

/// `copy_nonoverlapping` whose byte count overflows: with UB checks on (`-O0`)
/// its precondition raises `core::panicking::panic_nounwind`, which is NOT
/// `#[track_caller]` — the hook sees a Location inside `core`, not this line.
/// Only run at `-O0`: without the UB check the call is undefined behavior.
#[inline(never)]
fn copy_count_overflow() -> u32 {
    let a: [u64; 4] = black_box([1, 2, 3, 4]);
    let mut b: [u64; 4] = [0; 4];
    let n: usize = black_box(usize::MAX);
    unsafe { std::ptr::copy_nonoverlapping(a.as_ptr(), b.as_mut_ptr(), n) };
    b[0] as u32
}

unsafe extern "C" {
    fn getenv(name: *const std::ffi::c_char) -> *const std::ffi::c_char;
}

/// The shape to raise: the first byte of `PANIC_SHAPE` (`a`..`k`), read through
/// libc so the selector itself needs nothing beyond a raw byte load.
fn shape() -> u8 {
    let value = unsafe { getenv(c"PANIC_SHAPE".as_ptr()) };
    if value.is_null() { 0 } else { unsafe { *value as u8 } }
}

fn main() {
    std::panic::set_hook(Box::new(|info| {
        let l = info.location().expect("a location");
        let code = (l.line() * 7 + l.column() * 3 + l.file().len() as u32) % 251;
        std::process::exit(code as i32);
    }));
    let x = match shape() {
        b'a' => option_unwrap(),
        b'b' => option_expect(),
        b'c' => result_unwrap(),
        b'd' => panic_literal(),
        b'e' => panic_formatted(),
        b'f' => unreachable_arm(),
        b'g' => assert_message(),
        b'h' => divide_by_zero(),
        b'i' => range_index(),
        b'j' => split_at(),
        b'k' => copy_count_overflow(),
        _ => 250,
    };
    std::process::exit((x % 200) as i32 + 1);
}
