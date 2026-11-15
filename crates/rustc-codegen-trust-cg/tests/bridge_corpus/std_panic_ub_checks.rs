// CORPUS FIXTURE — std's debug-assertion precondition checks
// (`assert_unsafe_precondition!`), compiled with `-Cdebug-assertions=on` so
// `ub_checks()` is live. A violated precondition calls the check's
// `panic_nounwind_fmt("unsafe precondition(s) violated: ...", false)` with
// the `#[track_caller]` Location of the unsafe call: the hook runs with that
// message and Location, and the process aborts (the panic cannot unwind)
// under BOTH strategies.
//
// The shape is the first byte of `PANIC_SHAPE` (`z` = no panic); the hook is
// chosen by `PANIC_HOOK` as in `std_panic_intercepted.rs`.
use std::hint::black_box;

struct Guard;

impl Drop for Guard {
    fn drop(&mut self) {
        out(b"drop\n");
    }
}

#[inline(never)]
fn get_unchecked(s: &[u32], i: usize) -> usize {
    unsafe { *s.get_unchecked(i) as usize }
}

#[inline(never)]
fn from_raw_parts(p: *const u32, n: usize) -> usize {
    let s = unsafe { std::slice::from_raw_parts(p, n) };
    s.len()
}

#[inline(never)]
fn unchecked_add(a: u32, b: u32) -> usize {
    unsafe { a.unchecked_add(b) as usize }
}

#[inline(never)]
fn non_null_new_unchecked(p: *mut u32) -> usize {
    let n = unsafe { std::ptr::NonNull::new_unchecked(p) };
    n.as_ptr() as usize % 7
}

#[inline(never)]
fn shape(selector: u8) -> usize {
    let words: &[u32] = black_box(&[1, 2, 3][..]);
    match selector {
        b'a' => get_unchecked(words, black_box(9)),
        b'b' => from_raw_parts(black_box(std::ptr::null()), black_box(3)),
        b'c' => unchecked_add(black_box(u32::MAX), black_box(3)),
        b'e' => non_null_new_unchecked(black_box(std::ptr::null_mut())),
        // No panic: every shape, in range.
        _ => {
            let mut cell = 5u32;
            get_unchecked(words, black_box(2))
                + from_raw_parts(words.as_ptr(), black_box(3))
                + unchecked_add(black_box(7), black_box(3))
                + non_null_new_unchecked(black_box(&mut cell as *mut u32)) * 0
        }
    }
}

#[inline(never)]
fn run(selector: u8) -> usize {
    let _guard = Guard;
    shape(selector)
}

unsafe extern "C" {
    fn getenv(name: *const std::ffi::c_char) -> *const std::ffi::c_char;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

fn out(bytes: &[u8]) {
    unsafe { write(1, bytes.as_ptr(), bytes.len()) };
}

fn out_u32(mut n: u32) {
    let mut buf = [0u8; 10];
    let mut i = buf.len();
    loop {
        i -= 1;
        buf[i] = b'0' + (n % 10) as u8;
        n /= 10;
        if n == 0 {
            break;
        }
    }
    out(&buf[i..]);
}

/// The first byte of an environment variable, 0 when it is absent.
fn env_byte(name: &std::ffi::CStr) -> u8 {
    let value = unsafe { getenv(name.as_ptr()) };
    if value.is_null() {
        0
    } else {
        unsafe { *value as u8 }
    }
}

fn main() {
    match env_byte(c"PANIC_HOOK") {
        0 => panic_observer::install(),
        b'b' => std::panic::set_hook(Box::new(|info| {
            out(b"bridge-hook");
            if let Some(l) = info.location() {
                out(b" @ ");
                out(l.file().as_bytes());
                out(b":");
                out_u32(l.line());
                out(b":");
                out_u32(l.column());
            }
            out(b"\n");
        })),
        _ => {}
    }
    let x = run(env_byte(c"PANIC_SHAPE"));
    std::process::exit((x % 200) as i32 + 1);
}
