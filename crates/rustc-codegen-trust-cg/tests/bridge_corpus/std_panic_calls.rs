// CORPUS FIXTURE — panics a bridge-compiled body raises by CALLING a panic
// entry: a formatted `panic!` / `assert!` / `assert_eq!` / `unreachable!`
// (`panic_fmt` with placeholder arguments, `assert_failed`, `panic_display`),
// std's `#[track_caller]` helpers (`Option::unwrap`'s `unwrap_failed`,
// `expect_failed`, `Result`'s `unwrap_failed`), and std bodies the bridge
// compiles that call their own panic helpers (`u32::pow`'s
// `overflow_panic::pow`, `ilog2`'s `panic_for_nonpositive_argument`,
// `copy_within`'s `slice_index_fail`). Each call must reach the real entry
// with its real payload — std's message text and payload TYPE (`String` for
// a formatted message, `&'static str` for a literal) — and its real
// `#[track_caller]` Location.
//
// A formatted message runs its arguments' `Debug` impls, so those bodies are
// compiled: a derived `Debug` borrowing a `&str` field (`Config`), a tuple's
// `&str` element, `Option<Option<u32>>`'s inner `Option`, and `Vec<u32>`
// (through `assert_eq!`'s `assert_failed`, which calls `<Vec<u32> as
// Debug>::fmt` directly). The `z` row runs the same asserts PASSING: a
// program whose assert never fires still compiles its message.
//
// The shape is the first byte of `PANIC_SHAPE` (`z` = no panic); the hook is
// chosen by `PANIC_HOOK` as in `std_panic_intercepted.rs`, plus:
//
//   * `p` — a BRIDGE-compiled hook that itself panics with a FORMATTED message
//     (a panic raised in a bridge-compiled hook): std reports the nested panic
//     and aborts.
use std::hint::black_box;

struct Guard;

impl Drop for Guard {
    fn drop(&mut self) {
        out(b"drop\n");
    }
}

#[inline(never)]
fn panic_formatted(x: u32) -> usize {
    if x > 3 {
        panic!("bad value {} of {}", x, 3);
    }
    x as usize
}

#[inline(never)]
fn panic_display(x: u32) -> usize {
    if x > 3 {
        panic!("{}", x);
    }
    x as usize
}

#[inline(never)]
fn assert_formatted(x: u32) -> usize {
    assert!(x < 3, "x was {x}");
    x as usize
}

#[inline(never)]
fn assert_equal(x: u32) -> usize {
    assert_eq!(x, 3);
    x as usize
}

#[inline(never)]
fn assert_equal_formatted(x: u32) -> usize {
    assert_eq!(x, 3, "context {}", x + 1);
    x as usize
}

#[inline(never)]
fn assert_not_equal(x: u32) -> usize {
    assert_ne!(x, 9);
    x as usize
}

#[inline(never)]
fn unreachable_formatted(x: u32) -> usize {
    if x > 3 {
        unreachable!("x={}", x);
    }
    x as usize
}

#[inline(never)]
fn unreachable_literal(x: u32) -> usize {
    if x > 3 {
        unreachable!();
    }
    x as usize
}

#[inline(never)]
fn option_unwrap(x: Option<u32>) -> usize {
    x.unwrap() as usize
}

#[inline(never)]
fn option_expect(x: Option<u32>) -> usize {
    x.expect("wanted a value") as usize
}

#[inline(never)]
fn result_unwrap(x: Result<u32, i32>) -> usize {
    x.unwrap() as usize
}

#[inline(never)]
fn result_expect(x: Result<u32, i32>) -> usize {
    x.expect("wanted ok") as usize
}

#[inline(never)]
fn pow(base: u32, exp: u32) -> usize {
    base.pow(exp) as usize
}

#[inline(never)]
fn ilog2(x: u32) -> usize {
    x.ilog2() as usize
}

#[inline(never)]
fn copy_within(a: usize, b: usize) -> usize {
    let mut v = [1u32, 2, 3, 4];
    v.copy_within(a..b, 0);
    (v[0] * 1000 + v[1] * 100 + v[2] * 10 + v[3]) as usize
}

#[derive(Debug)]
struct Config {
    port: u32,
    host: &'static str,
}

#[inline(never)]
fn debug_struct_str_field(port: u32) -> usize {
    let c = Config { port, host: "h" };
    assert!(c.port != 0, "bad config: {:?}", c);
    c.port as usize % 7
}

#[inline(never)]
fn debug_tuple_str(x: u32) -> usize {
    if x > 3 {
        panic!("{:?}", (x, "t", 'c'));
    }
    x as usize
}

#[inline(never)]
fn debug_nested_option(x: u32) -> usize {
    if x > 3 {
        panic!("{:?}", Some(Some(x)));
    }
    x as usize
}

#[inline(never)]
fn assert_equal_vec(x: u32) -> usize {
    let v = vec![black_box(1u32), 2];
    assert_eq!(v, vec![1, x]);
    v.len()
}

#[inline(never)]
fn debug_vec(x: u32) -> usize {
    let v = vec![x, 7];
    if x > 3 {
        panic!("{:?}", v);
    }
    v.len()
}

#[inline(never)]
fn shape(selector: u8) -> usize {
    match selector {
        b'a' => panic_formatted(black_box(9)),
        b'b' => panic_display(black_box(9)),
        b'c' => assert_formatted(black_box(9)),
        b'e' => assert_equal(black_box(9)),
        b'f' => assert_equal_formatted(black_box(9)),
        b'g' => assert_not_equal(black_box(9)),
        b'h' => unreachable_formatted(black_box(9)),
        b'i' => unreachable_literal(black_box(9)),
        b'j' => option_unwrap(black_box(None)),
        b'k' => option_expect(black_box(None)),
        b'l' => result_unwrap(black_box(Err(-5))),
        b'm' => result_expect(black_box(Err(-5))),
        b'n' => pow(black_box(7), black_box(40)),
        b'o' => ilog2(black_box(0)),
        b'q' => copy_within(black_box(2), black_box(9)),
        b'r' => debug_struct_str_field(black_box(0)),
        b's' => debug_tuple_str(black_box(9)),
        b't' => debug_nested_option(black_box(9)),
        b'u' => assert_equal_vec(black_box(5)),
        b'v' => debug_vec(black_box(9)),
        // No panic: every shape, in range.
        _ => {
            panic_formatted(black_box(2))
                + panic_display(black_box(1))
                + assert_formatted(black_box(1))
                + assert_equal(black_box(3))
                + assert_equal_formatted(black_box(3))
                + assert_not_equal(black_box(2))
                + unreachable_formatted(black_box(3))
                + unreachable_literal(black_box(0))
                + option_unwrap(black_box(Some(4)))
                + option_expect(black_box(Some(5)))
                + result_unwrap(black_box(Ok(6)))
                + result_expect(black_box(Ok(7)))
                + pow(black_box(3), black_box(4))
                + ilog2(black_box(1024))
                + copy_within(black_box(1), black_box(3))
                + debug_struct_str_field(black_box(80))
                + debug_tuple_str(black_box(2))
                + debug_nested_option(black_box(1))
                + assert_equal_vec(black_box(2))
                + debug_vec(black_box(3))
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
        b'p' => std::panic::set_hook(Box::new(|info| {
            let line = info.location().map_or(0, |l| l.line());
            panic!("the hook saw line {} and panicked", black_box(line));
        })),
        _ => {}
    }
    let x = run(env_byte(c"PANIC_SHAPE"));
    std::process::exit((x % 200) as i32 + 1);
}
