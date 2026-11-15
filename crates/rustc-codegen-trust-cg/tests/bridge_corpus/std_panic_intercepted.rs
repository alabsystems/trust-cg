// CORPUS FIXTURE — std calls the bridge INTERCEPTS (replaces with its own
// lowering), each given an argument that violates the call's precondition. The
// failure edge must raise std's OWN panic: the helper std's body calls with the
// offending values (`slice_index_fail`, `Vec`'s `assert_failed`,
// `slice_error_fail`), the MIR bounds check / overflow assertion std's body
// fails, or the `panic!` / `assert!` / `expect` literal std's body raises —
// with std's payload TEXT and TYPE (`&'static str` for a literal, `String` for
// a formatted message) and std's Location: the caller's, when every frame
// between the call and the panic is `#[track_caller]`, else a span inside std
// (`Vec::swap_remove`, `rotate_left`, `extend_from_within`, `drain`, the
// `Sum` / `Product` closures, `str::split_at[_mut]`'s `slice_error_fail`).
//
// The shape is the first byte of `PANIC_SHAPE` (`z` = no panic, a checksum
// exit); the hook is chosen by `PANIC_HOOK`:
//
//   * absent — `panic_observer::install()`, an LLVM-compiled hook (the same
//     rlib in both lanes) that prints the payload's type and text and the
//     Location: the observer, not the code under test;
//   * `b` — a BRIDGE-compiled hook that prints the Location through raw `write`;
//   * `d` — std's DEFAULT hook (message and Location on stderr).
//
// After the hook, `panic=abort` aborts and `panic=unwind` unwinds through
// `run`'s live `Guard` (`drop` on stdout) to `lang_start`'s catch (exit 101).
// Each shape is its own `#[inline(never)]` function, called below `run`, so
// the guard's frame is not the shape's.
//
// `--cfg stride_loop` (the harness passes it at -O0/-O1) iterates the
// `chunks` / `windows` / `chunks_exact` iterators with `for`: the bridge
// intercepts their constructors there. At -O2/-O3 the shapes call `count()`
// instead (the inlined `for` iterator is a named refusal of its own,
// `[TCG-STRIDE-ITER-INLINE]`), and the constructor's `expect` / `assert!` is
// compiled from std's body.
use std::hint::black_box;

struct Guard;

impl Drop for Guard {
    fn drop(&mut self) {
        out(b"drop\n");
    }
}

#[inline(never)]
fn vec_range(a: usize, b: usize) -> usize {
    let v: Vec<u32> = vec![1, 2, 3, 4];
    v[a..b].len()
}

#[inline(never)]
fn vec_range_from(a: usize) -> usize {
    let v: Vec<u32> = vec![1, 2, 3, 4];
    v[a..].len()
}

#[inline(never)]
fn vec_range_to(b: usize) -> usize {
    let v: Vec<u32> = vec![1, 2, 3, 4];
    v[..b].len()
}

#[inline(never)]
fn array_range(a: usize, b: usize) -> usize {
    let v = black_box([1u32, 2, 3, 4, 5]);
    let s = &v[a..b];
    s.len() + s[0] as usize
}

#[inline(never)]
fn str_range(a: usize, b: usize) -> usize {
    let s = black_box("h\u{e9}llo");
    s[a..b].len()
}

#[inline(never)]
fn str_range_from(a: usize) -> usize {
    let s = black_box("hello");
    s[a..].len()
}

#[inline(never)]
fn str_range_to(b: usize) -> usize {
    let s = black_box("h\u{e9}llo");
    s[..b].len()
}

#[inline(never)]
fn split_at(s: &[u32], mid: usize) -> usize {
    let (a, b) = s.split_at(mid);
    a.len() * 10 + b.len()
}

#[inline(never)]
fn split_at_mut(mid: usize) -> usize {
    let mut v = [1u32, 2, 3];
    let (a, b) = v.split_at_mut(mid);
    a.len() * 10 + b.len()
}

/// `str::split_at` fails through `slice_error_fail(self, 0, mid)` past the
/// end and inside a char alike: std's formatted message, at a Location in
/// `core/src/str/mod.rs` (`split_at` is not `#[track_caller]`).
#[inline(never)]
fn str_split_at(s: &str, mid: usize) -> usize {
    let (a, b) = s.split_at(mid);
    a.len() * 10 + b.len()
}

/// `String` through its `Deref` to `str::split_at`.
#[inline(never)]
fn string_split_at(mid: usize) -> usize {
    let s = String::from("h\u{e9}llo");
    let (a, b) = s.split_at(mid);
    a.len() * 10 + b.len()
}

/// `str::split_at_mut` on a `&mut str`: its own `slice_error_fail` site.
#[inline(never)]
fn str_split_at_mut(mid: usize) -> usize {
    let mut s = String::from("h\u{e9}llo");
    let (a, b) = s.as_mut_str().split_at_mut(mid);
    a.make_ascii_uppercase();
    a.len() * 10 + b.len()
}

/// A `#[track_caller]` wrapper does not move std's Location: `split_at`
/// itself is untracked.
#[track_caller]
#[inline(never)]
fn str_split_at_tracked(s: &str, mid: usize) -> usize {
    let (a, b) = s.split_at(mid);
    a.len() * 10 + b.len()
}

#[inline(never)]
fn vec_insert(i: usize) -> usize {
    let mut v: Vec<u32> = vec![1, 2, 3];
    v.insert(i, 9);
    v.len() + v[0] as usize
}

#[inline(never)]
fn vec_remove(i: usize) -> usize {
    let mut v: Vec<u32> = vec![1, 2, 3];
    v.remove(i) as usize + v.len()
}

#[inline(never)]
fn vec_swap_remove(i: usize) -> usize {
    let mut v: Vec<u32> = vec![1, 2, 3];
    v.swap_remove(i) as usize + v.len()
}

#[inline(never)]
fn vec_split_off(at: usize) -> usize {
    let mut v: Vec<u32> = vec![1, 2, 3];
    let w = v.split_off(at);
    w.len() * 10 + v.len()
}

#[inline(never)]
fn vec_extend_from_within(a: usize, b: usize) -> usize {
    let mut v: Vec<u32> = vec![1, 2, 3];
    v.extend_from_within(a..b);
    v.len() + v[v.len() - 1] as usize
}

#[inline(never)]
fn vec_drain_from(a: usize) -> usize {
    let mut v: Vec<u32> = vec![1, 2, 3];
    let mut s = 0usize;
    // A wrapping sum: the drained loop's own overflow assert under
    // `panic=unwind` is a separate, existing refusal (`[TCG-SSA-071]`).
    for x in v.drain(a..) {
        s = s.wrapping_add(x as usize);
    }
    s + v.len()
}

#[inline(never)]
fn slice_swap(a: usize, b: usize) -> usize {
    let mut v = [1u32, 2, 3];
    v.swap(a, b);
    (v[0] * 100 + v[1] * 10 + v[2]) as usize
}

#[inline(never)]
fn rotate_left(mid: usize) -> usize {
    let mut v = [1u32, 2, 3];
    v.rotate_left(mid);
    (v[0] * 100 + v[1] * 10 + v[2]) as usize
}

#[inline(never)]
fn rotate_right(k: usize) -> usize {
    let mut v = [1u32, 2, 3];
    v.rotate_right(k);
    (v[0] * 100 + v[1] * 10 + v[2]) as usize
}

#[cfg(stride_loop)]
#[inline(never)]
fn chunks(s: &[u32], n: usize) -> usize {
    let mut t = 0;
    for c in s.chunks(n) {
        t = t * 10 + c.len();
    }
    t
}

#[cfg(not(stride_loop))]
#[inline(never)]
fn chunks(s: &[u32], n: usize) -> usize {
    s.chunks(n).count()
}

#[cfg(stride_loop)]
#[inline(never)]
fn chunks_exact(s: &[u32], n: usize) -> usize {
    let mut t = 0;
    for c in s.chunks_exact(n) {
        t = t * 10 + c.len();
    }
    t
}

#[cfg(not(stride_loop))]
#[inline(never)]
fn chunks_exact(s: &[u32], n: usize) -> usize {
    s.chunks_exact(n).count()
}

/// `chunks_exact` in range, for the no-panic row. Only the `for` form: the
/// `-O2`/`-O3` `chunks_exact(n).count()` of a non-panicking size returns a
/// wrong count through the bridge on the unmodified base as well (LLVM 1, the
/// bridge an unrelated large value) — an existing defect outside the panic
/// route this fixture checks, recorded rather than folded into the checksum.
#[cfg(stride_loop)]
fn chunks_exact_control(s: &[u32]) -> usize {
    chunks_exact(s, black_box(2))
}

#[cfg(not(stride_loop))]
fn chunks_exact_control(_: &[u32]) -> usize {
    0
}

#[cfg(stride_loop)]
#[inline(never)]
fn windows(s: &[u32], n: usize) -> usize {
    let mut t = 0;
    for w in s.windows(n) {
        t = t * 10 + w.len();
    }
    t
}

#[cfg(not(stride_loop))]
#[inline(never)]
fn windows(s: &[u32], n: usize) -> usize {
    s.windows(n).count()
}

#[inline(never)]
fn sum_u8(s: &[u8]) -> usize {
    s.iter().sum::<u8>() as usize
}

#[inline(never)]
fn product_u8(s: &[u8]) -> usize {
    s.iter().product::<u8>() as usize
}

#[inline(never)]
fn sum_copied_u8(s: &[u8]) -> usize {
    s.iter().copied().sum::<u8>() as usize
}

#[inline(never)]
fn shape(selector: u8) -> usize {
    let words: &[u32] = black_box(&[1, 2, 3][..]);
    match selector {
        b'a' => vec_range(black_box(1), black_box(9)),
        b'b' => vec_range(black_box(3), black_box(2)),
        b'c' => vec_range_from(black_box(6)),
        b'e' => vec_range_to(black_box(7)),
        b'f' => array_range(black_box(2), black_box(8)),
        b'g' => array_range(black_box(4), black_box(1)),
        b'h' => str_range(black_box(1), black_box(9)),
        b'i' => str_range(black_box(0), black_box(2)),
        b'j' => str_range(black_box(4), black_box(1)),
        b'k' => str_range_from(black_box(7)),
        b'l' => str_range_to(black_box(2)),
        b'm' => split_at(words, black_box(5)),
        b'n' => split_at_mut(black_box(4)),
        b'o' => vec_insert(black_box(5)),
        b'p' => vec_remove(black_box(3)),
        b'q' => vec_swap_remove(black_box(4)),
        b'r' => vec_split_off(black_box(4)),
        b's' => vec_extend_from_within(black_box(1), black_box(6)),
        b't' => vec_extend_from_within(black_box(2), black_box(1)),
        b'u' => vec_drain_from(black_box(5)),
        b'v' => slice_swap(black_box(1), black_box(7)),
        b'w' => slice_swap(black_box(8), black_box(7)),
        b'x' => rotate_left(black_box(4)),
        b'y' => rotate_right(black_box(5)),
        b'A' => chunks(words, black_box(0)),
        b'B' => chunks_exact(words, black_box(0)),
        b'C' => windows(words, black_box(0)),
        b'D' => sum_u8(black_box(&[200, 100][..])),
        b'E' => product_u8(black_box(&[20, 100][..])),
        b'F' => sum_copied_u8(black_box(&[250, 3, 9][..])),
        b'G' => str_split_at(black_box("abc"), black_box(4)),
        b'H' => str_split_at(black_box("h\u{e9}llo"), black_box(2)),
        b'I' => string_split_at(black_box(9)),
        b'J' => str_split_at_mut(black_box(2)),
        b'K' => str_split_at_mut(black_box(7)),
        b'L' => str_split_at_tracked(black_box("abc"), black_box(5)),
        // No panic: every shape, in range.
        _ => {
            vec_range(black_box(1), black_box(3))
                + vec_range_from(black_box(2))
                + vec_range_to(black_box(4))
                + array_range(black_box(1), black_box(4))
                + str_range(black_box(0), black_box(3))
                + str_range_from(black_box(2))
                + str_range_to(black_box(3))
                + split_at(words, black_box(1))
                + split_at_mut(black_box(2))
                + vec_insert(black_box(3))
                + vec_remove(black_box(1))
                + vec_swap_remove(black_box(0))
                + vec_split_off(black_box(1))
                + vec_extend_from_within(black_box(1), black_box(3))
                + vec_drain_from(black_box(1))
                + slice_swap(black_box(0), black_box(2))
                + rotate_left(black_box(1))
                + rotate_right(black_box(2))
                + chunks(words, black_box(2))
                + chunks_exact_control(words)
                + windows(words, black_box(2))
                + sum_u8(black_box(&[20, 100][..]))
                + product_u8(black_box(&[2, 100][..]))
                + sum_copied_u8(black_box(&[25, 3, 9][..]))
                + str_split_at(black_box("abc"), black_box(1))
                + string_split_at(black_box(3))
                + str_split_at_mut(black_box(1))
                + str_split_at_tracked(black_box("h\u{e9}llo"), black_box(3))
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
