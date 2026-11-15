// CORPUS FIXTURE — every arithmetic / bounds `AssertKind` rustc emits must, when
// it fails, call the exact panic entry rustc's codegen calls (with its payload
// and the caller Location), so the program's panic HOOK runs with rustc's own
// message before the strategy unwinds or aborts — exactly as under LLVM.
//
// The shape is chosen at run time by the first byte of `PANIC_SHAPE` (`z` = no
// panic), the hook by its second byte:
//
//   * absent — a `set_hook` closure that writes `hook` to stdout and exits
//     with a code derived from the reported file / line / column, so a skipped
//     hook (a signal) or a wrong Location (a different code) diverges;
//   * `d` — std's DEFAULT hook, which prints the Location and the panic MESSAGE
//     to stderr; then `panic=abort` aborts (SIGABRT) and `panic=unwind` unwinds
//     (running the live `Guard`'s Drop, which writes `drop` to stdout) to
//     `lang_start`'s catch (exit 101). (`catch_unwind` itself is not lowered by
//     the bridge, so the fixture does not catch.)
//
// The overflow shapes (`f`, `h`..`l`) panic only with `-Coverflow-checks=on`;
// with checks off they wrap and the program exits with a value-derived code.
// The division / remainder overflow and by-zero shapes panic under both.
use std::hint::black_box;

struct Guard(u8);

impl Drop for Guard {
    fn drop(&mut self) {
        // Runs on a normal return, and while UNWINDING from a panic in its
        // frame (never under abort, never when the custom hook exits first).
        let line = [b'd', b'r', b'o', b'p', b'0' + self.0, b'\n'];
        unsafe { write(1, line.as_ptr(), line.len()) };
    }
}

#[inline(never)]
fn array_index(a: [u32; 4], i: usize) -> u64 {
    let _g = Guard(1);
    a[i] as u64
}

#[inline(never)]
fn slice_index(s: &[u32], i: usize) -> u64 {
    let _g = Guard(2);
    s[i] as u64
}

#[inline(never)]
fn vec_index(i: usize) -> u64 {
    let v: Vec<u32> = vec![10, 20, 30];
    v[i] as u64
}

#[inline(never)]
fn nested_index(i: usize, j: usize) -> u64 {
    let m: [[u32; 3]; 2] = black_box([[1, 2, 3], [4, 5, 6]]);
    m[i][j] as u64
}

/// A counted loop whose trip count is one too many: every access but the last
/// is in bounds, so the loop passes must keep the check that fails and report
/// the first failing index.
#[inline(never)]
fn slice_loop(s: &[u32], n: usize) -> u64 {
    let mut acc: u64 = 0;
    for i in 0..n {
        acc = acc.wrapping_mul(31).wrapping_add(s[i] as u64);
    }
    acc
}

/// `while` loops whose header guard and bounds check test the SAME index: the
/// AArch64 bounds-check eliminator folds the check when the guard proves it
/// (`while j < a.len()`, `while k < s.len()`) and must keep it when it does
/// not (`while i < n` with `n` one past the end), where the last trip panics
/// with the first failing index. A fold justified by the wrong bound would read
/// past the end silently instead.
#[inline(never)]
fn while_array(n: usize) -> u64 {
    let a: [u32; 8] = black_box([3, 1, 4, 1, 5, 9, 2, 6]);
    let mut acc: u64 = 0;
    let mut j = 0usize;
    while j < a.len() {
        acc = acc.wrapping_add(a[j] as u64);
        j += 1;
    }
    let mut i = 0usize;
    while i < n {
        acc = acc.wrapping_mul(31).wrapping_add(a[i] as u64);
        i += 1;
    }
    acc
}

#[inline(never)]
fn while_slice(s: &[u32], n: usize) -> u64 {
    let mut acc: u64 = 0;
    let mut k = 0usize;
    while k < s.len() {
        acc = acc.wrapping_add(s[k] as u64);
        k += 1;
    }
    k = 0;
    while k < n {
        acc = acc.wrapping_mul(7).wrapping_add(s[k] as u64);
        k += 1;
    }
    acc
}

/// The saxpy shape over a `[u32; 4096]` (a bound the selector materializes in
/// a register): the first loop's guard `j < 4096` proves its check, which the
/// bounds-check eliminator folds; the second loop's guard `i < n` does not, and
/// at `n = 4097` its last trip must panic at index 4096.
#[inline(never)]
fn while_big_array(n: usize) -> u64 {
    let mut a = [0u32; 4096];
    let mut j = 0usize;
    while j < 4096 {
        a[j] = (j as u32).wrapping_mul(2654435761);
        j += 1;
    }
    let a = black_box(a);
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < n {
        acc = acc.wrapping_mul(31).wrapping_add(a[i] as u64);
        i += 1;
    }
    acc
}

/// A byte index into a 256-entry table is in bounds by the index's own
/// definition (the eliminator's narrow-index proof folds that check); into a
/// 255-entry table it is not, and `b = 255` must panic.
#[inline(never)]
fn byte_tables(bytes: &[u8]) -> u64 {
    let wide: [u32; 256] = black_box([7; 256]);
    let narrow: [u32; 255] = black_box([5; 255]);
    let mut acc: u64 = 0;
    let mut k = 0usize;
    while k < bytes.len() {
        let b = bytes[k];
        acc = acc
            .wrapping_add(wide[b as usize] as u64)
            .wrapping_mul(3)
            .wrapping_add(narrow[b as usize] as u64);
        k += 1;
    }
    acc
}

/// `while k < a.len() { .. b[k] .. }` over two `Vec`s: the guard tests `a`'s
/// length, the check `b`'s, so the guard proves nothing about the check, and
/// with `a` one element longer the last trip must panic.
#[inline(never)]
fn two_vecs(extra: u64) -> u64 {
    let a: Vec<u64> = (0..12 + extra).collect();
    let b: Vec<u64> = (100..112).collect();
    let mut acc: u64 = 0;
    let mut k = 0usize;
    while k < a.len() {
        acc = acc.wrapping_mul(5).wrapping_add(b[k]);
        k += 1;
    }
    acc
}

#[inline(never)]
fn add(x: u32, y: u32) -> u64 {
    (x + y) as u64
}

#[inline(never)]
fn sub(x: u64, y: u64) -> u64 {
    x - y
}

#[inline(never)]
fn mul(x: i32, y: i32) -> u64 {
    (x * y) as u64
}

#[inline(never)]
fn neg(x: i32) -> u64 {
    (-x) as u64
}

#[inline(never)]
fn shl(x: u32, n: u32) -> u64 {
    (x << n) as u64
}

#[inline(never)]
fn shr(x: u64, n: u32) -> u64 {
    x >> n
}

#[inline(never)]
fn div_overflow(x: i32, y: i32) -> u64 {
    (x / y) as u64
}

#[inline(never)]
fn rem_overflow(x: i64, y: i64) -> u64 {
    (x % y) as u64
}

#[inline(never)]
fn div_zero(x: u32, y: u32) -> u64 {
    (x / y) as u64
}

#[inline(never)]
fn rem_zero(x: i16, y: i16) -> u64 {
    (x % y) as u64
}

/// A bounds check inside a `#[track_caller]` function reports its CALLER's
/// Location (the function forwards its own hidden argument).
#[track_caller]
#[inline(never)]
fn tracked_index(s: &[u32], i: usize) -> u64 {
    s[i] as u64
}

/// An ordinary `#[inline]` helper: MIR-inlined into its caller at -O2/-O3, where
/// the assert's Location must still be the helper's own span.
#[inline]
fn inlined_div(x: u64, y: u64) -> u64 {
    x / y
}

#[inline(never)]
fn calls_inlined_div(x: u64, y: u64) -> u64 {
    let _g = Guard(3);
    inlined_div(x, y) + 1
}

/// A frame that cannot unwind: under `panic=unwind` its failed bounds check
/// raises on a `Terminate` edge, so the panic stops here and aborts through
/// `panic_cannot_unwind` after the hook runs.
#[inline(never)]
extern "C" fn nounwind_index(i: usize) -> u64 {
    let a: [u64; 3] = black_box([7, 8, 9]);
    a[i]
}

/// A bounds check inside a closure body.
#[inline(never)]
fn closure_index(s: &[u32], i: usize) -> u64 {
    let f = |k: usize| s[k] as u64 + 1;
    black_box(&f)(i)
}

static DATA: [u32; 12] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];

unsafe extern "C" {
    fn getenv(name: *const std::ffi::c_char) -> *const std::ffi::c_char;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

/// The `PANIC_SHAPE` byte at `at` (0 when absent), read through libc so the
/// selector itself needs nothing beyond a raw byte load.
fn selector(at: usize) -> u8 {
    let value = unsafe { getenv(c"PANIC_SHAPE".as_ptr()) };
    if value.is_null() {
        return 0;
    }
    let first = unsafe { *value as u8 };
    if at == 0 || first == 0 {
        first
    } else {
        unsafe { *value.add(1) as u8 }
    }
}

fn main() {
    if selector(1) != b'd' {
        std::panic::set_hook(Box::new(|info| {
            let l = info.location().expect("a location");
            let code = (l.line() * 7 + l.column() * 3 + l.file().len() as u32) % 251;
            // A fixed marker through raw libc `write`: the row's stdout proves
            // the hook ran, independently of the exit code.
            unsafe { write(1, b"hook\n".as_ptr(), 5) };
            std::process::exit(code as i32);
        }));
    }
    // A static, so `main` holds no value with drop glue: every call below
    // has no cleanup edge of its own.
    let s: &[u32] = black_box(&DATA[..]);
    let x = match selector(0) {
        b'a' => array_index(black_box([1, 2, 3, 4]), black_box(9)),
        b'b' => slice_index(s, black_box(17)),
        b'c' => vec_index(black_box(5)),
        b'e' => nested_index(black_box(1), black_box(3)),
        b'g' => slice_loop(s, black_box(13)),
        b'f' => add(black_box(u32::MAX), black_box(2)),
        b'h' => sub(black_box(0), black_box(1)),
        b'i' => mul(black_box(i32::MAX), black_box(2)),
        b'j' => neg(black_box(i32::MIN)),
        b'k' => shl(black_box(1), black_box(40)),
        b'l' => shr(black_box(1 << 63), black_box(70)),
        b'm' => div_overflow(black_box(i32::MIN), black_box(-1)),
        b'n' => rem_overflow(black_box(i64::MIN), black_box(-1)),
        b'o' => div_zero(black_box(10), black_box(0)),
        b'p' => rem_zero(black_box(-7), black_box(0)),
        b'q' => tracked_index(s, black_box(40)),
        b'r' => calls_inlined_div(black_box(100), black_box(0)),
        b's' => nounwind_index(black_box(3)),
        b'u' => closure_index(s, black_box(12)),
        b'v' => while_array(black_box(9)),
        b'w' => while_slice(s, black_box(13)),
        b'x' => while_big_array(black_box(4097)),
        b'y' => byte_tables(black_box(&[3, 254, 255, 9])),
        b'A' => two_vecs(black_box(1)),
        // No panic: every function above, in range.
        _ => {
            array_index(black_box([1, 2, 3, 4]), black_box(3))
                ^ slice_index(s, black_box(11))
                ^ vec_index(black_box(2))
                ^ nested_index(black_box(1), black_box(2))
                ^ slice_loop(s, black_box(12))
                ^ add(black_box(7), black_box(9))
                ^ sub(black_box(9), black_box(7))
                ^ mul(black_box(-3), black_box(5))
                ^ neg(black_box(12))
                ^ shl(black_box(3), black_box(4))
                ^ shr(black_box(1 << 40), black_box(33))
                ^ div_overflow(black_box(-100), black_box(7))
                ^ rem_overflow(black_box(-100), black_box(7))
                ^ div_zero(black_box(100), black_box(7))
                ^ rem_zero(black_box(-100), black_box(7))
                ^ tracked_index(s, black_box(4))
                ^ calls_inlined_div(black_box(100), black_box(9))
                ^ nounwind_index(black_box(2))
                ^ closure_index(s, black_box(3))
                ^ while_array(black_box(8))
                ^ while_slice(s, black_box(12))
                ^ while_big_array(black_box(4096))
                ^ byte_tables(black_box(&[3, 254, 0, 9]))
                ^ two_vecs(black_box(0))
        }
    };
    std::process::exit((x % 200) as i32 + 1);
}
