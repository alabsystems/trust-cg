// CORPUS FIXTURE — an out-of-bounds `a[i]` / `s[i]` / `v[i]` must run the
// program's panic HOOK with rustc's own message ("index out of bounds: the len
// is L but the index is I") and the caller Location before the process aborts
// or unwinds, exactly as LLVM's call to `core::panicking::panic_bounds_check`
// does. Before the fix the bridge lowered MIR's bounds check to a trapping
// `Inst::Assert` under `panic=abort` (SIGTRAP, the hook never ran), and after
// TrustIR v52 it refused the check outright (`[TCG-ASSERT-PANIC]`). Run by
// `tests/panic_assert_kinds_differential.rs`.
//
// The shape is chosen at run time by the first byte of `PANIC_SHAPE` (`a`..`j`,
// `z` = no panic), the hook by its second byte:
//
//   * absent — a `set_hook` closure that writes `hook` to stdout and exits
//     with a code derived from the reported file / line / column, so a skipped
//     hook (a signal) or a wrong Location (a different code) diverges from the
//     LLVM oracle;
//   * `d` — std's DEFAULT hook, which prints `thread 'main' panicked at
//     <file>:<line>:<col>:` and the panic MESSAGE to stderr before the abort
//     (SIGABRT) or the unwind to `lang_start`'s catch (exit 101), so a wrong
//     message (different stderr) or a trap instead of the panic diverges too.
//     The default hook is std's own precompiled code: the program never
//     formats the message itself.
//
// Rows `f`..`h` panic in the LAST trip of an otherwise in-bounds counted loop,
// so the loop passes (bounds-check elimination, unrolling, vectorization) must
// keep the check that fails and report the first failing index; row `z` runs
// the same loops in bounds.
use std::hint::black_box;

#[inline(never)]
fn array_index() -> u32 {
    let a: [u32; 4] = black_box([1, 2, 3, 4]);
    let i: usize = black_box(9);
    a[i]
}

#[inline(never)]
fn slice_index() -> u32 {
    let a: [u32; 6] = black_box([1, 2, 3, 4, 5, 6]);
    let s: &[u32] = black_box(&a[..]);
    let i: usize = black_box(17);
    s[i]
}

#[inline(never)]
fn vec_index() -> u32 {
    let v: Vec<u32> = vec![10, 20, 30];
    let i: usize = black_box(5);
    v[i]
}

// Rows `i` and `j`: the intercepted `Vec` index inside an `extern "C"` body,
// whose panic has a TERMINATE edge under `panic=unwind`: the hook still runs
// with rustc's message, then "panic in a function that cannot unwind" aborts.
#[inline(never)]
extern "C" fn vec_at(v: &Vec<u32>, i: usize) -> u32 {
    v[i]
}

#[inline(never)]
extern "C" fn vec_set(v: &mut Vec<u32>, i: usize, x: u32) {
    v[i] = x;
}

#[inline(never)]
fn array_store() -> u32 {
    let mut a: [u32; 4] = black_box([1, 2, 3, 4]);
    let i: usize = black_box(4);
    a[i] = 7;
    a[0]
}

#[inline(never)]
fn nested_index() -> u32 {
    let m: [[u32; 3]; 2] = black_box([[1, 2, 3], [4, 5, 6]]);
    let i: usize = black_box(1);
    let j: usize = black_box(3);
    m[i][j]
}

/// A counted loop over a constant-length array whose trip count is one too
/// many: every access but the last is in bounds.
#[inline(never)]
fn array_loop(n: usize) -> u32 {
    let a: [u32; 8] = black_box([3, 1, 4, 1, 5, 9, 2, 6]);
    let mut acc: u32 = 0;
    for i in 0..n {
        acc = acc.wrapping_mul(31).wrapping_add(a[i]);
    }
    acc
}

/// The same over a runtime-length slice.
#[inline(never)]
fn slice_loop(s: &[u32], n: usize) -> u32 {
    let mut acc: u32 = 0;
    for i in 0..n {
        acc = acc.wrapping_mul(31).wrapping_add(s[i]);
    }
    acc
}

/// The same over a `Vec`, with a store into a second `Vec`.
#[inline(never)]
fn vec_loop(v: &Vec<u32>, out: &mut Vec<u32>, n: usize) -> u32 {
    let mut acc: u32 = 0;
    for i in 0..n {
        out[i] = v[i].wrapping_add(1);
        acc = acc.wrapping_add(out[i]);
    }
    acc
}

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
    let data: Vec<u32> = (1..=12).collect();
    let mut out: Vec<u32> = vec![0; 12];
    let x = match selector(0) {
        b'a' => array_index(),
        b'b' => slice_index(),
        b'c' => vec_index(),
        b'd' => array_store(),
        b'e' => nested_index(),
        b'f' => array_loop(black_box(9)),
        b'g' => slice_loop(&data, black_box(13)),
        b'h' => vec_loop(&data, &mut out, black_box(13)),
        b'i' => {
            let v = vec![1u32, 2, 3];
            vec_at(&v, black_box(3))
        }
        b'j' => {
            let mut v = vec![1u32, 2, 3];
            vec_set(&mut v, black_box(4), 7);
            v[0]
        }
        // No panic: the same loops, in bounds.
        _ => {
            array_loop(black_box(8))
                ^ slice_loop(&data, black_box(12))
                ^ vec_loop(&data, &mut out, black_box(12))
        }
    };
    std::process::exit((x % 200) as i32 + 1);
}
