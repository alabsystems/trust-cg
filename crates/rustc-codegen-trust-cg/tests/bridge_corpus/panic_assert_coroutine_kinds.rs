// CORPUS FIXTURE — the coroutine state-machine `AssertKind`: resuming a
// finished coroutine (`ResumedAfterReturn(Coroutine)`) must call the exact
// `panic_const_coroutine_resumed` entry rustc's codegen calls, so the hook sees
// rustc's own message and the Location of the coroutine body. Not exercised:
// `ResumedAfterPanic` (reachable only after a CAUGHT panic; the bridge does not
// lower `catch_unwind`) and the `async fn` / `gen fn` variants (the bridge
// refuses `async fn` coroutine types).
//
// `PANIC_SHAPE` works as in `panic_assert_kinds.rs` (`z` = no panic; a second
// byte `d` selects std's default hook).
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::hint::black_box;
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

#[inline(never)]
fn resumed_after_return(again: bool) -> u64 {
    let mut co = #[coroutine]
    || {
        yield 1u64;
        2u64
    };
    let mut total = 0;
    for _ in 0..2 {
        match Pin::new(&mut co).resume(()) {
            CoroutineState::Yielded(v) | CoroutineState::Complete(v) => total += v,
        }
    }
    if again {
        // The coroutine has completed: this resume panics.
        if let CoroutineState::Complete(v) = Pin::new(&mut co).resume(()) {
            total += v;
        }
    }
    total
}

unsafe extern "C" {
    fn getenv(name: *const std::ffi::c_char) -> *const std::ffi::c_char;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

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
            unsafe { write(1, b"hook\n".as_ptr(), 5) };
            std::process::exit(code as i32);
        }));
    }
    let x = match selector(0) {
        b'a' => resumed_after_return(black_box(true)),
        _ => resumed_after_return(black_box(false)),
    };
    std::process::exit((x % 200) as i32 + 1);
}
