// CORPUS FIXTURE — a `#![no_std]` executable's OWN `#[panic_handler]` must run
// when its code panics under `panic=abort`, exactly as it does under LLVM. The
// handler is reached only through `core` (`panic` -> `panic_fmt` ->
// `panic_impl`), never by a call in this crate's MIR, so the bridge's
// reachability fixpoint must add that edge itself.
//
// The handler `_exit`s with a code derived from the reported line / column /
// file length, so a handler that never ran (SIGABRT from an inline `abort()`),
// a handler dropped from the link (undefined `rust_begin_unwind`) and a wrong
// Location all differ from the LLVM oracle. The shape is chosen at run time
// (`PANIC_SHAPE=a`..`c`; anything else returns 51 without panicking).
#![no_std]
#![no_main]

use core::hint::black_box;

unsafe extern "C" {
    fn getenv(name: *const core::ffi::c_char) -> *const core::ffi::c_char;
    fn _exit(code: i32) -> !;
}

#[panic_handler]
fn on_panic(info: &core::panic::PanicInfo) -> ! {
    let code = match info.location() {
        Some(l) => (l.line() * 7 + l.column() * 3 + l.file().len() as u32) % 251,
        None => 250,
    };
    unsafe { _exit(code as i32) }
}

/// The precompiled `core` carries unwind tables, so an unoptimized link of its
/// panic path asks for the personality routine even under `panic=abort`; a
/// `no_std` binary supplies one. Never called: nothing here unwinds.
#[no_mangle]
pub extern "C" fn rust_eh_personality() {}

#[inline(never)]
fn option_unwrap() -> u32 {
    let o: Option<u32> = black_box(None);
    o.unwrap()
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
fn divide_by_zero() -> u32 {
    let a: u32 = black_box(10);
    let b: u32 = black_box(0);
    a / b
}

fn shape() -> u8 {
    let value = unsafe { getenv(c"PANIC_SHAPE".as_ptr()) };
    if value.is_null() { 0 } else { unsafe { *value as u8 } }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let x = match shape() {
        b'a' => option_unwrap(),
        b'b' => panic_literal(),
        b'c' => divide_by_zero(),
        _ => 250,
    };
    (x % 200) as i32 + 1
}
