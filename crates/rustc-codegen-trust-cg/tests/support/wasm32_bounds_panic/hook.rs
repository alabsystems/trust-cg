// A canonical bounds check under wasm32 `panic=abort` runs the panic handler.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The `#[panic_handler]` is user code that observes the panic before the
// abort: it records the caller location, whether the message is a static
// string, and an FNV-1a hash and length of the formatted message into
// statics that later exports read back. LLVM calls core's
// `panic_bounds_check(index, len)` on the failure edge; a generic trap would
// skip the handler and leave every static at zero. `drive.mjs` replays one
// call sequence on both modules and compares every observation.
#![no_std]
use core::panic::PanicInfo;

static mut LINE: u32 = 0;
static mut COL: u32 = 0;
static mut MSG: u32 = 0;
static mut HITS: u32 = 0;
static mut HASH: u32 = 0;
static mut LEN: u32 = 0;

// FNV-1a over the formatted panic message: the payload as the handler sees it.
struct Fnv(u32, u32);
impl core::fmt::Write for Fnv {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for b in s.bytes() {
            self.0 = (self.0 ^ b as u32).wrapping_mul(16777619);
            self.1 += 1;
        }
        Ok(())
    }
}

// The handler is user code that observes the panic before the abort.
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    unsafe {
        HITS += 1;
        if let Some(l) = info.location() {
            LINE = l.line();
            COL = l.column();
        }
        // A static message (the cosmetic `panic("index out of bounds")`
        // route) has `as_str() == Some`; core's `panic_bounds_check` formats
        // `index out of bounds: the len is {len} but the index is {index}`.
        let mut h = Fnv(2166136261, 0);
        let _ = core::fmt::write(&mut h, format_args!("{}", info.message()));
        HASH = h.0;
        LEN = h.1;
        MSG = match info.message().as_str() {
            Some(s) => 1000 + s.len() as u32,
            None => 1,
        };
    }
    core::arch::wasm32::unreachable()
}

#[inline(never)]
fn get(a: &[u32; 4], i: usize) -> u32 {
    a[i]
}

#[inline(never)]
fn get_slice(a: &[u32], i: usize) -> u32 {
    a[i]
}

#[no_mangle]
pub extern "C" fn idx(i: u32) -> u32 {
    let a = [10, 20, 30, 40];
    get(&a, i as usize)
}

#[no_mangle]
pub extern "C" fn sidx(n: u32, i: u32) -> u32 {
    let a = [1u32, 2, 3, 4, 5, 6, 7, 8];
    let n = (n as usize) % 9;
    get_slice(&a[..n], i as usize)
}

#[no_mangle]
pub extern "C" fn sum_upto(n: u32) -> u32 {
    let a = [3u32; 16];
    let mut s = 0u32;
    let mut k = 0usize;
    while k < (n as usize) % 40 {
        s = s.wrapping_add(a[k]);
        k += 1;
    }
    s
}

#[no_mangle]
pub extern "C" fn last_line() -> u32 { unsafe { LINE } }
#[no_mangle]
pub extern "C" fn last_col() -> u32 { unsafe { COL } }
#[no_mangle]
pub extern "C" fn last_msg() -> u32 { unsafe { MSG } }
#[no_mangle]
pub extern "C" fn msg_hash() -> u32 { unsafe { HASH } }
#[no_mangle]
pub extern "C" fn msg_len() -> u32 { unsafe { LEN } }
#[no_mangle]
pub extern "C" fn hits() -> u32 { unsafe { HITS } }
