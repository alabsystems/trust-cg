// Function pointers stored in static data on wasm32.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// A wasm object symbol is typed: a function pointer in data is an undefined
// FUNCTION symbol with a table-index relocation, never a data symbol. Every
// export below stores a function's address in static data — a static table,
// a struct field, an `extern "C"` table, a table in another module, a promoted
// constant of `core` functions, and a `&dyn Debug` vtable whose method lives in
// the precompiled `core` — or takes a function's address with no indirect
// call, which still needs the indirect function table.
#![no_std]
#![allow(dead_code)]

use core::fmt::{self, Write};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

fn dbl(x: u32) -> u32 {
    x.wrapping_mul(2)
}
fn inc(x: u32) -> u32 {
    x.wrapping_add(1)
}
extern "C" fn nine(x: u32) -> u32 {
    x.wrapping_add(9)
}

static TABLE: [fn(u32) -> u32; 2] = [dbl, inc];

struct Handler {
    f: fn(u32) -> u32,
    k: u32,
}
static HANDLER: Handler = Handler { f: inc, k: 5 };

static C_TABLE: [extern "C" fn(u32) -> u32; 1] = [nine];

mod funcs {
    #[inline(never)]
    pub fn triple(x: u32) -> u32 {
        x.wrapping_mul(3)
    }
}
mod ops {
    pub static OPS: [fn(u32) -> u32; 1] = [crate::funcs::triple];
}

#[no_mangle]
pub extern "C" fn fp_table(x: u32, k: u32) -> u32 {
    (TABLE[(k & 1) as usize])(x)
}

#[no_mangle]
pub extern "C" fn fp_struct(x: u32, k: u32) -> u32 {
    (HANDLER.f)(x) ^ HANDLER.k ^ k
}

#[no_mangle]
pub extern "C" fn fp_extern_c(x: u32) -> u32 {
    C_TABLE[0](x)
}

#[no_mangle]
pub extern "C" fn fp_other_module(x: u32) -> u32 {
    (ops::OPS[0])(x)
}

type CharFmt = fn(&char, &mut fmt::Formatter<'_>) -> fmt::Result;

#[inline(never)]
fn char_formatters() -> &'static [CharFmt] {
    &[<char as fmt::Debug>::fmt, <char as fmt::Display>::fmt]
}

#[no_mangle]
pub extern "C" fn fp_core_const(a: i32) -> u32 {
    (char_formatters()[(a & 1) as usize] as usize != 0) as u32
}

struct Len(u32);
impl Write for Len {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0 += s.len() as u32;
        Ok(())
    }
}

struct Wrap(char);
impl fmt::Debug for Wrap {
    // `field(&self.0)` unsizes `&char` to `&dyn Debug`: the vtable's method is
    // `<char as Debug>::fmt`, defined in the precompiled `core`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("").field(&self.0).finish()
    }
}

#[no_mangle]
pub extern "C" fn fp_core_vtable(a: i32) -> u32 {
    let mut n = Len(0);
    let _ = write!(n, "{:?}", Wrap(char::from_u32(a as u32).unwrap_or('?')));
    n.0
}

fn add1(x: u64) -> u64 {
    x.wrapping_add(1)
}

#[inline(never)]
fn is_nonnull(f: fn(u64) -> u64) -> u32 {
    (f as usize != 0) as u32
}

#[no_mangle]
pub extern "C" fn fp_address_only(s: u32) -> u32 {
    is_nonnull(add1).wrapping_add(s)
}
