// wasm32 execution-differential corpus: pointer and fat-pointer MEMORY layout.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// On wasm32 a pointer and `usize` are 4 bytes and a `&[T]` / `&str` is the
// 8-byte `{ data@0, len@4 }` pair. These exports read and write pointers and
// fat pointers held in memory: a `&str` / `&[T]` loaded or stored through a
// thin reference, `static` and `static mut` slices, the `split_first` /
// `split_last` tail, thin pointers loaded through a reference (`&&u32`,
// `iter().rev()`, `derive(PartialEq)`, `{:?}`), structs with pointer fields,
// `#[repr(packed)]` fields reached through a reference and over-aligned
// single-scalar locals. Every export takes and returns scalars.

#![no_std]
#![allow(dead_code)]

use core::fmt::Write;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// --- `&str` / `&[T]` loaded through a thin reference -----------------------

static NAMES: [&str; 4] = ["a", "bcd", "efghij", ""];
static SLICES: [&[u8]; 3] = [&[1, 2], &[3], &[4, 5, 6, 7]];
static GREETING: &str = "hello";
static TABLE: &[u16] = &[10, 20, 30, 40, 50];

#[inline(never)]
fn strlen(r: &&str) -> usize {
    r.len()
}

#[inline(never)]
fn id_slice<'a>(r: &&'a [u8]) -> &'a [u8] {
    *r
}

#[no_mangle]
pub extern "C" fn fp_name_len(k: u32) -> u32 {
    let r: &&str = &NAMES[(k % 4) as usize];
    strlen(r) as u32 * 100 + r.len() as u32
}

#[no_mangle]
pub extern "C" fn fp_names_fold(k: u32) -> u32 {
    let mut t = 0u32;
    for s in NAMES.iter() {
        t = t * 10 + s.len() as u32;
    }
    t + k % 7
}

#[no_mangle]
pub extern "C" fn fp_slice_elem(k: u32) -> u32 {
    let s = id_slice(&SLICES[(k % 3) as usize]);
    s.len() as u32 * 100 + s[s.len() - 1] as u32
}

#[no_mangle]
pub extern "C" fn fp_statics(k: u32) -> u32 {
    let i = (k % 5) as usize;
    GREETING.len() as u32 * 1000 + TABLE.len() as u32 * 100 + TABLE[i] as u32
}

#[inline(never)]
fn pick(k: u32) -> &'static str {
    match k % 3 {
        0 => "alpha",
        1 => "beta",
        _ => "",
    }
}

#[inline(never)]
fn str_eq(a: &str, b: &str) -> bool {
    a == b
}

#[inline(never)]
fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    a == b
}

#[no_mangle]
pub extern "C" fn fp_str_eq(a: u32, b: u32) -> u32 {
    let lit = (pick(a) == "alpha") as u32;
    let other = str_eq(pick(a), pick(b)) as u32;
    let x = [1u8, 2, 3];
    let y = [1u8, 2, (a % 4) as u8];
    lit * 100 + other * 10 + bytes_eq(&x, &y) as u32
}

/// A `fmt::Write` sink folding every written byte (and so the length) into one
/// hash word.
struct Hash(u32);

impl Write for Hash {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for &b in s.as_bytes() {
            self.0 = self.0.wrapping_mul(31).wrapping_add(b as u32 + 1);
        }
        Ok(())
    }
}

#[no_mangle]
pub extern "C" fn fp_fmt_str(k: u32) -> u32 {
    let s = if k % 3 == 0 { "hello" } else { "" };
    let mut c = Hash(0);
    let _ = write!(c, "<{}>", s);
    c.0
}

// --- `&str` / `&[T]` stored through a thin reference ------------------------

static DATA6: [u8; 6] = [1, 2, 3, 4, 5, 6];
static DATA3: [u8; 3] = [9, 8, 7];

#[inline(never)]
fn set_slice(r: &mut &'static [u8], which: bool) {
    if which {
        *r = &DATA6;
    } else {
        *r = &DATA3;
    }
}

#[no_mangle]
pub extern "C" fn fp_store_slice(k: u32) -> u32 {
    let mut s: &'static [u8] = &[];
    let mut t: &'static [u8] = &[42];
    set_slice(&mut s, k & 1 != 0);
    set_slice(&mut t, k & 2 != 0);
    s.len() as u32 * 1000 + t.len() as u32 * 10 + s[0] as u32
}

#[inline(never)]
fn set_str(r: &mut &'static str, k: u32) {
    if k % 3 == 0 {
        *r = "hello";
    } else {
        *r = "xy";
    }
}

struct Pair {
    s: &'static str,
    guard: u32,
}

#[no_mangle]
pub extern "C" fn fp_store_str_field(k: u32) -> u32 {
    let mut p = Pair { s: "a", guard: 77 };
    set_str(&mut p.s, k);
    p.s.len() as u32 * 1000 + p.guard
}

static mut MSG: &str = "a";
static mut NEIGHBOUR: u32 = 77;

#[no_mangle]
pub extern "C" fn fp_static_mut_str(k: u32) -> u32 {
    unsafe {
        if k % 2 == 0 {
            MSG = "hello";
        } else {
            MSG = "xy";
        }
        let msg = MSG;
        let neighbour = core::ptr::read(&raw const NEIGHBOUR);
        msg.len() as u32 * 1000 + neighbour
    }
}

// --- `split_first` / `split_last` tails -------------------------------------

#[inline(never)]
fn head_tail(s: &[u16]) -> u32 {
    match s.split_first() {
        Some((h, rest)) => {
            *h as u32 * 1000 + rest.len() as u32 * 10 + rest.first().map_or(0, |v| *v as u32 % 10)
        }
        None => 7,
    }
}

#[inline(never)]
fn tail_head(s: &[u32]) -> u32 {
    match s.split_last() {
        Some((l, rest)) => *l * 1000 + rest.len() as u32 * 10 + rest.last().map_or(0, |v| *v % 10),
        None => 7,
    }
}

#[no_mangle]
pub extern "C" fn fp_split_first(k: u32) -> u32 {
    let data = [1u16, 3, 7, 9];
    head_tail(&data[..(k % 5) as usize])
}

#[no_mangle]
pub extern "C" fn fp_split_last(k: u32) -> u32 {
    let data = [2u32, 4, 6, 8];
    tail_head(&data[(k % 5) as usize..])
}

// --- Thin pointers loaded through a reference -------------------------------

#[inline(never)]
fn deref_u32(r: &&u32) -> u32 {
    **r
}

static COUNTS: [u32; 4] = [1, 2, 3, 4];
static REF_TO: &u32 = &COUNTS[2];

fn triple(x: u32) -> u32 {
    x * 3
}

fn square(x: u32) -> u32 {
    x * x
}

static FNS: [fn(u32) -> u32; 2] = [triple, square];

#[no_mangle]
pub extern "C" fn tp_refref(k: u32) -> u32 {
    let x = k;
    let r = &x;
    deref_u32(&r).wrapping_add(*REF_TO)
}

#[no_mangle]
pub extern "C" fn tp_rev(k: u32) -> u32 {
    let mut acc = 0u32;
    for v in COUNTS[(k % 5) as usize..].iter().rev() {
        acc = acc * 10 + *v;
    }
    acc
}

mod far {
    #[inline(never)]
    pub fn quad(x: u32) -> u32 {
        x.wrapping_mul(4).wrapping_add(1)
    }
}

static FAR: fn(u32) -> u32 = far::quad;

#[no_mangle]
pub extern "C" fn tp_fn_table(k: u32) -> u32 {
    let f = FNS[(k % 2) as usize];
    f(k % 1000).wrapping_add(FAR(k))
}

// Non-capturing closures coerced to `fn` in a static: rustc names each
// closure's `FnOnce::call_once` shim, whose `rust-call` ABI untuples the
// arguments, so the table entry must take exactly the pointer's `fn(u32)`
// parameter list.
static CLOSURES: [fn(u32) -> u32; 2] = [|x| x.wrapping_add(1), |x| x.wrapping_mul(2)];

#[no_mangle]
pub extern "C" fn tp_fn_closure_static(k: u32) -> u32 {
    CLOSURES[(k % 2) as usize](k)
}

#[no_mangle]
pub extern "C" fn tp_fn_promoted(k: u32) -> u32 {
    let table: &[fn(u32) -> u32; 3] = &[triple, far::quad, square];
    table[(k % 3) as usize](k % 1000)
}

#[derive(PartialEq)]
enum Shape {
    Dot(u32),
    Empty,
}

#[inline(never)]
fn shape(a: u32) -> Shape {
    if a & 1 == 0 {
        Shape::Dot(a)
    } else {
        Shape::Empty
    }
}

#[no_mangle]
pub extern "C" fn tp_derive_eq(a: u32, b: u32) -> u32 {
    (shape(a) == shape(b)) as u32
}

#[no_mangle]
pub extern "C" fn tp_debug(k: u32) -> u32 {
    let mut c = Hash(0);
    let r = &k;
    let _ = write!(c, "{:?}", &r);
    c.0
}

// --- Structs with pointer fields --------------------------------------------

#[derive(Clone, Copy)]
struct WithPtr {
    a: u32,
    p: *const u32,
    d: u64,
}

#[inline(never)]
fn mk_with_ptr(x: u32) -> WithPtr {
    WithPtr {
        a: x,
        p: &COUNTS[(x % 4) as usize],
        d: 9,
    }
}

#[inline(never)]
fn bump(w: &mut WithPtr) {
    w.a = w.a.wrapping_add(1);
}

#[inline(never)]
fn with_ptr_hash(w: WithPtr) -> u64 {
    w.a as u64 ^ unsafe { *w.p } as u64 ^ w.d
}

#[no_mangle]
pub extern "C" fn pf_copy(x: u32) -> u64 {
    let mut w = mk_with_ptr(x);
    bump(&mut w);
    with_ptr_hash(w)
}

struct Guard<'a>(&'a mut u32, u8);

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.0 = self.0.wrapping_mul(10).wrapping_add(self.1 as u32);
    }
}

#[no_mangle]
pub extern "C" fn pf_drop_guard(k: u32) -> u32 {
    let mut state = 1u32;
    {
        let g = Guard(&mut state, 4);
        if k & 1 == 1 {
            core::mem::forget(g);
        }
    }
    state
}

// --- `#[repr(packed)]` fields through a reference ---------------------------

#[repr(C, packed)]
#[derive(Clone, Copy)]
struct Packed {
    a: u8,
    b: u32,
}

#[repr(C, packed(2))]
#[derive(Clone, Copy)]
struct Packed2 {
    a: u8,
    b: u32,
    c: u16,
}

#[inline(never)]
fn mk_packed(x: u32) -> Packed {
    Packed { a: 7, b: x }
}

#[inline(never)]
fn packed_b(p: &Packed) -> u32 {
    p.b
}

#[inline(never)]
fn set_packed_b(p: &mut Packed, x: u32) {
    p.b = x;
}

#[inline(never)]
fn packed2_sum(p: &Packed2) -> u32 {
    let b = p.b;
    let c = p.c;
    b.wrapping_mul(3) ^ c as u32
}

#[no_mangle]
pub extern "C" fn pk_read(x: u32) -> u32 {
    packed_b(&mk_packed(x))
}

#[no_mangle]
pub extern "C" fn pk_write(x: u32) -> u32 {
    let mut p = mk_packed(0);
    set_packed_b(&mut p, x);
    let b = p.b;
    b ^ p.a as u32
}

#[inline(never)]
fn mk_packed2(x: u32) -> Packed2 {
    Packed2 {
        a: 3,
        b: x,
        c: (x >> 3) as u16,
    }
}

#[no_mangle]
pub extern "C" fn pk2_read(x: u32) -> u32 {
    packed2_sum(&mk_packed2(x))
}

// --- Over-aligned single-scalar locals --------------------------------------

#[repr(align(64))]
struct A64 {
    a: u64,
}

#[repr(align(32))]
struct A32 {
    a: u64,
}

#[repr(align(16))]
struct A16(u8);

#[inline(never)]
fn addr_mod<T>(x: &T, m: usize) -> usize {
    (x as *const T as usize) % m
}

#[no_mangle]
pub extern "C" fn oa_local(k: u32) -> u32 {
    let x = A64 { a: k as u64 };
    let y = A32 { a: k as u64 };
    let z = A16(k as u8);
    let misaligned = addr_mod(&x, 64) + addr_mod(&y, 32) + addr_mod(&z, 16);
    misaligned as u32 * 1000 + (x.a as u32 & 7) + (y.a as u32 & 7) + z.0 as u32 % 4
}
