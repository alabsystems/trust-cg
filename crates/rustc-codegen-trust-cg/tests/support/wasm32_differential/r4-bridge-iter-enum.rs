// wasm32 execution-differential corpus: the modeled iterator drive's
// evaluation order, fieldless-enum bindings, empty drop glue and closure
// fat-pointer arguments.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Every closure below records its calls into a `Cell` trace (`log` folds each
// argument into an order-sensitive hash), so an export compares the exact
// sequence of closure calls with core's, not only the result.
//
// * `tk_*`: `.take(n)` checks its count BEFORE the inner iterator is pulled
//   (`Take::next` / `Take::try_fold`), so no closure below a Take runs for
//   `take(0)` or after the n-th item, and a borrowed `Take` keeps its exact
//   count after a short-circuiting terminal. `tk_div*` panics exactly when core
//   would evaluate `100 / 0`.
// * `sk_*`: `map(f).skip(k).take(n)` over a `TrustedRandomAccess` source folds
//   through `SpecTake::spec_fold`, which evaluates nothing when nothing is
//   taken (`k >= len` or `n == 0`) and otherwise the skipped prefix then the
//   taken items.
// * `rv_*`: `.rev().count()` runs a map closure back to front (the counting
//   consumer must not drive a reversed chain forwards).
// * `en_*`: a fieldless enum reassigned in a loop (directly, through `&mut`,
//   through a raw pointer, under a labeled `continue`) and matched in and after
//   the loop; `ec_*`: a fieldless enum whose address is stored in a tuple, an
//   `Option` or a closure capture, including `Ordering`'s negative tag.
// * `dg_*`: calls to EMPTY drop glue (`drop_in_place::<u32>`,
//   `assume_init_drop`, `ManuallyDrop::drop`) and the core code that reaches it
//   (`select_unpredictable`, `binary_search*`, `partition_point`).
// * `cs_*`: closures taking `&[T]`, `&mut [T]` and `&str` arguments; `cr_*`:
//   closures returning aggregates of at most four bytes.
//
// Exports under `cfg(debug_assertions)` (the `-Copt-level=0` default) or its
// negation exercise a shape at the levels where this backend admits the
// rest of its chain: the remaining refusals there are adapter bodies outside
// the modeled drive (`advance_by`, `Take::{last,max,min}` at -O0, the
// optimized `try_fold` over `Filter`/`Take<Take>`/`Rev`), not these fixes.
//
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3

#![no_std]
#![allow(dead_code)]

use core::cell::Cell;
use core::cmp::Ordering;
use core::hint::black_box;
use core::mem::{ManuallyDrop, MaybeUninit};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

static V: [u32; 6] = [1, 2, 3, 4, 5, 6];
static W: [u32; 4] = [7, 8, 9, 10];
static Z: [u32; 4] = [4, 2, 0, 5];

/// Fold `x` into the order-sensitive call trace.
#[inline(always)]
fn log(t: &Cell<u32>, x: u32) {
    t.set(t.get().wrapping_mul(31).wrapping_add(x + 1));
}

/// The same trace for a non-capturing closure (a terminal's own closure must
/// be zero-sized for the modeled drive).
static mut TRACE: u32 = 0;

#[inline(always)]
fn slog(x: u32) {
    unsafe { TRACE = TRACE.wrapping_mul(31).wrapping_add(x + 1) }
}

fn take_trace() -> u32 {
    unsafe { core::mem::replace(&mut *core::ptr::addr_of_mut!(TRACE), 0) }
}

// ---- tk_*: Take gates its count before the pull ---------------------------

#[inline(never)]
fn take_map_sum(n: usize, t: &Cell<u32>) -> u32 {
    V.iter()
        .map(|&x| {
            log(t, x);
            x
        })
        .take(n)
        .sum()
}

#[no_mangle]
pub extern "C" fn tk_map_sum(n: u32) -> u32 {
    let t = Cell::new(0);
    let s = take_map_sum((n % 9) as usize, &t);
    t.get() ^ s
}

#[inline(never)]
fn take_div(n: usize) -> u32 {
    Z.iter().map(|&x| 100 / x).take(n).sum()
}

#[no_mangle]
pub extern "C" fn tk_div(n: u32) -> u32 {
    take_div((n % 3) as usize)
}

#[inline(never)]
fn take_div_range(n: usize) -> u32 {
    (0u32..4)
        .map(|i| 100 / Z[i as usize])
        .take(n)
        .fold(7, |a, x| a * 3 + x)
}

#[no_mangle]
pub extern "C" fn tk_div_range(n: u32) -> u32 {
    take_div_range((n % 3) as usize)
}

#[cfg(debug_assertions)]
#[inline(never)]
fn take_filter_count(n: usize, t: &Cell<u32>) -> usize {
    V.iter()
        .filter(|&&x| {
            log(t, x);
            x % 3 == 0
        })
        .take(n)
        .count()
}

#[cfg(debug_assertions)]
#[no_mangle]
pub extern "C" fn tk_filter_count(n: u32) -> u32 {
    let t = Cell::new(0);
    let c = take_filter_count((n % 4) as usize, &t);
    t.get() ^ c as u32
}

#[inline(never)]
fn take_enumerate_fold(n: usize, t: &Cell<u32>) -> u32 {
    V.iter()
        .map(|&x| {
            log(t, x);
            x
        })
        .enumerate()
        .map(|(i, x)| i as u32 * 10 + x)
        .take(n)
        .fold(0, |a, x| a * 7 + x)
}

#[no_mangle]
pub extern "C" fn tk_enumerate_fold(n: u32) -> u32 {
    let t = Cell::new(0);
    let s = take_enumerate_fold((n % 8) as usize, &t);
    t.get() ^ s
}

#[cfg(debug_assertions)]
#[inline(never)]
fn take_rev_sum(n: usize, t: &Cell<u32>) -> u32 {
    V.iter()
        .map(|&x| {
            log(t, x);
            x
        })
        .rev()
        .take(n)
        .sum()
}

#[cfg(debug_assertions)]
#[no_mangle]
pub extern "C" fn tk_rev_sum(n: u32) -> u32 {
    let t = Cell::new(0);
    let s = take_rev_sum((n % 8) as usize, &t);
    t.get() ^ s
}

#[cfg(debug_assertions)]
#[inline(never)]
fn take_take_count(a: usize, b: usize, t: &Cell<u32>) -> usize {
    V.iter()
        .map(|&x| {
            log(t, x);
            x
        })
        .take(a)
        .take(b)
        .count()
}

#[cfg(debug_assertions)]
#[no_mangle]
pub extern "C" fn tk_take_take(a: u32, b: u32) -> u32 {
    let t = Cell::new(0);
    let c = take_take_count((a % 8) as usize, (b % 8) as usize, &t);
    t.get() ^ c as u32
}

#[inline(never)]
fn take_for_each(n: usize, t: &Cell<u32>) {
    V.iter()
        .map(|&x| {
            log(t, x);
            x
        })
        .take(n)
        .for_each(|x| log(t, x * 100));
}

#[no_mangle]
pub extern "C" fn tk_for_each(n: u32) -> u32 {
    let t = Cell::new(0);
    take_for_each((n % 8) as usize, &t);
    t.get()
}

#[cfg(not(debug_assertions))]
#[inline(never)]
fn take_last_max_min(n: usize) -> u32 {
    let last = V
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .take(n)
        .last()
        .unwrap_or(99);
    let max = V
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .take(n)
        .max()
        .unwrap_or(98);
    let min = V
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .take(n)
        .min()
        .unwrap_or(97);
    last * 10000 + max * 100 + min
}

#[cfg(not(debug_assertions))]
#[no_mangle]
pub extern "C" fn tk_last_max_min(n: u32) -> u32 {
    take_trace();
    let s = take_last_max_min((n % 8) as usize);
    take_trace() ^ s
}

#[inline(never)]
fn take_short_circuit(n: usize) -> u32 {
    let any = V
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .take(n)
        .any(|x| x == 4) as u32;
    let all = V
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .take(n)
        .all(|x| x < 4) as u32;
    let find = V
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .take(n)
        .find(|&x| x >= 3)
        .unwrap_or(0);
    let pos = V
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .take(n)
        .position(|x| x == 5)
        .map_or(9, |p| p as u32);
    any * 1000 + all * 100 + find * 10 + pos
}

#[no_mangle]
pub extern "C" fn tk_short_circuit(n: u32) -> u32 {
    take_trace();
    let s = take_short_circuit((n % 8) as usize);
    take_trace() ^ s
}

/// A borrowed `Take` reused after `find` exhausted it: core leaves `n == 0`,
/// so the next `next()` is `None` and the source is not pulled past `n`.
#[inline(never)]
fn take_reuse(n: usize) -> u32 {
    let mut it = V.iter().take(n).map(|&x| x * 10);
    let a = it.find(|&x| x == 999).unwrap_or(7);
    a + it.next().unwrap_or(100)
}

#[no_mangle]
pub extern "C" fn tk_reuse(n: u32) -> u32 {
    take_reuse((n % 8) as usize)
}

// ---- sk_*: a Skip under a Take over a TrustedRandomAccess source ---------

#[inline(never)]
fn skip_take_sum(k: usize, n: usize, t: &Cell<u32>) -> u32 {
    V[..4]
        .iter()
        .map(|&x| {
            log(t, x);
            x
        })
        .skip(k)
        .take(n)
        .sum()
}

#[no_mangle]
pub extern "C" fn sk_sum(k: u32, n: u32) -> u32 {
    let t = Cell::new(0);
    let s = skip_take_sum((k % 7) as usize, (n % 4) as usize, &t);
    t.get() ^ s
}

#[inline(never)]
fn skip_take_div(k: usize, n: usize) -> u32 {
    Z.iter().map(|&x| 100 / x).skip(k).take(n).sum()
}

#[no_mangle]
pub extern "C" fn sk_div(k: u32, n: u32) -> u32 {
    skip_take_div((k % 7) as usize, (n % 3) as usize)
}

#[inline(never)]
fn skip_take_family(k: usize, n: usize) -> u32 {
    let count = V[..4]
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .skip(k)
        .take(n)
        .count() as u32;
    let fold = V[..4]
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .skip(k)
        .take(n)
        .fold(3, |a, x| a * 5 + x);
    let product: u32 = V[..4]
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .skip(k)
        .take(n)
        .product();
    V[..4]
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .skip(k)
        .take(n)
        .for_each(|x| slog(x + 50));
    count ^ fold.wrapping_mul(7) ^ product << 16
}

#[no_mangle]
pub extern "C" fn sk_family(k: u32, n: u32) -> u32 {
    take_trace();
    let s = skip_take_family((k % 7) as usize, (n % 4) as usize);
    take_trace() ^ s
}

/// `last` is core's `fold` too.
#[cfg(not(debug_assertions))]
#[inline(never)]
fn skip_take_last(k: usize, n: usize) -> u32 {
    V[..4]
        .iter()
        .map(|&x| {
            slog(x);
            x
        })
        .skip(k)
        .take(n)
        .last()
        .unwrap_or(9)
}

#[cfg(not(debug_assertions))]
#[no_mangle]
pub extern "C" fn sk_last(k: u32, n: u32) -> u32 {
    take_trace();
    let s = skip_take_last((k % 7) as usize, (n % 4) as usize);
    take_trace() ^ s
}

#[inline(never)]
fn skip_take_range(k: usize, n: usize, t: &Cell<u32>) -> u32 {
    (10u16..14)
        .map(|x| {
            log(t, x as u32);
            x as u32
        })
        .skip(k)
        .take(n)
        .map(|x| x * 2)
        .sum()
}

#[no_mangle]
pub extern "C" fn sk_range(k: u32, n: u32) -> u32 {
    let t = Cell::new(0);
    let s = skip_take_range((k % 7) as usize, (n % 4) as usize, &t);
    t.get() ^ s
}

#[inline(never)]
fn skip_take_nested(k1: usize, k2: usize, n: usize, t: &Cell<u32>) -> u32 {
    V.iter()
        .map(|&x| {
            log(t, x);
            x
        })
        .skip(k1)
        .map(|x| {
            log(t, x + 10);
            x
        })
        .skip(k2)
        .take(n)
        .sum()
}

#[no_mangle]
pub extern "C" fn sk_nested(k: u32, n: u32) -> u32 {
    let t = Cell::new(0);
    let s = skip_take_nested((k % 5) as usize, (k / 5 % 5) as usize, (n % 4) as usize, &t);
    t.get() ^ s
}

#[inline(never)]
fn skip_take_zip(k: usize, n: usize) -> u32 {
    V.iter()
        .zip(W.iter())
        .map(|(&a, &b)| {
            slog(a * b);
            a + b
        })
        .skip(k)
        .take(n)
        .sum()
}

#[no_mangle]
pub extern "C" fn sk_zip(k: u32, n: u32) -> u32 {
    take_trace();
    let s = skip_take_zip((k % 7) as usize, (n % 4) as usize);
    take_trace() ^ s
}

#[inline(never)]
fn skip_take_i8(k: usize, n: usize, lo: i8) -> i32 {
    (lo..lo.wrapping_add(3))
        .map(|x| {
            slog(x as u32);
            x as i32
        })
        .skip(k)
        .take(n)
        .sum()
}

#[no_mangle]
pub extern "C" fn sk_range_i8(k: u32, n: u32) -> i32 {
    take_trace();
    let s = skip_take_i8(
        (k % 5) as usize,
        (n % 4) as usize,
        (k as i8).wrapping_mul(37),
    );
    take_trace() as i32 ^ s
}

#[inline(never)]
fn skip_take_usize(k: usize, n: usize, lo: usize) -> usize {
    (lo..lo + 3)
        .map(|x| {
            slog(x as u32);
            x
        })
        .skip(k)
        .take(n)
        .sum()
}

#[no_mangle]
pub extern "C" fn sk_range_usize(k: u32, n: u32) -> u32 {
    take_trace();
    let s = skip_take_usize((k % 5) as usize, (n % 4) as usize, (k % 100) as usize);
    take_trace() ^ s as u32
}

/// An `Enumerate` and a `Map` above the Skip and a `Filter` above the Take:
/// `Filter::count` / `Map::fold` still reach `Take::fold`.
#[inline(never)]
fn skip_take_enumerate(k: usize, n: usize) -> u32 {
    V.iter()
        .map(|&x| {
            slog(x);
            x
        })
        .enumerate()
        .skip(k)
        .map(|(i, x)| i as u32 * 100 + x)
        .take(n)
        .filter(|x| x % 2 == 0)
        .count() as u32
}

#[no_mangle]
pub extern "C" fn sk_enumerate(k: u32, n: u32) -> u32 {
    take_trace();
    let s = skip_take_enumerate((k % 8) as usize, (n % 4) as usize);
    take_trace() ^ s
}

// ---- rv_*: rev().count() runs the map closure back to front ---------------

#[inline(never)]
fn rev_count(t: &Cell<u32>, m: usize) -> usize {
    V[..m]
        .iter()
        .map(|&x| {
            log(t, x);
            x
        })
        .rev()
        .count()
}

#[no_mangle]
pub extern "C" fn rv_count(m: u32) -> u32 {
    let t = Cell::new(0);
    let c = rev_count(&t, (m % 7) as usize);
    t.get() ^ c as u32
}

// ---- en_*: fieldless enums reassigned in loops ----------------------------

#[derive(Clone, Copy)]
enum S {
    A,
    B,
    C,
}

#[inline(never)]
fn toggle_after_loop(n: u32) -> u32 {
    let mut st = true;
    let mut x = S::C;
    for _ in 0..(n % 4) {
        x = if st { S::A } else { S::B };
        st = !st;
    }
    match x {
        S::A => 1,
        S::B => 2,
        S::C => 3,
    }
}

#[no_mangle]
pub extern "C" fn en_toggle(n: u32) -> u32 {
    toggle_after_loop(n)
}

#[inline(never)]
fn read_in_loop(n: u32) -> u32 {
    let mut x = S::A;
    let mut acc = 0;
    for i in 0..(n % 6) {
        acc = acc * 4
            + match x {
                S::A => 1,
                S::B => 2,
                S::C => 3,
            };
        x = if i % 3 == 0 {
            S::B
        } else if i % 3 == 1 {
            S::C
        } else {
            S::A
        };
    }
    acc
}

#[no_mangle]
pub extern "C" fn en_read_in_loop(n: u32) -> u32 {
    read_in_loop(n)
}

#[inline(never)]
fn adv(s: &mut S) {
    *s = match *s {
        S::A => S::B,
        S::B => S::C,
        S::C => S::A,
    };
}

#[inline(never)]
fn mut_callee_loop(n: u32) -> u32 {
    let mut s = S::B;
    let mut k = 0;
    while k < n % 3 {
        adv(&mut s);
        k += 1;
    }
    if let S::A = s {
        10
    } else if matches!(s, S::B) {
        20
    } else {
        30
    }
}

#[no_mangle]
pub extern "C" fn en_mut_callee(n: u32) -> u32 {
    mut_callee_loop(n)
}

#[inline(never)]
fn adv_raw(p: *mut S) {
    unsafe { adv(&mut *p) }
}

#[inline(never)]
fn raw_escape(n: u32) -> u32 {
    let mut s = S::A;
    let p = &mut s as *mut S;
    adv_raw(p);
    if n & 1 == 1 {
        adv_raw(p);
    }
    match s {
        S::A => 1,
        S::B => 2,
        S::C => 3,
    }
}

#[no_mangle]
pub extern "C" fn en_raw_escape(n: u32) -> u32 {
    raw_escape(n)
}

#[inline(never)]
fn raw_escape_loop(n: u32) -> u32 {
    let mut s = S::C;
    let mut i = 0;
    loop {
        if i >= n % 5 {
            break;
        }
        adv(&mut s);
        i += 1;
    }
    if let S::B = s { 7 } else { 9 }
}

#[no_mangle]
pub extern "C" fn en_raw_escape_loop(n: u32) -> u32 {
    raw_escape_loop(n)
}

#[inline(never)]
fn labeled_continue(n: u32) -> u32 {
    let mut x = S::A;
    let mut hits = 0;
    'outer: for i in 0..(n % 5) {
        for j in 0..3 {
            if j == i % 3 {
                x = if matches!(x, S::A) { S::C } else { S::A };
                continue 'outer;
            }
            if let S::C = x {
                hits += 1;
            }
        }
    }
    hits * 10
        + match x {
            S::A => 1,
            S::B => 2,
            S::C => 3,
        }
}

#[no_mangle]
pub extern "C" fn en_labeled_continue(n: u32) -> u32 {
    labeled_continue(n)
}

// ---- ec_*: fieldless enums with a stored address --------------------------

#[derive(Clone, Copy)]
enum Level {
    Low = 3,
    High = 200,
}

#[inline(never)]
fn look(t: &(&Level, Level)) -> u32 {
    *t.0 as u32 + t.1 as u32 * 3
}

#[inline(never)]
fn level_tuple(n: u32) -> u32 {
    let lv = if n % 2 == 0 { Level::High } else { Level::Low };
    let t = (&lv, lv);
    look(&t)
}

#[no_mangle]
pub extern "C" fn ec_tuple(n: u32) -> u32 {
    level_tuple(n)
}

#[inline(never)]
fn level_const_tuple() -> u32 {
    let lv = Level::High;
    let t = (&lv, lv);
    look(&t)
}

#[no_mangle]
pub extern "C" fn ec_const_tuple() -> u32 {
    level_const_tuple()
}

#[inline(never)]
fn get(o: Option<&Level>) -> u32 {
    o.map_or(1, |l| *l as u32)
}

#[inline(never)]
fn level_option(n: u32) -> u32 {
    let lv = Level::Low;
    let r = get(Some(&lv));
    let lh = Level::High;
    r * 1000 + get(if n % 3 == 0 { None } else { Some(&lh) })
}

#[no_mangle]
pub extern "C" fn ec_option(n: u32) -> u32 {
    level_option(n)
}

#[inline(never)]
fn call_it<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}

#[inline(never)]
fn level_closure(n: u32) -> u32 {
    let lv = Level::High;
    call_it(|x| lv as u32 + x, n % 100)
}

#[no_mangle]
pub extern "C" fn ec_closure(n: u32) -> u32 {
    level_closure(n)
}

#[inline(never)]
fn ordering_closure(a: i32, b: i32) -> u32 {
    let o = Ordering::Less;
    let p = a.cmp(&b);
    call_it(
        |x| (o as i32 + 5) as u32 * 10 + (p as i32 + 1) as u32 + x,
        0,
    )
}

#[no_mangle]
pub extern "C" fn ec_ordering(a: i32, b: i32) -> u32 {
    ordering_closure(a, b)
}

// ---- dg_*: empty drop glue ------------------------------------------------

#[inline(never)]
fn drop_u32(x: u32) -> u32 {
    let mut v = x;
    unsafe { core::ptr::drop_in_place(&mut v as *mut u32) };
    let mut m = MaybeUninit::new(x.wrapping_add(1));
    unsafe { m.assume_init_drop() };
    let mut d = ManuallyDrop::new(x.wrapping_add(2));
    unsafe { ManuallyDrop::drop(&mut d) };
    v
}

#[no_mangle]
pub extern "C" fn dg_drop(x: u32) -> u32 {
    drop_u32(x)
}

#[inline(never)]
fn drop_generic<T>(mut v: T) -> T {
    unsafe { (&mut v as *mut T).drop_in_place() };
    v
}

#[no_mangle]
pub extern "C" fn dg_drop_generic(x: u32) -> u32 {
    drop_generic(x).wrapping_mul(3)
}

#[no_mangle]
pub extern "C" fn dg_select(c: u32, a: u32) -> u32 {
    core::hint::select_unpredictable(c & 1 == 1, a, a ^ 0x55)
}

static SORTED: [u32; 7] = [1, 3, 5, 7, 9, 11, 13];

#[inline(never)]
fn search(a: u32) -> u32 {
    let s = &SORTED[..];
    let r = match s.binary_search(&(a % 16)) {
        Ok(i) => i as u32,
        Err(i) => i as u32 + 100,
    };
    let by = s
        .binary_search_by(|p| p.cmp(&(a % 15)))
        .unwrap_or_else(|e| e + 50) as u32;
    let key = s
        .binary_search_by_key(&(a % 30), |&p| p * 2)
        .map_or(77, |i| i as u32);
    let pp = s.partition_point(|&p| p < a % 14) as u32;
    r * 1_000_000 + by * 10_000 + key * 100 + pp
}

#[no_mangle]
pub extern "C" fn dg_search(a: u32) -> u32 {
    search(a)
}

// ---- cs_*: closures taking fat pointers; cr_*: small returns --------------

#[inline(never)]
fn apply_slice<F: Fn(&[u32]) -> u32>(f: F, n: usize) -> u32 {
    f(&V[..n])
}

#[no_mangle]
pub extern "C" fn cs_slice(n: u32) -> u32 {
    apply_slice(
        |s: &[u32]| s.len() as u32 * 100 + if s.is_empty() { 0 } else { s[s.len() - 1] },
        (n % 7) as usize,
    )
}

#[inline(never)]
fn bump_twice(a: &mut [u32]) -> u32 {
    let bump = |a: &mut [u32], i: usize| {
        if i < a.len() {
            a[i] += 1;
        }
    };
    bump(a, 0);
    bump(a, 2);
    a.iter().sum()
}

#[no_mangle]
pub extern "C" fn cs_mut_slice(x: u32, n: u32) -> u32 {
    let mut a = [x & 0xffff; 8];
    bump_twice(&mut a[..(n % 9) as usize])
}

#[inline(never)]
fn str_closure(n: usize) -> u32 {
    let s = "abracadabra";
    let f =
        |t: &str, k: u32| t.len() as u32 * 10 + k + t.as_bytes().first().map_or(0, |&b| b as u32);
    f(&s[n..], 3) + f(black_box(&s[..n]), 5)
}

#[no_mangle]
pub extern "C" fn cs_str(n: u32) -> u32 {
    str_closure((n % 12) as usize)
}

#[no_mangle]
pub extern "C" fn cr_u8x3(x: i32) -> i32 {
    let f = |x: i32| -> [u8; 3] { [x as u8, 2, (x as u8) >> 1] };
    let r = black_box(f)(x);
    r[0] as i32 + r[1] as i32 * 5 + r[2] as i32 * 7
}

#[no_mangle]
pub extern "C" fn cr_u16x2(x: u32) -> u32 {
    let f = |x: u32| -> [u16; 2] { [x as u16, (x >> 16) as u16 ^ 3] };
    let r = black_box(f)(x);
    r[0] as u32 * 3 + r[1] as u32
}

#[no_mangle]
pub extern "C" fn cr_triple(x: u32) -> u32 {
    let f = |x: u32| -> (u8, u8, u8) { (x as u8, (x >> 8) as u8, 9) };
    let r = black_box(f)(x);
    r.0 as u32 + r.1 as u32 * 300 + r.2 as u32 * 90000
}

#[no_mangle]
pub extern "C" fn cr_result(x: i32) -> i32 {
    let f = |x: i32| -> Result<i16, (u8, bool)> {
        if x % 3 == 0 {
            Err((13, x < 0))
        } else {
            Ok(x as i16)
        }
    };
    match black_box(f)(x) {
        Ok(v) => v as i32,
        Err((a, b)) => a as i32 * 1000 + b as i32,
    }
}
