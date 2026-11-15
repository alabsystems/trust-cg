// wasm32 execution-differential corpus: the rustc bridge's frontend — call
// models keyed on callee identity, `#[track_caller]` ABI, coroutine frames and
// the typing of reference values.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// * `nm_*`: user items that share a NAME (and argument shape) with a std item
//   the bridge models — a free fn `funnel_shl` / `reverse(Ordering)` /
//   `chars(&str)` / `eq(&ControlFlow, ..)` / `black_box`, an extension-trait
//   method `unchecked_funnel_shl` / `then` / `is_gt` / `chars` /
//   `wrapping_add`, a user enum named `ControlFlow` with its own `PartialEq`,
//   an orphan-legal `impl PartialEq<Local> for core::ops::ControlFlow<(), ()>`
//   and a `ControlFlow<Z, ()>` whose payload's `eq` is false. Each runs its own
//   body. The `*_core` exports call the genuine std items the models stand in
//   for (the checked `funnel_shl` panics for `n >= BITS`). `nm_minmax_*`:
//   `Iterator::max`/`min` over `core::cmp::Reverse` and a user `Ord` newtype
//   order by that `Ord`, not by the scalar they wrap.
// * `tc_*`: `#[track_caller]` functions take rustc's hidden trailing
//   `&'static Location` in their ABI: locally defined ones, a dependency this
//   backend builds (`extern/r6-bridge-frontend-dep.rs`) and one LLVM builds on
//   both sides (`extern/r6-bridge-frontend-llvm.rs`), called directly, through
//   `fn` pointers, through `Index`, through a shared `Into::into` instance and
//   through vtables in both directions. `Location::caller()` makes the
//   forwarded location observable.
// * `co_*`: coroutines that capture variables: the upvars are the frame's
//   outer fields, written by the construction and read by the resume body at
//   rustc's layout offsets.
// * `rl_*`: a reference assigned before a loop and read inside it, carried by
//   the loop header as a reference-typed block parameter.
// * `rr_*`: a reference to a reference whose referent is an aggregate or a
//   scalar newtype, the inner reference assigned directly, copied from another
//   reference, bound from a tuple, joined from two branches or reassigned in a
//   loop.
//
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-extern: r6bf_dep r6-bridge-frontend-dep.rs
// wasm32-differential-extern-llvm: r6bf_llvm r6-bridge-frontend-llvm.rs

#![no_std]
#![feature(funnel_shifts, coroutines, coroutine_trait, stmt_expr_attributes)]

use core::cmp::Ordering;
use core::ops::{Coroutine, CoroutineState};
use core::panic::Location;
use core::pin::Pin;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// ---- nm_*: funnel shifts ----

#[inline(never)]
fn funnel_shl(a: u32, b: u32, c: u32) -> u32 {
    a + b + c
}

#[inline(never)]
fn funnel_shr(a: u32, b: u32, c: u32) -> u32 {
    a ^ b ^ c
}

trait Fsh {
    fn unchecked_funnel_shl(self, b: Self, n: u32) -> Self;
}

impl Fsh for u32 {
    #[inline(never)]
    fn unchecked_funnel_shl(self, b: u32, n: u32) -> u32 {
        self.wrapping_sub(b).wrapping_add(n)
    }
}

#[no_mangle]
pub extern "C" fn nm_funnel_free(a: u32, b: u32) -> u32 {
    funnel_shl(a & 0xff, b & 0xff, 2) ^ funnel_shr(a, b, 7)
}

#[no_mangle]
pub extern "C" fn nm_funnel_trait(a: u32, b: u32) -> u32 {
    Fsh::unchecked_funnel_shl(a, b, 5)
}

#[no_mangle]
pub extern "C" fn nm_funnel_core(a: u32, b: u32) -> u32 {
    a.funnel_shl(b, b % 40) ^ a.funnel_shr(b, a % 32)
}

#[no_mangle]
pub extern "C" fn nm_rotate_u128(a: u64, b: u32) -> u64 {
    let x = ((a as u128) << 64) | (a.wrapping_mul(3) as u128);
    let r = x.rotate_left(b % 128);
    (r as u64) ^ ((r >> 64) as u64)
}

// ---- nm_*: Ordering combinators ----

#[inline(never)]
fn reverse(o: Ordering) -> Ordering {
    o
}

#[inline(never)]
fn is_lt(o: Ordering) -> bool {
    o != Ordering::Less
}

trait MyOrd {
    fn then(self, o: Ordering) -> Ordering;
    fn is_gt(self) -> bool;
}

impl MyOrd for Ordering {
    #[inline(never)]
    fn then(self, o: Ordering) -> Ordering {
        o
    }
    #[inline(never)]
    fn is_gt(self) -> bool {
        self == Ordering::Equal
    }
}

#[no_mangle]
pub extern "C" fn nm_ord_free(a: u32, b: u32) -> i32 {
    reverse(a.cmp(&b)) as i32 * 10 + is_lt(b.cmp(&a)) as i32
}

#[no_mangle]
pub extern "C" fn nm_ord_trait(a: u32, b: u32) -> i32 {
    MyOrd::then(a.cmp(&b), b.cmp(&a)) as i32 * 10 + <Ordering as MyOrd>::is_gt(a.cmp(&b)) as i32
}

#[no_mangle]
pub extern "C" fn nm_ord_core(a: u32, b: u32) -> i32 {
    let o = (a % 3).cmp(&(b % 3));
    o.reverse() as i32 * 100
        + o.then((a % 5).cmp(&(b % 5))) as i32 * 10
        + o.is_lt() as i32
        + o.is_ge() as i32 * 2
}

// ---- nm_*: str::chars ----

trait MyChars {
    fn chars(&self) -> core::str::Chars<'_>;
}

impl MyChars for str {
    #[inline(never)]
    fn chars(&self) -> core::str::Chars<'_> {
        "zz".chars()
    }
}

#[inline(never)]
fn chars(s: &str) -> core::str::Chars<'_> {
    s[1..].chars()
}

#[no_mangle]
pub extern "C" fn nm_chars_trait(a: u32) -> u32 {
    let buf = [b'a' + (a % 26) as u8];
    let s = core::str::from_utf8(&buf).unwrap();
    let mut n = 0u32;
    for c in MyChars::chars(s) {
        n = n * 1000 + c as u32;
    }
    n
}

#[no_mangle]
pub extern "C" fn nm_chars_free(a: u32) -> u32 {
    let buf = [b'x', b'a' + (a % 26) as u8];
    let s = core::str::from_utf8(&buf).unwrap();
    let mut n = 0u32;
    for c in chars(s) {
        n = n * 1000 + c as u32;
    }
    n
}

// The genuine `<str>::chars` loop is refused at -Copt-level=2 on every target
// (`Place projection field 0 before aggregate binding`), so it is compared in
// the debug configuration only.
#[cfg(debug_assertions)]
#[no_mangle]
pub extern "C" fn nm_chars_core(a: u32) -> u32 {
    let buf = [b'x', b'a' + (a % 26) as u8];
    let s = core::str::from_utf8(&buf).unwrap();
    let mut n = 0u32;
    for c in s.chars() {
        n = n * 1000 + c as u32;
    }
    n
}

// ---- nm_*: ControlFlow equality ----

mod user_cf {
    pub enum ControlFlow<B, C> {
        Continue(C),
        Break(B),
    }

    impl PartialEq for ControlFlow<(), ()> {
        #[inline(never)]
        fn eq(&self, _other: &Self) -> bool {
            true
        }
    }

    impl ControlFlow<(), ()> {
        #[inline(never)]
        pub fn eq(&self, n: u32) -> bool {
            n % 3 == 0
        }
    }

    #[inline(never)]
    pub fn mk(x: u32) -> ControlFlow<(), ()> {
        if x & 1 == 0 {
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(())
        }
    }
}

#[inline(never)]
fn eq(_a: &user_cf::ControlFlow<(), ()>, _b: &user_cf::ControlFlow<(), ()>) -> bool {
    false
}

#[no_mangle]
pub extern "C" fn nm_cf_user(a: u32, b: u32) -> u32 {
    let (x, y) = (user_cf::mk(a), user_cf::mk(b));
    (PartialEq::eq(&x, &y) as u32)
        + ((x == y) as u32) * 2
        + (eq(&x, &y) as u32) * 4
        + (user_cf::ControlFlow::eq(&x, b) as u32) * 8
}

#[derive(Clone, Copy)]
struct Z;

impl PartialEq for Z {
    #[inline(never)]
    fn eq(&self, _: &Z) -> bool {
        false
    }
}

struct Local {
    k: u32,
}

impl PartialEq<Local> for core::ops::ControlFlow<(), ()> {
    #[inline(never)]
    fn eq(&self, o: &Local) -> bool {
        o.k == 7
    }
}

#[inline(never)]
fn mkz(x: u32) -> core::ops::ControlFlow<Z, ()> {
    if x & 1 == 0 {
        core::ops::ControlFlow::Continue(())
    } else {
        core::ops::ControlFlow::Break(Z)
    }
}

#[inline(never)]
fn mkc(x: u32) -> core::ops::ControlFlow<(), ()> {
    if x & 1 == 0 {
        core::ops::ControlFlow::Continue(())
    } else {
        core::ops::ControlFlow::Break(())
    }
}

#[no_mangle]
pub extern "C" fn nm_cf_core(a: u32, b: u32) -> u32 {
    let l = Local { k: b % 8 };
    ((mkz(a) == mkz(b)) as u32) + ((mkc(a) == l) as u32) * 2 + ((mkc(a) == mkc(b)) as u32) * 4
}

#[no_mangle]
pub extern "C" fn nm_cf_any(a: u32, b: u32) -> u32 {
    let v = [a % 7, b % 7, (a ^ b) % 7, 3];
    (v.iter().any(|&x| x == 0) as u32) + (v.iter().all(|&x| x < 6) as u32) * 2
}

// ---- nm_*: value-identity barrier and wrapping arithmetic on a loop path ----

#[inline(never)]
fn black_box(x: u32) -> u32 {
    x ^ 0x55
}

trait Wr {
    fn wrapping_add(self, o: Self) -> Self;
}

impl Wr for u32 {
    #[inline(never)]
    fn wrapping_add(self, o: u32) -> u32 {
        self.wrapping_sub(o)
    }
}

#[no_mangle]
pub extern "C" fn nm_loop_names(a: u32, b: u32) -> u32 {
    let mut i = 0u32;
    let mut acc = a;
    while i < black_box(3) {
        acc = Wr::wrapping_add(acc, b);
        i += 1;
    }
    acc
}

#[no_mangle]
pub extern "C" fn nm_loop_core(a: u32, b: u32) -> u32 {
    let mut i = 0u32;
    let mut acc = a;
    while i < core::hint::black_box(4) {
        acc = acc.wrapping_add(b);
        i += 1;
    }
    acc
}

// ---- nm_*: Iterator::max / min order items by the item's own `Ord` ----

#[derive(Clone, Copy, PartialEq, Eq)]
struct Desc(u32);

impl PartialOrd for Desc {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for Desc {
    fn cmp(&self, o: &Self) -> Ordering {
        o.0.cmp(&self.0)
    }
}

// At -Copt-level=0 the body of `Iterator::max`/`min` (`max_by(Ord::cmp)`) is
// refused on every target, so these are compared optimized only.
#[cfg(not(debug_assertions))]
#[no_mangle]
pub extern "C" fn nm_minmax_reverse(a: u32, b: u32) -> u32 {
    let hi = (0..(a % 7))
        .map(|x| core::cmp::Reverse(x ^ b))
        .max()
        .map_or(99, |w| w.0);
    let lo = (0..(b % 5))
        .map(|x| core::cmp::Reverse(x.wrapping_mul(a)))
        .min()
        .map_or(77, |w| w.0);
    hi ^ lo.rotate_left(8)
}

#[cfg(not(debug_assertions))]
#[no_mangle]
pub extern "C" fn nm_minmax_user_ord(a: u32, b: u32) -> u32 {
    let hi = [Desc(a), Desc(b), Desc(a ^ b)]
        .iter()
        .copied()
        .max()
        .map_or(0, |w| w.0);
    let lo = [a, b, a.wrapping_add(b)]
        .iter()
        .map(|v| Desc(*v))
        .min()
        .map_or(1, |w| w.0);
    hi ^ lo.rotate_left(16)
}

#[cfg(not(debug_assertions))]
#[no_mangle]
pub extern "C" fn nm_minmax_core(a: u32, b: u32) -> i32 {
    let i = (0..(a % 7))
        .map(|x| (x as i32).wrapping_sub(3).wrapping_mul(b as i32))
        .max()
        .unwrap_or(99);
    let c = (0..(a % 7))
        .map(|x| char::from_u32(0x60 + ((x ^ b) & 31)).unwrap_or('a'))
        .max()
        .map_or(0, |c| c as i32);
    let o = (0..(b % 5))
        .map(|x| x.cmp(&(a % 4)))
        .min()
        .map_or(5, |o| o as i32);
    i ^ (c << 8) ^ (o << 20)
}

// ---- tc_*: #[track_caller] ABI ----

#[track_caller]
#[inline(never)]
fn loc() -> u32 {
    let l = Location::caller();
    l.line() * 1000 + l.column()
}

#[track_caller]
fn loc_fwd() -> u32 {
    loc()
}

#[inline(never)]
fn loc_plain() -> u32 {
    loc()
}

#[no_mangle]
pub extern "C" fn tc_local(x: u32) -> u32 {
    loc() ^ loc_fwd().wrapping_mul(3) ^ loc_plain().wrapping_mul(7) ^ x
}

#[no_mangle]
pub extern "C" fn tc_dep(x: u32) -> u32 {
    r6bf_dep::add_one(x)
        ^ r6bf_dep::here()
        ^ r6bf_dep::nested().wrapping_mul(5)
        ^ r6bf_llvm::add_one(x).wrapping_mul(9)
        ^ r6bf_llvm::nested().wrapping_mul(11)
}

#[no_mangle]
pub extern "C" fn tc_index(x: u32) -> u32 {
    let t = r6bf_dep::Tbl([10, 20, 30, x]);
    let u = r6bf_llvm::Tbl([x, 7, 8, 9]);
    t[x] ^ u[x.wrapping_add(1)].wrapping_mul(3)
}

#[no_mangle]
pub extern "C" fn tc_into(x: u32) -> u64 {
    let a: u64 = (x as u16).into();
    a ^ r6bf_dep::widen(x as u16 ^ 3) ^ r6bf_llvm::widen_l(x as u16 ^ 5)
}

struct Mine(u32);

impl r6bf_llvm::Tc for Mine {
    #[inline(never)]
    fn tc(&self, x: u32) -> u32 {
        self.0.wrapping_add(x) ^ Location::caller().line()
    }
}

impl r6bf_dep::Tc for Mine {
    #[inline(never)]
    fn tc(&self, x: u32) -> u32 {
        self.0.wrapping_sub(x) ^ Location::caller().column()
    }
}

#[no_mangle]
pub extern "C" fn tc_dyn(x: u32) -> u32 {
    let m = Mine(x ^ 0x55);
    let k1 = r6bf_llvm::K(x);
    let k2 = r6bf_dep::K(x ^ 1);
    let d1: &dyn r6bf_llvm::Tc = &k1;
    let d2: &dyn r6bf_dep::Tc = &k2;
    r6bf_llvm::call_dyn_l(&m, x)
        ^ r6bf_dep::call_dyn(&m, x).wrapping_mul(3)
        ^ d1.tc(x).wrapping_mul(5)
        ^ d2.tc(x).wrapping_mul(7)
}

#[no_mangle]
pub extern "C" fn tc_fnptr(x: u32) -> u32 {
    let f: fn(u32) -> u32 = r6bf_dep::add_one;
    let g: fn(u32) -> u32 = r6bf_llvm::add_one;
    let h: fn() -> u32 = loc;
    f(x) ^ g(x ^ 2) ^ h()
}

#[no_mangle]
pub extern "C" fn tc_unwrap(x: u32) -> u32 {
    let o = if x % 5 == 0 { None } else { Some(x) };
    let v = [1u32, 2, 3];
    o.unwrap() ^ v[(x % 4) as usize] ^ v[1..].len() as u32
}

// ---- co_*: coroutines that capture ----

#[no_mangle]
pub extern "C" fn co_gen1(x: u32) -> u32 {
    let mut c = #[coroutine]
    move || {
        yield x;
        x.wrapping_add(1)
    };
    match Pin::new(&mut c).resume(()) {
        CoroutineState::Yielded(v) => v,
        CoroutineState::Complete(v) => v,
    }
}

#[no_mangle]
pub extern "C" fn co_two_upvars(x: u32, y: u32) -> u32 {
    let mut c = #[coroutine]
    move || {
        yield x.wrapping_sub(y.wrapping_mul(3));
        y
    };
    match Pin::new(&mut c).resume(()) {
        CoroutineState::Yielded(v) => v,
        CoroutineState::Complete(v) => v,
    }
}

// Upvars of different alignment: rustc reorders the frame's outer fields.
#[no_mangle]
pub extern "C" fn co_mixed_upvars(x: i32, y: i64) -> i64 {
    let b = x as i8;
    let mut c = #[coroutine]
    move || {
        yield (b as i64).wrapping_add(y);
        x as i64
    };
    match Pin::new(&mut c).resume(()) {
        CoroutineState::Yielded(v) => v,
        CoroutineState::Complete(v) => v,
    }
}

#[inline(never)]
fn first_word<T>(t: &T) -> u32 {
    // SAFETY: every future below has a 4-byte-aligned frame whose first word is
    // its captured `u32` (rustc's layout, the same for both compiles).
    unsafe { *(t as *const T as *const u32) }
}

#[cfg(not(debug_assertions))]
async fn leaf(x: u32) -> u32 {
    x.wrapping_mul(3)
}

#[no_mangle]
pub extern "C" fn co_async_block(x: u32) -> u32 {
    let c = async move { x };
    first_word(&c)
}

// Optimized builds inline the async fn's `{coroutine}(x)` construction into
// the caller; at -Copt-level=0 the call returning the coroutine by value is
// refused on every target, so this is compared optimized only.
#[cfg(not(debug_assertions))]
#[no_mangle]
pub extern "C" fn co_async_fn(x: u32) -> u32 {
    let f = leaf(x ^ 9);
    first_word(&f)
}

// ---- rl_*: a reference carried by a loop header ----

#[inline(never)]
fn rl_elem(g: &[u32; 2], i: usize) -> u32 {
    let x = &g[i];
    let mut s = 0u32;
    let mut c = 0u32;
    while c < 3 {
        s = s.wrapping_add(*x);
        c += 1;
    }
    s
}

#[no_mangle]
pub extern "C" fn rl_array(a: u32) -> u32 {
    let g = [a, a ^ 5];
    rl_elem(&g, (a & 1) as usize)
}

#[inline(never)]
fn rows(g: &[[u8; 5]; 5]) -> u32 {
    let mut s = 0u32;
    let mut r = 0usize;
    'rows: while r < 5 {
        let row = &g[r];
        r += 1;
        for c in 0..5 {
            if row[c] == 3 {
                continue 'rows;
            }
            s += row[c] as u32;
        }
    }
    s
}

#[no_mangle]
pub extern "C" fn rl_rows(a: u32) -> u32 {
    let mut g = [[0u8; 5]; 5];
    for r in 0..5 {
        for c in 0..5 {
            g[r][c] = ((a >> (r + c)) & 7) as u8;
        }
    }
    rows(&g)
}

#[inline(never)]
fn rl_slice_elem(s: &[u32], i: usize) -> u32 {
    let x = &s[i];
    let mut acc = 0u32;
    let mut c = 0u32;
    while c < 4 {
        acc = acc.wrapping_mul(3).wrapping_add(*x);
        c += 1;
    }
    acc
}

#[no_mangle]
pub extern "C" fn rl_slice(a: u32) -> u32 {
    let g = [a, a.rotate_left(7), 3];
    rl_slice_elem(&g, (a % 3) as usize)
}

#[inline(never)]
fn plus_one(x: &u32) -> u32 {
    x.wrapping_add(1)
}

#[inline(never)]
fn rl_joined(g: &[u32; 2], i: usize, k: u32) -> u32 {
    let x = if k > 3 { &g[i] } else { &g[0] };
    let mut s = 0u32;
    let mut c = 0u32;
    while c < 3 {
        s = s.wrapping_add(plus_one(x));
        c += 1;
    }
    s
}

#[no_mangle]
pub extern "C" fn rl_join(a: u32) -> u32 {
    let g = [a & 0xffff, 5];
    rl_joined(&g, (a & 1) as usize, a % 8)
}

// ---- rr_*: a reference to a reference ----

#[inline(never)]
fn deref2(r: &&(u32, u8)) -> u32 {
    r.0.wrapping_add(r.1 as u32)
}

#[no_mangle]
pub extern "C" fn rr_tuple(x: u32) -> u32 {
    let v = (x, (x >> 3) as u8);
    let r = &v;
    deref2(&r)
}

struct Probe(u8);

trait Kind {
    fn kind(&self) -> u32;
}

impl Kind for &Probe {
    #[inline(never)]
    fn kind(&self) -> u32 {
        100 + self.0 as u32
    }
}

#[no_mangle]
pub extern "C" fn rr_newtype(x: u32) -> u32 {
    (&Probe(x as u8)).kind()
}

#[inline(never)]
fn bump2(r: &mut &mut (u32, u16)) {
    r.0 = r.0.wrapping_add(r.1 as u32);
    r.1 ^= 0x5a;
}

#[no_mangle]
pub extern "C" fn rr_mut(x: u32) -> u32 {
    let mut v = (x, x as u16);
    let mut r = &mut v;
    bump2(&mut r);
    v.0 ^ ((v.1 as u32) << 16)
}

#[derive(Clone, Copy)]
struct Byte(u8);

#[inline(never)]
fn deref2_byte(r: &&Byte) -> u32 {
    (**r).0 as u32
}

// The inner reference is a copy of another reference.
#[no_mangle]
pub extern "C" fn rr_copy(x: u32) -> u32 {
    let v = (x, 3u8);
    let r0 = &v;
    let r = r0;
    let rr = &r;
    (**rr).0 ^ (**rr).1 as u32 ^ deref2(rr).rotate_left(5)
}

// The inner reference is bound from a tuple (a reference copy when optimized).
#[no_mangle]
pub extern "C" fn rr_tuple_bind(x: u32) -> u32 {
    let p = Byte(x as u8);
    let (rp, k) = (&p, 3u32);
    deref2_byte(&rp) ^ k
}

// The inner reference is joined from two branches.
#[no_mangle]
pub extern "C" fn rr_cond_newtype(x: u32) -> u32 {
    let a = Byte(x as u8);
    let b = Byte((x >> 8) as u8);
    let r = if x & 1 == 0 { &a } else { &b };
    deref2_byte(&r)
}

// Optimized builds drop `&r` (only the debug info takes it) and then refuse the
// branch-joined aggregate reference on every target, so this is compared at
// -Copt-level=0 only.
#[cfg(debug_assertions)]
#[no_mangle]
pub extern "C" fn rr_cond(x: u32) -> u32 {
    let a = (x, 3u8);
    let b = (x ^ 5, 9u8);
    let r = if x & 1 == 0 { &a } else { &b };
    let rr = &r;
    (**rr).0 ^ (**rr).1 as u32
}

// The inner reference is reassigned inside a loop.
#[no_mangle]
pub extern "C" fn rr_loop_newtype(x: u32) -> u32 {
    let a = Byte(x as u8);
    let b = Byte((x >> 8) as u8);
    let mut r = &a;
    let mut acc = 0u32;
    let mut i = 0;
    while i < 5 {
        acc = acc.wrapping_mul(17).wrapping_add(deref2_byte(&r));
        r = if (x >> i) & 1 == 1 { &b } else { &a };
        i += 1;
    }
    acc
}
