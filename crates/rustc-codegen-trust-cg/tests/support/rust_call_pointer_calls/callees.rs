// Library of `extern "rust-call"` callees whose argument tuple does NOT place
// like one by-value aggregate (rustc passes `[f32; 4]` as a pointer to a copy,
// and a float pair in floating-point registers), or whose element rustc
// EXTENDS (a `bool` is `zeroext`, and LLVM's AArch64 callee tests all 32 bits
// of its register), and of closure-body addresses. Built by each backend: every
// `rust-call` callable is declared with its tuple's elements, as rustc's
// `FnAbi` lists them, so the bridge's definitions and calls of them agree with
// LLVM's.
#![feature(unboxed_closures, fn_traits)]
#![allow(improper_ctypes_definitions)]

#[inline]
pub fn mx(h: u64, v: u64) -> u64 {
    (h ^ v).wrapping_mul(0x100000001b3).rotate_left(5)
}

pub type Repro = extern "rust-call" fn((u64, [f32; 4], u8)) -> u64;

#[inline(never)]
pub extern "rust-call" fn repro(a: (u64, [f32; 4], u8)) -> u64 {
    mx(mx(a.0, a.1[3].to_bits() as u64), a.2 as u64)
}

#[inline(never)]
pub fn get_repro() -> Repro {
    repro
}

#[inline(never)]
pub extern "rust-call" fn float_pair(a: (f64, f64)) -> u64 {
    mx(a.0.to_bits(), a.1.to_bits())
}

#[inline(never)]
pub fn get_float_pair() -> extern "rust-call" fn((f64, f64)) -> u64 {
    float_pair
}

pub trait RcTr {
    extern "rust-call" fn m(&self, a: (u64, [f32; 4], u8)) -> u64;
}

pub struct S(pub u64);

impl RcTr for S {
    #[inline(never)]
    extern "rust-call" fn m(&self, a: (u64, [f32; 4], u8)) -> u64 {
        mx(repro(a), self.0)
    }
}

#[inline(never)]
pub fn make_tr(s: u64) -> Box<dyn RcTr> {
    Box::new(S(s))
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "rust-call" fn tcg_rust_call_foreign(a: (u64, [f32; 4], u8)) -> u64 {
    repro(a)
}

/// `(bool, u64)`: the bridge's lanes carry the elements, but rustc
/// zero-extends the `bool`. Measured while the bridge passed the tuple whole
/// (2026-10-02): a bridge binary counted every `false` whose tuple padding was
/// nonzero as `true`, through the pointer and through a direct call of the item.
#[inline(never)]
pub extern "rust-call" fn flag(a: (bool, u64)) -> u64 {
    if a.0 { a.1 } else { 0 }
}

#[inline(never)]
pub fn get_flag() -> extern "rust-call" fn((bool, u64)) -> u64 {
    flag
}

/// The address of a closure type's own `FnOnce::call_once`: for a `FnOnce`
/// closure, its BODY, whose 8-byte environment rustc passes in a register.
/// Measured while the bridge declared every environment as a pointer
/// (2026-10-02): SIGSEGV against 2123.
#[inline(never)]
pub fn reify_once<F: FnOnce(u64) -> u64>(_: &F) -> extern "rust-call" fn(F, (u64,)) -> u64 {
    <F as FnOnce<(u64,)>>::call_once
}

#[inline(never)]
pub fn once_closure(s: u64) -> impl FnOnce(u64) -> u64 + Copy {
    move |x| x * 3 + s
}

/// A `Fn` closure body whose `&str` is argument 7, after the environment
/// pointer and six `u64`: rustc passes it as a `Pair`, in `x7` and on the
/// stack. Measured while the bridge declared a closure body's pair as one
/// whole slot, which goes wholly on the stack (2026-10-02, at `65fc9aaf3`):
/// the address, made in a bridge binary through an inline `const` block or a
/// static and called here, crashed (SIGSEGV) at O0-O3; a runtime reification
/// did the same with its own check disabled.
pub type PairArgs = (u64, u64, u64, u64, u64, u64, &'static str);

type PairPointer = for<'a> extern "rust-call" fn(&'a u64, PairArgs) -> u64;

#[inline]
pub fn pair_value(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, t: &str, s: u64) -> u64 {
    mx(mx(a + b + c + d + e + f, t.len() as u64 * 256 + u64::from(t.as_bytes()[0])), s)
}

/// The address of a `Fn` closure's own body, reified at run time.
#[inline(never)]
pub fn reify_pair<F: Fn(u64, u64, u64, u64, u64, u64, &'static str) -> u64>(_: &F) -> *const () {
    (<F as Fn<PairArgs>>::call as for<'a> extern "rust-call" fn(&'a F, PairArgs) -> u64)
        as *const ()
}

/// The same address, read out of an inline `const` block.
#[inline(never)]
pub fn const_pair<F: Fn(u64, u64, u64, u64, u64, u64, &'static str) -> u64 + 'static>(
    _: &F,
) -> *const () {
    let r: &'static for<'a> extern "rust-call" fn(&'a F, PairArgs) -> u64 = const {
        &(<F as Fn<PairArgs>>::call as for<'a> extern "rust-call" fn(&'a F, PairArgs) -> u64)
    };
    *std::hint::black_box(r) as *const ()
}

/// The same address as a `const fn` result, for a static's initializer.
pub const fn pair_body<F: Fn(u64, u64, u64, u64, u64, u64, &'static str) -> u64>(
    _: &F,
) -> for<'a> extern "rust-call" fn(&'a F, PairArgs) -> u64 {
    <F as Fn<PairArgs>>::call
}

/// A static's copy of such an address.
pub struct Erased(pub *const ());

unsafe impl Sync for Erased {}

/// Calls such an address for a closure whose environment is at most one `u64`.
#[inline(never)]
pub fn call_pair(p: *const (), env: &u64, k: u64) -> u64 {
    let p: PairPointer = unsafe { std::mem::transmute(p) };
    p(env, (k, 2, 3, 4, 5, 6, std::hint::black_box("hello, world")))
}

/// A `Fn` closure body whose `&str` comes after a `u128` and three `u64`:
/// AAPCS64 starts a `u128` at an EVEN register, so with the environment in x0
/// it skips x1 and takes x2:x3, the `u64` take x4-x6, and rustc passes the
/// `&str` in x7 and on the stack. Measured while the bridge declared a closure
/// body's pair as one whole slot (2026-10-02, at `fd6f7475f`): the address,
/// reified in a bridge binary and called here, crashed (SIGSEGV) or panicked
/// at O0-O3.
pub type WideArgs = (u128, u64, u64, u64, &'static str);

#[inline]
pub fn wide_value(w: u128, a: u64, b: u64, c: u64, t: &str, s: u64) -> u64 {
    let text = t.len() as u64 * 256 + u64::from(t.as_bytes()[0]);
    mx(mx(mx(w as u64, (w >> 64) as u64), a + 3 * b + 5 * c), mx(text, s))
}

#[inline(never)]
pub fn reify_wide<F: Fn(u128, u64, u64, u64, &'static str) -> u64>(_: &F) -> *const () {
    (<F as Fn<WideArgs>>::call as for<'a> extern "rust-call" fn(&'a F, WideArgs) -> u64)
        as *const ()
}

#[inline(never)]
pub fn call_wide(p: *const (), env: &u64, k: u64) -> u64 {
    let p: for<'a> extern "rust-call" fn(&'a u64, WideArgs) -> u64 =
        unsafe { std::mem::transmute(p) };
    p(env, ((u128::from(k) << 64) | 3, 4, 5, 6, std::hint::black_box("hello, world")))
}

/// The same body with two `u64`: the `&str` takes x6:x7 in every register
/// state.
pub type FitArgs = (u128, u64, u64, &'static str);

#[inline]
pub fn fit_value(w: u128, a: u64, b: u64, t: &str, s: u64) -> u64 {
    let text = t.len() as u64 * 256 + u64::from(t.as_bytes()[0]);
    mx(mx(mx(w as u64, (w >> 64) as u64), a + 3 * b), mx(text, s))
}

#[inline(never)]
pub fn reify_fit<F: Fn(u128, u64, u64, &'static str) -> u64>(_: &F) -> *const () {
    (<F as Fn<FitArgs>>::call as for<'a> extern "rust-call" fn(&'a F, FitArgs) -> u64)
        as *const ()
}

#[inline(never)]
pub fn call_fit(p: *const (), env: &u64, k: u64) -> u64 {
    let p: for<'a> extern "rust-call" fn(&'a u64, FitArgs) -> u64 =
        unsafe { std::mem::transmute(p) };
    p(env, ((u128::from(k) << 64) | 3, 4, 5, std::hint::black_box("hello, world")))
}
