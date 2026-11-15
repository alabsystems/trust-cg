#![no_std]
#![feature(unsized_fn_params)]
// Unsized `[&str]` parameters: the element is itself a wide pointer, and
// AArch64 macOS packs narrow stack arguments where AArch64 Linux gives each an
// eight-byte slot, so the rows put the data/length pair in registers, split
// across x7 and the stack, and behind packed narrow stack arguments.
use unsized_str_types::*;
fn mix(t: &mut Acc, v: u64) {
    t.h = t.h.rotate_left(7) ^ v.wrapping_mul(0x100000001b3);
}
// A mirror of alloc's `String::push_str_slice`.
#[inline(never)]
fn push_str_slice(t: &mut Acc, slice: &[&str]) {
    let mut additional = 0usize;
    for x in slice.iter() {
        additional = additional.saturating_add(x.len());
    }
    t.n = t.n.wrapping_add(additional);
    for new in slice {
        let p = new.as_ptr();
        let mut i = 0;
        while i < new.len() {
            t.h =
                t.h.wrapping_mul(131)
                    .wrapping_add(unsafe { *p.add(i) } as u64);
            i += 1;
        }
        t.h ^= (new.len() as u64).wrapping_mul(0x9e3779b97f4a7c15);
    }
    t.p = slice.as_ptr() as usize;
}
// A mirror of alloc's private `SpecExtendStr` and its `[&str]` impl, whose
// `spec_extend_into` takes `self: [&str]` by value (alloc G5 root 1).
trait SpecExtendStrLike {
    fn spec_extend_into(self, t: &mut Acc);
}
impl SpecExtendStrLike for [&str] {
    #[inline(never)]
    fn spec_extend_into(self, t: &mut Acc) {
        push_str_slice(t, &self);
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn spec_strs(s: [&str], t: &mut Acc) {
    <[&str] as SpecExtendStrLike>::spec_extend_into(s, t)
}
// The callee walks its elements through the view itself. (Iterated, not
// indexed: a runtime-index read `s[i]` of a wide element is refused on this
// target for a reason unrelated to the parameter lane.)
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive_strs0(s: [&str], t: &mut Acc) {
    let mut total = 0usize;
    for p in s.iter() {
        total = total.wrapping_add(p.len());
        let b = p.as_bytes();
        if !b.is_empty() {
            mix(t, b[0] as u64 ^ (b[b.len() - 1] as u64) << 8);
        }
    }
    mix(t, total as u64);
    push_str_slice(t, &s);
}
// Data in x7, length on the stack.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive_strs7(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    s: [&str],
    t: &mut Acc,
) {
    for v in [a, b, c, d, e, f, g] {
        mix(t, v);
    }
    push_str_slice(t, &s);
}
// The whole pair on the stack.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive_strs8(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    h: u64,
    s: [&str],
    t: &mut Acc,
) {
    for v in [a, b, c, d, e, f, g, h] {
        mix(t, v);
    }
    push_str_slice(t, &s);
}
// Seven narrow scalars in x0-x6, data in x7, then the length and two packed
// narrow scalars on the stack before the accumulator.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive_narrow7(
    a: u8,
    b: i16,
    c: u32,
    d: i8,
    e: u16,
    f: i32,
    g: bool,
    s: [&str],
    tail: u8,
    guard: i16,
    t: &mut Acc,
) {
    mix(t, a as u64);
    mix(t, b as i64 as u64);
    mix(t, c as u64);
    mix(t, d as i64 as u64);
    mix(t, e as u64);
    mix(t, f as i64 as u64);
    mix(t, g as u64);
    push_str_slice(t, &s);
    mix(t, tail as u64);
    mix(t, guard as i64 as u64);
}
// Eight narrow scalars fill x0-x7; two more are packed at the bottom of the
// stack, so the data/length pair sits behind them.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive_narrow9(
    a: u8,
    b: i16,
    c: u32,
    d: i8,
    e: u16,
    f: i32,
    g: bool,
    h: u8,
    i: u8,
    j: i16,
    s: [&str],
    tail: u8,
    t: &mut Acc,
) {
    mix(t, a as u64);
    mix(t, b as i64 as u64);
    mix(t, c as u64);
    mix(t, d as i64 as u64);
    mix(t, e as u64);
    mix(t, f as i64 as u64);
    mix(t, g as u64);
    mix(t, h as u64);
    mix(t, i as u64);
    mix(t, j as i64 as u64);
    push_str_slice(t, &s);
    mix(t, tail as u64);
}
unsafe extern "Rust" {
    fn external_strs0(s: [&str], t: &mut Acc);
    fn external_narrow7(
        a: u8,
        b: i16,
        c: u32,
        d: i8,
        e: u16,
        f: i32,
        g: bool,
        s: [&str],
        tail: u8,
        guard: i16,
        t: &mut Acc,
    );
    fn external_narrow9(
        a: u8,
        b: i16,
        c: u32,
        d: i8,
        e: u16,
        f: i32,
        g: bool,
        h: u8,
        i: u8,
        j: i16,
        s: [&str],
        tail: u8,
        t: &mut Acc,
    );
}
// The caller side: forward the caller's own storage to an LLVM-built callee.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn send_strs0(s: [&str], t: &mut Acc) {
    unsafe { external_strs0(s, t) }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn send_narrow7(s: [&str], seed: u64, t: &mut Acc) {
    unsafe {
        external_narrow7(
            seed as u8,
            (seed >> 8) as i16,
            (seed >> 16) as u32 ^ 0x8000_0001,
            (seed as i8).wrapping_neg(),
            (seed as u16).wrapping_mul(40503),
            (seed as i32).wrapping_mul(-7),
            seed & 1 == 1,
            s,
            (seed >> 3) as u8 | 0x80,
            (seed as i16).wrapping_mul(-1237),
            t,
        )
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn send_narrow9(s: [&str], seed: u64, t: &mut Acc) {
    unsafe {
        external_narrow9(
            seed as u8,
            (seed >> 8) as i16,
            (seed >> 16) as u32 ^ 0x8000_0001,
            (seed as i8).wrapping_neg(),
            (seed as u16).wrapping_mul(40503),
            (seed as i32).wrapping_mul(-7),
            seed & 1 == 1,
            (seed >> 5) as u8 ^ 0xa5,
            (seed >> 1) as u8 | 0x81,
            (seed as i16).wrapping_mul(-311),
            s,
            (seed >> 3) as u8 | 0x80,
            t,
        )
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn through_pointer_strs(f: fn([&str], &mut Acc), s: [&str], t: &mut Acc) {
    f(s, t)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn through_virtual_strs(k: &dyn StrSink, s: [&str], seed: u8, t: &mut Acc) {
    k.take(s, seed, t)
}
