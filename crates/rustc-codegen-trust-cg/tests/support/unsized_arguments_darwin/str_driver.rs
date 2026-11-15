#![feature(unsized_fn_params)]
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicIsize, Ordering};
use unsized_str_types::*;
static LIVE: AtomicIsize = AtomicIsize::new(0);
struct Count;
unsafe impl GlobalAlloc for Count {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(l) };
        if !p.is_null() {
            LIVE.fetch_add(1, Ordering::SeqCst);
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        LIVE.fetch_sub(1, Ordering::SeqCst);
        unsafe { System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        unsafe { System.realloc(p, l, n) }
    }
}
#[global_allocator]
static ALLOC: Count = Count;
fn mix(t: &mut Acc, v: u64) {
    t.h = t.h.rotate_left(7) ^ v.wrapping_mul(0x100000001b3);
}
fn reference(t: &mut Acc, slice: &[&str]) {
    let additional = slice.iter().fold(0usize, |a, x| a.saturating_add(x.len()));
    t.n = t.n.wrapping_add(additional);
    for s in slice {
        for b in s.bytes() {
            t.h = t.h.wrapping_mul(131).wrapping_add(b as u64);
        }
        t.h ^= (s.len() as u64).wrapping_mul(0x9e3779b97f4a7c15);
    }
    t.p = slice.as_ptr() as usize;
}
unsafe extern "Rust" {
    fn spec_strs(s: [&str], t: &mut Acc);
    fn receive_strs0(s: [&str], t: &mut Acc);
    fn receive_strs7(
        a: u64,
        b: u64,
        c: u64,
        d: u64,
        e: u64,
        f: u64,
        g: u64,
        s: [&str],
        t: &mut Acc,
    );
    fn receive_strs8(
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
    );
    fn receive_narrow7(
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
    fn receive_narrow9(
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
    fn send_strs0(s: [&str], t: &mut Acc);
    fn send_narrow7(s: [&str], seed: u64, t: &mut Acc);
    fn send_narrow9(s: [&str], seed: u64, t: &mut Acc);
    fn through_pointer_strs(f: fn([&str], &mut Acc), s: [&str], t: &mut Acc);
    fn through_virtual_strs(k: &dyn StrSink, s: [&str], seed: u8, t: &mut Acc);
}
#[unsafe(no_mangle)]
pub fn external_strs0(s: [&str], t: &mut Acc) {
    t.h ^= 0x5555_aaaa_5555_aaaa;
    reference(t, &s);
}
#[unsafe(no_mangle)]
pub fn external_narrow7(
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
    narrow7_prefix(t, a, b, c, d, e, f, g);
    reference(t, &s);
    mix(t, tail as u64);
    mix(t, guard as i64 as u64);
}
#[unsafe(no_mangle)]
pub fn external_narrow9(
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
    narrow7_prefix(t, a, b, c, d, e, f, g);
    mix(t, h as u64);
    mix(t, i as u64);
    mix(t, j as i64 as u64);
    reference(t, &s);
    mix(t, tail as u64);
}
fn narrow7_prefix(t: &mut Acc, a: u8, b: i16, c: u32, d: i8, e: u16, f: i32, g: bool) {
    mix(t, a as u64);
    mix(t, b as i64 as u64);
    mix(t, c as u64);
    mix(t, d as i64 as u64);
    mix(t, e as u64);
    mix(t, f as i64 as u64);
    mix(t, g as u64);
}
// The narrow arguments `send_narrow7`/`send_narrow9` derive from `seed`; the
// receive rows pass the same values from this side.
struct Narrow {
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
    tail: u8,
    guard: i16,
}
fn narrow(seed: u64) -> Narrow {
    Narrow {
        a: seed as u8,
        b: (seed >> 8) as i16,
        c: (seed >> 16) as u32 ^ 0x8000_0001,
        d: (seed as i8).wrapping_neg(),
        e: (seed as u16).wrapping_mul(40503),
        f: (seed as i32).wrapping_mul(-7),
        g: seed & 1 == 1,
        h: (seed >> 5) as u8 ^ 0xa5,
        i: (seed >> 1) as u8 | 0x81,
        j: (seed as i16).wrapping_mul(-311),
        tail: (seed >> 3) as u8 | 0x80,
        guard: (seed as i16).wrapping_mul(-1237),
    }
}
fn pointer_a(s: [&str], t: &mut Acc) {
    t.h ^= 0xa;
    reference(t, &s);
}
fn pointer_b(s: [&str], t: &mut Acc) {
    t.h ^= 0xb0b0;
    reference(t, &s);
}
struct Sinker(u64);
impl StrSink for Sinker {
    fn take(&self, s: [&str], seed: u8, t: &mut Acc) {
        mix(t, self.0);
        mix(t, seed as u64);
        reference(t, &s);
    }
}
fn main() {
    let text = "alpha\u{e9}beta gamma\u{1F600}delta \u{20ac}psilon zeta eta theta iota kappa \u{3bb}ambda mu";
    let mut checks = 0u64;
    for seed in 0..48u64 {
        let seed = seed.wrapping_mul(0x9e3779b97f4a7c15) ^ seed;
        for len in 0..=12usize {
            let mut pieces: Vec<&str> = Vec::new();
            let mut x = seed.wrapping_add(len as u64);
            for _ in 0..len {
                x = x
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                let mut a = (x >> 33) as usize % text.len();
                while !text.is_char_boundary(a) {
                    a -= 1;
                }
                let mut b = (a + (x >> 13) as usize % 11).min(text.len());
                while !text.is_char_boundary(b) {
                    b -= 1;
                }
                pieces.push(&text[a..b]);
            }
            for off in 0..=len.min(2) {
                let s = &pieces[off..];
                let n = narrow(seed);
                let before = LIVE.load(Ordering::SeqCst);
                let boxed = || -> Box<[&str]> { s.into() };
                {
                    let b = boxed();
                    let mut want = Acc::new(seed);
                    reference(&mut want, &b);
                    let mut got = Acc::new(seed);
                    unsafe { spec_strs(*b, &mut got) };
                    assert_eq!(got, want, "spec_strs");
                    checks += 1;
                }
                {
                    let b = boxed();
                    let mut want = Acc::new(seed);
                    let mut total = 0usize;
                    for p in b.iter() {
                        total = total.wrapping_add(p.len());
                        let bytes = p.as_bytes();
                        if !bytes.is_empty() {
                            mix(
                                &mut want,
                                bytes[0] as u64 ^ (bytes[bytes.len() - 1] as u64) << 8,
                            );
                        }
                    }
                    mix(&mut want, total as u64);
                    reference(&mut want, &b);
                    let mut got = Acc::new(seed);
                    unsafe { receive_strs0(*b, &mut got) };
                    assert_eq!(got, want, "receive_strs0");
                    checks += 1;
                }
                {
                    let w: [u64; 8] =
                        core::array::from_fn(|i| seed.rotate_left(i as u32 * 9) ^ i as u64);
                    let b = boxed();
                    let mut want = Acc::new(seed);
                    for v in &w[..7] {
                        mix(&mut want, *v);
                    }
                    reference(&mut want, &b);
                    let mut got = Acc::new(seed);
                    unsafe {
                        receive_strs7(w[0], w[1], w[2], w[3], w[4], w[5], w[6], *b, &mut got)
                    };
                    assert_eq!(got, want, "receive_strs7");
                    checks += 1;
                    let b = boxed();
                    let mut want = Acc::new(seed);
                    for v in &w {
                        mix(&mut want, *v);
                    }
                    reference(&mut want, &b);
                    let mut got = Acc::new(seed);
                    unsafe {
                        receive_strs8(w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], *b, &mut got)
                    };
                    assert_eq!(got, want, "receive_strs8");
                    checks += 1;
                }
                {
                    let b = boxed();
                    let mut want = Acc::new(seed);
                    narrow7_prefix(&mut want, n.a, n.b, n.c, n.d, n.e, n.f, n.g);
                    reference(&mut want, &b);
                    mix(&mut want, n.tail as u64);
                    mix(&mut want, n.guard as i64 as u64);
                    let mut got = Acc::new(seed);
                    unsafe {
                        receive_narrow7(
                            n.a, n.b, n.c, n.d, n.e, n.f, n.g, *b, n.tail, n.guard, &mut got,
                        )
                    };
                    assert_eq!(got, want, "receive_narrow7");
                    checks += 1;
                    let b = boxed();
                    let mut want = Acc::new(seed);
                    narrow7_prefix(&mut want, n.a, n.b, n.c, n.d, n.e, n.f, n.g);
                    mix(&mut want, n.h as u64);
                    mix(&mut want, n.i as u64);
                    mix(&mut want, n.j as i64 as u64);
                    reference(&mut want, &b);
                    mix(&mut want, n.tail as u64);
                    let mut got = Acc::new(seed);
                    unsafe {
                        receive_narrow9(
                            n.a, n.b, n.c, n.d, n.e, n.f, n.g, n.h, n.i, n.j, *b, n.tail, &mut got,
                        )
                    };
                    assert_eq!(got, want, "receive_narrow9");
                    checks += 1;
                }
                {
                    let b = boxed();
                    let mut want = Acc::new(seed);
                    want.h ^= 0x5555_aaaa_5555_aaaa;
                    reference(&mut want, &b);
                    let mut got = Acc::new(seed);
                    unsafe { send_strs0(*b, &mut got) };
                    assert_eq!(got, want, "send_strs0");
                    checks += 1;
                    let b = boxed();
                    let mut want = Acc::new(seed);
                    narrow7_prefix(&mut want, n.a, n.b, n.c, n.d, n.e, n.f, n.g);
                    reference(&mut want, &b);
                    mix(&mut want, n.tail as u64);
                    mix(&mut want, n.guard as i64 as u64);
                    let mut got = Acc::new(seed);
                    unsafe { send_narrow7(*b, seed, &mut got) };
                    assert_eq!(got, want, "send_narrow7");
                    checks += 1;
                    let b = boxed();
                    let mut want = Acc::new(seed);
                    narrow7_prefix(&mut want, n.a, n.b, n.c, n.d, n.e, n.f, n.g);
                    mix(&mut want, n.h as u64);
                    mix(&mut want, n.i as u64);
                    mix(&mut want, n.j as i64 as u64);
                    reference(&mut want, &b);
                    mix(&mut want, n.tail as u64);
                    let mut got = Acc::new(seed);
                    unsafe { send_narrow9(*b, seed, &mut got) };
                    assert_eq!(got, want, "send_narrow9");
                    checks += 1;
                }
                for (f, salt) in [
                    (pointer_a as fn([&str], &mut Acc), 0xa),
                    (pointer_b as fn([&str], &mut Acc), 0xb0b0),
                ] {
                    let b = boxed();
                    let mut want = Acc::new(seed);
                    want.h ^= salt;
                    reference(&mut want, &b);
                    let mut got = Acc::new(seed);
                    unsafe { through_pointer_strs(f, *b, &mut got) };
                    assert_eq!(got, want, "through_pointer_strs");
                    checks += 1;
                }
                {
                    let k = Sinker(seed ^ 0xfedc_ba98_7654_3210);
                    let b = boxed();
                    let mut want = Acc::new(seed);
                    mix(&mut want, k.0);
                    mix(&mut want, n.tail as u64);
                    reference(&mut want, &b);
                    let mut got = Acc::new(seed);
                    unsafe { through_virtual_strs(&k, *b, n.tail, &mut got) };
                    assert_eq!(got, want, "through_virtual_strs");
                    checks += 1;
                }
                assert_eq!(
                    LIVE.load(Ordering::SeqCst),
                    before,
                    "owned buffers leaked or freed twice"
                );
                checks += 1;
            }
        }
    }
    assert_eq!(checks, 22464);
    println!("PASS unsized_str_arguments checks={checks}");
}
