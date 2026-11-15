// CORPUS FIXTURE — by-value `PassMode::Pair` ARGUMENTS, whole program.
//
// The cross-backend placement is measured by `m141_x86_scalar_pair_arg_xback`
// and `benchmarks/regclass-xback`; this fixture pins the BRIDGE-INTERNAL
// contract at every opt level: the declaration, the callee's entry block and
// every call site (direct, closure-body `?`, trait-object) agree on two values,
// the two lanes are loaded from and stored to the argument's slot at rustc's
// own offsets, and a pair that follows three scalar arguments or two pairs in
// one list lands in the right registers. Shapes are the `core` census's own:
// `Option<u8>` (`net::parser`'s `?`), `Option<u32>` (`unwrap_or`), `Range<u16>`
// (`Formatter::padding`), `(i16, i16)` after three scalars (`flt2dec`) and a
// `{u32, u16}` mixed-width struct (`fmt::PostPadding`).
#![no_std]
#![no_main]

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

use core::hint::black_box as bb;
use core::ops::Range;

pub struct Post {
    a: u32,
    b: u16,
}

pub trait Take {
    fn take(&self, o: Option<u32>) -> u32;
}
pub struct T1(u32);
impl Take for T1 {
    fn take(&self, o: Option<u32>) -> u32 {
        match o {
            Some(v) => v.wrapping_add(self.0),
            None => self.0.wrapping_mul(2),
        }
    }
}

#[inline(never)]
fn after3(a: u64, b: u64, c: u64, t: (i16, i16)) -> i64 {
    (a + b + c) as i64 + t.0 as i64 * 100 + t.1 as i64
}

#[inline(never)]
fn g(o: Option<u8>) -> u8 {
    o.map_or(7, |x| x.wrapping_add(1))
}

#[inline(never)]
fn h(r: Range<u16>) -> u32 {
    r.map(|x| x as u32).sum()
}

#[inline(never)]
fn post(p: Post) -> u32 {
    p.a.wrapping_mul(2).wrapping_add(p.b as u32)
}

#[inline(never)]
fn two(a: Option<u32>, b: (i16, i16), c: u64) -> u64 {
    let x = match a {
        Some(v) => v as u64,
        None => 1000,
    };
    x * 3 + (b.0 as i64 * 10 + b.1 as i64) as u64 + c
}

/// The `net::parser` shape: a closure BODY using `?` on `Option<u8>`, so the
/// closure calls `<Option<u8> as Try>::branch(self)` with the pair by value
/// through the direct-call lane. (A closure whose OWN parameter is a pair stays
/// refused by design: closure calls are hand-built, outside the lane's scope.)
#[inline(never)]
fn parse_pair(a: Option<u8>, b: Option<u8>) -> Option<u16> {
    let f = || -> Option<u16> {
        let x = a?;
        let y = b?;
        Some(x as u16 * 256 + y as u16)
    };
    f()
}

#[inline(never)]
fn via_dyn(t: &dyn Take, o: Option<u32>) -> u32 {
    t.take(o)
}

#[inline(never)]
fn mix(hash: u64, v: u64) -> u64 {
    (hash ^ v).wrapping_mul(0x100000001b3)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut hash: u64 = 0xcbf29ce484222325;
    hash = mix(hash, after3(bb(10), bb(20), bb(30), bb((7, 9))) as u64);
    hash = mix(hash, after3(bb(1), bb(2), bb(3), bb((-4, -5))) as u64);
    hash = mix(hash, g(bb(Some(3))) as u64);
    hash = mix(hash, g(bb(None)) as u64);
    hash = mix(hash, h(bb(3..10)) as u64);
    hash = mix(hash, h(bb(300..305)) as u64);
    hash = mix(
        hash,
        post(Post {
            a: bb(100_000),
            b: bb(65_535),
        }) as u64,
    );
    hash = mix(hash, two(bb(Some(4)), bb((2, 3)), bb(100)));
    hash = mix(hash, two(bb(None), bb((1, 5)), bb(7)));
    hash = mix(
        hash,
        parse_pair(bb(Some(1)), bb(Some(2))).map_or(9, |v| v as u64),
    );
    hash = mix(
        hash,
        parse_pair(bb(Some(1)), bb(None)).map_or(9, |v| v as u64),
    );
    let t = T1(bb(10));
    hash = mix(hash, via_dyn(&t, bb(Some(5))) as u64);
    hash = mix(hash, via_dyn(&t, bb(None)) as u64);
    (hash & 0x7f) as i32
}
