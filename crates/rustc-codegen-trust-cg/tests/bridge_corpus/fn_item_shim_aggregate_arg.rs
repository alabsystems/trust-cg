// Root (b): `Option<T>::map(fn_item)` / a generic `F: FnOnce(T, ..)` instantiated
// with a fn ITEM, where an argument `T` is a BY-VALUE AGGREGATE. The call is
// `<fn{item} as FnOnce<(T,)>>::call_once(move f, move tuple)`; the tupled-args
// `(T,)` is built from a memory-backed `T` (`_7 = (copy _4,)`) and failed
// "Place projection field 0 before aggregate binding"; the FnPtrShim body
// `_0 = move _1(move (_2.0: T))` fails "by-value aggregate call argument 0 uses a
// projected operand". The census root is
// `Option<Map<slice::Iter<u8>, EscapeByte>>::map(Map::into_inner)`.
// CORPUS FIXTURE. Correct exit = LLVM oracle (29 at O0/O2). Before: COMPILE-ERROR ("Place projection field 0 before aggregate binding", 7 sites).
#![no_std]
#![no_main]
use core::hint::black_box;
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }

pub struct Q2 { a: u64, b: u64 }
pub struct Map1<I> { iter: I }
#[derive(Clone, Copy)]
pub struct Z;
pub struct Map<I, F> { iter: I, f: F }
impl<I, F> Map<I, F> {
    #[inline(never)]
    pub fn into_inner(self) -> I { self.iter }
}
#[inline(never)] fn q2a(q: Q2) -> u64 { q.a * 3 + q.b }
#[inline(never)] fn q2q(q: Q2) -> Q2 { Q2 { a: q.b, b: q.a + 1 } }
#[inline(never)] fn m_in(m: Map1<Q2>) -> Q2 { m.iter }
#[inline(never)] fn two(q: Q2, k: u64) -> u64 { q.a * k + q.b }
#[inline(never)] fn apply2<F: FnOnce(Q2, u64) -> u64>(f: F, q: Q2, k: u64) -> u64 { f(q, k) }
#[inline(never)] fn apply_ref<F: Fn(Q2) -> u64>(f: &F, q: Q2) -> u64 { f(q) + f(Q2 { a: 1, b: 2 }) }
#[inline(never)] fn apply_mut<F: FnMut(Q2) -> u64>(mut f: F, q: Q2) -> u64 { f(q) }

// A two-pointer cursor with the same `PassMode::Pair` shape as the census
// root's `slice::Iter<u8>` (`{ NonNull<u8>, *const u8 }`), built from scalars so
// the fixture does not also exercise the separate class B0 (NOTES.md).
#[derive(Clone, Copy)]
pub struct Cur { p: *const u8, e: *const u8 }
impl Cur {
    fn sum(self) -> u64 {
        let mut acc = 0u64;
        let mut p = self.p;
        let mut i = 1u64;
        while p != self.e { acc += i * unsafe { *p } as u64; p = unsafe { p.add(1) }; i += 1; }
        acc
    }
}
#[inline(never)]
fn mk(s: &[u8; 5], on: bool) -> Option<Map<Cur, Z>> {
    let p = s.as_ptr();
    if on { Some(Map { iter: Cur { p, e: unsafe { p.add(5) } }, f: Z }) } else { None }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let o1 = black_box(Some(Q2 { a: 5, b: 7 }));
    acc += o1.map(q2a).unwrap_or(1000);
    let o2: Option<Q2> = black_box(None);
    acc += o2.map(q2a).unwrap_or(9);
    if let Some(q) = black_box(Some(Q2 { a: 20, b: 30 })).map(q2q) { acc += q.a * 2 + q.b; }
    if let Some(q) = black_box(Some(Map1 { iter: Q2 { a: 4, b: 6 } })).map(m_in) { acc += q.a + q.b * 5; }
    let bytes = black_box([3u8, 1, 4, 1, 5]);
    if let Some(c) = mk(&bytes, black_box(true)).map(Map::into_inner) { acc += c.sum(); }
    if mk(&bytes, black_box(false)).map(Map::into_inner).is_none() { acc += 13; }
    acc += apply2(two, black_box(Q2 { a: 3, b: 4 }), black_box(10));
    acc += apply_ref(&q2a, black_box(Q2 { a: 9, b: 1 }));
    acc += apply_mut(q2a, black_box(Q2 { a: 2, b: 2 }));
    (acc % 251) as i32
}
