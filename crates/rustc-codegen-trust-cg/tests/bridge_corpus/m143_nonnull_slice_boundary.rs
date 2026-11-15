// m143_nonnull_slice_boundary.rs — whole program, `#![no_std] #![no_main]`, run through
// scratchpad/lanes/diff.sh <this> <dylib|none> {0,2,3}. EXPECTED EXIT CODE: 52 on every lane
// (LLVM oracle `none` and the dylib at O0, O2, O3). A COMPILE-ERROR / TCG-* line on the
// trust-cg lane fails the bar. At O0 every #[inline(never)] wrapper calls the real core
// instances — the six census root shapes: NonNull::<[u8]>::{as_ptr, cast, from_ref, from_mut},
// NonNull::<str>::as_ptr, slice::Iter::<u8>::new (via `for &b in s`), IterMut::<u8>::new
// (via `iter_mut`). At O2/O3 the core methods inline into the wrappers: nn_len / nn_first /
// nn_after3 / nn_two become `_2 = copy _1 as *mut [u8] (Transmute)` from the NonNull param
// slot ((3b)-WIP slot + Transmute lane copy), nn_from_ref / nn_from_mut the `&raw (*_1)`
// reborrow slot + Transmute into the return slot, nn_ident the slot-to-slot Use; sum / bump
// keep their scalarized inlined Iter::new chain (the (3b) WIP restriction's canary).
#![no_std]
#![no_main]
use core::hint::black_box as bb;
use core::ptr::NonNull;

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

static BUF: [u8; 5] = [10, 20, 30, 40, 50];

#[inline(never)]
fn nn_from_ref(s: &[u8]) -> NonNull<[u8]> {
    NonNull::from_ref(s)
}
#[inline(never)]
fn nn_from_mut(s: &mut [u8]) -> NonNull<[u8]> {
    NonNull::from_mut(s)
}
#[inline(never)]
fn nn_ident(p: NonNull<[u8]>) -> NonNull<[u8]> {
    p
}
#[inline(never)]
fn nn_as_ptr(p: NonNull<[u8]>) -> *mut [u8] {
    p.as_ptr()
}
#[inline(never)]
fn nn_len(p: NonNull<[u8]>) -> usize {
    p.len()
}
#[inline(never)]
fn nn_first(p: NonNull<[u8]>) -> u8 {
    unsafe { *p.cast::<u8>().as_ptr() }
}
#[inline(never)]
fn nn_str(s: &str) -> NonNull<str> {
    NonNull::from_ref(s)
}
#[inline(never)]
fn nn_str_len(p: NonNull<str>) -> usize {
    unsafe { (&*p.as_ptr()).len() }
}
#[inline(never)]
fn nn_after3(a: u64, b: u64, c: u64, p: NonNull<[u8]>) -> u64 {
    a + b + c + p.len() as u64
}
#[inline(never)]
fn nn_two(p: NonNull<[u8]>, q: NonNull<[u8]>) -> usize {
    p.len() * 10 + q.len()
}
#[inline(never)]
fn nn_write_first(p: NonNull<[u8]>) {
    unsafe {
        *p.cast::<u8>().as_ptr() = 9;
    }
}
#[inline(never)]
fn sum(s: &[u8]) -> u32 {
    let mut t = 0u32;
    for &b in s {
        t += b as u32;
    }
    t
}
#[inline(never)]
fn bump(s: &mut [u8]) {
    for b in s.iter_mut() {
        *b += 1;
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let s: &[u8] = bb(&BUF[..]); // runtime {data, 5}
    let p = nn_from_ref(s); // &[u8] in, NonNull<[u8]> out (RAX:RDX)
    let q = nn_ident(p); // NonNull<[u8]> in (RDI:RSI) and out
    let a = nn_len(q) as i32; // 5   — the len lane survived two crossings
    let b = nn_first(q) as i32; // 10  — the data lane did too (cast + thin as_ptr)
    let r = nn_as_ptr(q); // *mut [u8] out
    let c = unsafe { (&*r)[4] } as i32; // 50  — the bounds check reads r's len lane
    let t: &str = bb("xyz!");
    let d = nn_str_len(nn_str(t)) as i32; // 4   — NonNull<str> in and out
    let e = sum(s) as i32; // 150 — slice::Iter::<u8>::new at O0
    let f = nn_after3(bb(1u64), bb(2u64), bb(3u64), q) as i32; // 11 — pair in RCX:R8 after three scalars
    let mut arr = [1u8, 2, 3];
    bump(&mut arr); // IterMut::<u8>::new at O0 -> [2, 3, 4]
    let g = arr[0] as i32 + arr[2] as i32; // 6
    let pm = nn_from_mut(&mut arr); // &mut [u8] in, NonNull<[u8]> out
    let h = nn_two(q, pm) as i32; // 53  — two pairs: RDI:RSI, RDX:RCX
    nn_write_first(pm); // arr[0] = 9 through the data lane
    let i = arr[0] as i32; // 9
    let mut w = p; // `_w = copy _p`: a bare NonNull local whole-copied from a slotted one
    if bb(false) {
        w = pm;
    } // a second def keeps the copy out of CopyProp ((3b) newtype whole-copy sub-arm)
    let j = nn_len(w) as i32; // 5
    (a + b + c + d + e + f + g + h + i + j) % 251 // 5+10+50+4+150+11+6+53+9+5 = 303; 303 % 251 = 52
}
// EXPECTED EXIT CODE: 52 (O0, O2, O3; LLVM oracle and trust-cg must agree).
