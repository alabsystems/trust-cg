// CORPUS FIXTURE — four small `library/core` refusal classes in one program:
//   * `core::array::from_fn` instantiates `array::try_from_fn::<NeverShortCircuit<T>, N, _>`,
//     whose `?` calls `from_residual` on an UNINHABITED residual — a dead arm
//     rustc lowers to `unreachable`;
//   * `AtomicPtr<T>::{store, load}` — an atomic over a POINTER element;
//   * `core::intrinsics::const_eval_select` whose runtime arm takes a `&[u8]`
//     slice argument PROJECTED out of the tupled-args place (rustc's
//     `remap_mir_for_const_eval_select` shape: `CStr::from_bytes_with_nul_unchecked`,
//     `run_utf8_validation`, `memchr_aligned`);
//   * a whole `Use` copy (`let q = p`) out of a struct whose ADDRESS was taken
//     first (`touch(&p)`), so its leaves live in a memory slot rather than in
//     SSA projections (`ZipImpl::new`, `str::escape_debug`).
#![no_std]
#![no_main]
#![feature(core_intrinsics)]
#![allow(internal_features)]

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

use core::hint::black_box as bb;
use core::sync::atomic::{AtomicPtr, Ordering};

#[derive(Clone, Copy)]
struct P {
    a: u32,
    b: u16,
    c: u8,
}

#[inline(never)]
fn touch(p: &P) -> u32 {
    p.a ^ 1
}

#[inline(never)]
fn whole_use_after_address(a: u32, b: u16, c: u8) -> u32 {
    let p = P { a, b, c };
    let t = touch(&p);
    let q = p;
    q.a.wrapping_mul(3) + q.b as u32 * 7 + q.c as u32 * 11 + t
}

#[inline(never)]
fn from_fn_array(k: u8) -> u32 {
    let a: [u8; 5] = core::array::from_fn(|i| (i as u8).wrapping_mul(3).wrapping_add(k));
    let mut s = 0u32;
    for (i, v) in a.iter().enumerate() {
        s = s.wrapping_add(*v as u32 * (i as u32 + 1));
    }
    s
}

static SLOT: AtomicPtr<u32> = AtomicPtr::new(core::ptr::null_mut());

#[inline(never)]
fn atomic_ptr_round_trip(x: &mut u32) -> u32 {
    SLOT.store(x as *mut u32, Ordering::Release);
    let q = SLOT.load(Ordering::Acquire);
    unsafe {
        *q = (*q).wrapping_add(5);
        *q
    }
}

const fn ct_sum(s: &[u8]) -> usize {
    let mut i = 0;
    let mut acc = 0usize;
    while i < s.len() {
        acc += s[i] as usize;
        i += 1;
    }
    acc
}

#[inline(never)]
fn rt_sum(s: &[u8]) -> usize {
    let mut acc = 0usize;
    for b in s {
        acc = acc.wrapping_add(*b as usize).wrapping_mul(3);
    }
    acc
}

#[inline(never)]
fn select_sum(s: &[u8]) -> usize {
    core::intrinsics::const_eval_select((s,), ct_sum, rt_sum)
}

#[inline(never)]
fn mix(hash: u64, v: u64) -> u64 {
    (hash ^ v).wrapping_mul(0x100000001b3)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut hash: u64 = 0xcbf29ce484222325;
    hash = mix(hash, whole_use_after_address(bb(1000), bb(9), bb(4)) as u64);
    hash = mix(hash, from_fn_array(bb(2)) as u64);
    let mut x = bb(40u32);
    hash = mix(hash, atomic_ptr_round_trip(&mut x) as u64);
    hash = mix(hash, x as u64);
    hash = mix(hash, select_sum(bb(b"abc" as &[u8])) as u64);
    (hash & 0x7f) as i32
}
