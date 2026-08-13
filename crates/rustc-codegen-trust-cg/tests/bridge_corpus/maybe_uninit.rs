// CORPUS FIXTURE — `MaybeUninit::<T>::uninit()` write-then-`assume_init` for a
// scalar `T`. Before union memory support this failed closed at every opt level
// (the union type itself didn't convert — "union MaybeUninit field 0 has
// unsupported scalar ABI type Unit" — and the `= const <uninit>` whole-union
// store / the address-taken union had no slot).
//
// Now correct at O0/O2/O3: the union types as its first NON-zero-sized field's
// scalar (skipping the ZST `uninit: ()`), an address-taken `MaybeUninit` is
// memory-backed (a real slot), the `uninit()` const is a no-op (the slot is left
// uninitialized), and `u.as_mut_ptr().write(v)` / `u.assume_init()` read/write that
// slot through the raw pointer. At -O2/-O3 the `MaybeUninit`/`as_mut_ptr` calls
// inline away; at -O0 they are NON-inlined libcore bodies the bridge now also
// compiles (union ZST-field construction, `&raw mut (*self)` through a reference
// param, the `assert_inhabited` no-op, and the by-value scalar-union ABI) — see the
// sibling `maybe_uninit_o0` fixture for the dedicated -O0 surface. An inlined
// `MaybeUninit::new`/`zeroed` (an INITIALIZED union const) stays fail-closed (sound).
//
// (a) u32 write-then-read; (b) u64 write-then-read; (c) write then in-place mutate.
// All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;
use core::mem::MaybeUninit;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) u32: uninit -> write -> assume_init.
    let mut a: MaybeUninit<u32> = MaybeUninit::uninit();
    unsafe {
        a.as_mut_ptr().write(black_box(42));
    }
    let ok_a = unsafe { a.assume_init() } == 42;

    // (b) u64: a wider scalar through the same path.
    let mut b: MaybeUninit<u64> = MaybeUninit::uninit();
    unsafe {
        b.as_mut_ptr().write(black_box(0x1_0000_0001u64));
    }
    let ok_b = unsafe { b.assume_init() } == 0x1_0000_0001u64;

    // (c) write then mutate in place through the pointer, then read.
    let mut c: MaybeUninit<u32> = MaybeUninit::uninit();
    unsafe {
        c.as_mut_ptr().write(black_box(10));
        *c.as_mut_ptr() += black_box(5);
    }
    let ok_c = unsafe { c.assume_init() } == 15;

    if ok_a && ok_b && ok_c {
        7
    } else {
        13
    }
}
