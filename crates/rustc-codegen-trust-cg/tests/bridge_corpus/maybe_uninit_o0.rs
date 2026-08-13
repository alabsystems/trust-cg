// CORPUS FIXTURE — `MaybeUninit<T>` at -O0, where `uninit()` / `as_mut_ptr()` /
// `assume_init()` are NON-inlined libcore function calls (they inline away at
// -O2/-O3, which the sibling `maybe_uninit` fixture covers). Compiling those
// bodies exercises the full O0 union surface:
//
//   * `MaybeUninit::<T>::uninit()` -> `MaybeUninit { uninit: () }`: a union
//     constructed THROUGH its zero-sized `uninit: ()` field. The shared storage is
//     left uninitialized, so the returned union's scalar ABI carrier is an
//     arbitrary (zero) value — sound because a defined program writes the real
//     value through the union before any read (LLVM emits `undef` here).
//   * `MaybeUninit::<T>::as_mut_ptr(&mut self)` -> `&raw mut (*self) as *mut T`: a
//     raw pointer taken THROUGH a reference PARAMETER (the entry-arg RawPtr path).
//   * `MaybeUninit::<T>::assume_init(self)` -> `assert_inhabited::<T>()` (a
//     compile-time no-op for an inhabited `T`) then a raw read of the union's
//     `value` field. The by-value union `self` crosses the ABI as its single
//     scalar carrier and is stored into the callee's union slot.
//   * `MaybeUninit::new(v).assume_init()`: a union constructed through its NON-ZST
//     `value` field (the ZST `uninit` sibling is skipped in the field validation).
//   * `[MaybeUninit<i64>; N]` element write-then-read (the common `uninit_array`
//     idiom): each element is an address-taken scalar-union slot.
//
// All four checks must reproduce their LLVM values -> exit 7. At -O2/-O3 the
// inlined `new()` / array shapes const-fold into an initialized / whole-array
// union const that stays fail-closed (sound — the differential harness treats a
// trust-cg fail-closed as safe, never a miscompile). The point of THIS fixture is
// the -O0 non-inlined path: a wrong byte in the union slot / raw-pointer address /
// scalar-carrier ABI would diverge from LLVM and fail the differential.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;
use core::mem::MaybeUninit;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) i32: uninit -> as_mut_ptr().write -> assume_init.
    let mut a: MaybeUninit<i32> = MaybeUninit::uninit();
    unsafe {
        a.as_mut_ptr().write(bb(42i32));
    }
    let ok_a = unsafe { a.assume_init() } == 42;

    // (b) u8: a narrow scalar through the same path.
    let mut b: MaybeUninit<u8> = MaybeUninit::uninit();
    unsafe {
        b.as_mut_ptr().write(bb(200u8));
    }
    let ok_b = unsafe { b.assume_init() } == 200;

    // (c) MaybeUninit::new(v) -> assume_init (non-ZST active union field).
    let ok_c = unsafe { MaybeUninit::new(bb(55i32)).assume_init() } == 55;

    // (d) an array of MaybeUninit written element-wise then read back.
    let mut arr: [MaybeUninit<i64>; 4] = [MaybeUninit::uninit(); 4];
    let mut i = 0usize;
    while i < 4 {
        unsafe {
            arr[i].as_mut_ptr().write(bb((i as i64) * 10));
        }
        i += 1;
    }
    let mut sum = 0i64;
    let mut j = 0usize;
    while j < 4 {
        sum += unsafe { arr[j].assume_init() };
        j += 1;
    }
    let ok_d = sum == 60;

    if ok_a && ok_b && ok_c && ok_d {
        7
    } else {
        13
    }
}
