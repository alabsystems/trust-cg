// CORPUS FIXTURE — `MaybeUninit<T>` for a NON-scalar (multi-field aggregate) `T`
// at -O0, where `uninit()` / `as_mut_ptr()` / `assume_init()` are NON-inlined
// libcore bodies (they inline away at -O2/-O3). Before this the aggregate-union
// path failed closed ("Ty::Adt multi-field struct core::mem::ManuallyDrop<(i64,
// i64)>"): the union's active `value: ManuallyDrop<T>` field, and the by-value
// aggregate-union ABI, had no memory-backed representation.
//
// Now correct at -O0: the aggregate union rides the SAME verified memory-aggregate
// machinery a same-sized struct/tuple uses. Its overlapping fields all begin at
// byte offset 0, so:
//   * `uninit()` returns the union by value (its slot lane tuple crosses the SysV
//     aggregate-return ABI); constructing `MaybeUninit { uninit: () }` leaves the
//     slot uninitialized (matching LLVM `undef` — a defined program writes through
//     it first).
//   * `m.as_mut_ptr()` = `&raw mut (*self) as *mut T` — a raw pointer to the union
//     slot, retyped to `*mut T`.
//   * `.write((..))` stores the aggregate's leaves through that pointer at their
//     rustc-layout offsets.
//   * `m.assume_init()` takes the union by value (its slot lane tuple crosses the
//     ABI), then reads `&raw const (self.value) as *const T` + `*ptr` — a whole
//     aggregate read out of the slot into the by-value return.
//
// Every shape uses a DISTINCT observable so a wrong byte offset (a swapped field,
// a dropped store, a mis-addressed leaf) diverges from the LLVM oracle:
//   (a) `(i64, i64)`            -> 20 + 22          = 42
//   (b) `(i32, i32, i32)`       -> 3*100 + 9*10 + 30 = 420 (mod 126 -> 42)
//   (c) `struct { a: i64, b }`  -> 7*10 + 5          = 75
//   (d) `(i8, i64)` (padding)   -> 5 + 40            = 45
//   (e) `[i64; 3]`              -> 11 + 22*2 + 33*3  = 154 (mod 126 -> 28)
//   (f) per-field distinct      -> 100 - 23          = 77 (diverges if fields swap)
//
// All correct -> exit 7. (At -O2/-O3 the `MaybeUninit`/`assume_init` calls inline
// away; the `[i64;3]` element read const-folds to a scalarized-array raw-pointer
// deref that stays fail-closed — sound, the differential treats a trust-cg
// fail-closed as safe, never a miscompile.)
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;
use core::mem::MaybeUninit;

struct Pair {
    a: i64,
    b: i64,
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) a two-field tuple.
    let mut a: MaybeUninit<(i64, i64)> = MaybeUninit::uninit();
    unsafe {
        a.as_mut_ptr().write((bb(20i64), bb(22i64)));
    }
    let ta = unsafe { a.assume_init() };
    let ok_a = (ta.0 + ta.1) == 42;

    // (b) a three-field tuple of i32.
    let mut b: MaybeUninit<(i32, i32, i32)> = MaybeUninit::uninit();
    unsafe {
        b.as_mut_ptr().write((bb(3i32), bb(9i32), bb(30i32)));
    }
    let tb = unsafe { b.assume_init() };
    let ok_b = (tb.0 * 100 + tb.1 * 10 + tb.2) == 420;

    // (c) a named struct.
    let mut c: MaybeUninit<Pair> = MaybeUninit::uninit();
    unsafe {
        c.as_mut_ptr().write(Pair { a: bb(7i64), b: bb(5i64) });
    }
    let tc = unsafe { c.assume_init() };
    let ok_c = (tc.a * 10 + tc.b) == 75;

    // (d) a mixed-width tuple (padding + rustc field reorder).
    let mut d: MaybeUninit<(i8, i64)> = MaybeUninit::uninit();
    unsafe {
        d.as_mut_ptr().write((bb(5i8), bb(40i64)));
    }
    let td = unsafe { d.assume_init() };
    let ok_d = (td.0 as i64 + td.1) == 45;

    // (e) an array element write-then-read.
    let mut e: MaybeUninit<[i64; 3]> = MaybeUninit::uninit();
    unsafe {
        e.as_mut_ptr().write([bb(11i64), bb(22i64), bb(33i64)]);
    }
    let te = unsafe { e.assume_init() };
    let ok_e = (te[0] + te[1] * 2 + te[2] * 3) == 154;

    // (f) per-field distinct observable (a - b diverges if fields are swapped).
    let mut f: MaybeUninit<(i64, i64)> = MaybeUninit::uninit();
    unsafe {
        f.as_mut_ptr().write((bb(100i64), bb(23i64)));
    }
    let tf = unsafe { f.assume_init() };
    let ok_f = (tf.0 - tf.1) == 77;

    if ok_a && ok_b && ok_c && ok_d && ok_e && ok_f {
        7
    } else {
        13
    }
}
