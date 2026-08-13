// CORPUS FIXTURE — `Option<NonZero<T>>` niche enum and `NonZero` / `ilog`. The niche
// encoding represents `Option<NonZeroU32>` as a bare `u32`: `0 == None`, any other
// value `n == Some(n)`. `NonZero::new(v)` is `v as Option<NonZero<u32>> (Transmute)`
// + a niche match, and `ilog2`/`ilog10` route through it too. It failed closed
// because the niche `Transmute(int -> Option<NonZero>)` into the enum's slot was an
// unhandled "memory-backed aggregate assignment Rvalue::Cast".
//
// The integer's bytes ARE the niche-encoded enum's in-memory image, so the
// transmute stores the integer into the enum's slot (a proven Store, after
// memory-backing the transmute destination); the existing memory niche
// discriminant + payload reads then decode `0 -> None` / `n -> Some(NonZero(n))`.
//
// Checks the niche end to end: `new(0) == None`, `new(7) == Some(7)`, a wider
// `NonZeroU64`, and `ilog2`. All correct -> exit 7. (Inline `NonZero::new` to keep
// every mono-item in the main CGU, so it links at O2/O3.)
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;
use core::num::{NonZeroU32, NonZeroU64};

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) the 0-niche: new(0) is None.
    let ok_z = matches!(NonZeroU32::new(black_box(0u32)), None);
    // (b) new(7) is Some(7).
    let ok_s = match NonZeroU32::new(black_box(7u32)) {
        Some(n) => n.get() == 7,
        None => false,
    };
    // (c) a wider NonZeroU64.
    let ok_w = match NonZeroU64::new(black_box(0x1_0000_0007u64)) {
        Some(n) => n.get() == 0x1_0000_0007u64,
        None => false,
    };
    // (d) ilog2 (routes through Option<NonZero> internally).
    let ok_l = black_box(64u32).ilog2() == 6;

    if ok_z && ok_s && ok_w && ok_l {
        7
    } else {
        13
    }
}
