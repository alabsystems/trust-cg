// CORPUS FIXTURE — a 128-bit `==` / `!=` / single-arm `match` on `i128`/`u128`. At
// O2/O3 (and sometimes O0) rustc lowers `if x == c` to a `switchInt(x) -> [c: then,
// otherwise: else]` directly on the 128-bit value, and the verified `Inst::Switch`
// lowering supports only 8/16/32/64-bit selectors ("unsupported switch selector
// width for I128/U128"). A SINGLE-case 128-bit switch is exactly `if discr ==
// case_value { case } else { otherwise }`, so the bridge now emits a 128-bit `Eq`
// compare + `CondBr` (an `Eq` is bit-equality, valid for both signednesses). A
// multi-case 128-bit match would need a synthesized comparison chain and still fails
// closed (never miscompiles).
//
// (a) u128 == with a non-zero high limb; (b) i128 != ; (c) negative i128 == ; (d)
// i128::MIN == ; (e) the (a^b)==1 pattern; (f) i128 == inside a loop. All correct ->
// exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut c = 0i32;

    // (a) u128 == with a high limb.
    let a = black_box(0xDEAD_BEEF_0000_0000_0000_0000_0000_0001u128);
    if a == black_box(0xDEAD_BEEF_0000_0000_0000_0000_0000_0001u128) {
        c += 1;
    }
    // (b) i128 != .
    if black_box(5i128) != black_box(99i128) {
        c += 1;
    }
    // (c) negative i128 == .
    if black_box(-42i128) == black_box(-42i128) {
        c += 1;
    }
    // (d) i128::MIN == .
    if black_box(i128::MIN) == black_box(i128::MIN) {
        c += 1;
    }
    // (e) (a^b)==1 (the reaudit pattern).
    let x: u128 = black_box(0x1111_2222_3333_4444_0000_0000_0000_0003u128);
    let y: u128 = black_box(0x1111_2222_3333_4444_0000_0000_0000_0002u128);
    if (x ^ y) == 1 {
        c += 1;
    }
    // (f) i128 == inside a loop (the value equals the index on one iteration).
    let mut i: i128 = black_box(0);
    let mut hits = 0i32;
    while i < black_box(5i128) {
        if i == black_box(2i128) {
            hits += 1;
        }
        i += 1;
    }
    if hits == 1 {
        c += 2;
    }

    c // 1+1+1+1+1+2 = 7
}
