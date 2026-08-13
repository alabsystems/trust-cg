// CORPUS FIXTURE — a 16-byte-aligned `i128` / `u128` aggregate (a `[u128; N]`
// array, an `[i128; N]` array, a struct of two `u128` fields). These memory-back to
// a stack slot whose alignment is 16; the bridge's `memory_slot_lane_ty` only knew
// 1/2/4/8-byte lanes and failed closed ("memory slot alignment 16 unsupported"). A
// 16-byte-aligned slot is now a tuple of `I128` lanes — the x86-64 frame allocator
// honors the alignment, and i128 leaves load/store as two i64 limbs at byte offsets,
// so the lane type only sizes/aligns the slot. (Aggregates whose size is not a
// multiple of 16, e.g. `{ i128, i64 }` of size 24, still fail closed.)
//
// (a) [u128; 5] sum; (b) [i128; 3] signed sum with negatives; (c) a write to an
// i128 array element in a loop then read back; (d) a struct of two u128 fields;
// (e) high-word arithmetic (values that don't fit in u64). All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[derive(Clone, Copy)]
struct Pair {
    a: u128,
    b: u128,
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) [u128; 5] sum = 10+20+30+40+50 = 150.
    let ua: [u128; 5] = [
        black_box(10u128),
        black_box(20u128),
        black_box(30u128),
        black_box(40u128),
        black_box(50u128),
    ];
    let mut s: u128 = 0;
    let mut i = 0usize;
    while i < 5 {
        s = s.wrapping_add(ua[i]);
        i += 1;
    }
    let ok_a = s == 150;

    // (b) [i128; 3] signed sum = -5 + 10 + -2 = 3.
    let ia: [i128; 3] = [black_box(-5i128), black_box(10i128), black_box(-2i128)];
    let mut ss: i128 = 0;
    let mut j = 0usize;
    while j < 3 {
        ss = ss.wrapping_add(ia[j]);
        j += 1;
    }
    let ok_b = ss == 3;

    // (c) write i128 array elements in a loop, read back: 0,7,14 -> sum 21.
    let mut wa: [u128; 3] = [black_box(0u128); 3];
    let mut k = 0usize;
    while k < 3 {
        wa[k] = (k as u128).wrapping_mul(7);
        k += 1;
    }
    let ok_c = wa[0].wrapping_add(wa[1]).wrapping_add(wa[2]) == 21;

    // (d) struct of two u128 fields.
    let p = Pair {
        a: black_box(15u128),
        b: black_box(27u128),
    };
    let ok_d = p.a.wrapping_add(p.b) == 42;

    // (e) high-word arithmetic (>u64).
    let hi: [u128; 2] = [
        black_box(0x1_0000_0000_0000_0000u128),
        black_box(0x2_0000_0000_0000_0000u128),
    ];
    let ok_e = (hi[0].wrapping_add(hi[1]) >> 64) == 3;

    if ok_a && ok_b && ok_c && ok_d && ok_e {
        7
    } else {
        13
    }
}
