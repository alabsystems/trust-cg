// CORPUS FIXTURE — 16-byte-aligned (i128-containing) aggregates crossing a BY-VALUE
// ABI boundary. These are SysV MEMORY-class (>16 bytes -> sret return / stack byval
// param) or register-pair aggregates whose only i128-specific piece is that a slot
// lane / eightbyte is 16 bytes wide. The bridge memory-backs them (a tuple of `I128`
// slot lanes via `memory_slot_lane_ty`), addresses each field at its rustc-LAYOUT
// byte offset (i128 loaded/stored as two i64 limbs), and relocates the sret bytes
// lane-by-lane; the backend's verified SysV classifier models the `i128` as two
// consecutive INTEGER eightbytes. Previously every one of these failed closed
// ("memory aggregate ... alignment 16 unsupported" / "Ty::(i128, bool)").
//
// Each case has a DISTINCT observable derived from limbs ACROSS the 64-bit boundary
// (high limb non-zero) so a swapped limb, a wrong field offset, or a dropped lane
// diverges from the LLVM oracle. All correct -> exit 7. (O0 is expected to compile
// too — these are direct by-value calls, not the range-iterator helper.)
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;

struct SI128I64 {
    x: i128,
    y: i64,
}

// (i128, bool) returned by value (size 32, align 16 -> sret).
#[inline(never)]
fn ret_i128_bool(x: i128, f: bool) -> (i128, bool) {
    (bb(x).wrapping_mul(3), f)
}

// (i128, i128) returned by value.
#[inline(never)]
fn ret_two_i128(a: i128, b: i128) -> (i128, i128) {
    (bb(a), bb(b))
}

// (bool, i128) — bool FIRST in source (rustc keeps bool@0, i128@16).
#[inline(never)]
fn ret_bool_i128(f: bool, x: i128) -> (bool, i128) {
    (f, bb(x).wrapping_mul(2))
}

// struct { i128, i64 } returned by value (size 32: x@0, y@16 + 8 pad).
#[inline(never)]
fn ret_struct(a: i128, b: i64) -> SI128I64 {
    SI128I64 {
        x: bb(a).wrapping_mul(4),
        y: bb(b) + 7,
    }
}

// [i128; 2] returned by value.
#[inline(never)]
fn ret_array(a: i128, b: i128) -> [i128; 2] {
    [bb(a).wrapping_add(2), bb(b).wrapping_mul(3)]
}

// (i128, bool) passed BY VALUE to a fn AND returned.
#[inline(never)]
fn passthru(t: (i128, bool)) -> (i128, bool) {
    (t.0.wrapping_add(1), !t.1)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) (i128, bool): high limb of the product observed + the bool.
    let (v, o) = ret_i128_bool(bb(7i128 << 64), bb(true));
    // 7<<64 * 3 = 21<<64; high 64 bits = 21.
    let ok_a = ((v >> 64) as i64 == 21) && o;

    // (b) (i128, i128) with fully distinct 128-bit values: every limb must survive.
    let x = bb(0x1122_3344_5566_7788_99AA_BBCC_DDEE_FF01u128 as i128);
    let y = bb(0x0F0E_0D0C_0B0A_0908_0706_0504_0302_0100u128 as i128);
    let (a2, b2) = ret_two_i128(x, y);
    let ok_b = a2 == x && b2 == y && (a2 >> 64) != (b2 >> 64);

    // (c) (bool, i128) reordered: bool@0, i128@16.
    let (f3, v3) = ret_bool_i128(bb(true), bb(9i128 << 70));
    // 9<<70 * 2 = 9<<71; bit 71 region observed.
    let ok_c = f3 && ((v3 >> 71) as i64 == 9);

    // (d) struct { i128, i64 }: both fields at distinct offsets.
    let s = ret_struct(bb(3i128 << 66), bb(11i64));
    // 3<<66 * 4 = 3<<68; high part + y.
    let ok_d = ((s.x >> 68) as i64 == 3) && (s.y == 18);

    // (e) [i128; 2]: element-wise.
    let arr = ret_array(bb(8i128 << 64), bb(4i128));
    let ok_e = ((arr[0] >> 64) as i64 == 8) && (arr[1] == 12);

    // (f) by-value tuple passed AND returned; read field after the call.
    let (pv, pf) = passthru((bb(6i128 << 64), bb(false)));
    let ok_f = ((pv >> 64) as i64 == 6) && ((pv & 0xFF) as i64 == 1) && pf;

    if ok_a && ok_b && ok_c && ok_d && ok_e && ok_f {
        7
    } else {
        13
    }
}
