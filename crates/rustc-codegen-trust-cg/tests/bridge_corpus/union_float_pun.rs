// CORPUS FIXTURE — type-punning a `union` between a float field and a same-width
// integer field (the classic `union { i: u32, f: f32 }` bit reinterpret). Writing
// one field and reading the OTHER reinterprets the raw bytes, which is exactly
// `f32::to_bits` / `f32::from_bits` — a proven `Bitcast`. It failed closed because
// `union_projection_cast_op` only modeled integer↔integer field casts ("union field
// 0 type U32 differs from active field 1 type F32"); a same-width float↔int field
// pair is now a `Bitcast` (different widths still fail closed — not a value-
// preserving reinterpret).
//
// (a) write f32, read u32, inspect the exponent; (b) write u32, read f32; (c) the
// f64↔u64 pair both directions; (d) a plain same-type union (regression guard for
// the unchanged integer path). All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

union F32 {
    i: u32,
    f: f32,
}
union F64 {
    i: u64,
    f: f64,
}
union Same {
    a: u32,
    b: u32,
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) write f32, read u32: 1.0f32 == 0x3F800000.
    let ua = F32 { f: black_box(1.0f32) };
    let ok_a = unsafe { ua.i } == 0x3F80_0000;

    // (b) write u32, read f32: 0x40400000 == 3.0f32.
    let ub = F32 { i: black_box(0x4040_0000u32) };
    let ok_b = unsafe { ub.f } == 3.0f32;

    // (c) f64<->u64 both directions: 2.0f64 == 0x4000000000000000.
    let uc = F64 { f: black_box(2.0f64) };
    let ok_c1 = unsafe { uc.i } == 0x4000_0000_0000_0000;
    let ud = F64 { i: black_box(0x4010_0000_0000_0000u64) }; // 4.0f64
    let ok_c2 = unsafe { ud.f } == 4.0f64;

    // (d) plain same-type union (the unchanged integer path).
    let ue = Same { a: black_box(42u32) };
    let ok_d = unsafe { ue.b } == 42;

    if ok_a && ok_b && ok_c1 && ok_c2 && ok_d {
        7
    } else {
        13
    }
}
