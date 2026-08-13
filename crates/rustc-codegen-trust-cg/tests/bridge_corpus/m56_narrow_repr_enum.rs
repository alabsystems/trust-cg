// CORPUS FIXTURE — bug #56: narrow-representation enum discriminant. An enum
// lowered to a narrow (i8) discriminant carrier; reading the discriminant must
// re-extend (the dirty-high-carrier invariant, sibling to #51/#66) before the
// match compare. A dirty carrier mis-selects the arm.
// Correct exit: 42 & 0xff = 42.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[repr(i8)]
enum Tag { A = -3, B = 5, C = 17 }
#[inline(never)]
fn pick(sel: i64) -> Tag {
    match sel { 0 => Tag::A, 1 => Tag::B, _ => Tag::C }
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let t = pick(black_box(1));
    let v = match t { Tag::A => 100i64, Tag::B => 42, Tag::C => 200 };
    (v & 0xff) as i32
}
