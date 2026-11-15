// (c) `discriminant(arg)` of a scalar-modeled enum ENTRY ARG after the arg was
// written THROUGH A RAW POINTER derived from `&mut arg`. The discriminant lane
// admitted `is_entry_arg` and read the ORIGINAL parameter (lane: 1 1 7 -1,
// LLVM: 3 3 7 1). Fixed: the celled local's cell is loaded first; an
// address-taken, uncelled entry arg is refused (`entry_arg_discriminant_admissible`).
#![feature(core_intrinsics)]
#![allow(internal_features)]
#[derive(Clone, Copy, PartialEq)]
pub enum Op { A, B, C }
#[inline(never)]
pub fn via_ptr(mut o: Op) -> u32 { let p = &mut o as *mut Op; unsafe { *p = Op::C; } match o { Op::A => 1, Op::B => 2, Op::C => 3 } }
#[inline(never)]
pub fn via_raw(mut o: Op) -> u32 { let p: *mut Op = &raw mut o; unsafe { *p = Op::C; } match o { Op::A => 1, Op::B => 2, Op::C => 3 } }
#[inline(never)]
pub fn via_ptr_u8(mut o: u8) -> u32 { let p = &mut o as *mut u8; unsafe { *p = 7; } o as u32 }
#[inline(never)]
pub fn via_ptr_ord(mut o: core::cmp::Ordering) -> i32 { let p = &mut o as *mut core::cmp::Ordering; unsafe { *p = core::cmp::Ordering::Greater; } match o { core::cmp::Ordering::Less => -1, core::cmp::Ordering::Equal => 0, core::cmp::Ordering::Greater => 1 } }
#[inline(never)]
pub fn via_ptr_disc(mut o: Op) -> isize { let p = &mut o as *mut Op; unsafe { *p = Op::B; } unsafe { core::intrinsics::discriminant_value(&o) } }
fn main() {
    let (a, b, d, e, f) = (via_ptr(Op::A), via_raw(Op::A), via_ptr_u8(1), via_ptr_ord(core::cmp::Ordering::Less), via_ptr_disc(Op::C));
    println!("{} {} {} {} {}", a, b, d, e, f);
}
