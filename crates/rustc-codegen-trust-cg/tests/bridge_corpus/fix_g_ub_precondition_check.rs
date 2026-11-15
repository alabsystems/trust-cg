// (g) A violated `assert_unsafe_precondition!` guarded by
// `Operand::RuntimeChecks(UbChecks)`: with UB checks ON (-O0, debug assertions)
// LLVM runs `precondition_check` and panics (exit 134). The bridge folded
// `UbChecks` to the real session value but ALSO dropped every
// `*::precondition_check` call (and stubbed an unlowerable helper as a no-op),
// so the check was silently skipped. Both drops are now gated on
// `tcx.sess.ub_checks() == false`. With UB checks OFF (-O2) the guard folds to
// false in both compilers, so this program takes the clean exit path instead of
// executing UB (whose -O2 outcome is not a differential fact).
#![feature(core_intrinsics)]
#![allow(internal_features)]
use core::ptr::NonNull;
#[inline(never)] fn nn_null() -> bool { let p = unsafe { NonNull::new_unchecked(core::ptr::null_mut::<u8>()) }; p.as_ptr().is_null() }
#[inline(never)] fn bad_char(v: u32) -> u32 { unsafe { char::from_u32_unchecked(v) as u32 } }
fn main() {
    println!("start");
    if !core::intrinsics::ub_checks() {
        println!("ub checks off");
        std::process::exit(7);
    }
    println!("nn_null {}", nn_null());
    println!("bad_char {}", bad_char(0x110000));
}
