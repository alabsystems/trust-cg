// (f) `core::intrinsics::abort_immediate()` must terminate the process the way LLVM's
// `llvm.trap` does — `brk #1` on AArch64 (SIGTRAP, exit 133), `ud2` on x86-64 —
// not through a `call abort` (SIGABRT, exit 134). Fixed in trust-cg-lower's
// AArch64 `select_trap` (`AArch64Opcode::Brk`, encoded 0xD4200020 = brk #1).
// `std::process::abort` is a real libc `abort()` call on both sides (exit 134).
#![feature(core_intrinsics)]
#![allow(internal_features)]
#[inline(never)] fn guarded(v: u32) -> u32 { if v == 41 { core::intrinsics::abort_immediate(); } v + 1 }
fn main() { println!("before {}", guarded(1)); let r = guarded(41); println!("after {}", r); }
