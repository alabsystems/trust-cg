// wasm32 execution-differential corpus: a `const` whose value points into
// the allocation a static's image reaches.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// `K` is read out of `A`, so it carries the provenance of `A`'s promoted
// array: `offset_from(K, A.as_ptr())` is defined and `K` equals `&C[3]`,
// whichever module reads it. Only single-CGU configurations are compared:
// with several codegen units the LLVM backend gives each CGU that references
// the allocation its own private copy, so its `offset_from` across two copies
// is not the abstract machine's answer, while this backend keeps one copy.
//
// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2

#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

mod shared {
    pub static A: &[u32; 5] = &[10, 20, 30, 40, 50];
    pub static C: &[u32; 5] = A;
    pub static AA: &&u16 = &&7;
}

const K: &u32 = &shared::A[3];
const KK: &u16 = *shared::AA;

#[no_mangle]
pub extern "C" fn ns_const(i: u32) -> u32 {
    let off = unsafe { (K as *const u32).offset_from(shared::A.as_ptr()) } as u32;
    let same = core::ptr::eq(K, &shared::C[3]) as u32;
    off | same << 4 | (*K).wrapping_add(i) << 8
}

#[no_mangle]
pub extern "C" fn ns_const_nested(i: u32) -> u32 {
    let same = core::ptr::eq(KK, *shared::AA) as u32;
    same | (*KK as u32).wrapping_mul(i) << 1
}
