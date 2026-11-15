// CORPUS FIXTURE — a CELLED entry-argument index (the W2 regression). `&raw const i`
// makes `i` a CELLED local (`compute_scalar_cell_locals`), so `i = 5` lands in the
// cell and never rebinds `i`'s SSA value. The `Index(i)` readers
// (`resolve_index_value`, `lower_slice_deref_element_load`, ...) read the index
// through `value_for_scalar_binding`, whose entry-argument fallback is the
// INCOMING parameter: trust-cg @ 874c4b3ef returned a[1] = 5 at O0/O2/O3 — a
// SILENT wrong value. The readers now load a celled index from its cell
// (`index_local_value`). Custom MIR because rustc's own MIR copies an index into a
// fresh temporary first; the same shape arises whenever a loop-carried index is
// celled (the SSA-071 cell retry). Correct exit = LLVM oracle (17 at O0/O2/O3).
#![no_std]
#![no_main]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::hint::black_box;
use core::intrinsics::mir::*;
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
fn f(a: &[u64; 8], i: usize) -> u64 {
    mir! {
        let p: *const usize;
        {
            p = &raw const i;
            i = 5;
            RET = (*a)[i];
            Return()
        }
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = black_box([3u64, 5, 7, 11, 13, 17, 19, 23]);
    let r = f(&a, black_box(1));
    (r % 251) as i32
}
