// CORPUS FIXTURE — a CELLED NON-argument index local. `&raw const j` cells `j`,
// so `j = 5` lands in the cell and never binds `j`'s SSA value; an `Index(j)`
// reader that reads `value_for_scalar_binding(j)` gets the synthetic,
// never-defined `ValueId(j)`: trust-cg @ 874c4b3ef failed closed at O0/O2/O3
// ([TCG-SSA-071] "value ValueId(4) ... never defined"). The readers now load a
// celled index from its cell (`index_local_value`), so this compiles. Custom MIR
// for the same reason as `celled_index_arg_custom_mir.rs`. Correct exit = LLVM
// oracle (17 at O0/O2/O3).
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
        let j: usize;
        {
            j = i;
            p = &raw const j;
            j = 5;
            RET = (*a)[j];
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
