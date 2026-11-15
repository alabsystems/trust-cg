// Dominated runtime-index bounds-check differential fixture.
// The bridge retains the original MIR bounds assertions. Loop guards and the
// last valid array index must produce the same observable result as LLVM.
// The dedicated dom_bounds_refutation_x86 test owns out-of-bounds trap checks;
// the looping panic handler here is unsuitable as a trap oracle.
// Expected exit: 44 untouched elements plus 4 boundary writes = 48.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut comp = [0u8; 64];

    // (a) The sieve marking loop: runtime start + runtime stride, guard
    //     `q < 64` dominating the `comp[q]` write check (Ult, K == len).
    let p = black_box(3usize);
    let mut q = black_box(4usize);
    while q < 64 {
        comp[q] = 1;
        q += p;
    }

    // (b) The counting loop: guard `i < 64` dominating the `comp[i]` read
    //     check.
    let mut count = 0i32;
    let mut i = black_box(0usize);
    while i < 64 {
        if comp[i] == 0 {
            count += 1;
        }
        i += 1;
    }

    // (c) An at-boundary `<=` guard: `j <= 63` dominates `comp[j]` (Ule,
    //     K == len - 1, discharges) and the loop's last write touches index
    //     63 — the LAST valid element.
    let mut j = black_box(60usize);
    while j <= 63 {
        comp[j] = 2;
        j += 1;
    }

    // (d) Recount so the boundary writes are observable.
    let mut c2 = 0i32;
    let mut k = black_box(0usize);
    while k < 64 {
        if comp[k] == 2 {
            c2 += 1;
        }
        k += 1;
    }

    count + c2
}
