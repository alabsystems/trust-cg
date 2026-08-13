// CORPUS FIXTURE (OPT-3a / LEVER 2) — verified x86 induction-variable
// strength reduction on a matmul-like nested loop with a NON-SIB stride.
//
// `a[i*N + k]`-style addressing with N = 24 lowers to a per-iteration
// `imul iv, 24` (24 is not a SIB scale, so the OPT-7 address fold cannot
// touch it) that sits on the critical path of the INNER loop even though it
// only changes with the OUTER induction variable — LICM cannot hoist it
// because x86 `imul` writes RFLAGS. The strength-reduction pass
// (`trust_cg_opt::x86_strength_reduce`) replaces it with a preheader seed +
// per-outer-iteration add recurrence, gated per (width, step, stride) on the
// solver-discharged identity `(iv+step)*s == iv*s + s*step (mod 2^64)`.
//
// This fixture pins that the rewrite is VALUE-preserving end-to-end: the
// row/column products feed a running checksum reduced mod 126, so a wrong
// seed, wrong advance placement, wrong stride scaling, or a clobbered flags
// state (the advance is inserted right after the IV update, before the loop
// back-edge compare) diverges from LLVM immediately.
//
// It value-oracles BOTH canonicalization shapes the pass admits:
//   * the k*N multiply reads its IV through single-def MovRR renames (the
//     copy-chain rule), and
//   * the i*N multiply reads the OUTER IV `i` through a MULTI-DEF
//     PASS-THROUGH block param of the inner loops (phi elimination threads
//     `i` through the k/j loops with one edge-copy def per header
//     predecessor), exercising the pass-through-param canonicalization
//     (module doc P1-P3: all-defs-are-copies, must-cover dataflow, per-def
//     source resolution). A staleness bug there (param read after the outer
//     IV update, uncovered path) would shift a whole row of products and
//     diverge the order-sensitive checksum.
//
// The matrices are black_box-seeded so every index and element is a genuine
// runtime value; N stays a compile-time constant (the constant-stride shape
// the pass admits).
//
// Hand-computed oracle: with N=6, a[i*N+k] = (i*N+k) % 7, b[k*N+j] =
// (k*N+j) % 5 + 1, c accumulates sum_k a_ik*b_kj over all i,j; the checksum
// folds every c element. The reference run (LLVM) defines the expected exit
// code; the differential harness compares bridge vs LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

const N: usize = 6;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let seed = black_box(1usize);
    let mut a = [0i64; N * N];
    let mut b = [0i64; N * N];
    let mut idx = 0usize;
    while idx < N * N {
        a[idx] = ((idx * seed) % 7) as i64;
        b[idx] = ((idx * seed) % 5 + 1) as i64;
        idx += 1;
    }

    // The kernel: c[i*N + j] += a[i*N + k] * b[k*N + j]. The i*N and k*N
    // multiplies are the strength-reduction candidates (stride 24 bytes-wise;
    // element stride N=6 times 8-byte scale — the element-index imul by 6 is
    // itself non-SIB).
    let mut c = [0i64; N * N];
    let mut i = 0usize;
    while i < N {
        let mut k = 0usize;
        while k < N {
            let aik = a[i * N + k];
            let mut j = 0usize;
            while j < N {
                c[i * N + j] = c[i * N + j].wrapping_add(aik.wrapping_mul(b[k * N + j]));
                j += 1;
            }
            k += 1;
        }
        i += 1;
    }

    // Checksum every element (order-sensitive fold: catches element
    // misplacement, not just wrong totals).
    let mut sum: i64 = 0;
    let mut t = 0usize;
    while t < N * N {
        sum = sum.wrapping_mul(3).wrapping_add(c[t]);
        t += 1;
    }
    (sum.rem_euclid(126)) as i32
}
