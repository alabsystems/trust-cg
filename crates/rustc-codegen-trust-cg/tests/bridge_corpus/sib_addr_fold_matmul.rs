// CORPUS FIXTURE (OPT-7 / LEVER 1) — verified x86 base+index*scale (SIB)
// address-mode fold on 8-byte array LOADS and STORES in a hot loop.
//
// Generic array indexing (`c[i] = c[i] + a * b[j]`) lowers, per element, to a
// separate scale-multiply of the index, an add to the base, and a plain `[reg]`
// load/store. The x86 SIB fold (`x86_peephole::sib_addr_fold_run_on_block`)
// collapses that `imul index,{1,2,4,8}` (or `shl`) + `add base` + `mov [reg]`
// into a single `mov (%base,%index,scale)` operand (MovRMSib/MovMRSib), the
// same effective address LLVM forms. This fixture pins that the fold is
// value-preserving: the address it computes (`base + index*scale`) must be
// byte-exact, so any wrong scale/base/index/disp would corrupt the running sum
// and diverge from LLVM.
//
// The arrays are `black_box`d so the indices are genuine runtime values (real
// scaled-index loads/stores, not const-folded), and BOTH read (`b[j]`, `c[i]`)
// and write (`c[i] = ..`) go through the folded addressing mode. The result is
// reduced mod 126 to a stable exit code oracle.
//
// Hand-computed oracle:
//   `row_update` is called once per outer i (i in 0..4), each call doing
//   `c[j] += a_i * b[j]` for all j, with a_i = i+1. So after all 4 calls each
//   c[j] = b[j] * sum_i(a_i) = b[j] * (1+2+3+4) = b[j] * 10.
//   b = [2,3,4,5] -> c = [20,30,40,50]; sum(c) = 140; 140 % 126 = 14 -> exit 14.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[inline(never)]
fn row_update(c: &mut [i64], a: i64, b: &[i64], n: usize) {
    let mut j = 0usize;
    while j < n {
        // c[j] += a * b[j]  — b[j] is a scaled-index LOAD; c[j] is a
        // scaled-index LOAD then STORE. All 8-byte, index = j (runtime).
        c[j] = c[j].wrapping_add(a.wrapping_mul(b[j]));
        j += 1;
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let n: usize = black_box(4);
    let b: [i64; 4] = [black_box(2i64), black_box(3), black_box(4), black_box(5)];
    let mut c: [i64; 4] = [black_box(0i64), black_box(0), black_box(0), black_box(0)];

    // c[i] accumulates a[i] * sum(b) via the inner loop; a[i] = i + 1.
    let mut i = 0usize;
    while i < n {
        let a = black_box((i as i64) + 1);
        row_update(&mut c[..], a, &b[..], n);
        i += 1;
    }

    let mut sum: i64 = 0;
    let mut k = 0usize;
    while k < n {
        sum = sum.wrapping_add(c[k]);
        k += 1;
    }
    (sum.rem_euclid(126)) as i32
}
