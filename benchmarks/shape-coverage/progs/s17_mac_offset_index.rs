// mac_reg_block / mac_row_unroll: the inner index is `j + 1`, not `j`. Both
// passes pinned it with `same_as(jc, iv)`, and `strip_copies` resolved the
// induction variable through its LATCH copy to `j + 1` — so `j + 1` compared
// equal to `j` and the spliced kernel addressed everything one element off.
// BOTH passes do this independently: disabling either alone still miscompiles,
// which is why a single-pass bisect misattributes it to `cmpbr` (the pass that
// normalises the branch into the form they recognise).
// Was: LLVM 2, trust-cg 121 at O2/O3 — 121 being the answer for plain `j`.
use std::hint::black_box as bb;
const N: usize = 8;
const L: usize = N * N + 1;

#[inline(never)]
fn kernel(seed: u64) -> i64 {
    let mut a = [0i64; L];
    let mut b = [0i64; L];
    let mut c = [0i64; L];
    let mut t = 0usize;
    while t < L {
        a[t] = (t as i64) + seed as i64;
        b[t] = (t as i64) ^ 3;
        t += 1;
    }
    let mut i = 0usize;
    while i < N {
        let mut k = 0usize;
        while k < N {
            let aik = a[i * N + k];
            let mut j = 0usize;
            while j < N {
                let jj = j + 1;
                c[i * N + jj] = c[i * N + jj].wrapping_add(aik.wrapping_mul(b[k * N + jj]));
                j = jj;
            }
            k += 1;
        }
        i += 1;
    }
    let mut s: i64 = 0;
    let mut u = 0usize;
    while u < L {
        s = s.wrapping_add(c[u].wrapping_mul(u as i64 + 1));
        u += 1;
    }
    s
}

fn main() {
    let s = kernel(bb(3u64));
    std::process::exit((((s as u64) % 251) as u8) as i32);
}
