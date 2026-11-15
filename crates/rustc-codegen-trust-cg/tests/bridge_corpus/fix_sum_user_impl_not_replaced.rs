// CORPUS FIXTURE — a USER `impl Sum` runs its OWN body.
//
// `Meters` and `Plain` are single-`u64` newtypes, so the bridge's type map collapses
// them to a scalar, and until 2026-09-27 the modeled `sum` loop admitted them and
// replaced the user's `sum` body with a bare add. Measured on the unpatched base:
// `Meters` (a max-with-1000) printed `6` where LLVM prints `1000` — a silent
// miscompile — while `Plain` (which merely adds) happened to MATCH. The impl-identity
// gate (`std_sum_product_arith`) now leaves every non-core impl alone and the
// interception STEPS ASIDE to the real `Iterator::sum` (`std_reduction_falls_through`),
// so BOTH run the user's own code: `Meters` is fixed and `Plain` keeps working.
//
// HOW IT FAILS IF THE CHANGE IS REVERTED: it COMPILES and the `Meters` line DIVERGES
// from LLVM — a hard failure. A change that REFUSED user impls instead would withdraw
// `Plain`, which worked on the base: a `Must` row of
// `sum_product_reduction_differential`, so that fails too.
use std::iter::Sum;

#[derive(Clone, Copy)]
struct Meters(u64);
impl Sum for Meters {
    fn sum<I: Iterator<Item = Meters>>(iter: I) -> Meters {
        let mut m = 1000;
        for x in iter {
            if x.0 > m {
                m = x.0;
            }
        }
        Meters(m)
    }
}

#[derive(Clone, Copy)]
struct Plain(u64);
impl Sum for Plain {
    fn sum<I: Iterator<Item = Plain>>(iter: I) -> Plain {
        Plain(iter.map(|p| p.0).sum())
    }
}

#[inline(never)]
fn meters(v: &[u64]) -> u64 {
    let s: Meters = v.iter().map(|&x| Meters(x)).sum();
    s.0
}
#[inline(never)]
fn plain(v: &[u64]) -> u64 {
    let s: Plain = v.iter().map(|&x| Plain(x)).sum();
    s.0
}

fn main() {
    println!("{} {}", meters(&[1, 2, 3]), meters(&[5000, 7]));
    println!("{} {}", plain(&[1, 2, 3]), plain(&[]));
}
