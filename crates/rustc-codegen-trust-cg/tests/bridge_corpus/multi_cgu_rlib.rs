// The library half of an rlib + downstream-binary pair (crate `multi_cgu_rlib`).
// Its modules use the same `#[inline]` core items as the binary's, and it
// exports `#[inline]` and generic items the binary instantiates in its own
// CGUs: with several codegen units on both sides, both crates carry
// `Internal` copies of one mangled name into one static link.

/// Instantiated by every downstream CGU that calls it.
#[inline]
pub fn spread(x: u64, y: u64) -> u64 {
    let lo = Ord::min(x, y);
    let hi = Ord::max(x, y);
    (hi - lo).wrapping_mul(3) ^ (PartialOrd::le(&x, &y) as u64)
}

/// A generic the binary instantiates with its own types.
#[inline]
pub fn count_le<T: PartialOrd + Copy>(xs: &[T], bound: T) -> usize {
    let mut n = 0;
    let mut i = 0;
    while i < xs.len() {
        if PartialOrd::le(&xs[i], &bound) {
            n += 1;
        }
        i += 1;
    }
    n
}

pub mod left {
    #[inline(never)]
    pub fn score(x: u64, y: u64) -> u64 {
        super::spread(x, y) + PartialOrd::lt(&x, &y) as u64 * 1000
    }
}

pub mod right {
    #[inline(never)]
    pub fn widen(x: i8) -> i64 {
        i64::from(x) * 5 + super::spread(x as u8 as u64, 9) as i64
    }
}

pub mod table {
    #[inline]
    fn inc(x: u64) -> u64 {
        x + 1
    }
    #[inline]
    fn le_ten(x: u64) -> u64 {
        PartialOrd::le(&x, &10) as u64
    }
    pub static OPS: [fn(u64) -> u64; 2] = [inc, le_ten];
    #[inline(never)]
    pub fn run(x: u64) -> u64 {
        let ops = std::hint::black_box(&OPS);
        ops[0](x) * 10 + ops[1](x)
    }
}
