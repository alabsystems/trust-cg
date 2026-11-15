// A multi-module program whose modules share `#[inline]` core and local
// items, so a build with several codegen units gives several CGUs their own
// `Internal` copy of one symbol: called directly, taken as a function
// pointer, stored in a static table, reached through a vtable and through a
// closure. Every value is printed, so a copy bound to the wrong body shows.
use std::hint::black_box as bb;

/// A local `#[inline]` helper every module instantiates for itself.
#[inline]
pub fn mix(x: u64, y: u64) -> u64 {
    x.rotate_left(7) ^ y.wrapping_mul(0x9e37_79b9_7f4a_7c15)
}

pub trait Shape {
    fn area(&self) -> u64;
    #[inline]
    fn scaled(&self, k: u64) -> u64 {
        self.area().wrapping_mul(k)
    }
}

pub struct Rect(pub u64, pub u64);
pub struct Square(pub u64);

impl Shape for Rect {
    #[inline]
    fn area(&self) -> u64 {
        self.0.wrapping_mul(self.1)
    }
}

impl Shape for Square {
    #[inline]
    fn area(&self) -> u64 {
        self.0.wrapping_mul(self.0)
    }
}

mod cmp {
    #[inline(never)]
    pub fn order(x: u64, y: u64) -> u64 {
        let le = PartialOrd::le(&x, &y) as u64;
        let lt = PartialOrd::lt(&x, &y) as u64;
        let m = Ord::max(x, y) - Ord::min(x, y);
        le * 100 + lt * 10 + m + super::mix(x, y) % 7
    }
}

mod conv {
    #[inline(never)]
    pub fn widen(x: i8, y: u8) -> i64 {
        i64::from(x) * 3 + i64::from(u32::from(y)) + (super::mix(y as u64, 1) % 5) as i64
    }
}

mod arith {
    #[inline(never)]
    pub fn checked(x: u32, y: u32) -> u32 {
        let a = x.checked_add(y).unwrap_or(7);
        let b = x.saturating_sub(y);
        let c = x.wrapping_mul(y);
        a ^ b ^ c ^ (PartialOrd::le(&x, &y) as u32)
    }
}

mod pointers {
    /// The addresses of `#[inline]` items, taken in this module's CGU.
    #[inline(never)]
    pub fn by_pointer(x: u64, y: u64) -> u64 {
        let le: fn(&u64, &u64) -> bool = PartialOrd::le;
        let lt: fn(&u64, &u64) -> bool = PartialOrd::lt;
        let m: fn(u64, u64) -> u64 = super::mix;
        let f = std::hint::black_box(le);
        let g = std::hint::black_box(lt);
        let h = std::hint::black_box(m);
        (f(&x, &y) as u64) + 2 * (g(&y, &x) as u64) + h(x, y) % 11
    }
}

mod table {
    #[inline]
    fn double(x: i64) -> i64 {
        x * 2
    }
    #[inline]
    fn widen_neg(x: i64) -> i64 {
        -i64::from(x as i8)
    }
    static OPS: [fn(i64) -> i64; 2] = [double, widen_neg];
    #[inline(never)]
    pub fn apply(x: i64) -> i64 {
        let ops = std::hint::black_box(&OPS);
        ops[0](x) + ops[1](x)
    }
}

mod shapes {
    use super::{Rect, Shape, Square};
    #[inline(never)]
    fn scaled_dyn(shape: &dyn Shape, k: u64) -> u64 {
        shape.scaled(k)
    }
    #[inline(never)]
    pub fn total(k: u64) -> u64 {
        let r = Rect(std::hint::black_box(3), 4);
        let s = Square(std::hint::black_box(5));
        scaled_dyn(&r, k).wrapping_add(scaled_dyn(&s, k))
    }
}

mod closures {
    #[inline]
    fn apply<F: Fn(u64) -> u64>(f: F, x: u64) -> u64 {
        f(x)
    }
    #[inline(never)]
    pub fn run(x: u64, y: u64) -> u64 {
        let add = |v: u64| v + y;
        let cmp = |v: u64| PartialOrd::lt(&v, &y) as u64;
        apply(add, x) * 10 + apply(cmp, x) + super::mix(x, y) % 3
    }
}

mod slices {
    #[inline(never)]
    pub fn fold(xs: &[u32]) -> u32 {
        let mut acc = 0u32;
        let mut max = 0u32;
        for &x in xs {
            acc = acc.wrapping_add(x);
            max = Ord::max(max, x);
        }
        acc ^ max ^ (PartialOrd::le(&acc, &max) as u32)
    }
}

fn main() {
    println!(
        "cmp {} {}",
        cmp::order(bb(3), bb(9)),
        cmp::order(bb(9), bb(3))
    );
    println!(
        "conv {} {}",
        conv::widen(bb(-4), bb(200)),
        conv::widen(bb(127), bb(1))
    );
    println!(
        "arith {} {}",
        arith::checked(bb(7), bb(5)),
        arith::checked(bb(u32::MAX), bb(2))
    );
    println!(
        "ptr {} {}",
        pointers::by_pointer(bb(2), bb(8)),
        pointers::by_pointer(bb(8), bb(2))
    );
    println!("table {} {}", table::apply(bb(21)), table::apply(bb(-3)));
    println!("shapes {}", shapes::total(bb(3)));
    println!(
        "closures {} {}",
        closures::run(bb(4), bb(6)),
        closures::run(bb(6), bb(4))
    );
    let xs = [bb(4u32), 9, 1, 30, 2];
    println!("slices {}", slices::fold(&xs));
    println!("mix {}", mix(bb(1), bb(2)) % 1000);
}
