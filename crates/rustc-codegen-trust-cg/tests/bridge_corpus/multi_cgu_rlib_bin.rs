// The binary half of the rlib + downstream-binary pair: links
// `multi_cgu_rlib` and calls its exported, `#[inline]` and generic items from
// several modules, each also using the `#[inline]` core items the library's
// modules use.
use std::hint::black_box as bb;

mod one {
    #[inline(never)]
    pub fn go(x: u64, y: u64) -> u64 {
        multi_cgu_rlib::spread(x, y) + PartialOrd::le(&y, &x) as u64
    }
}

mod two {
    #[inline(never)]
    pub fn go(x: i8) -> i64 {
        i64::from(x) - multi_cgu_rlib::right::widen(x)
    }
}

mod three {
    #[inline(never)]
    pub fn go(xs: &[u64], b: u64) -> usize {
        multi_cgu_rlib::count_le(xs, b) + multi_cgu_rlib::count_le(&[1i32, 5, 9], 5)
    }
}

mod four {
    #[inline(never)]
    pub fn go(x: u64) -> u64 {
        let f: fn(u64, u64) -> u64 = multi_cgu_rlib::spread;
        std::hint::black_box(f)(x, 4)
            + multi_cgu_rlib::table::run(x)
            + multi_cgu_rlib::left::score(x, 2)
    }
}

fn main() {
    println!("one {} {}", one::go(bb(3), bb(11)), one::go(bb(11), bb(3)));
    println!("two {} {}", two::go(bb(-7)), two::go(bb(100)));
    let xs = [bb(4u64), 12, 7, 30, 10];
    println!("three {}", three::go(&xs, bb(10)));
    println!("four {} {}", four::go(bb(6)), four::go(bb(20)));
    println!(
        "lib {} {}",
        multi_cgu_rlib::left::score(bb(5), bb(1)),
        multi_cgu_rlib::table::run(bb(10))
    );
}
