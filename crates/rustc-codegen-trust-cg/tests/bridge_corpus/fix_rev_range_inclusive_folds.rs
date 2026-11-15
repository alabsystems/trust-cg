// CORPUS FIXTURE — `Rev<RangeInclusive<T>>` folds, for
// `rev_range_inclusive_fold_differential.rs`. One CASE per run (`CASE=<name>`,
// read through libc), each printing integers on one line or panicking. Every
// reduction is an `#[inline(never)]` callee over `black_box` bounds, so it is a
// real call over runtime bounds at every opt level.
//
// Before the reversed inclusive walk was modeled, every case here failed closed
// on the bridge: at -O0/-O1 the `.rev()` constructor refused (`rev() over a
// RangeInclusive is not modeled`), at -O2/-O3 the inlined
// `<RangeInclusive<T> as DoubleEndedIterator>::rfold` reached
// `RangeInclusiveIteratorImpl::spec_try_rfold`, whose body does not lower
// (`[TCG-RET-UNBOUND]`). Printing sticks to integers: `{:?}` of an `Option`,
// tuple, `Vec` or range, and `RangeInclusive::start()`, are separate bridge
// limitations this fixture must not depend on.
use std::hint::black_box as bb;
use std::ops::RangeInclusive;

#[inline(never)]
fn sum_u64(a: u64, n: u64) -> u64 {
    (a..=n).rev().sum()
}
#[inline(never)]
fn prod_u64(a: u64, n: u64) -> u64 {
    (a..=n).rev().product()
}
#[inline(never)]
fn sum_i32(a: i32, n: i32) -> i32 {
    (a..=n).rev().sum()
}
#[inline(never)]
fn prod_i32(a: i32, n: i32) -> i32 {
    (a..=n).rev().product()
}
#[inline(never)]
fn sum_usize(a: usize, n: usize) -> usize {
    (a..=n).rev().sum()
}
#[inline(never)]
fn prod_usize(a: usize, n: usize) -> usize {
    (a..=n).rev().product()
}
#[inline(never)]
fn sum_u8(a: u8, n: u8) -> u8 {
    (a..=n).rev().sum()
}
#[inline(never)]
fn prod_u8(a: u8, n: u8) -> u8 {
    (a..=n).rev().product()
}
#[inline(never)]
fn sum_i8(a: i8, n: i8) -> i8 {
    (a..=n).rev().sum()
}
/// Order-sensitive: a different visiting order gives a different digest.
#[inline(never)]
fn digest_u64(a: u64, n: u64) -> u64 {
    (a..=n).rev().fold(7u64, |acc, x| acc.wrapping_mul(31).wrapping_add(x))
}
#[inline(never)]
fn digest_u8(a: u8, n: u8) -> u32 {
    (a..=n).rev().fold(0u32, |acc, x| acc.wrapping_mul(7).wrapping_add(u32::from(x)))
}
#[inline(never)]
fn digest_i8(a: i8, n: i8) -> i64 {
    (a..=n).rev().fold(1i64, |acc, x| acc.wrapping_mul(3).wrapping_add(i64::from(x)))
}
#[inline(never)]
fn each_i64(a: i64, n: i64) {
    (a..=n).rev().for_each(|x| print!("{x},"));
    println!();
}
#[inline(never)]
fn each_u8(a: u8, n: u8) -> u32 {
    let mut seen = 0u32;
    (a..=n).rev().for_each(|x| seen = seen.wrapping_mul(5).wrapping_add(u32::from(x)));
    seen
}
/// A partly consumed range: `exhausted` and both endpoints carry over.
#[inline(never)]
fn sum_after_next(mut r: RangeInclusive<u64>, k: usize) -> u64 {
    for _ in 0..k {
        r.next();
    }
    r.rev().sum()
}
#[inline(never)]
fn prod_after_next_back(mut r: RangeInclusive<u64>, k: usize) -> u64 {
    for _ in 0..k {
        r.next_back();
    }
    r.rev().product()
}

/// `Option` as a printable integer (`None` -> `NONE`).
const NONE: i64 = -999;
fn o<T: Into<i64>>(v: Option<T>) -> i64 {
    match v {
        Some(x) => x.into(),
        None => NONE,
    }
}

/// The other consumers a reversed inclusive chain reaches.
#[inline(never)]
fn count_rev(a: u32, n: u32) -> usize {
    (a..=n).rev().count()
}
/// u64, not u32: an `Option<u32>` accumulator hits an unrelated by-value
/// `Option<u32>` argument-ABI refusal on the general path at -O2/-O3.
#[inline(never)]
fn last_rev(a: u64, n: u64) -> Option<u64> {
    (a..=n).rev().last()
}
#[inline(never)]
fn any_rev(a: u32, n: u32) -> bool {
    (a..=n).rev().any(|x| x == 4)
}
#[inline(never)]
fn all_rev(a: u32, n: u32) -> bool {
    (a..=n).rev().all(|x| x > 2)
}
#[inline(never)]
fn nth_rev(a: u32, n: u32, k: usize) -> Option<u32> {
    (a..=n).rev().nth(k)
}
#[inline(never)]
fn max_rev(a: i32, n: i32) -> Option<i32> {
    (a..=n).rev().max()
}
#[inline(never)]
fn min_rev(a: i32, n: i32) -> Option<i32> {
    (a..=n).rev().min()
}
#[inline(never)]
fn find_rev(a: u32, n: u32) -> Option<u32> {
    (a..=n).rev().find(|x| x % 7 == 3)
}
#[inline(never)]
fn position_rev(a: u32, n: u32) -> Option<usize> {
    (a..=n).rev().position(|x| x % 5 == 1)
}
#[inline(never)]
fn rfind_incl(a: u32, n: u32) -> Option<u32> {
    (a..=n).rfind(|x| x % 4 == 1)
}
#[inline(never)]
fn map_rev(a: u64, n: u64) -> u64 {
    (a..=n).rev().map(|x| x * 3 + 1).sum()
}
#[inline(never)]
fn filter_rev(a: u64, n: u64) -> u64 {
    (a..=n).rev().filter(|x| x % 3 != 0).sum()
}
#[inline(never)]
fn take_rev(a: u64, n: u64) -> u64 {
    (a..=n).rev().take(3).fold(0, |acc, x| acc.wrapping_mul(100).wrapping_add(x))
}
#[inline(never)]
fn skip_rev(a: u64, n: u64) -> u64 {
    (a..=n).rev().skip(2).fold(0, |acc, x| acc.wrapping_mul(100).wrapping_add(x))
}
#[inline(never)]
fn rfold_incl(a: u64, n: u64) -> u64 {
    (a..=n).rfold(0, |acc, x| acc.wrapping_mul(10).wrapping_add(x))
}
#[inline(never)]
fn rev_rev(a: u64, n: u64) -> u64 {
    (a..=n).rev().rev().fold(0, |acc, x| acc.wrapping_mul(10).wrapping_add(x))
}
#[inline(never)]
fn collect_rev(a: u16, n: u16) -> u64 {
    let v: Vec<u16> = (a..=n).rev().collect();
    let mut digest = v.len() as u64;
    for x in &v {
        digest = digest.wrapping_mul(70001).wrapping_add(u64::from(*x));
    }
    digest
}
#[inline(never)]
fn for_loop_rev(a: i16, n: i16) -> i64 {
    let mut s = 0i64;
    for x in (a..=n).rev() {
        s = s * 7 + i64::from(x);
    }
    s
}
/// `map` with an EFFECT: the effects must run in rfold's back-to-front order.
#[inline(never)]
fn map_effect(n: u64) -> u64 {
    (0..=n)
        .rev()
        .map(|x| {
            print!("{x} ");
            x * 3
        })
        .sum()
}
/// A short-circuit over a BORROWED range: the state it leaves is observable.
#[inline(never)]
fn rfind5_in(r: &mut RangeInclusive<u64>) -> Option<u64> {
    r.rfind(|&x| x == 5)
}
#[inline(never)]
fn rfind3_in(r: &mut RangeInclusive<u64>) -> Option<u64> {
    r.rfind(|&x| x == 3)
}
#[inline(never)]
fn rfind1_in(r: &mut RangeInclusive<u64>) -> Option<u64> {
    r.rfind(|&x| x == 1)
}
#[inline(never)]
fn rfind9_in(r: &mut RangeInclusive<u64>) -> Option<u64> {
    r.rfind(|&x| x == 9)
}
#[inline(never)]
fn rfind_odd_in(r: &mut RangeInclusive<i8>) -> Option<i8> {
    r.rfind(|&x| x % 2 != 0)
}

#[inline(never)]
fn print_consumers_u32(a: u32, n: u32) {
    println!(
        "{} {} {} {} {} {} {} {} {} {}",
        count_rev(bb(a), bb(n)),
        o(last_rev(bb(u64::from(a)), bb(u64::from(n))).map(|x| x as i64)),
        u8::from(any_rev(bb(a), bb(n))),
        u8::from(all_rev(bb(a), bb(n))),
        o(nth_rev(bb(a), bb(n), bb(0))),
        o(nth_rev(bb(a), bb(n), bb(2))),
        o(nth_rev(bb(a), bb(n), bb(30))),
        o(find_rev(bb(a), bb(n))),
        o(position_rev(bb(a), bb(n)).map(|p| p as u32)),
        o(rfind_incl(bb(a), bb(n)))
    );
}
#[inline(never)]
fn print_consumers_u64(a: u64, n: u64) {
    println!(
        "{} {} {} {} {} {}",
        map_rev(bb(a), bb(n)),
        filter_rev(bb(a), bb(n)),
        take_rev(bb(a), bb(n)),
        skip_rev(bb(a), bb(n)),
        rfold_incl(bb(a), bb(n)),
        rev_rev(bb(a), bb(n))
    );
}
/// The range left behind: `is_empty`, how many items remain, and what `next` /
/// `next_back` yield from it.
fn print_state(r: &mut RangeInclusive<u64>, found: i64) {
    let empty = u8::from(r.is_empty());
    let left = r.clone().count();
    let next = o(r.next().map(|x| x as i64));
    let back = o(r.next_back().map(|x| x as i64));
    println!("{found} {empty} {left} {next} {back}");
}

unsafe extern "C" {
    fn getenv(name: *const std::ffi::c_char) -> *const std::ffi::c_char;
}

/// The `CASE` selector, read through libc (no `String` / `OsString` needed).
fn case() -> &'static [u8] {
    let value = unsafe { getenv(c"CASE".as_ptr()) };
    if value.is_null() { b"" } else { unsafe { std::ffi::CStr::from_ptr(value) }.to_bytes() }
}

fn main() {
    match case() {
        // empty (5..=4), single (n..=n), zero, ordinary
        b"sum_u64" => println!(
            "{} {} {} {} {}",
            sum_u64(bb(1), bb(10)),
            sum_u64(bb(5), bb(4)),
            sum_u64(bb(7), bb(7)),
            sum_u64(bb(0), bb(0)),
            sum_u64(bb(u64::MAX), bb(u64::MAX))
        ),
        // u64::MAX-1 + u64::MAX: overflows (panics under overflow checks)
        b"sum_u64_ovf" => println!("{}", sum_u64(bb(u64::MAX - 1), bb(u64::MAX))),
        b"prod_u64" => println!(
            "{} {} {} {}",
            prod_u64(bb(1), bb(10)),
            prod_u64(bb(5), bb(4)),
            prod_u64(bb(7), bb(7)),
            prod_u64(bb(0), bb(20))
        ),
        // 25! does not fit in a u64
        b"prod_u64_ovf" => println!("{}", prod_u64(bb(1), bb(25))),
        b"sum_i32" => println!(
            "{} {} {} {}",
            sum_i32(bb(-5), bb(10)),
            sum_i32(bb(5), bb(-4)),
            sum_i32(bb(-7), bb(-7)),
            sum_i32(bb(i32::MIN), bb(i32::MIN))
        ),
        b"sum_i32_ovf" => println!("{}", sum_i32(bb(i32::MAX - 1), bb(i32::MAX))),
        b"prod_i32" => println!(
            "{} {} {}",
            prod_i32(bb(-4), bb(-1)),
            prod_i32(bb(-3), bb(3)),
            prod_i32(bb(2), bb(1))
        ),
        // 13! does not fit in an i32 (12! does)
        b"prod_i32_ovf" => println!("{}", prod_i32(bb(1), bb(13))),
        b"sum_usize" => println!(
            "{} {} {} {}",
            sum_usize(bb(1), bb(100)),
            sum_usize(bb(3), bb(2)),
            prod_usize(bb(1), bb(12)),
            prod_usize(bb(9), bb(9))
        ),
        // full width, no overflow: 0..=20
        b"sum_u8" => println!("{} {}", sum_u8(bb(0), bb(20)), sum_u8(bb(255), bb(255))),
        // full width 0..=255: 255 + 254 overflows a u8 on the FIRST add
        b"sum_u8_full" => println!("{}", sum_u8(bb(0), bb(255))),
        b"prod_u8" => println!("{} {}", prod_u8(bb(1), bb(5)), prod_u8(bb(0), bb(0))),
        // 0..=255 back to front: 255 * 254 overflows before the 0 factor is
        // reached (a front-to-back walk would multiply by 0 first and never
        // overflow) — the order is observable under overflow checks.
        b"prod_u8_full" => println!("{}", prod_u8(bb(0), bb(255))),
        b"sum_i8" => println!("{} {}", sum_i8(bb(-3), bb(3)), sum_i8(bb(-128), bb(-128))),
        // full width -128..=127: 127 + 126 overflows on the first add
        b"sum_i8_full" => println!("{}", sum_i8(bb(-128), bb(127))),
        b"digest" => println!(
            "{} {} {} {} {} {}",
            digest_u64(bb(1), bb(9)),
            digest_u64(bb(5), bb(4)),
            digest_u64(bb(3), bb(3)),
            digest_u64(bb(u64::MAX - 3), bb(u64::MAX)),
            digest_u8(bb(0), bb(255)),
            digest_u8(bb(250), bb(255))
        ),
        b"digest_i8" => println!(
            "{} {} {}",
            digest_i8(bb(-128), bb(127)),
            digest_i8(bb(-128), bb(-125)),
            digest_i8(bb(127), bb(127))
        ),
        b"for_each" => {
            each_i64(bb(1), bb(6));
            each_i64(bb(4), bb(3));
            each_i64(bb(-2), bb(-2));
            each_i64(bb(i64::MAX - 1), bb(i64::MAX));
            each_i64(bb(i64::MIN), bb(i64::MIN + 1));
            println!("{} {}", each_u8(bb(0), bb(255)), each_u8(bb(9), bb(8)));
        }
        b"exhausted" => println!(
            "{} {} {} {} {} {} {}",
            sum_after_next(bb(5..=5), bb(1)),
            sum_after_next(bb(1..=4), bb(2)),
            sum_after_next(bb(1..=4), bb(3)),
            sum_after_next(bb(1..=4), bb(4)),
            prod_after_next_back(bb(2..=6), bb(1)),
            prod_after_next_back(bb(3..=3), bb(1)),
            prod_after_next_back(bb(2..=6), bb(4))
        ),
        b"consumers" => {
            print_consumers_u32(1, 6);
            print_consumers_u32(5, 4);
            print_consumers_u32(3, 3);
            print_consumers_u32(0, 0);
            print_consumers_u32(1, 20);
            println!(
                "{} {} {} {} {} {}",
                o(max_rev(bb(-3), bb(4))),
                o(min_rev(bb(-3), bb(4))),
                o(max_rev(bb(2), bb(1))),
                o(min_rev(bb(2), bb(1))),
                o(max_rev(bb(-5), bb(-5))),
                o(min_rev(bb(i32::MIN), bb(i32::MIN + 1)))
            );
            print_consumers_u64(1, 9);
            print_consumers_u64(4, 3);
            print_consumers_u64(4, 4);
            print_consumers_u64(1, 20);
            println!(
                "{} {} {}",
                collect_rev(bb(1), bb(5)),
                collect_rev(bb(65533), bb(65535)),
                collect_rev(bb(9), bb(8))
            );
            println!(
                "{} {} {}",
                for_loop_rev(bb(-3), bb(4)),
                for_loop_rev(bb(i16::MAX - 2), bb(i16::MAX)),
                for_loop_rev(bb(1), bb(0))
            );
        }
        b"map_effect" => {
            let a = map_effect(bb(3));
            let b = map_effect(bb(0));
            println!("= {a} = {b}");
        }
        b"state_after" => {
            let mut r = bb(1u64..=5);
            let f = o(rfind5_in(&mut r).map(|x| x as i64));
            print_state(&mut r, f);
            let mut r = bb(1u64..=5);
            let f = o(rfind3_in(&mut r).map(|x| x as i64));
            print_state(&mut r, f);
            let mut r = bb(1u64..=5);
            let f = o(rfind1_in(&mut r).map(|x| x as i64));
            print_state(&mut r, f);
            let mut r = bb(1u64..=5);
            let f = o(rfind9_in(&mut r).map(|x| x as i64));
            print_state(&mut r, f);
            let mut r = bb(4u64..=4);
            let f = o(rfind9_in(&mut r).map(|x| x as i64));
            print_state(&mut r, f);
            let mut r = bb(3u64..=3);
            let f = o(rfind3_in(&mut r).map(|x| x as i64));
            print_state(&mut r, f);
            let mut q = bb(-128i8..=127);
            let a = o(rfind_odd_in(&mut q));
            let b = o(rfind_odd_in(&mut q));
            println!("{a} {b} {} {}", q.clone().count(), o(q.clone().next_back()));
            let mut q = bb(-128i8..=-127);
            let a = o(rfind_odd_in(&mut q));
            let b = o(rfind_odd_in(&mut q));
            println!("{a} {b} {}", u8::from(q.is_empty()));
        }
        _ => {
            eprintln!("unknown CASE");
            std::process::exit(2);
        }
    }
}
