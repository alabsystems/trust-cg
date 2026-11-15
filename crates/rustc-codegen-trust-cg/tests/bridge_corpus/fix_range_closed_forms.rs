// CORPUS FIXTURE — core's O(1) `Range` / `RangeInclusive` iterator methods, for
// `range_closed_forms_differential.rs`. One CASE per run (`CASE=<name>`, read
// through libc), each printing integers on one line or panicking. Every method
// is an `#[inline(never)]` callee over `black_box` bounds, so it is a real call
// over runtime bounds at every opt level.
//
// core answers `count` (`Step::steps_between`), `last` / `max` (`next_back`),
// `min` (`next`), `nth` (`Step::forward_checked`) and `Skip`'s skip (one source
// `nth`) without visiting the items in between, so every span here returns at
// once under LLVM; a per-item walk of 2^62..2^64 items never finishes. (A
// `Take` count is core's per-item fold, so its spans stay small.) The
// panicking cases are core's own: `count` past `usize::MAX` ("count overflowed
// usize") and `Chain::count`'s add under overflow checks. Small spans, empty and
// inverted ranges, both signednesses and several widths are the controls.
// Printing sticks to integers (`{:?}` of an `Option` or a range is a separate
// bridge limitation this fixture must not depend on).
use std::hint::black_box as bb;
use std::ops::{Range, RangeInclusive};

const H: usize = 1 << 62;

#[inline(never)]
fn count_u64(r: Range<u64>) -> usize {
    r.count()
}
#[inline(never)]
fn count_i64(r: Range<i64>) -> usize {
    r.count()
}
#[inline(never)]
fn count_u32(r: Range<u32>) -> usize {
    r.count()
}
#[inline(never)]
fn count_i8(r: Range<i8>) -> usize {
    r.count()
}
#[inline(never)]
fn count_u128(r: Range<u128>) -> usize {
    r.count()
}
#[inline(never)]
fn count_incl_u64(r: RangeInclusive<u64>) -> usize {
    r.count()
}
#[inline(never)]
fn count_incl_i16(r: RangeInclusive<i16>) -> usize {
    r.count()
}
#[inline(never)]
fn count_skip(r: Range<u64>, n: usize) -> usize {
    r.skip(n).count()
}
#[inline(never)]
fn count_skip_incl(r: RangeInclusive<u64>, n: usize) -> usize {
    r.skip(n).count()
}
#[inline(never)]
fn count_take(r: Range<i64>, n: usize) -> usize {
    r.take(n).count()
}
#[inline(never)]
fn count_skip_take(r: Range<u64>, a: usize, b: usize) -> usize {
    r.skip(a).take(b).count()
}
#[inline(never)]
fn count_enumerate(r: RangeInclusive<u64>) -> usize {
    r.enumerate().count()
}
#[inline(never)]
fn count_chain(a: Range<u64>, b: Range<u64>) -> usize {
    a.chain(b).count()
}
#[inline(never)]
fn last_u64(r: Range<u64>) -> Option<u64> {
    r.last()
}
#[inline(never)]
fn last_i64(r: Range<i64>) -> Option<i64> {
    r.last()
}
#[inline(never)]
fn last_u32(r: Range<u32>) -> Option<u32> {
    r.last()
}
#[inline(never)]
fn last_incl(r: RangeInclusive<u64>) -> Option<u64> {
    r.last()
}
#[inline(never)]
fn last_skip(r: Range<u64>, n: usize) -> Option<u64> {
    r.skip(n).last()
}
#[inline(never)]
fn max_u64(r: Range<u64>) -> Option<u64> {
    r.max()
}
#[inline(never)]
fn min_u64(r: Range<u64>) -> Option<u64> {
    r.min()
}
#[inline(never)]
fn max_incl(r: RangeInclusive<i64>) -> Option<i64> {
    r.max()
}
#[inline(never)]
fn min_incl(r: RangeInclusive<i64>) -> Option<i64> {
    r.min()
}
#[inline(never)]
fn nth_u64(r: &mut Range<u64>, n: usize) -> Option<u64> {
    r.nth(n)
}
#[inline(never)]
fn nth_i32(r: &mut Range<i32>, n: usize) -> Option<i32> {
    r.nth(n)
}
#[inline(never)]
fn nth_incl(r: &mut RangeInclusive<i64>, n: usize) -> Option<i64> {
    r.nth(n)
}
#[inline(never)]
fn nth_rev(r: Range<u64>, n: usize) -> Option<u64> {
    r.rev().nth(n)
}
#[inline(never)]
fn skip_next(r: Range<u64>, n: usize) -> Option<u64> {
    r.skip(n).next()
}
#[inline(never)]
fn skip_next_incl(r: RangeInclusive<i64>, n: usize) -> Option<i64> {
    r.skip(n).next()
}
#[inline(never)]
fn skip_take_sum(r: Range<u64>, n: usize) -> u64 {
    r.skip(n).take(3).fold(0u64, |a, x| a.wrapping_add(x))
}
#[inline(never)]
fn rev_skip_sum(r: Range<i64>, n: usize) -> i64 {
    r.rev().skip(n).take(2).fold(0i64, |a, x| a.wrapping_add(x))
}

#[inline(never)]
fn take_skip_next(r: Range<u64>, t: usize, s: usize) -> Option<u64> {
    r.take(t).skip(s).next()
}
#[inline(never)]
fn skip_skip_next(r: Range<u64>, a: usize, b: usize) -> Option<u64> {
    r.skip(a).skip(b).next()
}
#[inline(never)]
fn take_nth(r: Range<u64>, t: usize, n: usize) -> Option<u64> {
    r.take(t).nth(n)
}
#[inline(never)]
fn skip_nth(r: Range<u64>, s: usize, n: usize) -> Option<u64> {
    r.skip(s).nth(n)
}
#[inline(never)]
fn rev_skip_next_incl(r: RangeInclusive<u64>, n: usize) -> Option<u64> {
    r.rev().skip(n).next()
}
#[inline(never)]
fn take_skip_sum(r: Range<u64>, t: usize, s: usize) -> u64 {
    r.take(t).skip(s).fold(0u64, |a, x| a.wrapping_add(x))
}
#[inline(never)]
fn skip_skip_last(r: Range<i64>, a: usize, b: usize) -> Option<i64> {
    r.skip(a).skip(b).last()
}
#[inline(never)]
fn skip_sum_incl(r: RangeInclusive<u64>, s: usize) -> u64 {
    r.skip(s).fold(0u64, |a, x| a.wrapping_add(x))
}

fn su(v: Option<u64>) {
    match v {
        Some(x) => print!("S{x} "),
        None => print!("N "),
    }
}
fn si(v: Option<i64>) {
    match v {
        Some(x) => print!("S{x} "),
        None => print!("N "),
    }
}
fn su32(v: Option<u32>) {
    match v {
        Some(x) => print!("S{x} "),
        None => print!("N "),
    }
}
fn si32(v: Option<i32>) {
    match v {
        Some(x) => print!("S{x} "),
        None => print!("N "),
    }
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
        b"count" => println!(
            "{} {} {} {} {} {} {} {} {}",
            count_u64(bb(0..u64::MAX)),
            count_u64(bb(3..9)),
            count_u64(bb(9..3)),
            count_i64(bb(i64::MIN..i64::MAX)),
            count_i64(bb(i64::MIN..0)),
            count_i64(bb(i64::MAX..i64::MIN)),
            count_u32(bb(0..u32::MAX)),
            count_i8(bb(-128..127)),
            count_i8(bb(5..-5))
        ),
        b"count_wide" => println!(
            "{} {} {} {} {} {}",
            count_u128(bb((1u128 << 100)..(1u128 << 100) + (1u128 << 40))),
            count_u128(bb(3..9)),
            count_u128(bb(9..3)),
            count_u128(bb(0..u64::MAX as u128)),
            count_incl_u64(bb(1..=u64::MAX)),
            count_incl_u64(bb(5..=4))
        ),
        b"count_incl" => println!(
            "{} {} {} {}",
            count_incl_u64(bb(0..=u64::MAX - 1)),
            count_incl_u64(bb(7..=7)),
            count_incl_i16(bb(i16::MIN..=i16::MAX)),
            count_incl_i16(bb(3..=-3))
        ),
        b"count_adapters" => println!(
            "{} {} {} {} {} {} {} {} {} {} {}",
            count_skip(bb(0..u64::MAX), bb(H)),
            count_skip(bb(0..100), bb(97)),
            count_skip(bb(0..10), bb(usize::MAX)),
            count_skip_incl(bb(0..=u64::MAX), bb(1)),
            count_skip_incl(bb(0..=u64::MAX), bb(usize::MAX)),
            count_take(bb(i64::MIN..i64::MAX), bb(100)),
            count_take(bb(-5..5), bb(100)),
            count_skip_take(bb(0..u64::MAX), bb(H), bb(5)),
            count_skip_take(bb(0..10), bb(4), bb(3)),
            count_enumerate(bb(1..=u64::MAX)),
            count_chain(bb(0..u64::MAX), bb(5..2))
        ),
        // `Range::count` / `RangeInclusive::count` panic "count overflowed usize".
        b"count_incl_full" => println!("{}", count_incl_u64(bb(0..=u64::MAX))),
        b"count_skip0_full" => println!("{}", count_skip_incl(bb(0..=u64::MAX), bb(0))),
        b"count_enumerate_full" => println!("{}", count_enumerate(bb(0..=u64::MAX))),
        b"count_u128_ovf" => println!("{}", count_u128(bb(0..u128::MAX))),
        // `Chain::count` adds the halves under the crate's overflow checks.
        b"count_chain_ovf" => println!("{}", count_chain(bb(0..u64::MAX), bb(0..u64::MAX))),
        b"last" => {
            su(last_u64(bb(0..u64::MAX)));
            su(last_u64(bb(3..9)));
            su(last_u64(bb(9..3)));
            si(last_i64(bb(i64::MIN..i64::MAX)));
            si(last_i64(bb(-3..-3)));
            su32(last_u32(bb(0..u32::MAX)));
            su(last_incl(bb(0..=u64::MAX)));
            su(last_incl(bb(4..=3)));
            su(last_skip(bb(0..u64::MAX), bb(H)));
            su(last_skip(bb(0..10), bb(10)));
            su(last_skip(bb(0..10), bb(9)));
            println!();
        }
        b"min_max" => {
            su(max_u64(bb(0..u64::MAX)));
            su(min_u64(bb(0..u64::MAX)));
            su(max_u64(bb(7..7)));
            su(min_u64(bb(8..7)));
            si(max_incl(bb(i64::MIN..=i64::MAX)));
            si(min_incl(bb(i64::MIN..=i64::MAX)));
            si(max_incl(bb(5..=4)));
            si(min_incl(bb(-2..=-2)));
            println!();
        }
        b"nth" => {
            let mut r = 0u64..u64::MAX;
            su(nth_u64(bb(&mut r), bb(H)));
            su(r.next());
            let mut r = 0u64..10;
            su(nth_u64(bb(&mut r), bb(7)));
            su(r.next());
            su(r.next());
            let mut r = 0u64..10;
            su(nth_u64(bb(&mut r), bb(usize::MAX)));
            su(r.next());
            // An inverted range: core's `nth` leaves it as `end..end`.
            let mut r = 9u64..3;
            su(nth_u64(bb(&mut r), bb(1)));
            let (start, end) = (r.start, r.end);
            print!("{start}..{end} ");
            let mut r = -5i32..5;
            si32(nth_i32(bb(&mut r), bb(9)));
            si32(nth_i32(bb(&mut r), bb(0)));
            let (start, end) = (r.start, r.end);
            print!("{start}..{end} ");
            let mut r = i64::MIN..=i64::MAX;
            si(nth_incl(bb(&mut r), bb(usize::MAX)));
            si(r.next());
            let mut r = i64::MIN..=i64::MAX;
            si(nth_incl(bb(&mut r), bb(H)));
            si(r.next());
            let mut r = -5i64..=5;
            si(nth_incl(bb(&mut r), bb(10)));
            si(r.next());
            let mut r = -5i64..=5;
            si(nth_incl(bb(&mut r), bb(11)));
            si(r.next());
            su(nth_rev(bb(0..u64::MAX), bb(H)));
            su(nth_rev(bb(0..10), bb(3)));
            su(nth_rev(bb(0..10), bb(10)));
            println!();
        }
        b"skip" => {
            su(skip_next(bb(0..u64::MAX), bb(H)));
            su(skip_next(bb(0..10), bb(3)));
            su(skip_next(bb(0..10), bb(10)));
            si(skip_next_incl(bb(i64::MIN..=i64::MAX), bb(usize::MAX)));
            si(skip_next_incl(bb(-3..=3), bb(6)));
            si(skip_next_incl(bb(-3..=3), bb(7)));
            print!("{} ", skip_take_sum(bb(0..u64::MAX), bb(H)));
            print!("{} ", skip_take_sum(bb(0..100), bb(90)));
            print!("{} ", skip_take_sum(bb(0..100), bb(99)));
            print!("{} ", rev_skip_sum(bb(i64::MIN..i64::MAX), bb(H)));
            print!("{} ", rev_skip_sum(bb(-10..10), bb(3)));
            println!();
        }
        // `Skip` / `Take` stacks: core skips with the inner `nth` in O(1).
        b"windows" => {
            su(take_skip_next(bb(0..u64::MAX), bb(H), bb(H / 2)));
            su(take_skip_next(bb(0..100), bb(10), bb(4)));
            su(take_skip_next(bb(0..100), bb(3), bb(4)));
            su(take_skip_next(bb(0..2), bb(10), bb(1)));
            su(skip_skip_next(bb(0..u64::MAX), bb(H), bb(H)));
            su(skip_skip_next(bb(0..20), bb(3), bb(4)));
            su(take_nth(bb(0..u64::MAX), bb(H), bb(H - 2)));
            su(take_nth(bb(0..100), bb(10), bb(9)));
            su(take_nth(bb(0..100), bb(10), bb(10)));
            su(take_nth(bb(0..5), bb(10), bb(7)));
            su(skip_nth(bb(0..u64::MAX), bb(H), bb(H)));
            su(skip_nth(bb(0..100), bb(10), bb(4)));
            su(skip_nth(bb(0..12), bb(10), bb(4)));
            su(rev_skip_next_incl(bb(0..=u64::MAX), bb(H)));
            su(rev_skip_next_incl(bb(0..=9), bb(3)));
            su(rev_skip_next_incl(bb(0..=9), bb(10)));
            print!("{} ", take_skip_sum(bb(0..u64::MAX), bb(H), bb(H - 3)));
            print!("{} ", take_skip_sum(bb(5..50), bb(10), bb(4)));
            print!("{} ", take_skip_sum(bb(5..8), bb(10), bb(2)));
            si(skip_skip_last(bb(i64::MIN..i64::MAX), bb(H), bb(H)));
            si(skip_skip_last(bb(-5..5), bb(3), bb(7)));
            print!("{} ", skip_sum_incl(bb(0..=u64::MAX), bb(usize::MAX)));
            print!("{} ", skip_sum_incl(bb(3..=9), bb(2)));
            println!();
        }
        _ => std::process::exit(2),
    }
}
