// Intercepted iterator terminals (`any`/`all`/`find`/`position`) handed a
// CAPTURING closure: by-reference captures, by-value captures, several
// captures, an FnMut closure counting its calls through a captured `&mut`,
// an FnMut `move` closure whose by-value state must persist across items,
// a borrowed iterator resumed after the terminal, a generic instantiation,
// ZST items, empty / one-element / large inputs, and core's `contains` over
// `char` and a user struct (which steps aside to core's body).
use std::hint::black_box;

#[derive(Clone, Copy, PartialEq, Debug)]
struct P {
    a: u16,
    b: i64,
}

#[inline(never)]
fn contains_char(v: &[char], x: char) -> bool {
    v.contains(&x)
}
#[inline(never)]
fn contains_p(v: &[P], x: P) -> bool {
    v.contains(&x)
}
#[inline(never)]
fn any_ref(v: &[i64], k: &i64) -> bool {
    v.iter().any(|x| *x == *k)
}
#[inline(never)]
fn all_two(v: &[i64], lo: i64, hi: i64) -> bool {
    v.iter().all(|x| *x >= lo && *x < hi)
}
#[inline(never)]
fn find_cap(v: &[i64], k: i64) -> Option<&i64> {
    v.iter().find(|x| **x > k)
}
#[inline(never)]
fn position_cap(v: &[u32], k: u32, m: u32) -> Option<usize> {
    v.iter().position(|x| *x % m == k)
}
#[inline(never)]
fn any_counting(v: &[i64], k: i64) -> (bool, u32) {
    let mut n = 0u32;
    let r = v.iter().any(|x| {
        n += 1;
        *x == k
    });
    (r, n)
}
#[inline(never)]
fn any_move_state(v: &[i64]) -> bool {
    let mut seen = 0i64;
    v.iter().any(move |x| {
        seen += *x;
        seen > 100
    })
}
#[inline(never)]
fn borrowed_then_rest(v: &[i64], k: i64) -> (bool, usize) {
    let mut it = v.iter();
    let hit = it.any(|x| *x == k);
    (hit, it.count())
}
#[inline(never)]
fn generic_contains<T: PartialEq + Copy>(v: &[T], x: T) -> bool {
    v.iter().any(|y| *y == x)
}
#[inline(never)]
fn zst_items(v: &[()], flag: bool) -> bool {
    v.iter().any(|_| flag)
}
#[inline(never)]
fn wide_capture(v: &[u64], k: u128) -> Option<usize> {
    v.iter().position(|x| (*x as u128) * 3 == k)
}

fn main() {
    let mut big: Vec<u32> = Vec::new();
    for i in 0..10_000u32 {
        big.push(i);
    }
    println!(
        "{} {}",
        contains_char(black_box(&['a', 'b', 'c']), 'c'),
        contains_char(black_box(&['a']), 'z')
    );
    println!("{}", contains_char(black_box(&[]), 'a'));
    let ps = [P { a: 1, b: -1 }, P { a: 2, b: 5 }];
    println!(
        "{} {}",
        contains_p(black_box(&ps), P { a: 2, b: 5 }),
        contains_p(black_box(&ps), P { a: 2, b: 6 })
    );
    let mut v: Vec<i64> = Vec::new();
    for i in 0..50 {
        v.push(i * 3 - 20);
    }
    let e: [i64; 0] = [];
    println!(
        "{} {} {}",
        any_ref(black_box(&v), &black_box(13)),
        any_ref(black_box(&v), &black_box(14)),
        any_ref(black_box(&e), &1)
    );
    println!(
        "{} {} {}",
        all_two(black_box(&v), -20, 200),
        all_two(black_box(&v), -19, 200),
        all_two(black_box(&e), 0, 0)
    );
    println!(
        "{:?} {:?} {:?}",
        find_cap(black_box(&v), 100),
        find_cap(black_box(&v), 1000),
        find_cap(black_box(&v[..1]), -21)
    );
    println!(
        "{:?} {:?}",
        position_cap(black_box(&big), 3, 7),
        position_cap(black_box(&big[..2]), 5, 7)
    );
    println!(
        "{:?} {:?} {:?}",
        any_counting(black_box(&v), 10),
        any_counting(black_box(&v), 11),
        any_counting(black_box(&e), 0)
    );
    println!(
        "{} {}",
        any_move_state(black_box(&v)),
        any_move_state(black_box(&v[..3]))
    );
    println!(
        "{:?} {:?}",
        borrowed_then_rest(black_box(&v), 1),
        borrowed_then_rest(black_box(&v), 2)
    );
    println!(
        "{} {}",
        generic_contains(black_box(&[1u16, 2, 3]), 3u16),
        generic_contains(black_box(&[(1u8, 2u8)]), (2u8, 1u8))
    );
    let mut units: Vec<()> = Vec::new();
    for _ in 0..3 {
        units.push(());
    }
    println!(
        "{} {} {}",
        zst_items(black_box(&[]), true),
        zst_items(black_box(units.as_slice()), true),
        zst_items(black_box(units.as_slice()), false)
    );
    println!(
        "{:?} {:?}",
        wide_capture(black_box(&[1, 5, 9]), 27),
        wide_capture(black_box(&[1, 5, 9]), 28)
    );
}
