// `min_by_key` / `max_by` / `min_by` with CAPTURING closures (a key closure
// counting its calls through a captured `&mut`, comparators capturing a
// modulus). At -O2/-O3 rustc inlines these into `map(..).reduce(..)` over
// `KeyAndValue`, which is not this interception: match or named refusal.
use std::hint::black_box;

#[inline(never)]
fn by_key_counted(v: &[i64]) -> (Option<&i64>, u32) {
    let mut calls = 0u32;
    let r = v.iter().min_by_key(|x| {
        calls += 1;
        (**x - 7).abs()
    });
    (r, calls)
}

#[inline(never)]
fn by_cmp(v: &[u32], m: u32) -> (Option<u32>, Option<u32>) {
    (
        v.iter().copied().min_by(|a, b| (a % m).cmp(&(b % m))),
        v.iter().copied().max_by(|a, b| (a % m).cmp(&(b % m))),
    )
}

fn main() {
    let mut v: Vec<i64> = Vec::new();
    for i in 0..20 {
        v.push(i * 5 - 3);
    }
    println!("{:?}", by_key_counted(black_box(&v)));
    println!("{:?}", by_key_counted(black_box(&v[..0])));
    let mut u: Vec<u32> = Vec::new();
    for i in 1..60 {
        u.push(i * 7 + 3);
    }
    println!(
        "{:?} {:?}",
        by_cmp(black_box(&u), black_box(11)),
        by_cmp(black_box(&u[..1]), black_box(11))
    );
}
