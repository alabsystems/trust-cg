// Holding locals that never escape: a field moved out of a by-value local
// and iterated by value, and a field reassigned from another local (the old
// buffer dropped, the moved-from local partially dropped).
use std::hint::black_box;
struct Ctx {
    id: u32,
    used: Vec<u32>,
    name: String,
}
#[inline(never)]
fn mkv(n: u32) -> Vec<u32> {
    let mut v = Vec::new();
    for i in 0..n {
        v.push(i);
    }
    v
}
#[inline(never)]
fn local_only(n: u32) -> u64 {
    let c = Ctx {
        id: n,
        used: mkv(n),
        name: String::new(),
    };
    let v = c.used;
    let mut t = c.id as u64;
    for x in v {
        t += x as u64;
    }
    t
}
#[inline(never)]
fn swap_fields(n: u32) -> u64 {
    let mut a = Ctx {
        id: 1,
        used: mkv(n),
        name: String::new(),
    };
    let b = Ctx {
        id: 2,
        used: mkv(n + 3),
        name: String::new(),
    };
    a.used = b.used;
    let k = a.id + b.id;
    k as u64 + a.used.len() as u64
}
fn main() {
    println!("{} {}", local_only(black_box(0)), local_only(black_box(9)));
    println!(
        "{} {}",
        swap_fields(black_box(0)),
        swap_fields(black_box(4))
    );
}
