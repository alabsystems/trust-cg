// Vec/String FIELDS held inline by a memory-backed aggregate (the checked
// 24-byte rustc header image): construction from moved locals, push through
// `&mut s.v`, reads through `&S`, a by-value pass, moves out of a field, field
// reassignment (old buffer dropped), a nested container, a generic container,
// an enum payload, a `const` holding empty headers, a `(Vec, u8)` tuple, ZST
// elements, empty / one-element / large buffers, and the drop glue of every
// shape (a double free aborts and fails the comparison; a leak is not seen).
use std::hint::black_box;

struct Ctx {
    id: u32,
    used: Vec<u32>,
    name: String,
}

struct Outer {
    tag: u8,
    inner: Ctx,
    extra: Vec<i64>,
}

struct Gen<T> {
    items: Vec<T>,
    n: usize,
}

enum Slot {
    Empty,
    Full(Vec<u16>, u8),
}

struct Units {
    u: Vec<()>,
    k: u64,
}

#[inline(never)]
fn mk(n: u32) -> Ctx {
    let mut c = Ctx {
        id: n,
        used: Vec::new(),
        name: String::new(),
    };
    for i in 0..n {
        c.used.push(i * 2);
    }
    c.name.push_str("ctx");
    c
}

#[inline(never)]
fn sum_used(c: &Ctx) -> u64 {
    let mut s = 0u64;
    for x in c.used.iter() {
        s += *x as u64;
    }
    s + c.id as u64 + c.name.len() as u64
}

#[inline(never)]
fn consume(c: Ctx) -> u64 {
    sum_used(&c)
}

#[inline(never)]
fn take_used(c: Ctx) -> Vec<u32> {
    c.used
}

#[inline(never)]
fn reset(c: &mut Ctx, n: u32) {
    let mut v = Vec::new();
    for i in 0..n {
        v.push(i + 100);
    }
    c.used = v;
}

#[inline(never)]
fn mk_outer(n: u32) -> Outer {
    let mut e = Vec::new();
    for i in 0..n as i64 {
        e.push(-i);
    }
    Outer {
        tag: 7,
        inner: mk(n),
        extra: e,
    }
}

#[inline(never)]
fn outer_total(o: &Outer) -> i64 {
    let mut t = o.tag as i64 + sum_used(&o.inner) as i64;
    for x in o.extra.iter() {
        t += *x;
    }
    t
}

#[inline(never)]
fn gen_len<T: Copy>(x: T, n: usize) -> usize {
    let mut g = Gen {
        items: Vec::new(),
        n,
    };
    for _ in 0..n {
        g.items.push(x);
    }
    g.items.len() + g.n
}

#[inline(never)]
fn slot(n: u16) -> Slot {
    if n == 0 {
        return Slot::Empty;
    }
    let mut v = Vec::new();
    for i in 0..n {
        v.push(i * 3);
    }
    Slot::Full(v, n as u8)
}

#[inline(never)]
fn slot_sum(s: &Slot) -> u64 {
    match s {
        Slot::Empty => 0,
        Slot::Full(v, k) => {
            let mut t = *k as u64;
            for x in v.iter() {
                t += *x as u64;
            }
            t
        }
    }
}

#[inline(never)]
fn units(n: usize) -> Units {
    let mut u = Units {
        u: Vec::new(),
        k: 5,
    };
    for _ in 0..n {
        u.u.push(());
    }
    u
}

const EMPTY: Ctx = Ctx {
    id: 9,
    used: Vec::new(),
    name: String::new(),
};

#[inline(never)]
fn from_const(n: u32) -> u64 {
    let mut c = EMPTY;
    for i in 0..n {
        c.used.push(i);
    }
    sum_used(&c)
}

#[inline(never)]
fn pair(n: u8) -> (Vec<u32>, u8) {
    let mut v = Vec::new();
    for i in 0..n {
        v.push(i as u32 * 7);
    }
    (v, n)
}

#[inline(never)]
fn pair_sum(p: &(Vec<u32>, u8)) -> u64 {
    let mut t = p.1 as u64;
    for x in p.0.iter() {
        t += *x as u64;
    }
    t
}

#[inline(never)]
fn show(x: u64) {
    println!("{}", x);
}

fn main() {
    // One call per input (no `println!` inside a loop: an O2 loop hoists the
    // format template into a loop-carried constant, a separate class).
    show(consume(mk(black_box(0))));
    show(consume(mk(black_box(1))));
    show(consume(mk(black_box(5))));
    show(consume(mk(black_box(1000))));
    let v = take_used(mk(black_box(4)));
    println!("{} {}", v.len(), v[3]);
    let mut c = mk(black_box(3));
    reset(&mut c, black_box(2));
    println!("{} {}", sum_used(&c), c.used.len());
    reset(&mut c, black_box(0));
    println!("{}", sum_used(&c));
    show(outer_total(&mk_outer(black_box(0))) as u64);
    show(outer_total(&mk_outer(black_box(2))) as u64);
    show(outer_total(&mk_outer(black_box(300))) as u64);
    println!(
        "{} {}",
        gen_len(black_box(7u8), 0),
        gen_len(black_box(1u64), 33)
    );
    println!("{}", gen_len(black_box((1u16, 2u32)), 2));
    show(slot_sum(&slot(black_box(0))));
    show(slot_sum(&slot(black_box(1))));
    show(slot_sum(&slot(black_box(50))));
    show(from_const(black_box(0)));
    show(from_const(black_box(6)));
    show(pair_sum(&pair(black_box(0))));
    show(pair_sum(&pair(black_box(40))));
    let u = units(black_box(9));
    println!("{} {}", u.u.len(), u.k);
}
