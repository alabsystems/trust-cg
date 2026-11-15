// Lane places-promoted-refs-aggregates, program 1: LOCAL callees returning
// `&mut T` / `&Adt` / `&[T; N]` / `&(A, B)` through the general direct-call
// path (the select-return recognizer used to REFUSE every such callee), plus
// stores through the returned `&mut` observed by later reads.
#![allow(dead_code)]

struct Counter {
    hits: u64,
    misses: u64,
}

#[inline(never)]
fn misses_mut(c: &mut Counter) -> &mut u64 {
    &mut c.misses
}

#[inline(never)]
fn pick_mut(c: &mut Counter, which: bool) -> &mut u64 {
    if which { &mut c.hits } else { &mut c.misses }
}

#[inline(never)]
fn whole(c: &mut Counter) -> &mut Counter {
    c
}

#[inline(never)]
fn view(c: &Counter) -> &Counter {
    c
}

#[inline(never)]
fn elem_mut(a: &mut [u32; 4], i: usize) -> &mut u32 {
    &mut a[i]
}

#[inline(never)]
fn arr_ref(a: &[u32; 4]) -> &[u32; 4] {
    a
}

#[inline(never)]
fn pair_ref<'a>(p: &'a (u16, i64), c: bool, q: &'a (u16, i64)) -> &'a (u16, i64) {
    if c { p } else { q }
}

#[inline(never)]
fn drive_counter(c: &mut Counter) -> u64 {
    *misses_mut(c) += 10;
    *pick_mut(c, false) *= 7;
    {
        let w = whole(c);
        w.hits += 100;
        w.misses -= 1;
    }
    let v = view(c);
    let (h, m) = (v.hits, v.misses);
    println!("hits={} misses={}", h, m);
    c.hits * 2 + c.misses
}

#[inline(never)]
fn drive_array(a: &mut [u32; 4]) -> u32 {
    for i in 0..4 {
        *elem_mut(a, i) += i as u32 * 100;
    }
    let r = arr_ref(a);
    let (r0, r1, r2, r3) = (r[0], r[1], r[2], r[3]);
    println!("a={} {} {} {}", r0, r1, r2, r3);
    a[0] + a[3]
}

fn main() {
    let mut c = Counter { hits: 1, misses: 2 };
    let mut a = [3u32, 5, 7, 9];
    let h = drive_counter(&mut c);
    let a0 = drive_array(&mut a);
    let p = (7u16, -3i64);
    let q = (9u16, 44i64);
    let s = pair_ref(&p, a0 > 2, &q);
    let t = pair_ref(&p, h > 500, &q);
    let (s0, s1, t0, t1) = (s.0, s.1, t.0, t.1);
    println!("s={} {} t={} {}", s0, s1, t0, t1);
}
