// CORPUS FIXTURE — a `Vec<T>` / `String` stored WHOLE through a pointer writes
// all 24 bytes of rustc's `{cap, ptr, len}` header.
//
// WHAT IT PINS. A default-`Global` `Vec`/`String` LOCAL is bound to the address
// of its own 24-byte slot, so its trust-ir type is a one-word `Ptr` carrier. The
// deref store `(*p) = move v` — the `ptr::write(end, value)` inside every
// `Vec<Vec<T>>::push`/`insert` and `Vec<String>::push`, and a user `*r = v`
// through `&mut Vec<T>` — took that carrier for the pointee's memory type and
// emitted ONE 8-byte store. The element in the outer buffer became
// `{cap, <stale>, <stale>}`: `g[1].len()` read 0 and `g[1][0]` panicked "index
// out of bounds: the len is 0 but the index is 0" (LLVM: the values in the
// trailing comments), at every opt level, on aarch64-apple-darwin.
//
// HOW IT FAILS IF THE FIX IS REVERTED. It COMPILES and DIVERGES from LLVM (a
// bounds panic, or a wrong value for `reset_through_ref`) — a hard failure of
// `collection_header_deref_store_differential`.
//
// The trailing tuple/array/struct sections are CONTROLS: the same
// mutate-through-`&mut`-then-push shape with a plain aggregate element, which
// the aggregate deref-store path already lowered at rustc's offsets.

use std::hint::black_box as bb;

/// Order-sensitive digest of a `Vec<Vec<i64>>`: every row's length and every
/// element are read back through `len()` and indexing.
#[inline(never)]
fn digest_rows(g: &Vec<Vec<i64>>) -> u64 {
    let mut s = g.len() as u64;
    let mut i = 0;
    while i < g.len() {
        s = s.wrapping_mul(31).wrapping_add(g[i].len() as u64);
        let mut j = 0;
        while j < g[i].len() {
            s = s.wrapping_mul(31).wrapping_add(g[i][j] as u64);
            j += 1;
        }
        i += 1;
    }
    s
}

#[inline(never)]
fn digest_bytes(b: &[u8]) -> u64 {
    let mut s = b.len() as u64;
    let mut i = 0;
    while i < b.len() {
        s = s.wrapping_mul(31).wrapping_add(b[i] as u64);
        i += 1;
    }
    s
}

// The minimized program: a `while` loop pushing a one-element row.
#[inline(never)]
fn rows_while(n: usize) -> u64 {
    let mut g: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        row.push(i as i64 + 10);
        g.push(row);
        i += 1;
    }
    (g[1].len() * 10 + g[1][0] as usize) as u64 * 1_000_000 + digest_rows(&g)
}

#[inline(never)]
fn rows_for(n: usize) -> u64 {
    let mut g: Vec<Vec<i64>> = Vec::new();
    for i in 0..n {
        let mut row: Vec<i64> = Vec::new();
        let mut k = 0;
        while k <= i {
            row.push((i * 7 + k) as i64);
            k += 1;
        }
        g.push(row);
    }
    digest_rows(&g)
}

#[inline(never)]
fn rows_single(x: i64) -> u64 {
    let mut g: Vec<Vec<i64>> = Vec::new();
    let mut row: Vec<i64> = Vec::new();
    row.push(x);
    row.push(x + 1);
    g.push(row);
    digest_rows(&g)
}

#[inline(never)]
fn rows_u8(n: usize) -> u64 {
    let mut g: Vec<Vec<u8>> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let mut row: Vec<u8> = Vec::new();
        row.push(i as u8 + 10);
        row.push(i as u8 + 40);
        g.push(row);
        i += 1;
    }
    let mut s = 0u64;
    let mut i = 0;
    while i < g.len() {
        s = s.wrapping_mul(131).wrapping_add(digest_bytes(&g[i]));
        i += 1;
    }
    s
}

#[inline(never)]
fn rows_insert_front(n: usize) -> u64 {
    let mut g: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        row.push(i as i64 + 10);
        row.push(i as i64 + 20);
        g.insert(0, row);
        i += 1;
    }
    digest_rows(&g)
}

#[inline(never)]
fn rows_nested3(n: usize) -> u64 {
    let mut outer: Vec<Vec<Vec<u8>>> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let mut mid: Vec<Vec<u8>> = Vec::new();
        let mut inner: Vec<u8> = Vec::new();
        inner.push(i as u8 + 5);
        inner.push(i as u8 + 6);
        mid.push(inner);
        outer.push(mid);
        i += 1;
    }
    let mut s = 0u64;
    let mut i = 0;
    while i < outer.len() {
        s = s.wrapping_mul(131).wrapping_add(outer[i].len() as u64);
        s = s.wrapping_mul(131).wrapping_add(digest_bytes(&outer[i][0]));
        i += 1;
    }
    s
}

#[inline(never)]
fn make_row(x: i64) -> Vec<i64> {
    let mut v = Vec::new();
    v.push(x);
    v.push(x + 1);
    v
}

#[inline(never)]
fn id<T>(t: T) -> T {
    t
}

// Rows that arrive as call results: returned by value, passed through a generic
// identity, then pushed (the pushed operand is a call-result temporary).
#[inline(never)]
fn rows_from_calls(x: i64) -> u64 {
    let v = make_row(x);
    let w = id(v);
    let mut g: Vec<Vec<i64>> = Vec::new();
    g.push(id(w));
    g.push(make_row(x + 4));
    digest_rows(&g)
}

#[inline(never)]
fn strings_push(n: usize) -> u64 {
    let mut g: Vec<String> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let mut s = String::new();
        s.push('a');
        s.push('b');
        g.push(s);
        i += 1;
    }
    let mut s = 0u64;
    let mut i = 0;
    while i < g.len() {
        s = s
            .wrapping_mul(131)
            .wrapping_add(digest_bytes(g[i].as_bytes()));
        i += 1;
    }
    s
}

#[inline(never)]
fn strings_from(n: usize) -> u64 {
    let mut g: Vec<String> = Vec::new();
    let mut i = 0usize;
    while i < n {
        g.push(String::from("xyz"));
        i += 1;
    }
    let mut s = 0u64;
    let mut i = 0;
    while i < g.len() {
        s = s
            .wrapping_mul(131)
            .wrapping_add(digest_bytes(g[i].as_bytes()));
        i += 1;
    }
    s
}

#[inline(never)]
fn set(r: &mut Vec<i64>, v: Vec<i64>) {
    *r = v;
}

#[inline(never)]
fn assign_through_ref(x: i64) -> u64 {
    let mut a: Vec<i64> = Vec::new();
    a.push(x);
    let mut b: Vec<i64> = Vec::new();
    b.push(x + 6);
    b.push(x + 7);
    set(&mut a, b);
    (a.len() * 10 + a[1] as usize) as u64
}

#[inline(never)]
fn reset(r: &mut Vec<i64>) {
    *r = Vec::new();
}

#[inline(never)]
fn reset_through_ref(x: i64) -> u64 {
    let mut a: Vec<i64> = Vec::new();
    a.push(x);
    reset(&mut a);
    a.push(x + 3);
    (a.len() * 10 + a[0] as usize) as u64
}

// ---- controls: plain aggregate elements, mutated through `&mut`, then pushed.

#[inline(never)]
fn bump_tuple(t: &mut (usize, usize, usize), v: usize) {
    t.0 += v;
    t.1 += 2 * v;
    t.2 += 3 * v;
}

#[inline(never)]
fn tuples(n: usize) -> u64 {
    let mut g: Vec<(usize, usize, usize)> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let mut row = (bb(1usize), bb(2usize), bb(3usize));
        bump_tuple(&mut row, i);
        g.push(row);
        i += 1;
    }
    let r = g[1];
    (r.0 + r.1 * 10 + r.2 * 100) as u64
}

#[inline(never)]
fn bump_array(t: &mut [usize; 3], v: usize) {
    t[0] += v;
    t[1] += 2 * v;
    t[2] += 3 * v;
}

#[inline(never)]
fn arrays(n: usize) -> u64 {
    let mut g: Vec<[usize; 3]> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let mut row = [bb(1usize), bb(2usize), bb(3usize)];
        bump_array(&mut row, i);
        g.push(row);
        i += 1;
    }
    let r = g[1];
    (r[0] + r[1] * 10 + r[2] * 100) as u64
}

// Declared `a, b, c`; rustc places `b` (the u64) first.
struct Reordered {
    a: u32,
    b: u64,
    c: u32,
}

#[inline(never)]
fn bump_reordered(t: &mut Reordered, v: u32) {
    t.a += v;
    t.b += 2 * v as u64;
    t.c += 3 * v;
}

#[inline(never)]
fn reordered(n: u32) -> u64 {
    let mut g: Vec<Reordered> = Vec::new();
    let mut i = 0u32;
    while i < n {
        let mut row = Reordered {
            a: bb(1),
            b: bb(2),
            c: bb(3),
        };
        bump_reordered(&mut row, i);
        g.push(row);
        i += 1;
    }
    let r = &g[1];
    r.a as u64 + r.b * 10 + r.c as u64 * 100
}

fn main() {
    let r = rows_while(bb(3)); // 2721415809
    println!("{r}");
    let r = rows_for(bb(4)); // 8537283844957940954
    println!("{r}");
    let r = rows_single(bb(17)); // 32258
    println!("{r}");
    let r = rows_u8(bb(3)); // 39293952
    println!("{r}");
    let r = rows_insert_front(bb(3)); // 81374393052105
    println!("{r}");
    let r = rows_nested3(bb(2)); // 37996700
    println!("{r}");
    let r = rows_from_calls(bb(5)); // 1837064226
    println!("{r}");
    let r = strings_push(bb(3)); // 86931911
    println!("{r}");
    let r = strings_from(bb(3)); // 3606731838
    println!("{r}");
    let r = assign_through_ref(bb(1)); // 28
    println!("{r}");
    let r = reset_through_ref(bb(1)); // 14
    println!("{r}");
    let r = tuples(bb(3)); // 642
    println!("{r}");
    let r = arrays(bb(3)); // 642
    println!("{r}");
    let r = reordered(bb(3)); // 642
    println!("{r}");
}
