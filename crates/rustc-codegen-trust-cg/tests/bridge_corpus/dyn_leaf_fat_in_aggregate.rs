// Corpus: a FAT POINTER STORED INTO and RELOADED FROM an aggregate — both
// metadata kinds: `{data, vtable}` (`&dyn Trait`) and `{data, len}`
// (`&[i64]` / `&str`), inside the same struct and the same tuple, so the
// byte-offset leaf machinery must place BOTH kinds from rustc's layout.
#![allow(dead_code)]

trait Shape {
    fn val(&self) -> i64;
}
struct Square(i64);
impl Shape for Square {
    fn val(&self) -> i64 {
        self.0 * self.0
    }
}

struct Both<'a> {
    head: i64,
    dynref: &'a dyn Shape,
    slice: &'a [i64],
    name: &'a str,
    tail: i64,
}

#[inline(never)]
fn store_and_reload<'a>(d: &'a dyn Shape, s: &'a [i64], n: &'a str) -> Both<'a> {
    Both {
        head: 1,
        dynref: d,
        slice: s,
        name: n,
        tail: 2,
    }
}

#[inline(never)]
fn read(b: &Both<'_>) -> i64 {
    let mut acc = b.head + b.tail + b.dynref.val();
    acc += b.slice.len() as i64;
    for v in b.slice {
        acc += *v;
    }
    acc += b.name.len() as i64;
    acc
}

#[inline(never)]
fn tuple_roundtrip<'a>(d: &'a dyn Shape, s: &'a [i64]) -> i64 {
    let t: (&dyn Shape, &[i64], i64) = (d, s, 9);
    let (dd, ss, k) = t;
    dd.val() + ss.len() as i64 + k
}

fn main() {
    let sq = Square(8);
    let data = [3i64, 5, 7];
    let b = store_and_reload(&sq, &data, "hello");
    println!("a {}", read(&b));
    println!("b {}", tuple_roundtrip(&sq, &data));
    println!("c {}", read(&store_and_reload(&sq, &data[1..], "hi")));
}
