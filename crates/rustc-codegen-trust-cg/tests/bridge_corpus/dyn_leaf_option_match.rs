// Corpus: `Option<&dyn Trait>` CONSTRUCTED, passed, and MATCHED on — the
// `<Option<&dyn Error>>::and_then` / `Error::source` shape. The payload is a
// `{data, vtable}` ScalarPair inside a niche-encoded enum (the data half's
// non-null niche encodes `None`).
#![allow(dead_code)]

trait Shape {
    fn val(&self) -> i64;
}
struct Square(i64);
struct Circle(i64);
impl Shape for Square {
    fn val(&self) -> i64 {
        self.0 * self.0
    }
}
impl Shape for Circle {
    fn val(&self) -> i64 {
        self.0 * 3
    }
}

// A RUNTIME-selected `Option<&dyn Shape>`: each arm coerces a different concrete
// referent, so the niche-encoded `None` and both vtables must survive the merge.
#[inline(never)]
fn pick<'a>(which: i64, a: &'a Square, b: &'a Circle) -> Option<&'a dyn Shape> {
    match which {
        0 => None,
        1 => Some(a),
        _ => Some(b),
    }
}

#[inline(never)]
fn eval(o: Option<&dyn Shape>) -> i64 {
    match o {
        None => -1,
        Some(s) => s.val(),
    }
}

#[inline(never)]
fn chain(o: Option<&dyn Shape>, k: i64) -> i64 {
    o.map(|s| s.val() + k).unwrap_or(-7)
}

fn main() {
    let sq = Square(11);
    let ci = Circle(13);
    let a: Option<&dyn Shape> = Some(&sq);
    let b: Option<&dyn Shape> = Some(&ci);
    let n: Option<&dyn Shape> = None;
    println!("a {} {} {}", eval(a), eval(b), eval(n));
    println!("b {} {} {}", chain(a, 5), chain(b, 5), chain(n, 5));
    println!(
        "c {} {} {}",
        eval(pick(0, &sq, &ci)),
        eval(pick(1, &sq, &ci)),
        eval(pick(2, &sq, &ci))
    );
}
