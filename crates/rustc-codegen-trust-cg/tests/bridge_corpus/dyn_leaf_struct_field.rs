// Corpus: a STRUCT holding a `&dyn Trait` FIELD, passed through calls and
// returned — the `core::fmt::Formatter { buf: &mut dyn Write }` /
// `DebugInner { fmt, .. }` shape. The field is a `{data, vtable}` ScalarPair
// memory leaf inside an aggregate that itself crosses call boundaries.
#![allow(dead_code)]

trait Shape {
    fn val(&self) -> i64;
    fn scale(&self, k: i64) -> i64;
}
struct Square(i64);
struct Circle(i64);
impl Shape for Square {
    fn val(&self) -> i64 {
        self.0 * self.0
    }
    fn scale(&self, k: i64) -> i64 {
        self.0 * k
    }
}
impl Shape for Circle {
    fn val(&self) -> i64 {
        self.0 * 3
    }
    fn scale(&self, k: i64) -> i64 {
        self.0 + k
    }
}

struct Holder<'a> {
    tag: i64,
    shape: &'a dyn Shape,
    bias: i64,
}

#[inline(never)]
fn sum(h: &Holder<'_>) -> i64 {
    h.tag + h.shape.val() + h.bias
}

#[inline(never)]
fn rebias<'a>(h: Holder<'a>, k: i64) -> Holder<'a> {
    Holder {
        tag: h.tag + 1,
        shape: h.shape,
        bias: h.bias * k,
    }
}

#[inline(never)]
fn build<'a>(s: &'a dyn Shape, tag: i64) -> Holder<'a> {
    Holder {
        tag,
        shape: s,
        bias: 100,
    }
}

fn main() {
    let sq = Square(6);
    let ci = Circle(9);
    let h1 = build(&sq, 1);
    let h2 = build(&ci, 2);
    println!("a {} {}", sum(&h1), sum(&h2));
    let h3 = rebias(h1, 3);
    let h4 = rebias(h2, -2);
    println!("b {} {}", sum(&h3), sum(&h4));
    println!("c {} {}", h3.shape.scale(5), h4.shape.scale(5));
}
