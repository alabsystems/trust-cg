// Corpus: a CLOSURE capturing a `&dyn Trait` BY REFERENCE (`&&dyn Debug`) — the
// shape `core::fmt::builders::DebugTuple::field`'s `and_then` closure has. The
// upvar is a memory leaf of the closure environment whose type is a
// `{data, vtable}` ScalarPair behind one more `&`.
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

#[inline(never)]
fn run(f: impl Fn() -> i64) -> i64 {
    f()
}

// `d` is captured BY REFERENCE: the upvar type is `&&dyn Shape`.
#[inline(never)]
fn capture_by_ref(d: &dyn Shape, k: i64) -> i64 {
    let c = || d.val() + k;
    run(c) + run(|| d.val() * 2)
}

// The same shape ONE LEVEL UP: the upvar is a `&&dyn Shape`. Taking `&d` inside
// the closure forces a BY-REFERENCE capture, so the environment holds a THIN
// pointer to a `{data, vtable}` fat pointer — exactly the `&&dyn Debug` upvar
// `core::fmt::builders::DebugTuple::field`'s `and_then` closure carries.
#[inline(never)]
fn capture_by_double_ref(d: &dyn Shape, k: i64) -> i64 {
    let c = || {
        let r: &&dyn Shape = &d;
        r.val() + k
    };
    run(c) + run(|| {
        let r: &&dyn Shape = &d;
        r.val() * 2
    })
}

fn main() {
    let sq = Square(7);
    let ci = Circle(5);
    println!("a {}", capture_by_ref(&sq, 3));
    println!("b {}", capture_by_ref(&ci, -4));
    println!("c {}", capture_by_double_ref(&sq, 3));
    println!("d {}", capture_by_double_ref(&ci, -4));
}
