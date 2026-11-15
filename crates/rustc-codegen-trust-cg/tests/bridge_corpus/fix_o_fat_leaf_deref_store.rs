// Corpus: STORING a `{data, meta}` FAT POINTER into a field of a memory-resident
// aggregate THROUGH a `&mut` reference — `(*p).field = <fat>`.
//
// The READ side of this shape has been covered since the `&dyn` leaf lane
// (`lower_memory_fat_leaf_use`). The WRITE side had no arm, so the store fell
// into the generic deref-store path, which resolves the projected leaf through
// `memory_scalar_leaf_ty` and fails closed: `memory leaf type is a fat pointer
// (ScalarPair {data,len}), not a single scalar`. Measured on a `library/core`
// census that is 22 failed roots (rank 4), every one of them the
// `core::net::parser::Parser { state: &[u8] }` cursor below.
//
// A one-lane store would write the data half and leave the LENGTH half whatever
// it was, so every later read of the field sees a slice of the wrong length —
// and the scalar field beside it must stay untouched, which is what `tail`
// pins. Both metadata kinds are exercised: a `{data,len}` slice/`str` and a
// `{data,vtable}` `&dyn`, the latter dispatched after the store so a dropped or
// mistyped vtable lane calls the wrong impl.
#![allow(dead_code)]

trait Sh {
    fn area(&self) -> i64;
}
struct Sq(i64);
struct Tri(i64);
impl Sh for Sq {
    fn area(&self) -> i64 {
        self.0 * self.0
    }
}
impl Sh for Tri {
    fn area(&self) -> i64 {
        self.0 * 3
    }
}

// The `core::net::parser::Parser` shape: a slice cursor advanced through
// `&mut self`, with an ordinary scalar field after it.
struct Cursor<'a> {
    state: &'a [u8],
    tail: i64,
}

struct Named<'a> {
    name: &'a str,
    tail: i64,
}

struct Holder<'a> {
    shape: &'a dyn Sh,
    tail: i64,
}

#[inline(never)]
fn set_slice<'a>(c: &mut Cursor<'a>, s: &'a [u8]) {
    c.state = s;
}

#[inline(never)]
fn set_name<'a>(n: &mut Named<'a>, s: &'a str) {
    n.name = s;
}

#[inline(never)]
fn set_shape<'a>(h: &mut Holder<'a>, s: &'a dyn Sh) {
    h.shape = s;
}

#[inline(never)]
fn read_cursor(c: &Cursor<'_>) -> i64 {
    let mut acc = c.state.len() as i64 * 1000 + c.tail;
    for v in c.state {
        acc += *v as i64;
    }
    acc
}

#[inline(never)]
fn read_named(n: &Named<'_>) -> i64 {
    n.name.len() as i64 * 1000 + n.tail
}

#[inline(never)]
fn read_holder(h: &Holder<'_>) -> i64 {
    h.shape.area() * 1000 + h.tail
}

fn main() {
    let a = [3u8, 5, 7, 11];
    let b = [1u8, 2];

    let mut c = Cursor {
        state: &a,
        tail: 42,
    };
    println!("a {}", read_cursor(&c));
    set_slice(&mut c, &b);
    println!("b {}", read_cursor(&c));
    set_slice(&mut c, &a[1..]);
    println!("c {}", read_cursor(&c));
    set_slice(&mut c, &[]);
    println!("d {}", read_cursor(&c));

    let mut n = Named {
        name: "hello",
        tail: 7,
    };
    println!("e {}", read_named(&n));
    set_name(&mut n, "hi");
    println!("f {}", read_named(&n));

    let sq = Sq(4);
    let tr = Tri(5);
    let mut h = Holder {
        shape: &sq,
        tail: 9,
    };
    println!("g {}", read_holder(&h));
    set_shape(&mut h, &tr);
    println!("h {}", read_holder(&h));
}
