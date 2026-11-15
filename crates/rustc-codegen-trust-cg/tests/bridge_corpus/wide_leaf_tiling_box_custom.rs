// The `Box<core::io::error::Custom>::new` shape, spelled in a user crate:
// a struct whose rustc layout holds a `NonNull<dyn Trait>` (a {data, vtable}
// pair behind `repr(transparent)` + a `!null` pattern type), two fn pointers
// and a one-byte enum, moved whole into a fresh `Box`.
#![allow(dead_code, internal_features)]
#![feature(core_intrinsics)]
use std::ptr::NonNull;

trait Tr {
    fn v(&self) -> u64;
}
struct A(u64);
impl Tr for A {
    fn v(&self) -> u64 {
        self.0 * 3 + 1
    }
}
struct B2(u64, u64);
impl Tr for B2 {
    fn v(&self) -> u64 {
        self.0 * 1000 + self.1
    }
}

#[derive(Clone, Copy)]
#[repr(u8)]
enum Kind {
    X = 1,
    Y = 7,
}

struct Custom {
    kind: Kind,
    error: NonNull<dyn Tr>,
    error_drop: unsafe fn(*mut dyn Tr),
    outer_drop: unsafe fn(*mut Custom),
}

static mut LOG: u64 = 0;
static SA: A = A(13);
static SB: B2 = B2(4, 56);

unsafe fn drop_err(p: *mut dyn Tr) {
    unsafe { LOG = LOG * 10 + (*p).v() % 10 };
}
unsafe fn drop_outer(p: *mut Custom) {
    unsafe { LOG = LOG * 10 + (*p).kind as u64 };
}

/// `Box::new`'s own body (library/alloc/src/boxed.rs), spelled in this crate:
/// a user crate's `Box::new` call is intercepted by the bridge, alloc's is not.
#[inline(never)]
fn mk(x: Custom) -> Box<Custom> {
    let ptr = unsafe { std::alloc::alloc(std::alloc::Layout::new::<Custom>()) } as *mut Custom;
    unsafe { core::intrinsics::write_via_move(ptr, x) };
    unsafe { std::mem::transmute::<*mut Custom, Box<Custom>>(ptr) }
}

#[inline(never)]
fn build(k: Kind, e: &'static dyn Tr) -> Custom {
    Custom {
        kind: k,
        error: unsafe { NonNull::new_unchecked(e as *const dyn Tr as *mut dyn Tr) },
        error_drop: drop_err,
        outer_drop: drop_outer,
    }
}

#[inline(never)]
fn use_box(b: &Box<Custom>) -> u64 {
    let e = unsafe { b.error.as_ref() };
    let mut r = e.v();
    r = r * 100 + b.kind as u64;
    unsafe { (b.error_drop)(b.error.as_ptr()) };
    unsafe { (b.outer_drop)(&**b as *const Custom as *mut Custom) };
    r
}

fn main() {
    let a: &'static A = &SA;
    let b: &'static B2 = &SB;
    let c1 = build(Kind::Y, a);
    let bx1 = mk(c1);
    let c2 = build(Kind::X, b);
    let bx2 = mk(c2);
    let r1 = use_box(&bx1);
    println!("{}", r1);
    let r2 = use_box(&bx2);
    println!("{}", r2);
    let log = unsafe { LOG };
    println!("{}", log);
    let sz = std::mem::size_of::<Custom>();
    println!("{}", sz);
}
