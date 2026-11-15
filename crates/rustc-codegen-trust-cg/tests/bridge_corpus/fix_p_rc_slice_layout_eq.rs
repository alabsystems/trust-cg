// `Rc<[u8]>` / `Arc<[u8]>` from a slice: `Rc::try_allocate_for_layout` /
// `Arc::initialize_arcinner` compare two `Layout`s with `debug_assert_eq!`,
// whose inlined `PartialEq` reads `discriminant((align.0: AlignmentEnum))` of
// a single-scalar `Alignment` newtype local. The exit code folds the lengths,
// bytes read back through both pointers and the strong count.
use std::rc::Rc;
use std::sync::Arc;
#[inline(never)]
fn mk_rc(v: &[u8]) -> Rc<[u8]> {
    Rc::from(v)
}
#[inline(never)]
fn mk_arc(v: &[u8]) -> Arc<[u8]> {
    Arc::from(v)
}
fn main() {
    let r = mk_rc(std::hint::black_box(b"hello"));
    let a = mk_arc(std::hint::black_box(b"worlds"));
    let r2 = Rc::clone(&r);
    let x = r.len() as u64 * 7 + r[1] as u64 + r[4] as u64 * 3
        + a.len() as u64 * 11 + a[0] as u64 * 5 + a[5] as u64
        + Rc::strong_count(&r2) as u64 * 13;
    std::process::exit((x % 251) as i32);
}
