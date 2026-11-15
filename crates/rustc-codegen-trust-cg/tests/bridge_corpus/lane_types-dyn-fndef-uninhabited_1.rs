// CORPUS FIXTURE (lane types-dyn-fndef-uninhabited, #1) — function ITEMS as
// VALUES. A `ty::FnDef` is a zero-sized value whose callee is fixed by its type;
// the bridge used to fail every generic combinator instantiated with one closed
// on `Ty::FnDef(..)`, and rustc's `FnPtrShim` `call*` bodies over it (`self(args)`
// with a `FnDef`-typed PLACE callee) were emitted as trapping stubs. Now: the
// type maps to `Unit`, a `FnDef`-typed place callee resolves statically
// (`direct_callee_instance`), `_f2 = move _f` of a ZST binds nothing, `&f` /
// `&mut f` of a ZST is a dangling aligned address, and a failed shim over a fn
// item FAILS CLOSED (it is statically reachable) instead of trapping.
// Exercises `Option::map` / `is_some_and` with fn items (an enum constructor, a
// `From::from`, an inherent method), and `FnOnce` / `FnMut` / `Fn` shims.
// Function ITEMS (zero-sized `FnDef` values) passed as the `F` of generic
// combinators and called through rustc's `FnPtrShim` `call*` bodies.
#[derive(Clone, Copy)]
enum Addr { V4(u32), V6(u64) }
fn make(x: Option<u32>) -> Option<Addr> { x.map(Addr::V4) }
fn widen(x: Option<i32>) -> Option<i64> { x.map(i64::from) }
fn lt(o: Option<core::cmp::Ordering>) -> bool { o.is_some_and(core::cmp::Ordering::is_lt) }
fn twice(x: i64) -> i64 { x * 2 }
fn add(a: i64, b: i64) -> i64 { a + b }
fn apply<F: FnOnce(i64) -> i64>(f: F, v: i64) -> i64 { f(v) }
fn apply_mut<F: FnMut(i64) -> i64>(mut f: F, v: i64) -> i64 { f(v) + f(v) }
fn apply2<F: Fn(i64, i64) -> i64>(f: F, a: i64, b: i64) -> i64 { f(a, b) * f(b, a) }
fn main() {
    let a = match make(Some(5)) { Some(Addr::V4(v)) => v as i64, Some(Addr::V6(v)) => v as i64, None => -1 };
    let b = match make(None) { Some(Addr::V4(v)) => v as i64, Some(Addr::V6(v)) => v as i64, None => -1 };
    let c = widen(Some(-7)).unwrap_or(0);
    let e = lt(Some(core::cmp::Ordering::Less)) as i64;
    let f = lt(Some(core::cmp::Ordering::Greater)) as i64;
    let g = apply(twice, 21);
    let h = apply_mut(twice, 5);
    let i = apply2(add, 3, 4);
    println!("{} {} {} {} {} {} {} {}", a, b, c, e, f, g, h, i);
}
