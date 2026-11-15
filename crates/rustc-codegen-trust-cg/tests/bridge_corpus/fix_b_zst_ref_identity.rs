// (b) Reference identity of ZERO-SIZED places. rustc gives every borrowed local
// its own entry-block alloca, so `&f == &f` (same place) and `&f != &g`
// (distinct locals) at -O0. The places lane minted a FRESH alloca per BORROW,
// so `ptr::eq(&f, &f)` was false. Fixed: one placeholder per place, allocated
// once in the entry block (`zst_ref_placeholders`).
fn twice(x: i64) -> i64 { x * 2 }
fn same<F>(a: &F, b: &F) -> bool { core::ptr::eq(a, b) }
struct U;
#[inline(never)] fn addr<T>(r: &T) -> usize { r as *const T as usize }
fn main() {
    let f = twice;
    let g = twice;
    let a = same(&f, &f) as u32;
    let b = same(&f, &g) as u32;
    let p = &f as *const _ as usize;
    let q = &g as *const _ as usize;
    let u = U;
    let e = (addr(&u) == addr(&u)) as u32;
    println!("{} {} {} {} {} {}", a, b, (p != 0) as u32, (q != 0) as u32, e, f(21));
}
