#[inline(never)]
fn hit(v: &[i64], lo: i64, hi: i64) -> bool {
    v.iter().any(|x| *x >= lo && *x < hi)
}
#[no_mangle]
pub extern "C" fn cap_terminal(a: i64, b: i64, c: i64) -> u32 {
    let v = [a, b, c];
    hit(&v, b, c) as u32
}
