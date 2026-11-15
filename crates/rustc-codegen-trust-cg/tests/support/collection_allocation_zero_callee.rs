#[inline(never)]
pub fn vnew() -> Vec<u64> {
    Vec::new()
}
#[inline(never)]
pub fn vzero() -> Vec<u64> {
    Vec::with_capacity(0)
}
#[inline(never)]
pub fn snew() -> String {
    String::new()
}
#[inline(never)]
pub fn szero() -> String {
    String::with_capacity(0)
}
