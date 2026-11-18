pub struct Ctx {
    pub id: u32,
    pub used: Vec<u32>,
}
#[inline(never)]
fn mk(n: u32) -> Ctx {
    let mut c = Ctx {
        id: n,
        used: Vec::new(),
    };
    let mut i = 0;
    while i < n {
        c.used.push(i);
        i += 1;
    }
    c
}
#[inline(never)]
fn total(c: &Ctx) -> u32 {
    let mut s = c.id;
    let mut i = 0;
    while i < c.used.len() {
        s += c.used[i];
        i += 1;
    }
    s
}
#[no_mangle]
pub extern "C" fn cap_collfield(n: u32) -> u32 {
    let c = mk(n);
    total(&c)
}
