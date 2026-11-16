#[derive(Clone, Copy, PartialEq)]
pub struct Name(pub u32);
#[derive(Clone, Copy)]
pub struct Ind {
    pub tag: u8,
    pub name: Name,
    pub w: u64,
}
#[no_mangle]
pub extern "C" fn cap_find(all: &[Ind; 3], n: &Name) -> usize {
    let all: &[Ind] = all;
    let mut i = 0;
    while i < all.len() {
        if &all[i].name == n {
            return i;
        }
        i += 1;
    }
    9
}
#[no_mangle]
pub extern "C" fn cap_bump(all: &mut [Ind; 3], i: usize) {
    let all: &mut [Ind] = all;
    let r = &mut all[i].name;
    r.0 += 3;
}
