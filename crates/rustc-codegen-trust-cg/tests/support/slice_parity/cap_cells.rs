#[derive(Clone, Copy, PartialEq)]
pub struct Name(pub u32);
#[inline(never)]
fn first(all: &[&Name], n: Name) -> u32 {
    let mut i = 0;
    while i < all.len() {
        if *all[i] == n {
            return i as u32;
        }
        i += 1;
    }
    99
}
#[no_mangle]
pub extern "C" fn cap_cells(a: u32, b: u32, c: u32) -> u32 {
    let x = Name(a);
    let y = Name(b);
    let one = [&x];
    let two = [&x, &y];
    let all: &[&Name] = if c >= 2 { &two } else { &one };
    first(all, Name(b))
}
