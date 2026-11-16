#[derive(Clone, Copy)]
pub struct Lr {
    pub start: u32,
    pub end: u32,
}
#[no_mangle]
pub extern "C" fn unflatten(flat: &[u32; 8], out: &mut [Lr; 4]) {
    let mut i = 0;
    while i < 4 {
        out[i] = Lr {
            start: flat[2 * i],
            end: flat[2 * i + 1],
        };
        i += 1;
    }
}
#[no_mangle]
pub extern "C" fn copy_el(out: &mut [Lr; 4], i: usize, j: usize) {
    out[i] = out[j];
}
