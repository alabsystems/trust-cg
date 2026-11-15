#![no_std]
#[unsafe(no_mangle)]
pub fn read_dependent(data: &[u8], mut a: u64, mut b: u64) -> (u64, u64) {
    let mut index = 0;
    while let Some(&byte) = data.get(index) {
        let old_a = a;
        a = b;
        b = old_a.wrapping_add(byte as u64);
        index += 1;
    }
    (a, b)
}
