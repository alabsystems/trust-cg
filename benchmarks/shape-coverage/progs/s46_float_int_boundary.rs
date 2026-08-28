// float->int at the EXACT saturation boundary (iN::MAX vs iN::MAX+1, just-below
// fractionals) — the precise edge of the f243d837 saturation fix; complements the
// out-of-range s37/s38.
use std::hint::black_box as bb;
fn main() {
    let mut acc: u64 = 0;
    // exact boundary f64 values around i32/u32/i16/u8 limits
    let fs: [f64; 12] = [bb(2147483647.0), bb(2147483648.0), bb(2147483647.9), bb(-2147483648.0),
                         bb(-2147483649.0), bb(4294967295.0), bb(4294967296.0), bb(32767.0), bb(32768.0),
                         bb(255.0), bb(255.9), bb(256.0)];
    for &f in fs.iter() {
        acc = acc.wrapping_add(f as i32 as u32 as u64).wrapping_add(f as u32 as u64);
        acc = acc.wrapping_add(f as i16 as u16 as u64).wrapping_add(f as u8 as u64);
    }
    std::process::exit((acc % 241) as i32);
}
