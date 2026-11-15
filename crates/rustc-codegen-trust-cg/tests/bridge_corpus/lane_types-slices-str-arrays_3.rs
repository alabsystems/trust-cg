// CORPUS FIXTURE — lane types-slices-str-arrays #3: a NESTED-ARRAY pointee.
//
// `&[[u8; 4]; 3]` (the shape of `core::unicode::bitset_search`'s chunk table)
// is typed as a thin pointer to the flat memory slot; every `t[i][j]` read walks
// `data + i*4 + j` over rustc's layout with RUNTIME indices. The printed values
// depend on both strides, so a wrong stride or a dropped inner index diverges
// from LLVM.
#[inline(never)]
fn pick(t: &[[u8; 4]; 3], i: usize, j: usize) -> u8 { t[i][j] }
#[inline(never)]
fn row_sum(t: &[[u8; 4]; 3], i: usize) -> u32 {
    let mut s = 0u32;
    let mut j = 0;
    while j < 4 { s += t[i][j] as u32; j += 1; }
    s
}
#[inline(never)]
fn corner(t: &[[u16; 3]; 2]) -> u32 { t[0][0] as u32 * 1000 + t[1][2] as u32 }
fn main() {
    let t: [[u8; 4]; 3] = [[1, 2, 3, 4], [10, 20, 30, 40], [7, 8, 9, 11]];
    println!("{} {} {}", pick(&t, 0, 3), pick(&t, 1, 1), pick(&t, 2, 0));
    println!("{} {} {}", row_sum(&t, 0), row_sum(&t, 1), row_sum(&t, 2));
    let w: [[u16; 3]; 2] = [[5, 6, 7], [8, 9, 12]];
    println!("{}", corner(&w));
}
