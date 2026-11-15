use core::cell::Cell;
macro_rules! wrapper {
    ($name:ident, $ty:ty) => {
        #[repr(transparent)]
        pub struct $name(pub $ty);
    };
}
wrapper!(Word, u64);
wrapper!(Signed, i32);
wrapper!(Wide, u128);
wrapper!(Float32, f32);
wrapper!(Float64, f64);
wrapper!(Flag, bool);
wrapper!(Character, char);
wrapper!(Address, *mut u8);
wrapper!(CellWord, Cell<u64>);
unsafe extern "Rust" {
    fn cell_word(value: u64, present: bool) -> Word;
    fn cell_signed(value: i32, present: bool) -> Signed;
    fn cell_wide(value: u128, present: bool) -> Wide;
    fn cell_float32(value: f32, present: bool) -> Float32;
    fn cell_float64(value: f64, present: bool) -> Float64;
    fn cell_bool(value: bool, present: bool) -> Flag;
    fn cell_char(value: char, present: bool) -> Character;
    fn cell_pointer(value: *mut u8, present: bool) -> Address;
    fn cell_mutated(value: u64, delta: u64, branch: bool) -> CellWord;
}
fn main() {
    let boundaries = [0, 1, u64::MAX, 1 << 63, (1 << 63) - 1, 0xffff, 0xffffffff];
    let f32_edges = [
        0, 0x80000000, 0x7f800000, 0xff800000, 0x7fc12345, 0x7f812345, 1, 0x007fffff, 0x00800000,
        0x7f7fffff,
    ];
    let f64_edges = [
        0,
        0x8000000000000000,
        0x7ff0000000000000,
        0xfff0000000000000,
        0x7ff8123456789abc,
        0x7ff0123456789abc,
        1,
        0x000fffffffffffff,
        0x0010000000000000,
        0x7fefffffffffffff,
    ];
    let chars = [
        '\0',
        'a',
        '\u{d7ff}',
        '\u{e000}',
        '\u{ffff}',
        '\u{10000}',
        '\u{10ffff}',
    ];
    let mut bytes = [0u8; 13];
    let mut random = 0x91e10da5c79e7b1du64;
    let mut checks = 0;
    for index in 0..4096 {
        random ^= random << 13;
        random ^= random >> 7;
        random ^= random << 17;
        let word = boundaries.get(index).copied().unwrap_or(random);
        let wide = ((word as u128) << 64) | random.rotate_left(19) as u128;
        let f32_bits = f32_edges.get(index).copied().unwrap_or(random as u32);
        let f64_bits = f64_edges.get(index).copied().unwrap_or(random);
        let character = chars[index % chars.len()];
        let address = unsafe { bytes.as_mut_ptr().add(index % bytes.len()) };
        let delta = random.rotate_left(29);
        for present in [false, true] {
            unsafe {
                assert_eq!(cell_word(word, present).0, word);
                assert_eq!(cell_signed(word as i32, present).0, word as i32);
                assert_eq!(cell_wide(wide, present).0, wide);
                assert_eq!(
                    cell_float32(f32::from_bits(f32_bits), present).0.to_bits(),
                    f32_bits
                );
                assert_eq!(
                    cell_float64(f64::from_bits(f64_bits), present).0.to_bits(),
                    f64_bits
                );
                assert_eq!(cell_bool(word & 1 != 0, present).0, word & 1 != 0);
                assert_eq!(cell_char(character, present).0, character);
                assert_eq!(cell_pointer(address, present).0, address);
                let change = if present {
                    delta
                } else {
                    delta.rotate_left(17)
                };
                assert_eq!(
                    cell_mutated(word, delta, present).0.get(),
                    word.wrapping_add(change)
                );
            }
            checks += 9;
        }
    }
    assert_eq!(bytes, [0; 13]);
    assert_eq!(checks, 73728);
    println!("PASS scalar_cell_returns checks={checks}");
}
