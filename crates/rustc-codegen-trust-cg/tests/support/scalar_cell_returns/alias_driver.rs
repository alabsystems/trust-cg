unsafe extern "Rust" {
    fn alias_u64(before: u64, after: u64) -> u64;
    fn alias_i8(before: i8, after: i8) -> i8;
    fn alias_i32(before: i32, after: i32) -> i32;
    fn alias_u128(before: u128, after: u128) -> u128;
    fn alias_bool(before: bool, after: bool) -> bool;
    fn alias_f32(before: f32, after: f32) -> f32;
    fn alias_f64(before: f64, after: f64) -> f64;
    fn alias_pointer(before: *mut u8, after: *mut u8) -> *mut u8;
}
fn main() {
    let mut bytes = [0u8; 32];
    let mut state = 0x319a_b327_58af_115du64;
    let mut checks = 0;
    let edge32 = [
        0, 1, 0x80000000, 0x7f800000, 0xff800000, 0x7fc00123, 0xffc7abce, 0xffffffff,
    ];
    let edge64 = [
        0,
        1,
        0x8000000000000000,
        0x7ff0000000000000,
        0xfff0000000000000,
        0x7ff800001234abcd,
        0xfff8abce01234567,
        u64::MAX,
    ];
    for i in 0..2048 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let before = state;
        let after = state.rotate_left(29) ^ 0xfedc_ba98_7654_3210;
        let before128 = ((before as u128) << 64) | (!after as u128);
        let after128 = ((after as u128) << 64) | (!before as u128);
        let f32bits = if i < 8 { edge32[i] } else { after as u32 };
        let f64bits = if i < 8 { edge64[i] } else { after };
        let pointer = unsafe { bytes.as_mut_ptr().add(i % 32) };
        unsafe {
            assert_eq!(alias_u64(before, after), after);
            assert_eq!(alias_i8(before as i8, after as i8), after as i8);
            assert_eq!(alias_i32(before as i32, after as i32), after as i32);
            assert_eq!(alias_u128(before128, after128), after128);
            assert_eq!(alias_bool(i % 2 == 0, i % 2 != 0), i % 2 != 0);
            assert_eq!(
                alias_f32(f32::from_bits(before as u32), f32::from_bits(f32bits)).to_bits(),
                f32bits
            );
            assert_eq!(
                alias_f64(f64::from_bits(before), f64::from_bits(f64bits)).to_bits(),
                f64bits
            );
            assert_eq!(alias_pointer(bytes.as_mut_ptr(), pointer), pointer);
        }
        checks += 8;
    }
    assert_eq!(checks, 16384);
    println!("PASS scalar_cell_return_alias checks={checks}");
}
