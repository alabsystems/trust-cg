use projected_aggregate_types::Union24;
unsafe extern "Rust" {
    fn selected(value: Union24, salt: u64) -> u64;
}
fn main() {
    let mut state = 0xa762_bc41_d58e_09f3u64;
    for i in 0..32768 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let a = if i < 64 { 1u64 << i } else { state };
        let b = !state;
        let c = state.wrapping_mul(0x9e37_79b9_7f4a_7c15);
        let salt = state.rotate_left(29);
        let value = Union24 { words: [a, b, c] };
        let actual = unsafe { selected(value, salt) };
        assert_eq!(
            actual,
            a.rotate_left(7) ^ b.wrapping_add(salt) ^ c.rotate_right(11)
        );
        assert_eq!(unsafe { value.words }, [a, b, c]);
    }
    println!("PASS projected_union_tuple checks=65536");
}
