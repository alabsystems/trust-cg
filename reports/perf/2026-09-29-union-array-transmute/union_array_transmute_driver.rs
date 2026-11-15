unsafe extern "C" {
    fn zeroed_fixed() -> u64;
    fn zeroed_four(seed: u64, index: usize) -> u64;
    fn assume_four(seed: u64, index: usize) -> u64;
    fn union_four(seed: u64, index: usize) -> u64;
    fn packed_three(seed: u64, index: usize) -> u64;
    fn branch_four(seed: u64, index: usize) -> u64;
    fn nested_words(seed: u64, index: usize) -> u64;
    fn pointer_words(seed: u64, index: usize) -> u64;
    fn float_words(seed: u64, index: usize) -> u64;
}

fn main() {
    for index in 0..4096usize {
        let seed = (index as u64).wrapping_mul(0x9e3779b97f4a7c15);
        let words = [seed, !seed, seed.rotate_left(17), seed.wrapping_add(91)];
        let rotated = if index & 4 == 0 {
            words
        } else {
            [words[1], words[0], words[3], words[2]]
        };
        let floats = [seed as f64, (seed as u32) as f64, -1.25, 0.0];
        unsafe {
            assert_eq!(zeroed_fixed(), 0);
            assert_eq!(
                zeroed_four(seed, index),
                seed.rotate_left([0, 7, 19, 37][index & 3])
            );
            assert_eq!(assume_four(seed, index), words[index & 3]);
            assert_eq!(union_four(seed, index), words[index & 3]);
            assert_eq!(packed_three(seed, index), words[index % 3]);
            assert_eq!(branch_four(seed, index), rotated[index & 3]);
            assert_eq!(nested_words(seed, index), words[index & 3]);
            assert_eq!(pointer_words(seed, index), words[index & 1]);
            assert_eq!(float_words(seed, index), floats[index & 3].to_bits());
        }
    }
    println!("PASS union_array_transmute checks=36864");
}
