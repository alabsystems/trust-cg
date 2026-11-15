unsafe extern "Rust" {
    fn zeroed_words() -> u64;
    fn zeroed_option() -> bool;
}
fn main() {
    for _ in 0..4096 {
        unsafe {
            assert_eq!(zeroed_words(), 0);
            assert!(zeroed_option());
        }
    }
    println!("PASS intrinsic_validity checks=8192");
}
