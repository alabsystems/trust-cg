unsafe extern "C" {
    fn reference_identity_driver() -> i32;
}
fn main() {
    assert_eq!(unsafe { reference_identity_driver() }, 0);
}
