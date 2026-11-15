unsafe extern "C" {
    fn variadic_driver() -> i32;
}
fn main() {
    assert_eq!(unsafe { variadic_driver() }, 0);
}
