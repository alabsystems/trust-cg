pub static mut LOG: u32 = 0;
pub struct G(pub u32);
impl Drop for G {
    fn drop(&mut self) {
        unsafe {
            LOG = LOG.wrapping_mul(31).wrapping_add(self.0);
        }
    }
}
#[no_mangle]
pub extern "C" fn cap_box(x: u32) -> u32 {
    let b = Box::new(G(x));
    let o: Option<Box<G>> = Some(Box::new(G(x + 1)));
    drop(o);
    drop(b);
    unsafe { LOG }
}
