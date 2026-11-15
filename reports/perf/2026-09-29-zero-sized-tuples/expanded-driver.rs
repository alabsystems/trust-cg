use std::sync::atomic::{AtomicU64, Ordering};
static EVENTS: AtomicU64 = AtomicU64::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn zst_event(code: u64) { let old = EVENTS.load(Ordering::Relaxed); EVENTS.store(old*10+code,Ordering::Relaxed); }
unsafe extern "C" {
    fn unit_call(seed:u64)->u64;
    fn flow_map(seed:u64)->u64;
    fn nested_mut(seed:u64)->u64;
    fn tuple_pointer(seed:u64)->u64;
    fn tuple_arguments(seed:u64)->u64;
    fn tuple_drop(seed:u64)->u64;
    fn tuple_alignment(seed:u64)->u64;
    fn tuple_return(seed:u64)->u64;
}
fn main() {
    for index in 0..4096u64 {
        let seed = index.wrapping_mul(0x9e3779b97f4a7c15);
        EVENTS.store(0,Ordering::Relaxed);
        unsafe {
            assert_eq!(unit_call(seed),seed.wrapping_add(17));
            assert_eq!(flow_map(seed),seed.wrapping_add(if seed&1==0 {7}else{11}));
            assert_eq!(nested_mut(seed),seed.wrapping_add(19)^seed.wrapping_add(38));
            assert_eq!(tuple_pointer(seed),seed.wrapping_add(31));
            assert_eq!(tuple_arguments(seed),seed.rotate_left(23));
            assert_eq!(tuple_drop(seed),seed.wrapping_add(23));
            assert_eq!(tuple_alignment(seed),seed);
            assert_eq!(tuple_return(seed),seed);
        }
        assert_eq!(EVENTS.load(Ordering::Relaxed),35);
    }
    println!("PASS zero_sized_tuples checks=36864");
}
