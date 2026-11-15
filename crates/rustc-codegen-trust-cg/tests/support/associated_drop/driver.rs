use std::sync::Mutex;
static LOG: Mutex<Vec<(u64, usize)>> = Mutex::new(Vec::new());
static OWNED: Mutex<Vec<usize>> = Mutex::new(Vec::new());
static COUNTS: Mutex<(usize, usize)> = Mutex::new((0, 0));
extern "C" fn record(id: u64, ptr: usize) {
    LOG.lock().unwrap().push((id, ptr));
}
#[unsafe(no_mangle)]
pub extern "C" fn associated_zero() {
    record(901, 0);
}
#[unsafe(no_mangle)]
pub extern "C" fn associated_allocate(value: u64) -> *mut u64 {
    let p = Box::into_raw(Box::new(value));
    OWNED.lock().unwrap().push(p as usize);
    COUNTS.lock().unwrap().0 += 1;
    p
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn associated_release(p: *mut u64) {
    let mut owned = OWNED.lock().unwrap();
    let i = owned
        .iter()
        .position(|&q| q == p as usize)
        .expect("exactly-once free");
    owned.swap_remove(i);
    unsafe {
        drop(Box::from_raw(p));
    }
    COUNTS.lock().unwrap().1 += 1;
}
type Observe = extern "C" fn(u64, usize);
unsafe extern "C" {
    fn associated_leaf(seed: u64, cb: Observe, owned: bool);
    fn associated_array(seed: u64, cb: Observe, owned: bool);
    fn associated_tuple(seed: u64, cb: Observe, owned: bool);
    fn associated_nested(seed: u64, cb: Observe, owned: bool);
    fn associated_option(seed: u64, cb: Observe, owned: bool);
    fn associated_zero_case(seed: u64, owned: bool);
    fn associated_replace(seed: u64, cb: Observe, owned: bool);
    fn associated_buffer(seed: u64, cb: Observe, ptr: *const u64, len: usize, owned: bool);
}
fn check(want: &[u64], checks: &mut usize) {
    let mut log = LOG.lock().unwrap();
    assert_eq!(log.iter().map(|e| e.0).collect::<Vec<_>>(), want);
    for &(id, p) in log.iter() {
        if id != 901 {
            assert!(p != 0 && p % 8 == 0);
        }
    }
    log.clear();
    *checks += 1;
}
fn main() {
    let mut checks = 0;
    let data = [11, 12, 13, 14];
    for i in 0..1024_u64 {
        let seed = i.wrapping_mul(0x9e3779b97f4a7c15);
        let a = seed ^ 0x5a;
        let b = seed ^ 123 ^ 0x5a;
        let c = seed ^ 234 ^ 0x5a;
        let values = [a, b, c];
        let without_payload = [a, c];
        let buffer_value = [seed ^ 7 ^ 1];
        for owned in [false, true] {
            unsafe {
                associated_leaf(seed, record, owned);
                check(if owned { &values[..1] } else { &[] }, &mut checks);
                associated_array(seed, record, owned);
                check(if owned { &values } else { &[] }, &mut checks);
                associated_tuple(seed, record, owned);
                check(if owned { &values[..2] } else { &[] }, &mut checks);
                associated_nested(seed, record, owned);
                check(if owned { &values[..2] } else { &[] }, &mut checks);
                associated_option(seed, record, owned);
                check(if owned { &values } else { &without_payload }, &mut checks);
                associated_zero_case(seed, owned);
                check(if owned { &[901] } else { &[] }, &mut checks);
                associated_replace(seed, record, owned);
                check(
                    if owned { &values[..2] } else { &values[1..2] },
                    &mut checks,
                );
                associated_buffer(seed, record, data.as_ptr(), (i % 5) as usize, owned);
                check(if owned { &buffer_value } else { &[] }, &mut checks);
                assert!(OWNED.lock().unwrap().is_empty());
            }
        }
        assert_eq!(
            *COUNTS.lock().unwrap(),
            ((i + 1) as usize, (i + 1) as usize)
        );
    }
    println!("PASS associated_drop checks={checks}");
}
