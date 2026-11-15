use std::sync::Mutex;
static LOG: Mutex<Vec<(u64, usize)>> = Mutex::new(Vec::new());
extern "C" fn record(n: u64, p: usize) {
    LOG.lock().unwrap().push((n, p));
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_zero() {
    record(901, 0);
}
static OWNED: Mutex<Vec<usize>> = Mutex::new(Vec::new());
static COUNTS: Mutex<(usize, usize)> = Mutex::new((0, 0));
#[unsafe(no_mangle)]
pub extern "C" fn structural_allocate(value: u64) -> *mut u64 {
    let p = Box::into_raw(Box::new(value));
    OWNED.lock().unwrap().push(p as usize);
    COUNTS.lock().unwrap().0 += 1;
    p
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn structural_release(p: *mut u64) {
    let mut owned = OWNED.lock().unwrap();
    let i = owned
        .iter()
        .position(|&q| q == p as usize)
        .expect("allocation freed exactly once");
    owned.swap_remove(i);
    unsafe {
        drop(Box::from_raw(p));
    }
    COUNTS.lock().unwrap().1 += 1;
}
unsafe extern "C" {
    fn structural_owned(seed: u64, cb: extern "C" fn(u64, usize), reverse: bool);
    fn structural_pair(seed: u64, cb: extern "C" fn(u64, usize));
    fn structural_parent(seed: u64, cb: extern "C" fn(u64, usize));
    fn structural_partial(seed: u64, cb: extern "C" fn(u64, usize), flag: bool);
    fn structural_tuple(seed: u64, cb: extern "C" fn(u64, usize));
    fn structural_choice(seed: u64, cb: extern "C" fn(u64, usize), flag: u8);
    fn structural_option(seed: u64, cb: extern "C" fn(u64, usize), flag: bool);
    fn structural_array(seed: u64, cb: extern "C" fn(u64, usize));
    fn structural_replace(seed: u64, cb: extern "C" fn(u64, usize));
    fn structural_pointer(seed: u64, cb: extern "C" fn(u64, usize));
    fn structural_zero_field(seed: u64, cb: extern "C" fn(u64, usize));
}
fn check(expected: &[u64], count: &mut usize) {
    let mut log = LOG.lock().unwrap();
    assert_eq!(log.iter().map(|r| r.0).collect::<Vec<_>>(), expected);
    for &(id, p) in log.iter() {
        if ![900, 901].contains(&id) {
            assert!(p != 0 && p % 8 == 0);
        }
    }
    log.clear();
    *count += 1;
}
fn main() {
    let mut checks = 0;
    for i in 0..1024_u64 {
        let seed = i.wrapping_mul(0x9e3779b97f4a7c15);
        let a = seed ^ 0x5a;
        let b = seed ^ 123 ^ 0x5a;
        unsafe {
            structural_owned(seed, record, false);
            check(&[a, b], &mut checks);
            structural_owned(seed, record, true);
            check(&[b, a], &mut checks);
            assert!(OWNED.lock().unwrap().is_empty());
            assert_eq!(
                *COUNTS.lock().unwrap(),
                (((i + 1) * 4) as usize, ((i + 1) * 4) as usize)
            );
            structural_pair(seed, record);
            check(&[a, b], &mut checks);
            structural_parent(seed, record);
            check(&[900, a ^ 0x1234, b ^ 0x4321], &mut checks);
            structural_partial(seed, record, false);
            check(&[a, b], &mut checks);
            structural_partial(seed, record, true);
            check(&[b, a], &mut checks);
            structural_tuple(seed, record);
            check(&[a, b], &mut checks);
            structural_choice(seed, record, 0);
            check(&[], &mut checks);
            structural_choice(seed, record, 1);
            check(&[a], &mut checks);
            structural_choice(seed, record, 2);
            check(&[a, b], &mut checks);
            structural_option(seed, record, false);
            check(&[], &mut checks);
            structural_option(seed, record, true);
            check(&[a], &mut checks);
            structural_array(seed, record);
            check(&[a, b, seed ^ 234 ^ 0x5a], &mut checks);
            structural_replace(seed, record);
            check(&[a, seed ^ 345 ^ 0x5a, b], &mut checks);
            structural_pointer(seed, record);
            {
                let mut log = LOG.lock().unwrap();
                assert_eq!(log.len(), 4);
                assert_eq!((log[0].0, log[1].0), (1000, 1001));
                assert_eq!(log[0].1, log[2].1);
                assert_eq!(log[1].1, log[3].1);
                assert_ne!(log[0].1, log[1].1);
                log.drain(..2);
            }
            check(&[a, b], &mut checks);
            structural_zero_field(seed, record);
            check(&[901, a, 901], &mut checks);
        }
    }
    println!("PASS structural_drop checks={checks}");
}
