use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
#[repr(C)]
pub struct Mixed {
    pub integer: i64,
    pub real: f64,
    pub boolean: bool,
    pub character: char,
}
pub enum Payload {
    Empty,
    Value { prefix: u8, integer: i64 },
}
static INTEGER: AtomicUsize = AtomicUsize::new(0);
static REAL: AtomicUsize = AtomicUsize::new(0);
static BOOLEAN: AtomicUsize = AtomicUsize::new(0);
static CHARACTER: AtomicUsize = AtomicUsize::new(0);
static CHECKS: AtomicUsize = AtomicUsize::new(0);
fn equal<T: PartialEq + std::fmt::Debug>(a: T, b: T) {
    assert_eq!(a, b);
    CHECKS.fetch_add(1, Relaxed);
}
unsafe extern "Rust" {
    fn borrow_fields(value: &Mixed) -> u64;
    fn borrow_deep(value: &Mixed) -> u64;
    fn borrow_payload(value: &Payload) -> u64;
    fn borrow_array(seed: u64) -> u64;
}
#[unsafe(no_mangle)]
pub fn observe_integer(value: &&i64) -> u64 {
    equal(*value as *const i64 as usize, INTEGER.load(Relaxed));
    **value as u64
}
#[unsafe(no_mangle)]
pub fn observe_real(value: &&f64) -> u64 {
    equal(*value as *const f64 as usize, REAL.load(Relaxed));
    value.to_bits()
}
#[unsafe(no_mangle)]
pub fn observe_boolean(value: &&bool) -> u64 {
    equal(*value as *const bool as usize, BOOLEAN.load(Relaxed));
    u64::from(**value)
}
#[unsafe(no_mangle)]
pub fn observe_character(value: &&char) -> u64 {
    equal(*value as *const char as usize, CHARACTER.load(Relaxed));
    **value as u64
}
#[unsafe(no_mangle)]
pub fn observe_deep(value: &&&&i64) -> u64 {
    equal(***value as *const i64 as usize, INTEGER.load(Relaxed));
    ****value as u64
}
#[unsafe(no_mangle)]
pub fn observe_array(value: &[u64; 3], address: usize, seed: u64) -> u64 {
    equal(value as *const [u64; 3] as usize, address);
    equal(*value, [seed, seed.wrapping_add(3), seed ^ 0xfeedface]);
    value[0] ^ value[1] ^ value[2]
}
fn main() {
    for i in 0..512u64 {
        let seed = i.wrapping_mul(0x9e3779b97f4a7c15);
        let value = Mixed {
            integer: seed as i64,
            real: f64::from_bits(seed),
            boolean: i % 2 == 0,
            character: ['a', '\u{10ffff}', '\u{0}', '\u{1f642}'][i as usize % 4],
        };
        INTEGER.store(&value.integer as *const i64 as usize, Relaxed);
        REAL.store(&value.real as *const f64 as usize, Relaxed);
        BOOLEAN.store(&value.boolean as *const bool as usize, Relaxed);
        CHARACTER.store(&value.character as *const char as usize, Relaxed);
        equal(
            unsafe { borrow_fields(&value) },
            value.integer as u64
                ^ value.real.to_bits()
                ^ u64::from(value.boolean)
                ^ value.character as u64,
        );
        equal(unsafe { borrow_deep(&value) }, value.integer as u64);
        equal(unsafe { borrow_payload(&Payload::Empty) }, 17);
        let payload = Payload::Value {
            prefix: i as u8,
            integer: !seed as i64,
        };
        if let Payload::Value { ref integer, .. } = payload {
            INTEGER.store(integer as *const i64 as usize, Relaxed);
        }
        equal(unsafe { borrow_payload(&payload) }, !seed);
        equal(
            unsafe { borrow_array(seed) },
            seed ^ seed.wrapping_add(3) ^ (seed ^ 0xfeedface),
        );
    }
    println!(
        "PASS format_reference_expanded checks={}",
        CHECKS.load(Relaxed)
    );
}
