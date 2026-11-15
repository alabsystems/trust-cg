// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Observe reference identity and live mutation before normal or unwinding drop.
use std::hint::black_box;

#[cfg(float_home)]
type Field = f64;
#[cfg(not(float_home))]
type Field = u64;
#[cfg(float_home)]
const INITIAL_A: Field = 10.25;
#[cfg(not(float_home))]
const INITIAL_A: Field = 10;
#[cfg(float_home)]
const INITIAL_B: Field = 20.25;
#[cfg(not(float_home))]
const INITIAL_B: Field = 20;
#[cfg(float_home)]
const REPLACEMENT: Field = 42.5;
#[cfg(not(float_home))]
const REPLACEMENT: Field = 42;
#[cfg(float_home)]
const INTERMEDIATE: Field = 31.75;
#[cfg(not(float_home))]
const INTERMEDIATE: Field = 31;

#[cfg_attr(padded_home, repr(C, align(16)))]
#[cfg_attr(not(padded_home), repr(transparent))]
struct Value(Field);

#[cfg(float_home)]
fn bits(value: Field) -> u64 {
    value.to_bits()
}
#[cfg(not(float_home))]
fn bits(value: Field) -> u64 {
    value
}

extern "C" {
    fn observe(a: &Value, b: &Value, same: i32, bits_a: u64, bits_b: u64, align: usize) -> usize;
    fn replace(a: &mut Value, old_address: usize, replacement: u64, extent: usize) -> i32;
    fn dropped(value: u64);
    fn drop_count() -> u64;
    fn drop_sum() -> u64;
    fn observation_count() -> u64;
}
impl Drop for Value {
    fn drop(&mut self) {
        unsafe {
            dropped(bits(self.0));
        }
    }
}

#[inline(never)]
fn rust_replace(value: &mut Value, replacement: Field) {
    value.0 = replacement;
}

#[inline(never)]
fn scenario(unwind: bool) {
    let mut a = Value(black_box(INITIAL_A));
    let b = Value(black_box(INITIAL_B));
    let align = std::mem::align_of::<Value>();
    let address = unsafe { observe(&a, &a, 1, bits(INITIAL_A), bits(INITIAL_A), align) };
    assert_ne!(address, 0);
    assert_eq!(
        unsafe { observe(&a, &b, 0, bits(INITIAL_A), bits(INITIAL_B), align) },
        address
    );
    rust_replace(&mut a, black_box(INTERMEDIATE));
    assert_eq!(
        unsafe { observe(&a, &b, 0, bits(INTERMEDIATE), bits(INITIAL_B), align) },
        address
    );
    assert_eq!(
        unsafe {
            replace(
                &mut a,
                address,
                bits(REPLACEMENT),
                std::mem::size_of::<Value>(),
            )
        },
        1
    );
    assert_eq!(bits(a.0), bits(REPLACEMENT));
    assert_eq!(
        unsafe { observe(&a, &b, 0, bits(REPLACEMENT), bits(INITIAL_B), align) },
        address
    );
    if unwind {
        panic!("intentional scalar-home cleanup");
    }
}

fn main() {
    assert_eq!(std::panic::catch_unwind(|| black_box(17u64)).unwrap(), 17);
    #[cfg(scalar_unwind)]
    assert!(std::panic::catch_unwind(|| scenario(black_box(true))).is_err());
    #[cfg(not(scalar_unwind))]
    scenario(black_box(false));
    let (count, sum, observations) = unsafe { (drop_count(), drop_sum(), observation_count()) };
    assert_eq!(count, 2);
    assert_eq!(sum, bits(REPLACEMENT).wrapping_add(bits(INITIAL_B)));
    assert_eq!(observations, 4);
    println!("{count} {sum} {observations}");
}
