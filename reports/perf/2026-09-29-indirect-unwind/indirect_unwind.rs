#![no_std]
#[repr(C)]
pub struct Words {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub d: u64,
}
#[repr(C)]
pub struct Pair {
    pub a: u64,
    pub b: u64,
}
#[repr(C)]
pub struct Floats {
    pub a: f64,
    pub b: f64,
    pub c: f64,
}
unsafe extern "Rust" {
    fn aggregate_read_union(slot: &mut core::mem::MaybeUninit<u64>) -> u64;
}
unsafe extern "C" {
    fn aggregate_event(kind: u64, value: u64);
}
struct Guard(*const u64);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { aggregate_event(5, *self.0) }
    }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_rust_pair(
    callback: unsafe extern "Rust" fn(&mut u64, u64) -> (u64, u64),
    v: u64,
) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let pair = unsafe { callback(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    pair.0 ^ pair.1 ^ cell
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_pair(
    callback: unsafe extern "C-unwind" fn(&mut u64, u64) -> Pair,
    v: u64,
) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let pair = unsafe { callback(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    pair.a ^ pair.b ^ cell
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_floats(
    callback: unsafe extern "C-unwind" fn(&mut u64, u64) -> Floats,
    v: u64,
) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let floats = unsafe { callback(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    floats.a.to_bits() ^ floats.b.to_bits() ^ floats.c.to_bits() ^ cell
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_union(
    callback: unsafe extern "Rust" fn(&mut u64, u64) -> core::mem::MaybeUninit<u64>,
    v: u64,
) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let mut storage = unsafe { callback(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    unsafe { aggregate_read_union(&mut storage) ^ cell }
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_scalar(
    callback: unsafe extern "C-unwind" fn(&mut u64, u64) -> u64,
    v: u64,
) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let result = unsafe { callback(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    result ^ cell
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_wide(
    callback: unsafe extern "C-unwind" fn(&mut u64, u64) -> u128,
    v: u64,
) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let result = unsafe { callback(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    result as u64 ^ (result >> 64) as u64 ^ cell
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_many(
    callback: unsafe extern "C-unwind" fn(
        &mut u64,
        u64,
        u64,
        u64,
        u64,
        u64,
        u64,
        u64,
        u64,
        u64,
        f64,
        f64,
        f64,
        f64,
        f64,
        f64,
        f64,
        f64,
        f64,
    ) -> u64,
    v: u64,
) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let result = unsafe {
        callback(
            &mut cell,
            v,
            v.wrapping_add(1),
            v.wrapping_add(2),
            v.wrapping_add(3),
            v.wrapping_add(4),
            v.wrapping_add(5),
            v.wrapping_add(6),
            v.wrapping_add(7),
            v.wrapping_add(8),
            1.25,
            2.25,
            3.25,
            4.25,
            5.25,
            6.25,
            7.25,
            8.25,
            9.25,
        )
    };
    unsafe { aggregate_event(2, cell) }
    result ^ cell
}
