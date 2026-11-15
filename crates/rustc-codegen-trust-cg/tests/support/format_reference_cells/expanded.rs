#![no_std]
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
unsafe extern "Rust" {
    fn observe_integer(value: &&i64) -> u64;
    fn observe_real(value: &&f64) -> u64;
    fn observe_boolean(value: &&bool) -> u64;
    fn observe_character(value: &&char) -> u64;
    fn observe_deep(value: &&&&i64) -> u64;
    fn observe_array(value: &[u64; 3], address: usize, seed: u64) -> u64;
}
#[unsafe(no_mangle)]
pub fn borrow_fields(value: &Mixed) -> u64 {
    let integer = &value.integer;
    let real = &value.real;
    let boolean = &value.boolean;
    let character = &value.character;
    unsafe {
        observe_integer(&integer)
            ^ observe_real(&real)
            ^ observe_boolean(&boolean)
            ^ observe_character(&character)
    }
}
#[unsafe(no_mangle)]
pub fn borrow_deep(value: &Mixed) -> u64 {
    let first = &value.integer;
    let second = &first;
    let third = &second;
    unsafe { observe_deep(&third) }
}
#[unsafe(no_mangle)]
pub fn borrow_payload(value: &Payload) -> u64 {
    match value {
        Payload::Empty => 17,
        Payload::Value { integer, .. } => unsafe { observe_integer(&integer) },
    }
}
#[unsafe(no_mangle)]
pub fn borrow_array(seed: u64) -> u64 {
    let array = [seed, seed.wrapping_add(3), seed ^ 0xfeedface];
    let reference = &array;
    let address = reference as *const [u64; 3] as usize;
    unsafe { observe_array(reference, address, seed) }
}
