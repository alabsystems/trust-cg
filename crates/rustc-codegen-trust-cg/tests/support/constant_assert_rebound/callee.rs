extern crate assert_rebound_provider as provider;

#[inline(never)]
pub fn rebinding_bounds(mut index: usize) -> u64 {
    let table = core::hint::black_box([7_u64, 11_u64]);
    let value = table[index];
    index = 0;
    value.wrapping_add(provider::after_write(index))
}

#[inline(never)]
pub fn dynamic_bounds(index: usize) -> u64 {
    let table = core::hint::black_box([7_u64, 11_u64]);
    table[index]
}

#[inline(never)]
pub fn immutable_local_constant() -> u64 {
    let table = core::hint::black_box([7_u64, 11_u64]);
    let index = 0_usize;
    table[index].wrapping_add(table[1])
}
