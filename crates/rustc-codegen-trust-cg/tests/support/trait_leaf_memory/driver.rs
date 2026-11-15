unsafe extern "C" {
    fn projected_trait_wrapper(seed: u64, value: u64, storage: *mut u64) -> u64;
}
unsafe extern "C" {
    fn trait_leaf_shared(storage: *const u64, mode: u64) -> u64;
    fn trait_leaf_raw(storage: *const u64, mode: u64) -> u64;
}
fn main() {
    let values = [
        0,
        1,
        7,
        127,
        255,
        256,
        65535,
        (1u64 << 32) - 1,
        1u64 << 32,
        1u64 << 63,
        u64::MAX - 1,
        u64::MAX,
    ];
    let mut checks = 0;
    for seed in values {
        for value in values {
            let mut storage = [0x7192_3344_5506_aabb, 0, 0xcd17_0511_1000_789a];
            let expected = seed.wrapping_add(value.wrapping_add(1));
            assert_eq!(
                unsafe { projected_trait_wrapper(seed, value, &mut storage[1]) },
                expected.wrapping_add(17)
            );
            assert_eq!(storage[1], expected);
            assert_eq!(storage[0], 0x7192_3344_5506_aabb);
            assert_eq!(storage[2], 0xcd17_0511_1000_789a);
            checks += 4;
        }
    }
    for seed in values {
        for mode in 0..2 {
            let storage = [0x7192_3344_5506_aabb, seed, 0xcd17_0511_1000_789a];
            let expected = if mode == 0 { seed } else { !seed };
            assert_eq!(
                unsafe { trait_leaf_shared(&storage[1], mode) },
                expected.wrapping_add(46)
            );
            assert_eq!(
                unsafe { trait_leaf_raw(&storage[1], mode) },
                expected ^ 0x77
            );
            assert_eq!(storage[1], seed);
            assert_eq!(storage[0], 0x7192_3344_5506_aabb);
            assert_eq!(storage[2], 0xcd17_0511_1000_789a);
            checks += 5;
        }
    }
    println!("PASS trait_leaf_memory checks={checks}");
}
