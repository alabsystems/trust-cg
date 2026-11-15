use std::panic::{AssertUnwindSafe, catch_unwind};
unsafe extern "Rust" {
    fn cg_fat_closure(data: &[u64], seed: u64) -> u64;
    fn cg_fat_closure_ordered(data: &[u64], seed: u64) -> u64;
}
#[unsafe(no_mangle)]
pub fn invoke_dynamic(
    op: &dyn Fn(u64, u64, u64, u64, u64, u64, &[u64], u64) -> u64,
    data: &[u64],
    seed: u64,
) -> u64 {
    op(
        seed,
        seed + 1,
        seed + 2,
        seed + 3,
        seed + 4,
        seed + 5,
        data,
        seed + 6,
    )
}
fn sum_reference(data: &[u64], seed: u64) -> u64 {
    (0..7).map(|k| seed + k).sum::<u64>() + data.len() as u64 + data[0]
}
fn ordered_reference(data: &[u64], seed: u64) -> u64 {
    let v: Vec<u64> = (0..7).map(|k| seed + k).collect();
    v[0] ^ v[1].rotate_left(7)
        ^ v[2].rotate_left(13)
        ^ v[3].rotate_left(19)
        ^ v[4].rotate_left(29)
        ^ v[5].rotate_left(37)
        ^ v[6].rotate_left(43)
        ^ (data.len() as u64).rotate_left(51)
        ^ data[data.len() - 1].rotate_left(57)
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let pool: Vec<u64> = (1..=16u64)
        .map(|i| i.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 8)
        .collect();
    let mut checks = 0u64;
    let mut panics = 0u64;
    for start in 0..4 {
        for len in 0..=12 {
            let data = &pool[start..start + len];
            for seed in [0u64, 1, 7, 0x1234_5678, 0xFFFF_FF00] {
                if len == 0 {
                    // An empty slice panics inside the closure body; under
                    // unwind the panic crosses both crates back to here.
                    if cfg!(panic = "unwind") {
                        for call in [cg_fat_closure, cg_fat_closure_ordered] {
                            let result =
                                catch_unwind(AssertUnwindSafe(|| unsafe { call(data, seed) }));
                            assert!(result.is_err());
                            panics += 1;
                        }
                    }
                    continue;
                }
                assert_eq!(unsafe { cg_fat_closure(data, seed) }, sum_reference(data, seed));
                assert_eq!(
                    unsafe { cg_fat_closure_ordered(data, seed) },
                    ordered_reference(data, seed)
                );
                checks += 2;
            }
        }
    }
    println!("PASS fat_fn_callee checks={checks} panics={panics}");
}
