unsafe extern "C" { fn closure_hash(seed: u64, x: u32) -> u64; }
fn main() {
    for seed in [0,1,0xabcdef12947650ff, u64::MAX] {
        for x in [0,97,u32::MAX] {
            let want = seed.wrapping_mul(31).wrapping_add(x as u64);
            assert_eq!(unsafe { closure_hash(seed, x) }, want);
        }
    }
    println!("PASS closure hash");
}
