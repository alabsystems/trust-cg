#[repr(C, align(8))]
struct Payload {
    bits: u64,
}
unsafe extern "Rust" {
    fn packed_owner_address(p: *mut Payload) -> usize;
}
fn main() {
    let mut values: [Payload; 128] = core::array::from_fn(|i| Payload {
        bits: (i as u64).wrapping_mul(0x9e3779b97f4a7c15),
    });
    let mut checks = 0;
    for round in 0..32 {
        for (i, value) in values.iter_mut().enumerate() {
            let before = value.bits;
            let p = value as *mut Payload;
            assert_eq!(
                unsafe { packed_owner_address(p) },
                p.addr() + 1,
                "round={round} index={i}"
            );
            assert_eq!(value.bits, before);
            checks += 2;
        }
    }
    assert_eq!(checks, 8192);
    println!("PASS tagged_owner_return checks={checks}");
}
