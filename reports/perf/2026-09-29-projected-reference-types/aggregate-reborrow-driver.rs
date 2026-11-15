#[repr(C)]
pub struct Arrays { pub first: [u32; 3], pub last: [u32; 3] }
#[repr(C)]
pub struct Triple { pub a: u32, pub b: u32, pub c: u32 }
#[repr(C)]
pub struct Records { pub tag: u64, pub values: [Triple; 3] }
unsafe extern "Rust" {
    fn shared_from_mut_array(v: &mut Arrays) -> &[u32; 3];
    fn shared_from_mut_record(v: &mut Records, i: usize) -> &Triple;
    fn first_array_field(v: &Arrays) -> &[u32; 3];
    fn last_array_field(v: &Arrays) -> &[u32; 3];
    fn last_array_field_mut(v: &mut Arrays) -> &mut [u32; 3];
    fn indexed_record(v: &Records, i: usize) -> &Triple;
    fn indexed_record_mut(v: &mut Records, i: usize) -> &mut Triple;
    fn reborrow_array_field(v: &Arrays) -> &[u32; 3];
}
fn main() {
    for seed in 0..4096u32 {
        let mut a = Arrays { first: [seed; 3], last: [seed ^ 0x12345678; 3] };
        let mut r = Records { tag: 10, values: core::array::from_fn(|i| Triple { a: seed, b: i as u32, c: seed.rotate_left(i as u32) }) };
        unsafe {
            assert_eq!(first_array_field(&a) as *const _, &a.first as *const _);
            assert_eq!(last_array_field(&a) as *const _, &a.last as *const _);
            assert_eq!(reborrow_array_field(&a) as *const _, &a.last as *const _);
            let expected = &a.last as *const _;
            assert_eq!(shared_from_mut_array(&mut a) as *const _, expected);
            last_array_field_mut(&mut a)[2] = seed ^ 0xabcd;
            assert_eq!(a.last[2], seed ^ 0xabcd);
            for i in 0..3 {
                assert_eq!(indexed_record(&r, i) as *const _, &r.values[i] as *const _);
                let expected = &r.values[i] as *const _;
                assert_eq!(shared_from_mut_record(&mut r, i) as *const _, expected);
                indexed_record_mut(&mut r, i).c = seed ^ i as u32;
                assert_eq!(r.values[i].c, seed ^ i as u32);
            }
        }
    }
    println!("PASS aggregate_reference_types checks=57344");
}
