extern crate loop_header_library;
extern crate loop_header_provider;

unsafe extern "C" {
    fn memory_loop_sum(data: *const u64, count: usize) -> u64;
}

fn main() {
    let values = [11u64, 7, u64::MAX, 19, 0, 23, 37];
    for start in 0..=values.len() {
        for count in 0..=values.len() - start {
            let expected = values[start..start + count].iter()
                .fold(0u64, |sum, value| sum.wrapping_add(*value))
                ^ (count as u64).wrapping_mul(0x101);
            let actual = unsafe { memory_loop_sum(values.as_ptr().add(start), count) };
            assert_eq!(actual, expected, "start={start} count={count}");
        }
    }
    println!("MEMORY_ONLY_LOOP_HEADER_NATIVE checks=36");
}
