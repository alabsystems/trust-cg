unsafe extern "C" {
    fn array_map(value: u32, present: bool, out: *mut u16) -> u16;
    fn selected_array(value: u32, choose: bool, out: *mut u16) -> u16;
    fn aggregate_capture(value: u32, out: *mut u64) -> u16;
}
fn main() {
    let mut checks = 0usize;
    let mut random = 0x91e10da5u32;
    for index in 0..4096 {
        random ^= random << 13;
        random ^= random >> 17;
        random ^= random << 5;
        let value = match index {
            0 => 0,
            1 => 1,
            2 => u32::MAX,
            3 => 0xffff,
            4 => 0x10000,
            5 => 0x80000000,
            6 => 0x7fffffff,
            _ => random,
        };
        for present in [false, true] {
            let mut output = [0xdead_u16; 5];
            let result = unsafe { array_map(value, present, output.as_mut_ptr().add(1)) };
            let (lo, hi, extra, want) = if present {
                (
                    value as u16,
                    (value >> 16) as u16,
                    (value >> 16) as u16,
                    value as u16,
                )
            } else {
                (0x1357, 0x2468, 0xaaaa, 0xbbbb)
            };
            assert_eq!(output, [0xdead, lo, hi, extra, 0xdead]);
            assert_eq!(result, want);
            checks += 2;
        }
        for choose in [false, true] {
            let mut expected = [0xbeef, 0x1122u16, 0x3344, 0x5566, 0x7788, 0xbeef];
            let i = if choose { 1 } else { 3 };
            let mut want = 0;
            for v in [value, value.rotate_left(7)] {
                expected[i] = expected[i].wrapping_add(v as u16);
                expected[i + 1] ^= (v >> 16) as u16;
                want ^= expected[i] ^ expected[i + 1];
            }
            let mut output = [0xbeef; 6];
            let result = unsafe { selected_array(value, choose, output.as_mut_ptr().add(1)) };
            assert_eq!(output, expected);
            assert_eq!(result, want);
            checks += 2;
        }
        let mut expected = [
            0xfeed,
            0x123456789abcdef0u64,
            0xfedcba9876543210,
            0x1234,
            0x5678,
            0x1020304050607080,
            value as u64,
            0x8877665544332211,
            0xfffffffffffffff0,
            0x0102030405060708,
            0xfeed,
        ];
        let selected = if value & 1 == 0 { 1 } else { 8 };
        let mut want = 0;
        for v in [value, value.rotate_left(7)] {
            expected[selected] = expected[selected].wrapping_add(v as u64);
            expected[selected + 1] ^= expected[5] ^ expected[6] ^ expected[7];
            expected[3] = (expected[3] as u16).wrapping_add(v as u16) as u64;
            expected[4] ^= (v >> 16) as u64;
            want ^=
                (expected[selected] ^ expected[selected + 1] ^ expected[3] ^ expected[4]) as u16;
        }
        let mut output = [0xfeed; 11];
        let result = unsafe { aggregate_capture(value, output.as_mut_ptr().add(1)) };
        assert_eq!(output, expected);
        assert_eq!(result, want);
        checks += 2;
    }
    assert_eq!(checks, 40960);
    println!("PASS borrowed_aggregate_captures checks={checks}");
}
