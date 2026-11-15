unsafe extern "Rust" {
    fn native_chars(text: &str, stop: char) -> u64;
    fn native_utf16(text: &[u16]) -> u64;
    fn native_str_sum(parts: &[&str]) -> usize;
    fn native_array_back(values: [u32; 3]) -> u64;
    fn native_take(values: &[u8]) -> usize;
    fn native_chunks(values: &[u64], size: usize) -> u64;
}

fn main() {
    let chars = ['\0', 'A', 'é', 'Σ', '\u{200d}', '🙂', '\u{10ffff}'];
    let units = [
        0, 0x41, 0xd800, 0xdfff, 0xd83d, 0xde42, 0xd834, 0xdd1e, 0x1234, 0xffff,
    ];
    let mut checks = 0;
    for seed in 0..256usize {
        for len in 0..65usize {
            let mut text = String::new();
            let mut scalars = Vec::new();
            let mut utf16 = Vec::new();
            let mut bytes = Vec::new();
            let mut values = Vec::new();
            for i in 0..len {
                let c = chars[(i * 17 + seed) % chars.len()];
                text.push(c);
                scalars.push(c);
                utf16.push(units[(i * 3 + seed) % units.len()]);
                bytes.push((seed + i * 13) as u8);
                values.push(
                    (seed as u64)
                        .wrapping_mul(0x9e3779b97f4a7c15)
                        .wrapping_add(i as u64),
                );
            }
            let stop = chars[seed % chars.len()];
            let mut i = scalars.len();
            while i != 0 && scalars[i - 1] == stop {
                i -= 1;
            }
            let mut expected = 1u64;
            while i != 0 {
                i -= 1;
                expected = expected.wrapping_mul(31).wrapping_add(scalars[i] as u64);
            }
            assert_eq!(
                unsafe { native_chars(&text, stop) },
                expected,
                "chars seed={seed} len={len}"
            );
            checks += 1;

            let mut i = 0;
            let mut expected = 7u64;
            while i < utf16.len() {
                let first = utf16[i] as u32;
                i += 1;
                let scalar = if (0xd800..=0xdbff).contains(&first) {
                    if i < utf16.len() && (0xdc00..=0xdfff).contains(&utf16[i]) {
                        let low = utf16[i] as u32;
                        i += 1;
                        0x10000 + ((first - 0xd800) << 10) + low - 0xdc00
                    } else {
                        0xfffd
                    }
                } else if (0xdc00..=0xdfff).contains(&first) {
                    0xfffd
                } else {
                    first
                };
                expected = expected.wrapping_mul(37).wrapping_add(scalar as u64);
            }
            assert_eq!(
                unsafe { native_utf16(&utf16) },
                expected,
                "utf16 seed={seed} len={len}"
            );
            checks += 1;

            let parts = [&text[..], "", "hé🙂", &text[..]];
            assert_eq!(
                unsafe { native_str_sum(&parts) },
                text.len() * 2 + "hé🙂".len()
            );
            checks += 1;
            let array = [
                u32::MAX.wrapping_sub(seed as u32),
                len as u32 * 137,
                seed as u32 * 977,
            ];
            assert_eq!(
                unsafe { native_array_back(array) },
                u64::from(array[2]) + 17 * u64::from(array[0]) + 71 * u64::from(array[1])
            );
            checks += 1;
            assert_eq!(unsafe { native_take(&bytes) }, len * 7);
            checks += 1;
            let size = seed % 17 + 1;
            let mut count = len.div_ceil(size);
            let mut expected = count as u64;
            while count != 0 {
                count -= 1;
                expected = expected.wrapping_mul(43).wrapping_add(values[count * size]);
            }
            assert_eq!(
                unsafe { native_chunks(&values, size) },
                expected,
                "chunks seed={seed} len={len}"
            );
            checks += 1;
        }
    }
    assert_eq!(checks, 99840);
    println!("PASS native_iterators checks={checks}");
}
