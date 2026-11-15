unsafe extern "Rust" {
    fn constant_bytes(which: u32) -> u64;
    fn const_reinterpret() -> u64;
    fn char_indices(text: &str) -> u64;
    fn embedded_vec(value: &mut String, seed: u64) -> u64;
    fn embedded_owned(bytes: Vec<u8>, seed: u64) -> u64;
}

fn bytes_hash(value: &[u8]) -> u64 {
    value.iter().fold(value.len() as u64, |h, &v| {
        h.wrapping_mul(37).wrapping_add(v as u64)
    })
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn touch_vec(value: &mut Vec<u8>, seed: u64) -> u64 {
    // Force growth, then replace the backing allocation on alternate calls.
    // All bytes are ASCII so String's UTF-8 invariant is maintained.
    for i in 0..(seed % 97 + 1) {
        value.push(b'a' + ((i + seed) % 26) as u8);
    }
    if seed & 1 != 0 {
        *value = value.iter().rev().copied().collect();
    }
    if seed % 3 == 0 {
        value.truncate((seed as usize / 3) % (value.len() + 1));
    }
    bytes_hash(value).rotate_left(13) ^ seed
}

fn main() {
    let cases = ["", "replacement: �", "éΣ🙂", "\0ab\0"];
    let mut checks = 0;
    for (which, text) in cases.iter().enumerate() {
        assert_eq!(
            unsafe { constant_bytes(which as u32) },
            bytes_hash(text.as_bytes())
        );
        checks += 1;
    }
    assert_eq!(
        unsafe { const_reinterpret() },
        bytes_hash(&[0x34, 0x12, 0xcd])
    );
    checks += 1;
    let scalars = ['\0', 'A', 'é', 'Σ', '\u{200d}', '🙂', '\u{10ffff}'];
    for seed in 0..256u64 {
        for n in 0..65 {
            let text: String = (0..n)
                .map(|i| scalars[(i * 3 + seed as usize) % scalars.len()])
                .collect();
            let mut want = 3u64;
            let mut offset = 0;
            for c in text.chars() {
                want = want
                    .wrapping_mul(71)
                    .wrapping_add(offset)
                    .wrapping_add(c as u64);
                offset += c.len_utf8() as u64;
            }
            assert_eq!(
                unsafe { char_indices(&text) },
                want,
                "indices seed={seed} n={n}"
            );
            let original: String = (0..n)
                .map(|i| (b'A' + ((i + seed as usize) % 26) as u8) as char)
                .collect();
            let mut expected = original.clone().into_bytes();
            let result = touch_vec(&mut expected, seed);
            let mut got = original.clone();
            assert_eq!(
                unsafe { embedded_vec(&mut got, seed) },
                result ^ expected.len() as u64,
                "borrow seed={seed} n={n}"
            );
            assert_eq!(got.as_bytes(), expected);
            assert_eq!(
                unsafe { embedded_owned(original.into_bytes(), seed) },
                bytes_hash(&expected) ^ result ^ expected.len() as u64,
                "owned seed={seed} n={n}"
            );
            checks += 4;
        }
    }
    println!("PASS optimized_alloc checks={checks}");
}
