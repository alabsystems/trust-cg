unsafe extern "Rust" {
    fn mapped_cursor(bytes: &[u8], present: bool) -> (usize, usize);
    fn mapped_advanced_cursor(
        bytes: &[u8],
        present: bool,
        front: bool,
        back: bool,
    ) -> (usize, usize);
}
fn main() {
    let bytes = [0x39u8; 96];
    let mut checks = 0;
    for start in 0..32 {
        for len in 0..65 {
            for present in [false, true] {
                let slice = &bytes[start..start + len];
                let expected = if present {
                    (slice.as_ptr() as usize, slice.len())
                } else {
                    (0, usize::MAX)
                };
                assert_eq!(
                    unsafe { mapped_cursor(slice, present) },
                    expected,
                    "original start={start} len={len} present={present}"
                );
                checks += 1;
                for front in [false, true] {
                    for back in [false, true] {
                        let mut rest = slice;
                        if front && !rest.is_empty() {
                            rest = &rest[1..];
                        }
                        if back && !rest.is_empty() {
                            rest = &rest[..rest.len() - 1];
                        }
                        let expected = if present {
                            (rest.as_ptr() as usize, rest.len())
                        } else {
                            (0, usize::MAX)
                        };
                        assert_eq!(
                            unsafe { mapped_advanced_cursor(slice, present, front, back) },
                            expected,
                            "advanced start={start} len={len} present={present} front={front} back={back}"
                        );
                        checks += 1;
                    }
                }
            }
        }
    }
    assert_eq!(checks, 20800);
    println!("PASS option_aggregate_map_advanced checks={checks}");
}
