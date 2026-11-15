unsafe extern "C" {
    fn escape_chars(value: u32, mode: u32, out: *mut u32) -> usize;
}
fn main() {
    let mut checks = 0usize;
    let mut values: Vec<u32> = (0..256).collect();
    values.extend([
        0x301,
        0x7ff,
        0x800,
        0xd7ff,
        0xd800,
        0xdfff,
        0xe000,
        0xffff,
        0x10000,
        0x1f600,
        0x10ffff,
        0x110000,
        u32::MAX,
    ]);
    for value in values {
        for mode in 0..6 {
            let expected: Vec<u32> = match char::from_u32(value) {
                None => Vec::new(),
                Some(c) => match mode % 3 {
                    0 => c.escape_default().map(|x| x as u32).collect(),
                    1 => c.escape_debug().map(|x| x as u32).collect(),
                    _ => c.escape_unicode().map(|x| x as u32).collect(),
                },
            };
            let mut out = [0xdeadbeefu32; 14];
            let n = unsafe { escape_chars(value, mode, out.as_mut_ptr().add(2)) };
            assert_eq!(n, expected.len(), "value={value:x} mode={mode}");
            checks += 1;
            assert_eq!(
                &out[2..2 + n],
                expected.as_slice(),
                "value={value:x} mode={mode}"
            );
            checks += 1;
            assert!(
                out[..2]
                    .iter()
                    .chain(out[2 + n..].iter())
                    .all(|x| *x == 0xdeadbeef)
            );
            checks += 1;
        }
    }
    println!("PASS char_escape checks={checks}");
}
