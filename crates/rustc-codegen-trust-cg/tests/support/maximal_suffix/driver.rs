use std::cmp::Ordering;
unsafe extern "Rust" {
    fn maximal_suffix(data: &[u8], reverse_alphabet: bool) -> (usize, usize);
}
// Exhaustively compare whole suffixes. Reversing the alphabet reverses byte
// comparisons; a longer equal-prefix suffix still ranks above a shorter one.
fn oracle(data: &[u8], reverse: bool) -> (usize, usize) {
    let mut start = 0;
    for candidate in 1..data.len() {
        let a = &data[candidate..];
        let b = &data[start..];
        let order = a
            .iter()
            .zip(b)
            .find_map(|(x, y)| (x != y).then(|| if reverse { y.cmp(x) } else { x.cmp(y) }))
            .unwrap_or_else(|| a.len().cmp(&b.len()));
        if order == Ordering::Greater {
            start = candidate;
        }
    }
    let tail = &data[start..];
    let period = (1..=tail.len().max(1))
        .find(|&p| (p..tail.len()).all(|i| tail[i] == tail[i - p]))
        .unwrap();
    (start, period)
}
fn check(data: &[u8], count: &mut usize) {
    for reverse in [false, true] {
        assert_eq!(
            unsafe { maximal_suffix(data, reverse) },
            oracle(data, reverse),
            "data={data:?} reverse={reverse}"
        );
        *count += 1;
    }
}
fn main() {
    let mut checks = 0;
    for n in 0..=8 {
        for mut encoding in 0..3usize.pow(n as u32) {
            let mut data = vec![0; n];
            for byte in &mut data {
                *byte = [0, 1, 255][encoding % 3];
                encoding /= 3;
            }
            check(&data, &mut checks);
        }
    }
    let mut state = 0x4755d1b871209acd_u64;
    for iteration in 0..4096 {
        let n = iteration % 257;
        let mut data = vec![0; n];
        for byte in &mut data {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *byte = if iteration & 1 == 0 {
                (state % 3) as u8
            } else {
                state as u8
            };
        }
        check(&data, &mut checks);
    }
    for n in 0..=256 {
        check(&vec![0; n], &mut checks);
        check(&vec![255; n], &mut checks);
        check(&(0..n).map(|i| i as u8).collect::<Vec<_>>(), &mut checks);
        check(
            &(0..n)
                .map(|i| if i % 2 == 0 { 0 } else { 255 })
                .collect::<Vec<_>>(),
            &mut checks,
        );
    }
    assert_eq!(checks, 29930);
    println!("PASS maximal_suffix checks={checks}");
}
