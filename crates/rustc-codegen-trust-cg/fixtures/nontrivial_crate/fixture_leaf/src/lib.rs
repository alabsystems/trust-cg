enum LeafChoice {
    Pair(u64, u64),
    Raw,
}

#[inline(never)]
pub fn leaf_mix(left: u64, right: u64) -> u64 {
    let pair = (left | 1, right ^ 5);
    let mut words = [pair.0, pair.1, left & right];
    let words_copy = words;
    words = [words_copy[1], words_copy[2], words_copy[0]];
    let choice = LeafChoice::Pair(words[0] ^ words[2], words.len() as u64);
    match choice {
        LeafChoice::Pair(a, b) => (a & 31) ^ b ^ words[1],
        LeafChoice::Raw => right,
    }
}
