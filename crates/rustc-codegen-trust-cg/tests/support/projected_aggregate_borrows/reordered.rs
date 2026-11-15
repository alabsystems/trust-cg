#![no_std]
// repr(Rust) places the wide field before the byte. Both the callee and the
// whole-value move must observe physical offsets rather than declaration order.
struct Pair {
    byte: u8,
    wide: u64,
}
struct PairWrapper {
    pair: Pair,
}
#[inline(never)]
fn mutate_pair(pair: &mut Pair) {
    pair.byte = pair.byte.wrapping_add(37);
    pair.wide = pair.wide.rotate_left(13) ^ 0xa758_60b1_5d9c_3e2f;
}
#[inline(never)]
fn consume_pair(wrapper: PairWrapper) -> u64 {
    wrapper.pair.wide ^ (wrapper.pair.byte as u64).wrapping_mul(0x0101_0101_0101_0101)
}
#[unsafe(no_mangle)]
pub extern "C" fn reordered_pair(byte: u8, wide: u64) -> u64 {
    let mut wrapper = PairWrapper {
        pair: Pair { byte, wide },
    };
    mutate_pair(&mut wrapper.pair);
    consume_pair(wrapper)
}
