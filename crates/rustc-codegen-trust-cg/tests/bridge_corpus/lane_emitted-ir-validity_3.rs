// CORPUS FIXTURE — lane emitted-ir-validity, shape 3: a shift whose COUNT is
// WIDER than the shifted value (`u32 >> usize`, `core::num::bignum::Big32x40::
// get_bit`). The bridge emitted the mixed-width shift as is; the AArch64
// encoder produced a byte-correct `LSR Wd, Wn, Wm` (it keys the size on the
// destination and takes only the count's register number), but the verifier's
// operand reconstruction — the genuine credit for LSL/LSR/ASR — models only a
// same-width or narrower count, so the function was refused at proof promotion
// ([TCG-PROOF-465] "no proof mapping for opcode LsrRR"). The count is now
// truncated to the value width first (rustc's own `cast_shift_expr_rhs` order).
// The printed bits depend on the shift consuming exactly the low 5 bits of the
// (64-bit) count, including counts with high bits set.
use std::hint::black_box;

struct Big {
    base: [u32; 40],
}

impl Big {
    #[inline(never)]
    fn get_bit(&self, i: usize) -> u8 {
        let (d, b) = (i / 32, i % 32);
        ((self.base[d] >> b) & 1) as u8
    }
}

#[inline(never)]
fn shl_u16_by_usize(x: u16, n: usize) -> u16 {
    x.wrapping_shl(n as u32) // count is u32 here: narrower-or-equal path
}

#[inline(never)]
fn shr_i32_by_u64(x: i32, n: u64) -> i32 {
    x >> (n & 31)
}

#[inline(never)]
fn shl_u8_by_usize(x: u8, n: usize) -> u8 {
    x << (n & 7)
}

fn main() {
    let mut big = Big { base: [0u32; 40] };
    big.base[1] = black_box(0b1010);
    big.base[39] = black_box(0x8000_0000);
    println!(
        "{}{}{}{}{}",
        big.get_bit(33),
        big.get_bit(34),
        big.get_bit(35),
        big.get_bit(0),
        big.get_bit(39 * 32 + 31)
    );
    println!("{}", shl_u16_by_usize(black_box(3), black_box(4)));
    println!("{}", shr_i32_by_u64(black_box(-256), black_box(4)));
    println!("{}", shl_u8_by_usize(black_box(3), black_box(6)));
}
