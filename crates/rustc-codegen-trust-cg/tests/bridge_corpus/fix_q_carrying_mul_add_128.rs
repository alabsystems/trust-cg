// Corpus: `u128::carrying_mul_add` — the 256-bit `a*b + c + d`, returned as
// `(low, high)`.
//
// trust-ir has no 256-bit type, so the 8/16/32-bit arms compute in I64 and the
// 64-bit arm computes in U128. Width 128 had no arm and failed closed. It is now
// SCHOOLBOOK 64x64 partial products accumulated into a `(lo, hi)` pair of U128
// values — every operation a plain U128 `Mul`/`Add`/`Shl`/`LShr`/`And` the backend
// already lowers, plus an unsigned `Ult` compare for carry.
//
// CARRY DETECTION IS THE WHOLE RISK, because a wrong carry is SILENT — it produces
// a wrong NUMBER, and the census would have scored the change as -1 either way.
// It is done the one way that cannot be off by a case: after `new = x + y` on
// unsigned 128-bit values, the add overflowed IFF `new < x`. Exact for `y == 0`
// (no overflow, `new == x`, `Ult` false) and for `x == y == MAX`.
//
// THE VECTORS ARE THE PROOF. Each row is value-compared against LLVM, and they are
// chosen to make every carry path observable rather than to look thorough:
//   2  `MAX*MAX`            — every partial product carries
//   3  `MAX*MAX + MAX + MAX`— and then the addends overflow the low word too
//   4  `(2^64-1)^2`         — exactly fills 128 bits, high word still 0
//   5,6 `(2^64-1)^2 + 1`    — the +1 carries OUT of the low word into the high
//   7  `2^64 * 2^64`        — pure high word, low exactly 0
//   8  `H * 2`              — high-limb-only operand shifting out
//   9,10 `MAX*1 + MAX`      — the addend path alone
//   13 `(2^64-1)*3 * (2^64-1)*5 + ..` — cross products that overflow their own
//      64-bit limb, which is where a naive limb split goes wrong
//
// A model that drops the cross-product carry prints a value SMALLER by 2^64 on
// rows 2/3/13; one that mis-shifts prints the halves swapped.
#![allow(dead_code)]
#[inline(never)]
fn cm(a: u128, b: u128, c: u128, d: u128) -> (u128, u128) { a.carrying_mul_add(b, c, d) }
fn main() {
    const M: u128 = u128::MAX;
    const L: u128 = 0xFFFF_FFFF_FFFF_FFFF;
    const H: u128 = 0xFFFF_FFFF_FFFF_FFFF_0000_0000_0000_0000;
    let vs: [(u128, u128, u128, u128); 14] = [
        (0, 0, 0, 0),
        (1, 1, 0, 0),
        (M, M, 0, 0),
        (M, M, M, M),
        (L, L, 0, 0),
        (L, L, 1, 0),
        (L, L, 0, 1),
        (L + 1, L + 1, 0, 0),
        (H, 2, 0, 0),
        (M, 1, M, 0),
        (1, M, 0, M),
        (0x1234_5678_9ABC_DEF0, 0x0FED_CBA9_8765_4321, 0xDEAD_BEEF, 0xCAFE),
        (M / 3, M / 5, M / 7, M / 11),
        (L * 3, L * 5, L, L),
    ];
    let mut i = 0usize;
    while i < 14 {
        let (a, b, c, d) = vs[i];
        let (lo, hi) = cm(a, b, c, d);
        println!("m {} {} {}", i, lo, hi);
        i += 1;
    }
}
