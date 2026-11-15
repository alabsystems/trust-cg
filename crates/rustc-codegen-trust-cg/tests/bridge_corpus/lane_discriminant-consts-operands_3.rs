// CORPUS FIXTURE — lane discriminant-consts-operands: `ConstValue::Indirect`
// constants — a const whose evaluated value is an in-memory const allocation
// rather than a scalar. Two shapes core reaches:
//   * a NAMED `&[u8]` const (`fmt::num`'s `const DIG_TAB: &[u8] = b"0123…"`,
//     read as `_x = const DIG_TAB` in every radix `fmt` impl): const-eval hands
//     back its 16-byte fat-pointer IMAGE (data relocation + length), which the
//     bridge canonicalizes to the `ConstValue::Slice` form — a wrong length or
//     data address changes `dig_len` / every digit below;
//   * an inline-const `[const { MaybeUninit::<T>::uninit() }; N]` element
//     (`array::try_from_fn`), a fully-uninitialized union image lowered to a
//     zero of the element's scalar type — every element is then written before
//     it is read, so the fold depends only on the writes landing per element.
// The digit buffer is written back-to-front through `MaybeUninit::new` /
// `as_ptr` (the by-value `write` / `assume_init` shapes are outside this lane).
use core::mem::MaybeUninit;
const DIG_TAB: &[u8] = b"0123456789abcdef";

#[inline(never)]
fn dig(i: usize) -> u8 { DIG_TAB[i] }
#[inline(never)]
fn dig_len() -> usize { DIG_TAB.len() }
#[inline(never)]
fn radix_fold<const N: usize>(mut n: u64) -> u64 {
    let base = dig_len() as u64;
    let mut buf = [MaybeUninit::<u8>::uninit(); N];
    let mut off = N;
    loop {
        off -= 1;
        buf[off] = MaybeUninit::new(dig((n % base) as usize));
        n /= base;
        if n == 0 { break; }
    }
    let mut acc = 0u64;
    while off < N {
        acc = acc.wrapping_mul(131).wrapping_add(unsafe { *buf[off].as_ptr() } as u64);
        off += 1;
    }
    acc
}
#[inline(never)]
fn from_fn_fold<const N: usize>(seed: u32) -> u64 {
    let mut arr = [const { MaybeUninit::<u32>::uninit() }; N];
    let mut i = 0;
    while i < N { unsafe { *arr[i].as_mut_ptr() = seed.wrapping_mul(i as u32 + 1); } i += 1; }
    let mut acc = 0u64;
    i = 0;
    while i < N { acc = acc * 7 + unsafe { *arr[i].as_ptr() } as u64; i += 1; }
    acc
}
fn main() {
    println!("digits {} {} {} {}", dig_len(), dig(0), dig(9), dig(15));
    println!("hex {} {} {}", radix_fold::<16>(0xdead_beef), radix_fold::<16>(0), radix_fold::<22>(u64::MAX));
    println!("from_fn {} {}", from_fn_fold::<6>(3), from_fn_fold::<3>(1000));
}
