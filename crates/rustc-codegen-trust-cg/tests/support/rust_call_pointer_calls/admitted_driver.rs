// Binary half of `admitted.rs`: calls every library pointer, and hands the
// library a pointer to its own `extern "rust-call"` function.
#![feature(unboxed_closures)]
#![allow(improper_ctypes_definitions)]
extern crate admitted;
use admitted::*;
use std::hint::black_box as bb;

#[inline(never)]
extern "rust-call" fn mine(a: (u64, u64)) -> u64 {
    mx(a.1, a.0)
}

fn main() {
    let k = bb(41u64);
    let s = S(bb(3));
    println!("one {}", bb(get_one())((k,)));
    println!("two {}", bb(get_two())((k, k * 3)));
    // Every byte of the `(u8, u64)` that is not an element is 0xAB, so a callee
    // that read the `u8`'s whole lane would see them.
    let mut words = [0xABAB_ABAB_ABAB_ABABu64; 2];
    let base = words.as_mut_ptr().cast::<u8>();
    unsafe {
        base.add(std::mem::offset_of!((u8, u64), 0))
            .write(k as u8 ^ 0x80);
        base.add(std::mem::offset_of!((u8, u64), 1))
            .cast::<u64>()
            .write_unaligned(k);
    }
    let narrow: (u8, u64) = unsafe { std::ptr::read(words.as_ptr().cast()) };
    println!("narrow {}", bb(get_narrow())(narrow));
    println!(
        "text {}",
        bb(get_text())((&"hello world, rust-call!"[..(k as usize % 20) + 2],))
    );
    println!("unit {}", bb(get_unit())(()));
    println!("m {}", bb(get_m())(&s, (k, k + 1)));
    println!(
        "mine {}",
        call_two(bb(mine as extern "rust-call" fn((u64, u64)) -> u64), k)
    );
}
