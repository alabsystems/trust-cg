// Corpus: `Iterator::max` / `min` over items whose `Ord` is not the order of
// the integer they wrap — `core::cmp::Reverse<u32>` and a user newtype whose
// `cmp` is reversed — beside primitive `i32`/`char` and `Ordering` items, whose
// `Ord` is. Each result follows the item type's own `Ord::cmp`.
#![allow(dead_code)]

use std::cmp::{Ordering, Reverse};

#[derive(Clone, Copy, PartialEq, Eq)]
struct Desc(u32);

impl PartialOrd for Desc {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for Desc {
    fn cmp(&self, o: &Self) -> Ordering {
        o.0.cmp(&self.0)
    }
}

#[inline(never)]
fn reverse_max(a: u32, b: u32) -> u32 {
    (0..(a % 7))
        .map(|x| Reverse(x ^ b))
        .max()
        .map_or(99, |w| w.0)
}

#[inline(never)]
fn reverse_min(a: u32, b: u32) -> u32 {
    (0..(b % 5))
        .map(|x| Reverse(x.wrapping_mul(a)))
        .min()
        .map_or(77, |w| w.0)
}

#[inline(never)]
fn user_max(a: u32, b: u32) -> u32 {
    [Desc(a), Desc(b), Desc(a ^ b)]
        .iter()
        .copied()
        .max()
        .map_or(0, |w| w.0)
}

#[inline(never)]
fn user_min(a: u32, b: u32) -> u32 {
    [a, b, a.wrapping_add(b)]
        .iter()
        .map(|v| Desc(*v))
        .min()
        .map_or(1, |w| w.0)
}

#[inline(never)]
fn primitive(a: u32, b: u32) -> i32 {
    let i = (0..(a % 7))
        .map(|x| (x as i32).wrapping_sub(3).wrapping_mul(b as i32))
        .max()
        .unwrap_or(99);
    let c = (0..(a % 7))
        .map(|x| char::from_u32(0x60 + ((x ^ b) & 31)).unwrap_or('a'))
        .max()
        .map_or(0, |c| c as i32);
    let o = (0..(b % 5))
        .map(|x| x.cmp(&(a % 4)))
        .min()
        .map_or(5, |o| o as i32);
    i ^ (c << 8) ^ (o << 20)
}

fn main() {
    let grid = [0u32, 1, 2, 3, 5, 6, 7, 11, 250, 65_535, u32::MAX];
    let mut acc = 0u64;
    for a in grid {
        for b in grid {
            let r = [
                reverse_max(a, b),
                reverse_min(a, b),
                user_max(a, b),
                user_min(a, b),
                primitive(a, b) as u32,
            ];
            for v in r {
                println!("{a} {b}: {v}");
                acc = acc.wrapping_mul(31).wrapping_add(u64::from(v));
            }
        }
    }
    println!("acc {acc}");
}
