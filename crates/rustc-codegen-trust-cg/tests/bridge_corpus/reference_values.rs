// Corpus: reference values whose trust-ir typing the bridge must get right.
// * A reference assigned before a loop and read inside it is carried by the
//   loop header as a `&T` block parameter; the address bound to it (an element
//   of an array, a slice or a row, or a join of two such) is retyped to `&T`
//   on every edge.
// * A reference to a reference (`&&T`, `&mut &mut T`) whose referent is an
//   aggregate or a scalar newtype: the inner reference is assigned directly,
//   copied from another reference, bound from a tuple, joined from two
//   branches or reassigned in a loop, and its referent has a real address.
// Elements are reached through `get`, patterns and iterators, never a
// bounds-checked index: a native `panic=abort` canonical bounds check is
// refused (`[TCG-ASSERT-PANIC]`).
#![allow(dead_code)]

#[inline(never)]
fn rl_elem(g: &[u32; 2], i: usize) -> u32 {
    let Some(x) = g.get(i) else {
        return 0;
    };
    let mut s = 0u32;
    let mut c = 0u32;
    while c < 3 {
        s = s.wrapping_add(*x);
        c += 1;
    }
    s
}

#[inline(never)]
fn rows(g: &[[u8; 5]; 5]) -> u32 {
    let mut s = 0u32;
    let mut r = 0usize;
    'rows: while r < 5 {
        let Some(row) = g.get(r) else {
            break;
        };
        r += 1;
        for &cell in row.iter() {
            if cell == 3 {
                continue 'rows;
            }
            s += cell as u32;
        }
    }
    s
}

#[inline(never)]
fn rl_slice_elem(s: &[u32], i: usize) -> u32 {
    let Some(x) = s.get(i) else {
        return 0;
    };
    let mut acc = 0u32;
    let mut c = 0u32;
    while c < 4 {
        acc = acc.wrapping_mul(3).wrapping_add(*x);
        c += 1;
    }
    acc
}

#[inline(never)]
fn plus_one(x: &u32) -> u32 {
    x.wrapping_add(1)
}

#[inline(never)]
fn rl_joined(g: &[u32; 2], i: usize, k: u32) -> u32 {
    let [g0, _] = g;
    let x = if k > 3 {
        match g.get(i) {
            Some(e) => e,
            None => g0,
        }
    } else {
        g0
    };
    let mut s = 0u32;
    let mut c = 0u32;
    while c < 3 {
        s = s.wrapping_add(plus_one(x));
        c += 1;
    }
    s
}

#[derive(Clone, Copy)]
struct Byte(u8);

#[inline(never)]
fn deref2(r: &&(u32, u8)) -> u32 {
    r.0.wrapping_add(r.1 as u32)
}

#[inline(never)]
fn deref2_byte(r: &&Byte) -> u32 {
    (**r).0 as u32
}

#[inline(never)]
fn bump2(r: &mut &mut (u32, u16)) {
    r.0 = r.0.wrapping_add(r.1 as u32);
    r.1 ^= 0x5a;
}

#[inline(never)]
fn rr_direct(x: u32) -> u32 {
    let v = (x, (x >> 3) as u8);
    let r = &v;
    deref2(&r)
}

#[inline(never)]
fn rr_copy(x: u32) -> u32 {
    let v = (x, 3u8);
    let r0 = &v;
    let r = r0;
    let rr = &r;
    (**rr).0 ^ (**rr).1 as u32 ^ deref2(rr).rotate_left(5)
}

#[inline(never)]
fn rr_tuple_bind(x: u32) -> u32 {
    let p = Byte(x as u8);
    let (rp, k) = (&p, 3u32);
    deref2_byte(&rp) ^ k
}

#[inline(never)]
fn rr_cond_newtype(x: u32) -> u32 {
    let a = Byte(x as u8);
    let b = Byte((x >> 8) as u8);
    let r = if x & 1 == 0 { &a } else { &b };
    deref2_byte(&r)
}

#[inline(never)]
fn rr_loop_newtype(x: u32) -> u32 {
    let a = Byte(x as u8);
    let b = Byte((x >> 8) as u8);
    let mut r = &a;
    let mut acc = 0u32;
    let mut i = 0;
    while i < 5 {
        acc = acc.wrapping_mul(17).wrapping_add(deref2_byte(&r));
        r = if (x >> i) & 1 == 1 { &b } else { &a };
        i += 1;
    }
    acc
}

// Optimized builds drop `&r` (only the debug info takes it) and then refuse
// the branch-joined aggregate reference, so this runs at -Copt-level=0 only.
#[cfg(debug_assertions)]
#[inline(never)]
fn rr_cond(x: u32) -> u32 {
    let a = (x, 3u8);
    let b = (x ^ 5, 9u8);
    let r = if x & 1 == 0 { &a } else { &b };
    let rr = &r;
    (**rr).0 ^ (**rr).1 as u32
}

#[cfg(not(debug_assertions))]
fn rr_cond(x: u32) -> u32 {
    x
}

#[inline(never)]
fn rr_mut(x: u32) -> u32 {
    let mut v = (x, x as u16);
    let mut r = &mut v;
    bump2(&mut r);
    v.0 ^ ((v.1 as u32) << 16)
}

fn main() {
    let mut acc = 0u64;
    for a in [
        0u32,
        1,
        2,
        3,
        4,
        7,
        250,
        0x302,
        0xffff,
        0x8000_0001,
        u32::MAX,
    ] {
        let mut g = [[0u8; 5]; 5];
        for (r, row) in g.iter_mut().enumerate() {
            for (c, cell) in row.iter_mut().enumerate() {
                *cell = ((a >> (r + c)) & 7) as u8;
            }
        }
        let s = [a, a.rotate_left(7), 3];
        let r = [
            rl_elem(&[a, a ^ 5], (a & 1) as usize),
            rows(&g),
            rl_slice_elem(&s, (a % 3) as usize),
            rl_joined(&[a & 0xffff, 5], (a & 1) as usize, a % 8),
            rr_direct(a),
            rr_copy(a),
            rr_tuple_bind(a),
            rr_cond_newtype(a),
            rr_cond(a),
            rr_loop_newtype(a),
            rr_mut(a),
        ];
        for v in r {
            println!("{a}: {v}");
            acc = acc.wrapping_mul(31).wrapping_add(u64::from(v));
        }
    }
    println!("acc {acc}");
}
