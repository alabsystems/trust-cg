#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[inline(never)]
fn many(
    a: u8,
    b: i16,
    c: u32,
    d: i64,
    e: f32,
    f: f64,
    g: u128,
    h: bool,
    i: char,
    j: usize,
    k: i8,
    l: u64,
) -> u64 {
    (a as u64)
        ^ (b as i64 as u64).rotate_left(3)
        ^ (c as u64).rotate_left(7)
        ^ (d as u64).rotate_left(11)
        ^ (e.to_bits() as u64).rotate_left(13)
        ^ f.to_bits().rotate_left(17)
        ^ (g as u64)
        ^ ((g >> 64) as u64).rotate_left(19)
        ^ (h as u64) << 23
        ^ (i as u64) << 29
        ^ (j as u64).rotate_left(31)
        ^ (k as i64 as u64).rotate_left(37)
        ^ l.rotate_left(41)
}

#[no_mangle]
pub extern "C" fn abi_many(x: u64, y: u64) -> u64 {
    let g = ((x as u128) << 64) | y as u128;
    many(
        x as u8,
        y as i16,
        x as u32,
        y as i64,
        x as u32 as f32,
        y as i64 as f64,
        g,
        x > y,
        char::from_u32((y % 0xd000) as u32).unwrap_or('#'),
        x as usize,
        y as i8,
        x ^ y,
    )
}

#[derive(Clone, Copy)]
struct Mixed {
    a: f32,
    b: f64,
    c: u8,
}

#[derive(Clone, Copy)]
struct Wide {
    a: u8,
    b: u128,
}

#[inline(never)]
fn mk_mixed(x: u32) -> Mixed {
    Mixed {
        a: x as f32 * 0.5,
        b: x as f64 * 0.25,
        c: x as u8,
    }
}

#[inline(never)]
fn use_mixed(m: Mixed, n: Mixed) -> f64 {
    (m.a as f64 + n.b) * 2.0 - (n.a as f64) + m.b + (m.c as f64) - (n.c as f64)
}

#[no_mangle]
pub extern "C" fn abi_mixed(x: u32, y: u32) -> f64 {
    let m = mk_mixed(x);
    let n = mk_mixed(y);
    use_mixed(m, n) + use_mixed(n, m) * 3.0
}

#[inline(never)]
fn mk_wide(x: u64) -> Wide {
    Wide {
        a: x as u8,
        b: (x as u128) * 0x1_0000_0001,
    }
}

#[inline(never)]
fn wide_sum(w: &Wide, v: &Wide) -> u128 {
    w.b.wrapping_add(v.b).wrapping_mul(w.a as u128 + 1) ^ v.a as u128
}

#[inline(never)]
fn ret_tuple(x: u32) -> (u8, u64, f32, i16) {
    (x as u8, (x as u64) << 33, x as f32, -(x as i16))
}

#[inline(never)]
fn ret_i128(x: i64, y: i64) -> i128 {
    (x as i128) * (y as i128) - (1i128 << 100)
}

#[no_mangle]
pub extern "C" fn abi_rets(x: u32, y: u32) -> u64 {
    let t = ret_tuple(x);
    let u = ret_tuple(y);
    let w = ret_i128(x as i64, -(y as i64));
    (t.0 as u64)
        ^ t.1
        ^ (t.2.to_bits() as u64) << 7
        ^ (u.3 as i64 as u64)
        ^ (w as u64)
        ^ ((w >> 64) as u64).rotate_left(9)
}

type Op = fn(i64, f64, u8) -> f64;

fn op_a(a: i64, b: f64, c: u8) -> f64 {
    a as f64 * b + c as f64
}
fn op_b(a: i64, b: f64, c: u8) -> f64 {
    b - a as f64 / (c as f64 + 1.0)
}
fn op_c(_a: i64, b: f64, c: u8) -> f64 {
    if c & 1 == 1 { -b } else { b * 0.5 }
}

#[no_mangle]
pub extern "C" fn abi_fnptr(x: i64, y: f64) -> f64 {
    let ops: [Op; 3] = [op_a, op_b, op_c];
    let mut acc = y;
    for i in 0..6 {
        let f = ops[(x.rem_euclid(3) as usize + i) % 3];
        acc = f(x.wrapping_add(i as i64), acc, i as u8);
    }
    if acc.is_nan() { 0.125 } else { acc }
}

#[inline(never)]
fn recurse_agg(depth: u32, m: Mixed, acc: u64) -> u64 {
    if depth == 0 {
        return acc ^ m.c as u64;
    }
    let n = Mixed {
        a: m.a + 1.0,
        b: m.b * 1.5,
        c: m.c.wrapping_add(3),
    };
    let r = recurse_agg(depth - 1, n, acc.wrapping_mul(31).wrapping_add(m.b as u64));
    r ^ (m.a as u64)
}

#[no_mangle]
pub extern "C" fn abi_recurse(x: u32, d: u32) -> u64 {
    recurse_agg(d % 40, mk_mixed(x), 7)
}

#[inline(never)]
fn opt_args(a: Option<u32>, b: Option<&u64>, c: Result<i16, u8>, d: Option<char>) -> u64 {
    let x = a.unwrap_or(1) as u64;
    let y = b.copied().unwrap_or(2);
    let z = match c {
        Ok(v) => v as i64 as u64,
        Err(e) => 1000 + e as u64,
    };
    let w = d.map(|c| c as u64).unwrap_or(3);
    x ^ y.rotate_left(8) ^ z.rotate_left(16) ^ w.rotate_left(24)
}

#[no_mangle]
pub extern "C" fn abi_options(x: u32, y: u32) -> u64 {
    let v = (x as u64) << 20 | y as u64;
    let a = if x & 1 == 0 { Some(y) } else { None };
    let b = if y & 1 == 0 { Some(&v) } else { None };
    let c = if x & 2 == 0 {
        Ok(y as i16)
    } else {
        Err(x as u8)
    };
    let d = char::from_u32(y % 0x11_0000);
    opt_args(a, b, c, d)
}

#[no_mangle]
pub extern "C" fn abi_wide_ref(x: u64, y: u64) -> u64 {
    let r = wide_sum(&mk_wide(x), &mk_wide(y));
    (r as u64) ^ (r >> 64) as u64
}

#[inline(never)]
fn arr_ret(x: u16) -> [u16; 7] {
    let mut a = [0u16; 7];
    for i in 0..7 {
        a[i] = x.rotate_left(i as u32 * 2) ^ i as u16;
    }
    a
}

#[no_mangle]
pub extern "C" fn abi_arr_ret(x: u32, y: u32) -> u64 {
    let a = arr_ret(x as u16);
    let b = arr_ret(y as u16);
    let mut h = 0u64;
    for i in 0..7 {
        h = h * 65599 + (a[i] ^ b[6 - i]) as u64;
    }
    h
}
