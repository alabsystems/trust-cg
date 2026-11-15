#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

const B64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

#[inline(never)]
fn b64_encode(src: &[u8], dst: &mut [u8]) -> Option<usize> {
    let need = (src.len() + 2) / 3 * 4;
    if dst.len() < need {
        return None;
    }
    let mut o = 0;
    let mut ci = 0;
    while ci < src.len() {
        let chunk = &src[ci..core::cmp::min(ci + 3, src.len())];
        ci += 3;
        let b0 = chunk[0] as u32;
        let b1 = if chunk.len() > 1 { chunk[1] as u32 } else { 0 };
        let b2 = if chunk.len() > 2 { chunk[2] as u32 } else { 0 };
        let n = (b0 << 16) | (b1 << 8) | b2;
        dst[o] = B64[(n >> 18) as usize & 63];
        dst[o + 1] = B64[(n >> 12) as usize & 63];
        dst[o + 2] = if chunk.len() > 1 {
            B64[(n >> 6) as usize & 63]
        } else {
            b'='
        };
        dst[o + 3] = if chunk.len() > 2 {
            B64[n as usize & 63]
        } else {
            b'='
        };
        o += 4;
    }
    Some(o)
}

#[inline(never)]
fn b64_val(c: u8) -> Option<u8> {
    match c {
        b'A'..=b'Z' => Some(c - b'A'),
        b'a'..=b'z' => Some(c - b'a' + 26),
        b'0'..=b'9' => Some(c - b'0' + 52),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum DecErr {
    Len,
    Char(usize),
    Pad,
}

#[inline(never)]
fn b64_decode(src: &[u8], dst: &mut [u8; 48]) -> Result<usize, DecErr> {
    if src.len() % 4 != 0 {
        return Err(DecErr::Len);
    }
    let mut o = 0;
    let mut i = 0;
    while i < src.len() {
        let mut v = [0u8; 4];
        let mut pad = 0;
        for j in 0..4 {
            let c = src[i + j];
            if c == b'=' {
                if i + 4 != src.len() || j < 2 {
                    return Err(DecErr::Pad);
                }
                pad += 1;
            } else if pad > 0 {
                return Err(DecErr::Pad);
            } else {
                v[j] = b64_val(c).ok_or(DecErr::Char(i + j))?;
            }
        }
        let n = ((v[0] as u32) << 18) | ((v[1] as u32) << 12) | ((v[2] as u32) << 6) | v[3] as u32;
        let bytes = [(n >> 16) as u8, (n >> 8) as u8, n as u8];
        for k in 0..3 - pad {
            if o >= dst.len() {
                return Err(DecErr::Len);
            }
            dst[o] = bytes[k];
            o += 1;
        }
        i += 4;
    }
    Ok(o)
}

#[inline(never)]
fn gen(seed: u32, out: &mut [u8; 32]) {
    let mut s = seed;
    for b in out.iter_mut() {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        *b = s as u8;
    }
}

#[no_mangle]
pub extern "C" fn b64_roundtrip(seed: u32, n: u32) -> u32 {
    let mut src = [0u8; 32];
    gen(seed | 1, &mut src);
    let n = (n % 33) as usize;
    let mut enc = [0u8; 48];
    let el = match b64_encode(&src[..n], &mut enc) {
        Some(l) => l,
        None => return 0xffff_ffff,
    };
    let mut dec = [0u8; 48];
    match b64_decode(&enc[..el], &mut dec) {
        Ok(dl) => {
            let same = dl == n && dec[..dl] == src[..n];
            let mut h = el as u32 * 1000 + dl as u32;
            for &b in &enc[..el] {
                h = h.wrapping_mul(31).wrapping_add(b as u32);
            }
            h ^ ((same as u32) << 31)
        }
        Err(e) => match e {
            DecErr::Len => 1,
            DecErr::Char(p) => 2 + p as u32,
            DecErr::Pad => 3,
        },
    }
}

#[no_mangle]
pub extern "C" fn b64_dec_bad(a: u32, b: u32) -> u32 {
    let mut s = *b"SGVsbG8sIHdvcmxkIQ==";
    let i = (a as usize) % s.len();
    s[i] = b as u8;
    let mut dec = [0u8; 48];
    match b64_decode(&s, &mut dec) {
        Ok(l) => {
            let mut h = l as u32;
            for &x in &dec[..l] {
                h = h.wrapping_mul(131) ^ x as u32;
            }
            h
        }
        Err(DecErr::Char(p)) => 0x1000 + p as u32,
        Err(DecErr::Pad) => 0x2000,
        Err(DecErr::Len) => 0x3000,
    }
}

#[inline(never)]
fn hex_encode(src: &[u8], dst: &mut [u8; 64]) -> usize {
    const H: &[u8] = b"0123456789abcdef";
    let mut o = 0;
    for &b in src.iter().take(32) {
        dst[o] = H[(b >> 4) as usize];
        dst[o + 1] = H[(b & 15) as usize];
        o += 2;
    }
    o
}

#[inline(never)]
fn hex_decode(src: &[u8], dst: &mut [u8]) -> Result<usize, usize> {
    if src.len() % 2 != 0 || src.len() / 2 > dst.len() {
        return Err(usize::MAX);
    }
    for i in 0..src.len() / 2 {
        let pair = &src[2 * i..2 * i + 2];
        let hi = (pair[0] as char).to_digit(16).ok_or(2 * i)?;
        let lo = (pair[1] as char).to_digit(16).ok_or(2 * i + 1)?;
        dst[i] = (hi * 16 + lo) as u8;
    }
    Ok(src.len() / 2)
}

#[no_mangle]
pub extern "C" fn hex_roundtrip(seed: u32, n: u32) -> u32 {
    let mut src = [0u8; 32];
    gen(seed ^ 0x55, &mut src);
    let n = (n % 33) as usize;
    let mut enc = [0u8; 64];
    let el = hex_encode(&src[..n], &mut enc);
    let mut dec = [0u8; 32];
    match hex_decode(&enc[..el], &mut dec) {
        Ok(l) => {
            let mut h = l as u32;
            for i in 0..l {
                h = h.wrapping_mul(7) ^ (dec[i] as u32) ^ ((dec[i] == src[i]) as u32) << 9;
            }
            h
        }
        Err(p) => 0x8000_0000 | p as u32,
    }
}

#[no_mangle]
pub extern "C" fn hex_bad(a: u32, b: u32) -> u32 {
    let mut s = *b"DEADbeef0123456789aBcD";
    let i = (a as usize) % s.len();
    s[i] = b as u8;
    let mut dec = [0u8; 11];
    match hex_decode(&s, &mut dec) {
        Ok(l) => {
            let mut h = 0u32;
            for &x in &dec[..l] {
                h = h.rotate_left(5) ^ x as u32;
            }
            h
        }
        Err(p) => 0xdead_0000 | p as u32,
    }
}

#[inline(never)]
fn rle_encode(src: &[u8], dst: &mut [u8; 80]) -> Option<usize> {
    let mut o = 0;
    let mut i = 0;
    while i < src.len() {
        let c = src[i];
        let mut run = 1;
        while i + run < src.len() && src[i + run] == c && run < 255 {
            run += 1;
        }
        if o + 2 > dst.len() {
            return None;
        }
        dst[o] = run as u8;
        dst[o + 1] = c;
        o += 2;
        i += run;
    }
    Some(o)
}

#[inline(never)]
fn rle_decode(src: &[u8], dst: &mut [u8; 40]) -> Option<usize> {
    let mut o = 0;
    for q in 0..src.len() / 2 {
        let p = &src[2 * q..];
        let (n, c) = (p[0] as usize, p[1]);
        if o + n > dst.len() {
            return None;
        }
        for k in 0..n {
            dst[o + k] = c;
        }
        o += n;
    }
    Some(o)
}

#[no_mangle]
pub extern "C" fn rle(seed: u32, n: u32) -> u32 {
    let mut src = [0u8; 40];
    let mut s = seed | 3;
    for b in src.iter_mut() {
        s = s.wrapping_mul(69069).wrapping_add(1);
        *b = ((s >> 29) & 3) as u8 + b'a';
    }
    let n = (n % 41) as usize;
    let mut enc = [0u8; 80];
    let el = match rle_encode(&src[..n], &mut enc) {
        Some(l) => l,
        None => return 1,
    };
    let mut dec = [0u8; 40];
    let dl = match rle_decode(&enc[..el], &mut dec) {
        Some(l) => l,
        None => return 2,
    };
    ((el as u32) << 16) | ((dl as u32) << 8) | (dec[..dl] == src[..n]) as u32
}
