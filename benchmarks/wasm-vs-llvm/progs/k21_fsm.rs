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
fn gen(seed: u32, out: &mut [u8; 24], alphabet: &[u8]) -> usize {
    let mut s = seed | 1;
    for b in out.iter_mut() {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        *b = alphabet[(s % alphabet.len() as u32) as usize];
    }
    (seed >> 8) as usize % 25
}

// glob: '*' any run, '?' any single, else literal
#[inline(never)]
fn glob(p: &[u8], s: &[u8]) -> bool {
    let (mut pi, mut si) = (0usize, 0usize);
    let mut star: Option<usize> = None;
    let mut mark = 0usize;
    let mut guard = 0;
    while si < s.len() {
        guard += 1;
        if guard > 2000 {
            return false;
        }
        if pi < p.len() && (p[pi] == b'?' || p[pi] == s[si]) {
            pi += 1;
            si += 1;
        } else if pi < p.len() && p[pi] == b'*' {
            star = Some(pi);
            mark = si;
            pi += 1;
        } else if let Some(sp) = star {
            pi = sp + 1;
            mark += 1;
            si = mark;
        } else {
            return false;
        }
    }
    while pi < p.len() && p[pi] == b'*' {
        pi += 1;
    }
    pi == p.len()
}

#[no_mangle]
pub extern "C" fn glob_match(a: u32, b: u32) -> u32 {
    let mut p = [0u8; 24];
    let mut s = [0u8; 24];
    let pn = gen(a, &mut p, b"ab*?") % 8;
    let sn = gen(b, &mut s, b"abc");
    glob(&p[..pn], &s[..sn]) as u32 | (pn as u32) << 8 | (sn as u32) << 16
}

// tiny regex: c . ^ $ * (Pike/Kernighan)
#[inline(never)]
fn match_here(re: &[u8], text: &[u8], depth: u32) -> bool {
    if depth > 200 {
        return false;
    }
    if re.is_empty() {
        return true;
    }
    if re.len() >= 2 && re[1] == b'*' {
        return match_star(re[0], &re[2..], text, depth + 1);
    }
    if re[0] == b'$' && re.len() == 1 {
        return text.is_empty();
    }
    if !text.is_empty() && (re[0] == b'.' || re[0] == text[0]) {
        return match_here(&re[1..], &text[1..], depth + 1);
    }
    false
}

#[inline(never)]
fn match_star(c: u8, re: &[u8], text: &[u8], depth: u32) -> bool {
    let mut t = text;
    loop {
        if match_here(re, t, depth + 1) {
            return true;
        }
        if t.is_empty() || (t[0] != c && c != b'.') {
            return false;
        }
        t = &t[1..];
    }
}

#[inline(never)]
fn re_match(re: &[u8], text: &[u8]) -> bool {
    if !re.is_empty() && re[0] == b'^' {
        return match_here(&re[1..], text, 0);
    }
    let mut t = text;
    loop {
        if match_here(re, t, 0) {
            return true;
        }
        if t.is_empty() {
            return false;
        }
        t = &t[1..];
    }
}

#[no_mangle]
pub extern "C" fn regex(a: u32, b: u32) -> u32 {
    let pats: [&[u8]; 8] = [
        b"ab*c", b"^a.c$", b"a*", b".*b$", b"^$", b"c.*a", b"b*b*b*c", b"^ab*a*",
    ];
    let mut s = [0u8; 24];
    let sn = gen(b, &mut s, b"abc");
    let p = pats[(a as usize) % 8];
    re_match(p, &s[..sn]) as u32 | (sn as u32) << 4
}

// Hoehrmann-style UTF-8 DFA (hand-built classification)
#[inline(never)]
fn utf8_class(b: u8) -> u8 {
    match b {
        0x00..=0x7f => 0,
        0x80..=0x8f => 1,
        0x90..=0x9f => 9,
        0xa0..=0xbf => 7,
        0xc0..=0xc1 => 8,
        0xc2..=0xdf => 2,
        0xe0 => 10,
        0xe1..=0xec | 0xee..=0xef => 3,
        0xed => 4,
        0xf0 => 11,
        0xf1..=0xf3 => 6,
        0xf4 => 5,
        _ => 8,
    }
}

#[derive(Clone, Copy, PartialEq)]
enum St {
    Accept,
    Reject,
    Need1,
    Need2,
    Need3,
    E0,
    Ed,
    F0,
    F4,
}

#[inline(never)]
fn step(st: St, cls: u8) -> St {
    use St::*;
    match (st, cls) {
        (Accept, 0) => Accept,
        (Accept, 2) => Need1,
        (Accept, 3) => Need2,
        (Accept, 10) => E0,
        (Accept, 4) => Ed,
        (Accept, 6) => Need3,
        (Accept, 11) => F0,
        (Accept, 5) => F4,
        (Need1, 1) | (Need1, 7) | (Need1, 9) => Accept,
        (Need2, 1) | (Need2, 7) | (Need2, 9) => Need1,
        (Need3, 1) | (Need3, 7) | (Need3, 9) => Need2,
        (E0, 7) => Need1,
        (Ed, 1) | (Ed, 9) => Need1,
        (F0, 7) | (F0, 9) => Need2,
        (F4, 1) => Need2,
        _ => Reject,
    }
}

#[no_mangle]
pub extern "C" fn utf8_dfa(a: u32, b: u32) -> u32 {
    let mut buf = [0u8; 24];
    let n = gen(
        a ^ b,
        &mut buf,
        &[
            0x41, 0xc3, 0xa9, 0xe2, 0x82, 0xac, 0xf0, 0x9f, 0x98, 0x80, 0xed, 0xa0, 0xff, 0xc0,
            0xf4, 0x90,
        ],
    );
    let mut st = St::Accept;
    let mut valid_prefix = 0;
    for (i, &c) in buf[..n].iter().enumerate() {
        st = step(st, utf8_class(c));
        if st == St::Reject {
            break;
        }
        if st == St::Accept {
            valid_prefix = i + 1;
        }
    }
    let core_ok = core::str::from_utf8(&buf[..n]).is_ok();
    let core_valid = match core::str::from_utf8(&buf[..n]) {
        Ok(_) => n,
        Err(e) => e.valid_up_to(),
    };
    ((st == St::Accept) as u32)
        | (core_ok as u32) << 1
        | (valid_prefix as u32) << 8
        | (core_valid as u32) << 16
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum NumSt {
    Start,
    Sign,
    Int0,
    Int,
    Dot,
    Frac,
    Exp,
    ExpSign,
    ExpDigits,
    Bad,
}

#[inline(never)]
fn json_number(s: &[u8]) -> (bool, u32) {
    use NumSt::*;
    let mut st = Start;
    let mut transitions = 0u32;
    'outer: for &c in s {
        transitions = transitions.wrapping_mul(10).wrapping_add(st as u32);
        st = match st {
            Start => match c {
                b'-' => Sign,
                b'0' => Int0,
                b'1'..=b'9' => Int,
                _ => break 'outer,
            },
            Sign => match c {
                b'0' => Int0,
                b'1'..=b'9' => Int,
                _ => Bad,
            },
            Int0 => match c {
                b'.' => Dot,
                b'e' | b'E' => Exp,
                _ => Bad,
            },
            Int => match c {
                b'0'..=b'9' => Int,
                b'.' => Dot,
                b'e' | b'E' => Exp,
                _ => Bad,
            },
            Dot => match c {
                b'0'..=b'9' => Frac,
                _ => Bad,
            },
            Frac => match c {
                b'0'..=b'9' => Frac,
                b'e' | b'E' => Exp,
                _ => Bad,
            },
            Exp => match c {
                b'+' | b'-' => ExpSign,
                b'0'..=b'9' => ExpDigits,
                _ => Bad,
            },
            ExpSign | ExpDigits => match c {
                b'0'..=b'9' => ExpDigits,
                _ => Bad,
            },
            Bad => break 'outer,
        };
    }
    (matches!(st, Int0 | Int | Frac | ExpDigits), transitions)
}

#[no_mangle]
pub extern "C" fn json_num(a: u32, b: u32) -> u64 {
    let mut buf = [0u8; 24];
    let n = gen(a, &mut buf, b"-0123.eE+9") % (b as usize % 12 + 1);
    let (ok, t) = json_number(&buf[..n]);
    ok as u64 | (t as u64) << 1 | (n as u64) << 40
}

#[no_mangle]
pub extern "C" fn labeled(a: u32, b: u32) -> u32 {
    let grid = [[a, b, a ^ b], [a >> 1, b >> 2, 7], [3, a & b, a | b]];
    let target = (a.wrapping_add(b)) & 7;
    let found = 'search: {
        for (i, row) in grid.iter().enumerate() {
            for (j, &v) in row.iter().enumerate() {
                if v & 7 == target {
                    break 'search Some((i, j));
                }
                if v == 0 {
                    continue;
                }
            }
        }
        None
    };
    let mut count = 0u32;
    'rows: for row in grid.iter() {
        for &v in row.iter() {
            if v % 5 == 0 {
                continue 'rows;
            }
            count += 1;
        }
    }
    match found {
        Some((i, j)) => (i * 3 + j) as u32 | count << 8,
        None => 99 | count << 8,
    }
}
