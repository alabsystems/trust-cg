#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

struct Kw {
    name: &'static str,
    code: u32,
    prec: u8,
}

static KEYWORDS: [Kw; 6] = [
    Kw {
        name: "let",
        code: 1,
        prec: 0,
    },
    Kw {
        name: "fn",
        code: 2,
        prec: 0,
    },
    Kw {
        name: "if",
        code: 3,
        prec: 1,
    },
    Kw {
        name: "else",
        code: 4,
        prec: 1,
    },
    Kw {
        name: "while",
        code: 5,
        prec: 2,
    },
    Kw {
        name: "return",
        code: 6,
        prec: 3,
    },
];

static SOURCES: [&str; 5] = [
    "let x = 10 + y * 3; fn f(a) { return a; }",
    "while (i < 100) { i = i + 1; } else",
    "if a >= b { return 0x1f; } else { let z = a - b; }",
    "   ",
    "fn main ( ) { let q = 7 * ( 3 + 4 ) / 2 ; }",
];

static NESTED: &[&[u16]] = &[&[1, 2, 3], &[], &[400, 500], &[6; 7]];

#[derive(Clone, Copy, PartialEq, Debug)]
enum Tok<'a> {
    Kw(u32),
    Ident(&'a str),
    Num(u64),
    Punct(u8),
    Op2([u8; 2]),
}

#[inline(never)]
fn lookup(word: &str) -> Option<&'static Kw> {
    KEYWORDS.iter().find(|k| k.name == word)
}

#[inline(never)]
fn next_tok<'a>(s: &'a str, pos: &mut usize) -> Option<Tok<'a>> {
    let b = s.as_bytes();
    while *pos < b.len() && b[*pos] == b' ' {
        *pos += 1;
    }
    if *pos >= b.len() {
        return None;
    }
    let start = *pos;
    let c = b[start];
    if c.is_ascii_alphabetic() || c == b'_' {
        while *pos < b.len() && (b[*pos].is_ascii_alphanumeric() || b[*pos] == b'_') {
            *pos += 1;
        }
        let w = &s[start..*pos];
        return Some(match lookup(w) {
            Some(k) => Tok::Kw(k.code * 10 + k.prec as u32),
            None => Tok::Ident(w),
        });
    }
    if c.is_ascii_digit() {
        let mut radix = 10;
        if c == b'0' && start + 1 < b.len() && b[start + 1] == b'x' {
            radix = 16;
            *pos += 2;
        }
        let ds = *pos;
        while *pos < b.len() && (b[*pos] as char).is_digit(radix) {
            *pos += 1;
        }
        let v = u64::from_str_radix(&s[ds..*pos], radix).unwrap_or(0);
        return Some(Tok::Num(v));
    }
    if start + 1 < b.len() && b[start + 1] == b'=' && matches!(c, b'<' | b'>' | b'=' | b'!') {
        *pos += 2;
        return Some(Tok::Op2([c, b'=']));
    }
    *pos += 1;
    Some(Tok::Punct(c))
}

#[inline(never)]
fn lex_hash(s: &str, limit: usize) -> u64 {
    let mut pos = 0;
    let mut h = 0xcbf29ce484222325u64;
    let mut n = 0;
    while let Some(t) = next_tok(s, &mut pos) {
        let v = match t {
            Tok::Kw(k) => 1000 + k as u64,
            Tok::Ident(w) => 2000 + w.len() as u64 * 7 + w.as_bytes()[0] as u64,
            Tok::Num(x) => 3000 + x,
            Tok::Punct(p) => 4000 + p as u64,
            Tok::Op2(o) => 5000 + o[0] as u64,
        };
        h = (h ^ v).wrapping_mul(0x100000001b3);
        n += 1;
        if n >= limit {
            break;
        }
    }
    h ^ n as u64
}

type Handler = fn(u32, u32) -> u32;

fn h_add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}
fn h_xor(a: u32, b: u32) -> u32 {
    a ^ b
}
fn h_mulhi(a: u32, b: u32) -> u32 {
    ((a as u64 * b as u64) >> 32) as u32
}
fn h_rot(a: u32, b: u32) -> u32 {
    a.rotate_left(b)
}

static DISPATCH: [(&str, Handler); 4] = [
    ("add", h_add),
    ("xor", h_xor),
    ("mulhi", h_mulhi),
    ("rot", h_rot),
];

static mut COUNTERS: [u64; 4] = [0; 4];
static mut LAST: Option<&'static str> = None;

#[no_mangle]
pub extern "C" fn kw_lookup(k: u32) -> u32 {
    let words = ["let", "fn", "iff", "else", "", "whilE", "return", "le"];
    let w = words[(k as usize) % words.len()];
    match lookup(w) {
        Some(kw) => kw.code << 8 | kw.prec as u32 | (kw.name.len() as u32) << 16,
        None => 0xdead,
    }
}
