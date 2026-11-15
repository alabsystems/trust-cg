#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Tok {
    Num(i64),
    Op(u8),
    LParen,
    RParen,
    End,
}

#[inline(never)]
fn lex(s: &[u8], pos: &mut usize) -> Tok {
    while *pos < s.len() && s[*pos] == b' ' {
        *pos += 1;
    }
    if *pos >= s.len() {
        return Tok::End;
    }
    let c = s[*pos];
    *pos += 1;
    match c {
        b'0'..=b'9' => {
            let mut v = (c - b'0') as i64;
            while *pos < s.len() && s[*pos].is_ascii_digit() {
                v = v * 10 + (s[*pos] - b'0') as i64;
                *pos += 1;
            }
            Tok::Num(v)
        }
        b'(' => Tok::LParen,
        b')' => Tok::RParen,
        _ => Tok::Op(c),
    }
}

#[inline(never)]
fn prec(op: u8) -> u8 {
    match op {
        b'+' | b'-' => 1,
        b'*' | b'/' | b'%' => 2,
        b'^' => 3,
        _ => 0,
    }
}

#[inline(never)]
fn apply(op: u8, a: i64, b: i64) -> Option<i64> {
    match op {
        b'+' => a.checked_add(b),
        b'-' => a.checked_sub(b),
        b'*' => a.checked_mul(b),
        b'/' => a.checked_div(b),
        b'%' => a.checked_rem(b),
        b'^' => {
            if b < 0 || b > 20 {
                None
            } else {
                a.checked_pow(b as u32)
            }
        }
        _ => None,
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum EvalErr {
    Syntax(usize),
    Arith,
    Overflow,
}

#[inline(never)]
fn eval(s: &[u8]) -> Result<i64, EvalErr> {
    let mut vals = [0i64; 16];
    let mut nv = 0usize;
    let mut ops = [0u8; 16];
    let mut no = 0usize;
    let mut pos = 0usize;
    let mut expect_num = true;
    let mut steps = 0;
    loop {
        steps += 1;
        if steps > 200 {
            return Err(EvalErr::Overflow);
        }
        let t = lex(s, &mut pos);
        match t {
            Tok::Num(v) => {
                if !expect_num || nv == 16 {
                    return Err(EvalErr::Syntax(pos));
                }
                vals[nv] = v;
                nv += 1;
                expect_num = false;
            }
            Tok::LParen => {
                if !expect_num || no == 16 {
                    return Err(EvalErr::Syntax(pos));
                }
                ops[no] = b'(';
                no += 1;
            }
            Tok::RParen | Tok::End => {
                if expect_num {
                    return Err(EvalErr::Syntax(pos));
                }
                while no > 0 && ops[no - 1] != b'(' {
                    no -= 1;
                    if nv < 2 {
                        return Err(EvalErr::Syntax(pos));
                    }
                    let b = vals[nv - 1];
                    let a = vals[nv - 2];
                    nv -= 2;
                    vals[nv] = apply(ops[no], a, b).ok_or(EvalErr::Arith)?;
                    nv += 1;
                }
                if t == Tok::RParen {
                    if no == 0 {
                        return Err(EvalErr::Syntax(pos));
                    }
                    no -= 1;
                } else {
                    if no != 0 || nv != 1 {
                        return Err(EvalErr::Syntax(pos));
                    }
                    return Ok(vals[0]);
                }
            }
            Tok::Op(op) => {
                if expect_num || prec(op) == 0 {
                    return Err(EvalErr::Syntax(pos));
                }
                while no > 0 && ops[no - 1] != b'(' && prec(ops[no - 1]) >= prec(op) && op != b'^' {
                    no -= 1;
                    let b = vals[nv - 1];
                    let a = vals[nv - 2];
                    nv -= 2;
                    vals[nv] = apply(ops[no], a, b).ok_or(EvalErr::Arith)?;
                    nv += 1;
                }
                if no == 16 {
                    return Err(EvalErr::Overflow);
                }
                ops[no] = op;
                no += 1;
                expect_num = true;
            }
        }
    }
}

#[inline(never)]
fn enc(r: Result<i64, EvalErr>) -> i64 {
    match r {
        Ok(v) => v,
        Err(EvalErr::Syntax(p)) => -1_000_000 - p as i64,
        Err(EvalErr::Arith) => -2_000_000,
        Err(EvalErr::Overflow) => -3_000_000,
    }
}

#[no_mangle]
pub extern "C" fn expr_fixed(k: u32) -> i64 {
    let exprs: [&[u8]; 10] = [
        b"1 + 2 * 3",
        b"(1 + 2) * 3",
        b"2 ^ 3 ^ 2",
        b"100 / (5 - 5)",
        b"7 % 3 + 12 / 4 - 1",
        b"((2))",
        b"1 +",
        b"(1 + 2",
        b"9223372036854775807 + 1",
        b"42",
    ];
    enc(eval(exprs[(k as usize) % 10]))
}

#[no_mangle]
pub extern "C" fn expr_gen(seed: u32, len: u32) -> i64 {
    let alphabet = b"0123456789+-*/%()^ ";
    let mut buf = [b' '; 24];
    let mut s = seed | 1;
    let n = (len % 24) as usize;
    for i in 0..n {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        buf[i] = alphabet[(s % alphabet.len() as u32) as usize];
    }
    enc(eval(&buf[..n]))
}

#[no_mangle]
pub extern "C" fn tok_stream(seed: u32) -> u64 {
    let text: &[u8] = b"12 + (34 * 5) - 6 / 78 % (9)";
    let mut pos = (seed as usize) % 5;
    let mut h = 0u64;
    let mut prev = Tok::End;
    for _ in 0..20 {
        let t = lex(text, &mut pos);
        let v = match t {
            Tok::Num(n) => n as u64,
            Tok::Op(o) => 1000 + o as u64,
            Tok::LParen => 2000,
            Tok::RParen => 3000,
            Tok::End => 4000,
        };
        h = h.wrapping_mul(31) ^ v ^ ((t == prev) as u64) << 40;
        prev = t;
        if t == Tok::End {
            break;
        }
    }
    h
}
