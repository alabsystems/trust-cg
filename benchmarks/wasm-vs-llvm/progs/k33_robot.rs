#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Dir {
    N,
    E,
    S,
    W,
}

impl Dir {
    #[inline(never)]
    fn right(self) -> Dir {
        match self {
            Dir::N => Dir::E,
            Dir::E => Dir::S,
            Dir::S => Dir::W,
            Dir::W => Dir::N,
        }
    }
    #[inline(never)]
    fn left(self) -> Dir {
        match self {
            Dir::N => Dir::W,
            Dir::W => Dir::S,
            Dir::S => Dir::E,
            Dir::E => Dir::N,
        }
    }
}

// Robot walk: bits of `prog` choose turn-left / turn-right / forward.
#[no_mangle]
pub extern "C" fn robot_walk(prog: u32, steps: u32) -> i64 {
    let mut d = Dir::N;
    let (mut x, mut y) = (0i32, 0i32);
    for i in 0..(steps % 16) {
        match (prog >> (2 * i)) & 3 {
            0 => d = d.left(),
            1 => d = d.right(),
            _ => match d {
                Dir::N => y += 1,
                Dir::E => x += 1,
                Dir::S => y -= 1,
                Dir::W => x -= 1,
            },
        }
    }
    (x as i64) << 32 | (y as u32 as i64) ^ (d as i64) << 60
}

// Same walk with inline turning (no helper calls).
#[no_mangle]
pub extern "C" fn robot_walk_inline(prog: u32, steps: u32) -> i64 {
    let mut d = Dir::N;
    let (mut x, mut y) = (0i32, 0i32);
    for i in 0..(steps % 16) {
        let op = (prog >> (2 * i)) & 3;
        if op == 1 {
            d = match d {
                Dir::N => Dir::E,
                Dir::E => Dir::S,
                Dir::S => Dir::W,
                Dir::W => Dir::N,
            };
        } else if op >= 2 {
            match d {
                Dir::N => y += 1,
                Dir::E => x += 1,
                Dir::S => y -= 1,
                Dir::W => x -= 1,
            }
        }
    }
    (x as i64) << 32 | (y as u32 as i64)
}

#[derive(Clone, Copy, PartialEq)]
enum Lex {
    Ws,
    Ident,
    Num,
    Other,
}

// Count tokens in a byte stream with a lexer-mode state machine.
#[no_mangle]
pub extern "C" fn lexer_modes(seed: u32, n: u32) -> u32 {
    let alphabet = b"ab1 2_;x9  ";
    let mut s = seed | 1;
    let mut mode = Lex::Ws;
    let mut idents = 0u32;
    let mut nums = 0u32;
    let mut others = 0u32;
    for _ in 0..(n % 40) {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        let c = alphabet[(s % alphabet.len() as u32) as usize];
        let next = if c == b' ' {
            Lex::Ws
        } else if c.is_ascii_digit() && mode != Lex::Ident {
            Lex::Num
        } else if c.is_ascii_alphanumeric() || c == b'_' {
            Lex::Ident
        } else {
            Lex::Other
        };
        match (mode, next) {
            (Lex::Ident, Lex::Ident) | (Lex::Num, Lex::Num) | (_, Lex::Ws) => {}
            (_, Lex::Ident) => idents += 1,
            (_, Lex::Num) => nums += 1,
            (_, Lex::Other) => others += 1,
        }
        mode = next;
    }
    idents | nums << 8 | others << 16 | (mode as u32) << 24
}

#[derive(Clone, Copy, PartialEq)]
enum Parity {
    Even,
    Odd,
}

#[no_mangle]
pub extern "C" fn parity_fsm(x: u32) -> u32 {
    let mut p = Parity::Even;
    for i in 0..32 {
        if (x >> i) & 1 == 1 {
            p = match p {
                Parity::Even => Parity::Odd,
                Parity::Odd => Parity::Even,
            };
        }
    }
    let fsm = match p {
        Parity::Even => 0,
        Parity::Odd => 1,
    };
    fsm | (x.count_ones() & 1) << 1
}
