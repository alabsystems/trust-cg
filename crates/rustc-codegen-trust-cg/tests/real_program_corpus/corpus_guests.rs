// crates/rustc-codegen-trust-cg/tests/real_program_corpus/corpus_guests.rs
//
// THE SHARED REAL-PROGRAM CORPUS — single source for every architecture row.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// `include!`d by tests/real_program_corpus_x86.rs (compile+run differential
// gate) and tests/real_program_corpus_a64.rs (cross-compile verdict gate) so
// the guest set can NEVER drift between architecture rows. Guests are
// real-program-shaped, exit-code checksums (mod 251), no println,
// panic=abort-safe.

struct Guest {
    name: &'static str,
    what: &'static str,
    src: &'static str,
}

fn corpus() -> Vec<Guest> {
    vec![
        Guest {
            name: "p01_interp",
            what: "bytecode interpreter loop (dispatch match, registers, backward jump)",
            src: r#"
fn main() {
    // ops: 0 imm -> acc += imm ; 1 imm -> acc *= imm (wrapping)
    //      2 imm -> ctr = imm  ; 3 addr -> ctr -= 1, jnz addr
    //      4     -> acc ^= ctr*0x9e ; 5 -> halt
    let prog: [u8; 12] = [2, 9, 0, 3, 1, 2, 4, 3, 2, 5, 0, 0];
    let mut acc: u64 = 0;
    let mut ctr: u64 = 0;
    let mut pc: usize = 0;
    let mut steps: u32 = 0;
    while pc < prog.len() && steps < 100_000 {
        steps += 1;
        match prog[pc] {
            0 => { acc = acc.wrapping_add(prog[pc + 1] as u64); pc += 2; }
            1 => { acc = acc.wrapping_mul(prog[pc + 1] as u64); pc += 2; }
            2 => { ctr = prog[pc + 1] as u64; pc += 2; }
            3 => {
                ctr = ctr.wrapping_sub(1);
                if ctr != 0 { pc = prog[pc + 1] as usize; } else { pc += 2; }
            }
            4 => { acc ^= ctr.wrapping_mul(0x9e); pc += 1; }
            _ => break,
        }
    }
    std::process::exit(((acc ^ steps as u64) % 251) as i32);
}
"#,
        },
        Guest {
            name: "p02_sort_vec",
            what: "insertion sort over Vec<u64> filled by an LCG",
            src: r#"
fn main() {
    let mut v: Vec<u64> = Vec::new();
    let mut x: u64 = 0x2545_f491_4f6c_dd1d;
    let mut i: u32 = 0;
    while i < 40 {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        v.push(x >> 33);
        i += 1;
    }
    // insertion sort
    let mut j: usize = 1;
    while j < v.len() {
        let key = v[j];
        let mut k = j;
        while k > 0 && v[k - 1] > key {
            v[k] = v[k - 1];
            k -= 1;
        }
        v[k] = key;
        j += 1;
    }
    // sortedness-sensitive checksum
    let mut h: u64 = 0;
    let mut m: usize = 0;
    while m < v.len() {
        h = h.wrapping_mul(31).wrapping_add(v[m].wrapping_mul(m as u64 + 1));
        m += 1;
    }
    std::process::exit((h % 251) as i32);
}
"#,
        },
        Guest {
            name: "p03_tokenizer",
            what: "string-less tokenizer over &[u8] (ident/number/symbol classes)",
            src: r#"
fn main() {
    let src: &[u8] = b"let x1 = 42 + foo * 7; if x1 >= 13 { bar(x1, 99); } while y_2 < 8 { y_2 = y_2 + 1; }";
    let mut i: usize = 0;
    let mut idents: u64 = 0;
    let mut numbers: u64 = 0;
    let mut symbols: u64 = 0;
    let mut h: u64 = 1469598103934665603;
    while i < src.len() {
        let c = src[i];
        if c == b' ' {
            i += 1;
        } else if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < src.len() && (src[i].is_ascii_alphanumeric() || src[i] == b'_') {
                i += 1;
            }
            idents += 1;
            h = h.wrapping_mul(0x100000001b3) ^ ((i - start) as u64) ^ 0x10;
        } else if c.is_ascii_digit() {
            let mut val: u64 = 0;
            while i < src.len() && src[i].is_ascii_digit() {
                val = val.wrapping_mul(10).wrapping_add((src[i] - b'0') as u64);
                i += 1;
            }
            numbers += 1;
            h = h.wrapping_mul(0x100000001b3) ^ val;
        } else {
            symbols += 1;
            h = h.wrapping_mul(0x100000001b3) ^ (c as u64) << 1;
            i += 1;
        }
    }
    let sum = h ^ idents.wrapping_mul(101) ^ numbers.wrapping_mul(211) ^ symbols;
    std::process::exit((sum % 251) as i32);
}
"#,
        },
        Guest {
            name: "p04_matmul",
            what: "fixed-size 6x6 matrix multiply + trace/checksum",
            src: r#"
fn main() {
    let mut a = [[0u64; 6]; 6];
    let mut b = [[0u64; 6]; 6];
    let mut i = 0usize;
    while i < 6 {
        let mut j = 0usize;
        while j < 6 {
            a[i][j] = (i as u64).wrapping_mul(7).wrapping_add(j as u64 * 3 + 1);
            b[i][j] = (j as u64).wrapping_mul(5) ^ (i as u64 + 2);
            j += 1;
        }
        i += 1;
    }
    let mut c = [[0u64; 6]; 6];
    let mut r = 0usize;
    while r < 6 {
        let mut col = 0usize;
        while col < 6 {
            let mut acc: u64 = 0;
            let mut k = 0usize;
            while k < 6 {
                acc = acc.wrapping_add(a[r][k].wrapping_mul(b[k][col]));
                k += 1;
            }
            c[r][col] = acc;
            col += 1;
        }
        r += 1;
    }
    let mut h: u64 = 0;
    let mut x = 0usize;
    while x < 6 {
        let mut y = 0usize;
        while y < 6 {
            h = h.wrapping_mul(31).wrapping_add(c[x][y]);
            y += 1;
        }
        h = h.wrapping_add(c[x][x]); // trace-weighted
        x += 1;
    }
    std::process::exit((h % 251) as i32);
}
"#,
        },
        Guest {
            name: "p05_state_machine",
            what: "DFA over a byte input (match-based transition table)",
            src: r#"
fn main() {
    let input: &[u8] = b"aab0b_11a bb_0a1_ab0 9zz_z9 a0b1c2d3";
    let mut state: u8 = 0;
    let mut visits = [0u32; 4];
    let mut i = 0usize;
    while i < input.len() {
        let c = input[i];
        let class: u8 = if c.is_ascii_alphabetic() {
            0
        } else if c.is_ascii_digit() {
            1
        } else if c == b'_' {
            2
        } else {
            3
        };
        state = match (state, class) {
            (0, 0) => 1,
            (0, 1) => 2,
            (0, _) => 0,
            (1, 0) => 1,
            (1, 1) => 3,
            (1, 2) => 1,
            (1, _) => 0,
            (2, 1) => 2,
            (2, 0) => 3,
            (2, _) => 0,
            (3, 3) => 0,
            (3, _) => 3,
            _ => 0,
        };
        visits[state as usize] += 1;
        i += 1;
    }
    let mut h: u64 = state as u64;
    let mut s = 0usize;
    while s < 4 {
        h = h.wrapping_mul(37).wrapping_add(visits[s] as u64);
        s += 1;
    }
    std::process::exit((h % 251) as i32);
}
"#,
        },
        Guest {
            name: "p06_rdp",
            what: "recursive-descent expression parser/evaluator over a byte slice",
            src: r#"
struct Parser {
    s: &'static [u8],
    pos: usize,
}

impl Parser {
    fn peek(&self) -> u8 {
        if self.pos < self.s.len() { self.s[self.pos] } else { 0 }
    }
    fn bump(&mut self) {
        self.pos += 1;
    }
    fn expr(&mut self) -> u64 {
        let mut v = self.term();
        loop {
            match self.peek() {
                b'+' => { self.bump(); v = v.wrapping_add(self.term()); }
                b'-' => { self.bump(); v = v.wrapping_sub(self.term()); }
                _ => return v,
            }
        }
    }
    fn term(&mut self) -> u64 {
        let mut v = self.factor();
        while self.peek() == b'*' {
            self.bump();
            v = v.wrapping_mul(self.factor());
        }
        v
    }
    fn factor(&mut self) -> u64 {
        if self.peek() == b'(' {
            self.bump();
            let v = self.expr();
            if self.peek() == b')' { self.bump(); }
            return v;
        }
        let mut v: u64 = 0;
        while self.peek().is_ascii_digit() {
            v = v.wrapping_mul(10).wrapping_add((self.peek() - b'0') as u64);
            self.bump();
        }
        v
    }
}

fn main() {
    let mut p = Parser { s: b"2+3*(4+5)-6*2+(1+2)*(3+4*2)-7", pos: 0 };
    let v = p.expr();
    let mut q = Parser { s: b"((10+2)*(3+1))-(5*5)+99", pos: 0 };
    let w = q.expr();
    std::process::exit(((v.wrapping_mul(17) ^ w) % 251) as i32);
}
"#,
        },
        Guest {
            name: "p07_wordcount",
            what: "hashmap-free word count over byte arrays (26 fixed buckets)",
            src: r#"
fn main() {
    let text: &[u8] = b"the quick brown fox jumps over the lazy dog and the dog barks at the quick fox while a lazy cat naps";
    let mut buckets = [0u32; 26];
    let mut words: u64 = 0;
    let mut longest: usize = 0;
    let mut i = 0usize;
    while i < text.len() {
        while i < text.len() && text[i] == b' ' {
            i += 1;
        }
        if i >= text.len() { break; }
        let start = i;
        let first = text[i];
        while i < text.len() && text[i] != b' ' {
            i += 1;
        }
        let len = i - start;
        if len > longest { longest = len; }
        words += 1;
        if first.is_ascii_lowercase() {
            buckets[(first - b'a') as usize] += 1;
        }
    }
    let mut h: u64 = words.wrapping_mul(131).wrapping_add(longest as u64);
    let mut b = 0usize;
    while b < 26 {
        h = h.wrapping_mul(33).wrapping_add(buckets[b] as u64);
        b += 1;
    }
    std::process::exit((h % 251) as i32);
}
"#,
        },
        Guest {
            name: "p08_fnv_hash",
            what: "FNV-1a hash over an LCG-generated byte buffer",
            src: r#"
fn main() {
    let mut buf = [0u8; 256];
    let mut x: u64 = 88172645463325252;
    let mut i = 0usize;
    while i < buf.len() {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        buf[i] = (x >> 24) as u8;
        i += 1;
    }
    let mut h: u64 = 1469598103934665603;
    let mut j = 0usize;
    while j < buf.len() {
        h ^= buf[j] as u64;
        h = h.wrapping_mul(0x100000001b3);
        j += 1;
    }
    std::process::exit((h % 251) as i32);
}
"#,
        },
        Guest {
            name: "p09_sieve",
            what: "prime sieve over a fixed byte array + prime-sum checksum",
            src: r#"
fn main() {
    const N: usize = 1000;
    let mut composite = [false; N];
    let mut p: usize = 2;
    while p * p < N {
        if !composite[p] {
            let mut m = p * p;
            while m < N {
                composite[m] = true;
                m += p;
            }
        }
        p += 1;
    }
    let mut count: u64 = 0;
    let mut sum: u64 = 0;
    let mut i: usize = 2;
    while i < N {
        if !composite[i] {
            count += 1;
            sum = sum.wrapping_add(i as u64);
        }
        i += 1;
    }
    std::process::exit(((sum ^ count.wrapping_mul(7)) % 251) as i32);
}
"#,
        },
        Guest {
            name: "p10_struct_logic",
            what: "struct-heavy business logic (orders, tiered pricing, for-range loops)",
            src: r#"
#[derive(Clone, Copy)]
struct Order {
    qty: u32,
    unit_price: u32,
    flags: u8,
}

fn total_for(o: &Order) -> u64 {
    let gross = (o.qty as u64).wrapping_mul(o.unit_price as u64);
    // tiered discount: >=100 units 15%, >=20 units 5%, else none; rush flag +8%
    let mut net = if o.qty >= 100 {
        gross - gross * 15 / 100
    } else if o.qty >= 20 {
        gross - gross * 5 / 100
    } else {
        gross
    };
    if o.flags & 0x2 != 0 {
        net = net + net * 8 / 100;
    }
    net
}

fn main() {
    let mut orders = [Order { qty: 0, unit_price: 0, flags: 0 }; 16];
    for i in 0..16u32 {
        orders[i as usize] = Order {
            qty: (i * 13 + 3) % 140,
            unit_price: 50 + (i * 7) % 90,
            flags: (i % 4) as u8,
        };
    }
    let mut total: u64 = 0;
    let mut skipped: u64 = 0;
    for o in orders.iter() {
        if o.flags & 0x1 != 0 {
            skipped += 1; // on-hold orders excluded
            continue;
        }
        total = total.wrapping_add(total_for(o));
    }
    std::process::exit(((total ^ skipped.wrapping_mul(41)) % 251) as i32);
}
"#,
        },
        Guest {
            name: "p11_vec_stack",
            what: "bracket matcher using Vec as an explicit stack (push/pop/depth)",
            src: r#"
fn main() {
    let input: &[u8] = b"([]{()[]}([{}]))[[({})]]{}()((([[{{}}]])))";
    let mut stack: Vec<u8> = Vec::new();
    let mut max_depth: usize = 0;
    let mut balanced: u64 = 1;
    let mut i = 0usize;
    while i < input.len() {
        let c = input[i];
        if c == b'(' || c == b'[' || c == b'{' {
            stack.push(c);
            if stack.len() > max_depth {
                max_depth = stack.len();
            }
        } else {
            let open = match stack.pop() {
                Some(o) => o,
                None => { balanced = 0; 0 }
            };
            let want = match c {
                b')' => b'(',
                b']' => b'[',
                _ => b'{',
            };
            if open != want { balanced = 0; }
        }
        i += 1;
    }
    if !stack.is_empty() { balanced = 0; }
    let h = (max_depth as u64).wrapping_mul(19).wrapping_add(balanced).wrapping_add(input.len() as u64);
    std::process::exit((h % 251) as i32);
}
"#,
        },
        Guest {
            name: "p12_box_tree",
            what: "Box'd binary tree build + recursive weighted sum (heap + recursion)",
            src: r#"
struct Node {
    v: u64,
    l: Option<Box<Node>>,
    r: Option<Box<Node>>,
}

fn leaf(v: u64) -> Option<Box<Node>> {
    Some(Box::new(Node { v, l: None, r: None }))
}

fn sum(n: &Option<Box<Node>>, depth: u64) -> u64 {
    match n {
        None => 0,
        Some(b) => b
            .v
            .wrapping_mul(depth)
            .wrapping_add(sum(&b.l, depth + 1))
            .wrapping_add(sum(&b.r, depth + 1)),
    }
}

fn main() {
    let tree = Some(Box::new(Node {
        v: 10,
        l: Some(Box::new(Node { v: 21, l: leaf(7), r: leaf(33) })),
        r: Some(Box::new(Node {
            v: 4,
            l: leaf(15),
            r: Some(Box::new(Node { v: 9, l: leaf(2), r: None })),
        })),
    }));
    let s = sum(&tree, 1);
    std::process::exit((s % 251) as i32);
}
"#,
        },
        Guest {
            name: "p13_sort_std",
            what: "std sort_unstable + dedup + binary_search over Vec<i64> (std-breadth probe)",
            src: r#"
fn main() {
    let mut v: Vec<i64> = Vec::new();
    let mut x: i64 = 12345;
    let mut i = 0u32;
    while i < 48 {
        x = x.wrapping_mul(1103515245).wrapping_add(12345);
        v.push((x >> 16) % 40);
        i += 1;
    }
    v.sort_unstable();
    v.dedup();
    let found = v.binary_search(&7).is_ok() as u64;
    let mut h: u64 = found;
    let mut m = 0usize;
    while m < v.len() {
        h = h.wrapping_mul(31).wrapping_add((v[m].rem_euclid(1_000_003)) as u64);
        m += 1;
    }
    std::process::exit((h % 251) as i32);
}
"#,
        },
    ]
}

// ---------------------------------------------------------------------------
// THE GATE
// ---------------------------------------------------------------------------

