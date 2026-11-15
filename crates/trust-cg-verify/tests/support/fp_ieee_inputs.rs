// Copyright 2026 Andrew Yates | Apache-2.0
//! Input sets shared by the ledger `L04-P3` IEEE 754 differentials: the
//! instruction-level target (`trust-cg-verify/tests/aarch64_fp_ieee_differential.rs`)
//! and the lowering target (`trust-cg-codegen/tests/e2e_aarch64_fp_ieee_lowering.rs`),
//! which includes this file by path. Every set is deterministic; its `name`
//! states what it contains and `exhaustive` whether it is a whole input space.

#![allow(dead_code)]

use std::sync::Arc;

use trust_cg_verify::ieee754_reference::{self as ieee, Format, Rounding};

const RNE: Rounding = Rounding::TiesToEven;

// ===========================================================================
// Inputs
// ===========================================================================

/// Deterministic xorshift64* stream.
pub struct Rng(pub u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed | 1)
    }
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
}

/// A random tail, generated per index (no storage), deterministic in the
/// set's seed.
#[derive(Clone, Copy, Debug)]
pub enum Random {
    /// Uniform encodings of a format.
    Bits(Format),
    /// Integers of `width` bits, stratified by significant length.
    Int(u32),
    /// Pairs, half of them with a nearby exponent (where additions round and
    /// cancel most often).
    PairNear(Format),
    /// Triples, alternately uniform and with `c` within two ulps of
    /// `-(a * b)` (where a fused and an unfused multiply-add differ).
    TripleCancel(Format),
}

/// SplitMix64: the `n`-th value of the stream seeded by `seed`.
fn mix(seed: u64, n: u64) -> u64 {
    let mut z = seed.wrapping_add(n.wrapping_mul(0x9e37_79b9_7f4a_7c15));
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

impl Random {
    fn get(self, seed: u64, index: u64) -> [u64; 3] {
        let r = |k: u64| mix(seed, index.wrapping_mul(8).wrapping_add(k));
        match self {
            Random::Bits(f) => [r(0) & f.mask(), 0, 0],
            Random::Int(width) => {
                let len = (r(0) % u64::from(width)) as u32 + 1;
                let mask = if len == 64 {
                    u64::MAX
                } else {
                    (1u64 << len) - 1
                };
                [r(1) & mask, 0, 0]
            }
            Random::PairNear(f) => {
                let a = r(0) & f.mask();
                let b = if r(1) & 1 == 0 {
                    r(2) & f.mask()
                } else {
                    let spread = 1u64 << (f.frac_bits() + 3);
                    a ^ (r(2) % spread) ^ (r(3) & f.sign_bit())
                };
                [a, b & f.mask(), 0]
            }
            Random::TripleCancel(f) => {
                let (a, b) = (r(0) & f.mask(), r(1) & f.mask());
                if index & 1 == 0 {
                    [a, b, r(2) & f.mask()]
                } else {
                    let product = ieee::mul(f, a, b, RNE).value;
                    let c = (product ^ f.sign_bit())
                        .wrapping_add(r(2) % 5)
                        .wrapping_sub(2)
                        & f.mask();
                    [a, b, c]
                }
            }
        }
    }
}

/// How an input set is generated.
#[derive(Clone)]
pub enum Gen {
    /// `a = index`.
    Index,
    /// `a = index & 0xffff`, `b = index >> 16` (every binary16 pair).
    HalfPairs,
    /// Every binary16 encoding against each edge value in both operand
    /// orders (`edges.len() * 2^17` pairs), then `random` random pairs.
    HalfCross {
        edges: Arc<Vec<u64>>,
        random: Random,
        seed: u64,
    },
    /// An explicit list, then `random` generated entries.
    List {
        list: Arc<Vec<[u64; 3]>>,
        random: Random,
        seed: u64,
    },
}

#[derive(Clone)]
pub struct InputSet {
    pub name: String,
    pub exhaustive: bool,
    pub len: u64,
    pub generator: Gen,
}

impl InputSet {
    pub fn get(&self, index: u64) -> [u64; 3] {
        match &self.generator {
            Gen::Index => [index, 0, 0],
            Gen::HalfPairs => [index & 0xffff, index >> 16, 0],
            Gen::HalfCross {
                edges,
                random,
                seed,
            } => {
                let cross = edges.len() as u64 * (1 << 17);
                if index < cross {
                    let edge = edges[(index >> 17) as usize];
                    let value = index & 0xffff;
                    if index & 0x1_0000 == 0 {
                        [edge, value, 0]
                    } else {
                        [value, edge, 0]
                    }
                } else {
                    random.get(*seed, index - cross)
                }
            }
            Gen::List { list, random, seed } => {
                let n = list.len() as u64;
                if index < n {
                    list[index as usize]
                } else {
                    random.get(*seed, index - n)
                }
            }
        }
    }

    pub fn strength(&self) -> &'static str {
        if self.exhaustive {
            "exhaustive"
        } else {
            "statistical"
        }
    }

    /// `values` followed by `random` generated entries.
    pub fn list(
        name: String,
        values: Vec<[u64; 3]>,
        random: Random,
        count: u64,
        seed: u64,
    ) -> InputSet {
        InputSet {
            name,
            exhaustive: false,
            len: values.len() as u64 + count,
            generator: Gen::List {
                list: Arc::new(values),
                random,
                seed,
            },
        }
    }
}

/// The random sample of a statistical set: `base` in the default (floor)
/// run, 100 times that under the exhaustive switch (run in release).
pub fn sample(base: u64) -> u64 {
    if exhaustive_mode() { base * 100 } else { base }
}

pub fn exhaustive_mode() -> bool {
    std::env::var("TRUST_CG_FP_IEEE_EXHAUSTIVE").is_ok_and(|v| v == "1")
}

/// Boundary significands for format `f`.
pub fn boundary_fracs(f: Format) -> Vec<u64> {
    let m = f.frac_mask();
    let q = f.quiet_bit();
    let mut v = vec![
        0,
        1,
        2,
        3,
        q - 1,
        q,
        q + 1,
        m - 2,
        m - 1,
        m,
        q >> 1,
        q | (q >> 1),
    ];
    let alternating = 0x5555_5555_5555_5555 & m;
    v.extend([alternating, !alternating & m]);
    v.sort_unstable();
    v.dedup();
    v
}

pub fn encode(f: Format, neg: bool, biased: u64, frac: u64) -> u64 {
    f.zero(neg) | (biased << f.frac_bits()) | (frac & f.frac_mask())
}

/// Every exponent field and sign with boundary significands plus `random`
/// random significands each.
pub fn structured_values(f: Format, random: usize, rng: &mut Rng) -> Vec<u64> {
    let mut out = Vec::new();
    let max_biased = (1u64 << f.exp_bits()) - 1;
    for neg in [false, true] {
        for biased in 0..=max_biased {
            for frac in boundary_fracs(f) {
                out.push(encode(f, neg, biased, frac));
            }
            for _ in 0..random {
                out.push(encode(f, neg, biased, rng.next()));
            }
        }
    }
    out
}

/// Encodings within `radius` ulps of each power of two a conversion or a
/// rounding treats specially, both signs.
pub fn boundary_windows(f: Format, radius: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let max_biased = (1i64 << f.exp_bits()) - 2;
    for exp in [
        -1, 0, 1, 7, 8, 10, 11, 15, 16, 23, 24, 31, 32, 52, 53, 63, 64,
    ] {
        let biased = exp + i64::from(f.bias());
        if !(1..=max_biased).contains(&biased) {
            continue;
        }
        for neg in [false, true] {
            let center = encode(f, neg, biased as u64, 0);
            for delta in 0..=radius {
                out.push(center.wrapping_add(delta) & f.mask());
                out.push(center.wrapping_sub(delta) & f.mask());
            }
        }
    }
    out
}

/// A small edge set for pair and triple products.
pub fn edge_values(f: Format) -> Vec<u64> {
    let mut v = Vec::new();
    let max_biased = (1u64 << f.exp_bits()) - 1;
    let one = f.bias() as u64;
    for neg in [false, true] {
        for (biased, frac) in [
            (0, 0),
            (0, 1),
            (0, 2),
            (0, f.frac_mask()),
            (0, f.quiet_bit()),
            (1, 0),
            (1, 1),
            (one - 1, 0),
            (one - 1, f.frac_mask()),
            (one, 0),
            (one, 1),
            (one, f.quiet_bit()),
            (one + 1, 0),
            (one + 1, f.quiet_bit()),
            (one + 1, f.quiet_bit() | 1),
            (max_biased - 1, f.frac_mask() - 1),
            (max_biased - 1, f.frac_mask()),
            (max_biased, 0),
            (max_biased, f.quiet_bit()),
            (max_biased, f.quiet_bit() | 0x5),
            (max_biased, 1),
            (max_biased, 0x3),
        ] {
            v.push(encode(f, neg, biased, frac));
        }
        let step = (max_biased / 16).max(1);
        let mut biased = 2;
        while biased < max_biased - 1 {
            v.push(encode(f, neg, biased, 0x2a5 & f.frac_mask()));
            biased += step;
        }
    }
    v.sort_unstable();
    v.dedup();
    v
}

pub fn single_set(f: Format) -> InputSet {
    if exhaustive_mode() && f == Format::Single {
        return InputSet {
            name: "every binary32 encoding".into(),
            exhaustive: true,
            len: 1 << 32,
            generator: Gen::Index,
        };
    }
    if f == Format::Half {
        return InputSet {
            name: "every binary16 encoding".into(),
            exhaustive: true,
            len: 1 << 16,
            generator: Gen::Index,
        };
    }
    let mut rng = Rng::new(0x5eed_0000 ^ u64::from(f.width()));
    let structured_random = if f == Format::Single { 24 } else { 6 };
    let mut values = structured_values(f, structured_random, &mut rng);
    values.extend(boundary_windows(f, 4096));
    let count = sample(if f == Format::Single {
        600_000
    } else {
        400_000
    });
    InputSet::list(
        format!(
            "{}: every exponent field x boundary/random significands, +-4096-ulp integer-boundary windows, {count} random",
            f.name()
        ),
        values.into_iter().map(|a| [a, 0, 0]).collect(),
        Random::Bits(f),
        count,
        0x5eed_0001 ^ u64::from(f.width()),
    )
}

pub fn int_set(width: u32) -> InputSet {
    if width <= 16 {
        return InputSet {
            name: format!("every {width}-bit integer"),
            exhaustive: true,
            len: 1 << width,
            generator: Gen::Index,
        };
    }
    if exhaustive_mode() && width == 32 {
        return InputSet {
            name: "every 32-bit integer".into(),
            exhaustive: true,
            len: 1 << 32,
            generator: Gen::Index,
        };
    }
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let mut values = Vec::new();
    // Every value of 17 significant bits and both signs (every 16-bit
    // integer, sign- and zero-extended).
    for v in 0..=0x1_ffffu64 {
        values.push(v & mask);
        values.push(v.wrapping_neg() & mask);
    }
    // Powers of two and their neighbours, and the rounding-boundary patterns
    // of every binary format: for a value of L significant bits rounding to
    // p bits, the tie (half the dropped quantum) and its neighbours.
    for k in 0..width {
        for d in 0..=64u64 {
            for v in [(1u64 << k).wrapping_add(d), (1u64 << k).wrapping_sub(d)] {
                values.push(v & mask);
                values.push(v.wrapping_neg() & mask);
            }
        }
    }
    for p in [11u32, 24, 53] {
        for len in (p + 1)..=width {
            let dropped = len - p;
            let top = 1u64 << (len - 1);
            let half = 1u64 << (dropped - 1);
            for body in [0u64, 1, 2, 3, (1u64 << (p - 1)) - 1] {
                let base = top | (body << dropped);
                for v in [
                    base | half,
                    (base | half) - 1,
                    (base | half) + 1,
                    base | (half - 1),
                    base,
                ] {
                    values.push(v & mask);
                    values.push(v.wrapping_neg() & mask);
                }
            }
        }
    }
    let count = sample(600_000);
    InputSet::list(
        format!(
            "i{width}/u{width}: every 17-bit value, powers of two +-64, p=11/24/53 tie patterns, {count} length-stratified random"
        ),
        values.into_iter().map(|a| [a, 0, 0]).collect(),
        Random::Int(width),
        count,
        0x1a7e_0001 ^ u64::from(width),
    )
}

pub fn pair_set(f: Format) -> InputSet {
    if exhaustive_mode() && f == Format::Half {
        return InputSet {
            name: "every binary16 pair".into(),
            exhaustive: true,
            len: 1 << 32,
            generator: Gen::HalfPairs,
        };
    }
    let edges = edge_values(f);
    let count = sample(400_000);
    let seed = 0x9a1e_0001 ^ u64::from(f.width());
    if f == Format::Half {
        let cross = edges.len() as u64 * (1 << 17);
        return InputSet {
            name: format!(
                "f16 pairs: every binary16 encoding against each of {} edge values, both operand orders, {count} random (half exponent-near)",
                edges.len()
            ),
            exhaustive: false,
            len: cross + count,
            generator: Gen::HalfCross {
                edges: Arc::new(edges),
                random: Random::PairNear(f),
                seed,
            },
        };
    }
    let mut values = Vec::new();
    for &a in &edges {
        for &b in &edges {
            values.push([a, b, 0]);
        }
    }
    InputSet::list(
        format!(
            "{} pairs: edge x edge ({} edges), {count} random (half exponent-near)",
            f.name(),
            edges.len()
        ),
        values,
        Random::PairNear(f),
        count,
        seed,
    )
}

pub fn triple_set(f: Format) -> InputSet {
    let edges = edge_values(f);
    let small: Vec<u64> = edges.iter().copied().step_by(2).collect();
    let mut values = Vec::new();
    for &a in &small {
        for &b in &small {
            for &c in &small {
                values.push([a, b, c]);
            }
        }
    }
    let count = sample(600_000);
    InputSet::list(
        format!(
            "{} triples: ({} edges)^3, {count} random of which half have c within two ulps of -(a*b)",
            f.name(),
            small.len()
        ),
        values,
        Random::TripleCancel(f),
        count,
        0x7a1e_0001 ^ u64::from(f.width()),
    )
}

pub fn threads() -> usize {
    let available = std::thread::available_parallelism().map_or(4, usize::from);
    let default = if exhaustive_mode() { 12 } else { 4 };
    std::env::var("TRUST_CG_FP_IEEE_THREADS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
        .clamp(1, available)
}
