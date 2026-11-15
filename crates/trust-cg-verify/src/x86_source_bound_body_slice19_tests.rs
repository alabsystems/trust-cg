// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 19: the full canonical spelling (OD-195): after slice 18's
//! spelling, every value-numbered single-query theorem, every one-path
//! theorem `(= S M)` and every part is spelled again by
//! `x86_source_bound_body/normal.rs`, with slice 18's whole "v18"
//! normalizer, the ten slice-19 identity groups and `peel`.
//!
//! The spelling is trusted code. These tests check each identity group
//! exhaustively at small widths against this crate's exact SMT-LIB
//! evaluator (`slice18::exact_eval`), sweep the normalizer over random terms
//! and the whole pipeline over random definition lists, sweep every fixture
//! and wrong-lowering theorem and every part against its plain or slice-18
//! spelling, and keep the goldens' historical custody (slice 18's spelling
//! re-renders every golden before slice 19 byte for byte).

use super::slice18::{
    Built, PLAIN, Val, built, bv, definitions_of, evaluate_theorem, every_fixture,
    every_refutation, exact_eval, fit, golden_files, part_definitions, part_free, render, sample,
    sweep,
};
use super::slice22::fixture_owner;
use super::*;
use normal::Groups;

/// Slice 18's spelling (the canonical cascade without slice 19's step).
pub(crate) const SLICE18: PathEncoding = PathEncoding {
    normal: Groups::NONE,
    ..PathEncoding::CANONICAL
};

/// Slice 18's "v18" groups (OD-195's first part).
const V18: Groups = Groups::EXT
    .with(Groups::FOLD)
    .with(Groups::BOOL)
    .with(Groups::BIT1)
    .with(Groups::OVF)
    .with(Groups::SUBZ)
    .with(Groups::ARITH);

// ---------------------------------------------------------------------------
// Each identity group, exhaustively at small widths
// ---------------------------------------------------------------------------

/// Every assignment of `vars` (each at most 6 bits; at most 2^12 in all).
fn every_assignment(vars: &[(&str, u32)]) -> Vec<HashMap<String, u128>> {
    let bits: u32 = vars.iter().map(|(_, width)| width).sum();
    assert!(bits <= 12, "{bits} bits of inputs");
    (0..1u128 << bits)
        .map(|mut packed| {
            vars.iter()
                .map(|(name, width)| {
                    let value = packed & ((1 << width) - 1);
                    packed >>= width;
                    ((*name).to_owned(), value)
                })
                .collect()
        })
        .collect()
}

/// `term` normalized with `groups`, checked against `term` on every
/// assignment of `vars`: the same width and the same value. Returns how many
/// inputs were checked when the normalizer rewrites `term`, `None` when it
/// leaves it as it is.
fn exhaustive(term: &E, vars: &[(&str, u32)], groups: Groups) -> Option<usize> {
    let normal = normal::normalized_term(term, groups)
        .unwrap_or_else(|| panic!("{term} is outside the spelling's vocabulary"));
    if normal == *term {
        return None;
    }
    assert_eq!(
        normal.try_bv_width().ok(),
        term.try_bv_width().ok(),
        "{term} -> {normal} changes the width"
    );
    let inputs = every_assignment(vars);
    for env in &inputs {
        let (mut a, mut b) = (HashMap::new(), HashMap::new());
        assert_eq!(
            exact_eval(term, env, &mut a),
            exact_eval(&normal, env, &mut b),
            "{term} -> {normal} at {env:?}"
        );
    }
    Some(inputs.len())
}

/// A tally of rewritten instances and checked inputs per group.
#[derive(Default)]
struct Tally(std::collections::BTreeMap<&'static str, (usize, usize)>);

impl Tally {
    fn add(&mut self, group: &'static str, checked: Option<usize>) {
        let entry = self.0.entry(group).or_default();
        if let Some(inputs) = checked {
            entry.0 += 1;
            entry.1 += inputs;
        }
    }
}

/// A Boolean condition over a one-bit input `c`.
fn condition() -> E {
    E::var("c", 1).eq_expr(E::bv_const(1, 1))
}

/// Every identity group of OD-195, alone (a slice-19 group over slice 18's
/// "v18" groups, as the measurement checked them), on every shape it
/// rewrites and every value of every input at widths 1 to 5: the normalized
/// term keeps the width and the value. Each group rewrites at least one
/// instance.
#[test]
fn every_identity_group_is_exact_exhaustively() {
    let mut tally = Tally::default();
    // Slice 18's "v18" groups, each alone.
    for w in 1..=4u32 {
        let (x, y) = (E::var("x", w), E::var("y", w));
        let vars: &[(&str, u32)] = &[("x", w), ("y", w)];
        for k in 0..=3u32 {
            let zx = x.clone().zero_ext(k);
            let sx = x.clone().sign_ext(k);
            let wide = w + k;
            for high in 0..wide {
                for low in 0..=high {
                    tally.add(
                        "ext",
                        exhaustive(&sx.clone().extract(high, low), vars, Groups::EXT),
                    );
                    tally.add(
                        "ext",
                        exhaustive(&zx.clone().extract(high, low), vars, Groups::EXT),
                    );
                    let pair = x.clone().concat(y.clone());
                    if high < 2 * w && low <= high {
                        tally.add(
                            "ext",
                            exhaustive(&pair.extract(high, low), vars, Groups::EXT),
                        );
                    }
                }
            }
            for j in 0..=2u32 {
                tally.add(
                    "ext",
                    exhaustive(&zx.clone().zero_ext(j), vars, Groups::EXT),
                );
                tally.add(
                    "ext",
                    exhaustive(&sx.clone().sign_ext(j), vars, Groups::EXT),
                );
                tally.add(
                    "ext",
                    exhaustive(&zx.clone().sign_ext(j), vars, Groups::EXT),
                );
            }
            tally.add(
                "ext",
                exhaustive(
                    &E::bv_const(0, k.max(1)).concat(x.clone()),
                    vars,
                    Groups::EXT,
                ),
            );
        }
        let zero = E::bv_const(0, w);
        let ones = E::bv_const((1u64 << w) - 1, w);
        let one = E::bv_const(1, w);
        for term in [
            x.clone().bvadd(zero.clone()),
            zero.clone().bvadd(x.clone()),
            x.clone().bvor(zero.clone()),
            x.clone().bvxor(x.clone()),
            x.clone().bvor(x.clone()),
            x.clone().bvsub(zero.clone()),
            x.clone().bvsub(x.clone()),
            x.clone().bvand(zero.clone()),
            ones.clone().bvand(x.clone()),
            x.clone().bvand(x.clone()),
            x.clone().bvmul(zero.clone()),
            one.clone().bvmul(x.clone()),
            x.clone().bvshl(zero.clone()),
            x.clone().bvlshr(zero.clone()),
            x.clone().bvashr(zero.clone()),
        ] {
            tally.add("arith", exhaustive(&term, vars, Groups::ARITH));
        }
        for term in [
            x.clone().bvsub(y.clone()).eq_expr(zero.clone()),
            zero.clone().eq_expr(x.clone().bvsub(y.clone())),
            x.clone().bvsub(x.clone()).eq_expr(zero.clone()),
        ] {
            tally.add("subz", exhaustive(&term, vars, Groups::SUBZ));
        }
        let c = condition();
        let cv: &[(&str, u32)] = &[("x", w), ("y", w), ("c", 1)];
        for term in [
            x.clone().eq_expr(x.clone()),
            x.clone().eq_expr(y.clone()).eq_expr(E::bool_const(true)),
            E::bool_const(false).eq_expr(c.clone()),
            E::bool_const(true).not_expr(),
            c.clone().not_expr().not_expr(),
            c.clone().and_expr(E::bool_const(true)),
            E::bool_const(false).and_expr(c.clone()),
            c.clone().and_expr(c.clone()),
            c.clone().or_expr(E::bool_const(false)),
            E::bool_const(true).or_expr(c.clone()),
            c.clone().or_expr(c.clone()),
            E::ite(E::bool_const(true), x.clone(), y.clone()).eq_expr(x.clone()),
            E::ite(c.clone(), x.clone(), x.clone()).eq_expr(y.clone()),
            E::ite(c.clone(), E::bool_const(true), E::bool_const(false)),
        ] {
            tally.add("bool", exhaustive(&term, cv, Groups::BOOL));
        }
        for (t, e) in [(1u64, 0u64), (0, 1)] {
            for constant in [0u64, 1] {
                let bit = E::ite(c.clone(), E::bv_const(t, 1), E::bv_const(e, 1));
                tally.add(
                    "bit1",
                    exhaustive(
                        &bit.clone().eq_expr(E::bv_const(constant, 1)),
                        cv,
                        Groups::BIT1,
                    ),
                );
                tally.add(
                    "bit1",
                    exhaustive(&E::bv_const(constant, 1).eq_expr(bit), cv, Groups::BIT1),
                );
            }
        }
        for a in 0..1u64 << w {
            for b in 0..1u64 << w {
                let (a, b) = (E::bv_const(a, w), E::bv_const(b, w));
                for term in [
                    a.clone().bvadd(b.clone()),
                    a.clone().bvmul(b.clone()),
                    a.clone().bvudiv(b.clone()),
                    a.clone().bvurem(b.clone()),
                    a.clone().bvlshr(b.clone()),
                    a.clone().bvult(b.clone()),
                    a.clone().concat(b.clone()),
                    a.clone().eq_expr(b.clone()),
                ] {
                    tally.add("fold", exhaustive(&term, &[], Groups::FOLD));
                }
            }
        }
        // The widening product's overflow test, on the extract (`ovf`).
        for k in 1..=2u32 {
            let product = x.clone().zero_ext(k).bvmul(y.clone().zero_ext(k));
            for (ext, term) in [
                ("zero", product.clone().extract(w - 1, 0).zero_ext(k)),
                ("sign", product.clone().extract(w - 1, 0).sign_ext(k)),
            ] {
                let test = term.eq_expr(product.clone());
                tally.add(
                    if ext == "zero" {
                        "ovf"
                    } else {
                        "ovf (sign: none)"
                    },
                    exhaustive(&test, vars, Groups::OVF),
                );
            }
        }
    }
    // The slice-19 groups, each alone over the "v18" groups.
    for w in 2..=5u32 {
        let (x, y) = (E::var("x", w), E::var("y", w));
        let vars: &[(&str, u32)] = &[("x", w), ("y", w)];
        for high in 0..w - 1 {
            tally.add(
                "mullo",
                exhaustive(
                    &x.clone().bvmul(y.clone()).extract(high, 0),
                    vars,
                    V18.with(Groups::MULLO),
                ),
            );
            type Build = fn(E, E) -> E;
            let binary: [Build; 5] = [
                |a, b| a.bvadd(b),
                |a, b| a.bvsub(b),
                |a, b| a.bvand(b),
                |a, b| a.bvor(b),
                |a, b| a.bvxor(b),
            ];
            for build in binary {
                tally.add(
                    "addlo",
                    exhaustive(
                        &build(x.clone(), y.clone()).extract(high, 0),
                        vars,
                        V18.with(Groups::ADDLO),
                    ),
                );
            }
            tally.add(
                "addlo",
                exhaustive(
                    &x.clone().bvneg().extract(high, 0),
                    vars,
                    V18.with(Groups::ADDLO),
                ),
            );
        }
        for amount in 0..=w {
            let k = E::bv_const(u64::from(amount), w);
            let shr = V18.with(Groups::SHR);
            tally.add("shr", exhaustive(&x.clone().bvlshr(k.clone()), vars, shr));
            tally.add("shr", exhaustive(&x.clone().bvshl(k), vars, shr));
        }
        for constant in 2..1u64 << w {
            let k = E::bv_const(constant, w);
            let pow2 = V18.with(Groups::MULPOW2);
            tally.add(
                "mulpow2",
                exhaustive(&x.clone().bvmul(k.clone()), vars, pow2),
            );
            tally.add("mulpow2", exhaustive(&k.bvmul(x.clone()), vars, pow2));
        }
        let cmp = V18.with(Groups::CMP);
        type Relation = fn(E, E) -> E;
        let relations: [Relation; 6] = [
            |a, b| a.bvuge(b),
            |a, b| a.bvugt(b),
            |a, b| a.bvule(b),
            |a, b| a.bvsge(b),
            |a, b| a.bvsgt(b),
            |a, b| a.bvsle(b),
        ];
        for relation in relations {
            tally.add(
                "cmp",
                exhaustive(&relation(x.clone(), y.clone()), vars, cmp),
            );
        }
        let lt = x.clone().bvult(y.clone());
        for term in [
            lt.clone().or_expr(x.clone().eq_expr(y.clone())),
            y.clone().eq_expr(x.clone()).or_expr(lt.clone()),
            lt.clone().or_expr(y.clone().eq_expr(y.clone())),
        ] {
            tally.add("cmp", exhaustive(&term, vars, cmp));
        }
    }
    // `ovf2` / `sovf`: a widened product against an extension of its low
    // bits spelled as the narrow product (`ovf2`, `sovf`) or as the extract
    // (`sovf`'s second form).
    for n in 1..=3u32 {
        for k in 1..=3u32 {
            let (a, b) = (E::var("a", n), E::var("b", n));
            let vars: &[(&str, u32)] = &[("a", n), ("b", n)];
            for signed in [false, true] {
                let extend = |t: E| if signed { t.sign_ext(k) } else { t.zero_ext(k) };
                let product = extend(a.clone()).bvmul(extend(b.clone()));
                for low in [
                    a.clone().bvmul(b.clone()),
                    product.clone().extract(n - 1, 0),
                ] {
                    for (group, test) in [
                        ("ovf2", low.clone().zero_ext(k)),
                        ("sovf", low.clone().sign_ext(k)),
                    ] {
                        let groups = V18.with(if group == "ovf2" {
                            Groups::OVF2.with(Groups::MULLO)
                        } else {
                            Groups::SOVF.with(Groups::MULLO)
                        });
                        tally.add(
                            group,
                            exhaustive(&test.eq_expr(product.clone()), vars, groups),
                        );
                    }
                }
            }
            let (p, q) = (E::var("p", n + k), E::var("q", n + k));
            let pq: &[(&str, u32)] = &[("p", n + k), ("q", n + k)];
            let product = p.clone().bvmul(q.clone());
            for low in [
                p.clone()
                    .extract(n - 1, 0)
                    .bvmul(q.clone().extract(n - 1, 0)),
                product.clone().extract(n - 1, 0),
            ] {
                for (group, test) in [
                    ("ovf2", low.clone().zero_ext(k)),
                    ("sovf", low.clone().sign_ext(k)),
                ] {
                    let groups = V18.with(if group == "ovf2" {
                        Groups::OVF2.with(Groups::MULLO)
                    } else {
                        Groups::SOVF.with(Groups::MULLO)
                    });
                    if (n + k) * 2 <= 12 {
                        tally.add(
                            group,
                            exhaustive(&test.eq_expr(product.clone()), pq, groups),
                        );
                    }
                }
            }
        }
    }
    // `itepull`: `ite` of two equal extensions or extracts.
    for w in 1..=4u32 {
        let (a, b) = (E::var("a", w), E::var("b", w));
        let vars: &[(&str, u32)] = &[("a", w), ("b", w), ("c", 1)];
        let pull = V18.with(Groups::ITEPULL);
        for k in 1..=3u32 {
            for signed in [false, true] {
                let extend = |t: E| if signed { t.sign_ext(k) } else { t.zero_ext(k) };
                let term = E::ite(condition(), extend(a.clone()), extend(b.clone()));
                tally.add("itepull", exhaustive(&term, vars, pull));
            }
        }
        for high in 0..w {
            for low in 0..=high {
                let term = E::ite(
                    condition(),
                    a.clone().extract(high, low),
                    b.clone().extract(high, low),
                );
                tally.add("itepull", exhaustive(&term, vars, pull));
            }
        }
        // Different extensions are not pulled.
        let mixed = E::ite(condition(), a.clone().zero_ext(1), b.clone().sign_ext(1));
        assert_eq!(exhaustive(&mixed, vars, pull), None, "{mixed}");
    }
    // `look` and `peel`: the low bits of a kept name defined as an
    // extension of `t`.
    for w in 1..=4u32 {
        let t = E::var("t", w).bvadd(E::var("u", w));
        for k in 1..=4u32 {
            for signed in [false, true] {
                let rhs = if signed {
                    t.clone().sign_ext(k)
                } else {
                    t.clone().zero_ext(k)
                };
                let low = E::var("v", w + k).extract(w - 1, 0);
                let definitions = vec![("v".to_owned(), rhs.clone())];
                let without = normal::looked_through(&low, &definitions, V18.with(Groups::LOOK))
                    .expect("in the vocabulary");
                assert_eq!(without, low, "`look` alone keeps {low} (no variable left)");
                let peeled = normal::looked_through(
                    &low,
                    &definitions,
                    V18.with(Groups::LOOK).with(Groups::PEEL),
                )
                .expect("in the vocabulary");
                assert_eq!(peeled, t, "`peel` gives {t}");
                let mut checked = 0;
                for env in every_assignment(&[("t", w), ("u", w)]) {
                    let mut env = env;
                    let v = bv(&rhs, &env, &mut HashMap::new());
                    env.insert("v".to_owned(), v);
                    let (mut a, mut b) = (HashMap::new(), HashMap::new());
                    assert_eq!(
                        exact_eval(&low, &env, &mut a),
                        exact_eval(&peeled, &env, &mut b)
                    );
                    checked += 1;
                }
                tally.add("peel", Some(checked));
                // Any other window is no `peel`.
                if w > 1 {
                    let higher = E::var("v", w + k).extract(w - 1, 1);
                    let kept = normal::looked_through(
                        &higher,
                        &definitions,
                        V18.with(Groups::LOOK).with(Groups::PEEL),
                    )
                    .expect("in the vocabulary");
                    assert_ne!(kept, t.clone().extract(w - 1, 1).zero_ext(0));
                }
            }
        }
    }
    for (group, (instances, inputs)) in &tally.0 {
        eprintln!("SLICE19_EXHAUSTIVE {group}: {instances} rewritten instances, {inputs} inputs");
    }
    for group in [
        "ext", "arith", "subz", "bool", "bit1", "fold", "ovf", "mullo", "addlo", "shr", "mulpow2",
        "cmp", "ovf2", "sovf", "itepull", "peel",
    ] {
        assert!(
            tally
                .0
                .get(group)
                .is_some_and(|(instances, _)| *instances > 0),
            "{group} rewrites no instance"
        );
    }
}

/// The rules that must NOT apply do not: a shift by zero or by the width or
/// more is no `shr`; a product by 1, 0 or a non-power of two is no
/// `mulpow2`; the full width of a product is no `mullo`; a sign test whose
/// all-ones constant needs more than 64 bits is left as it is (a constant
/// field holds 64); `bvult` and `bvslt` stay as they are under `cmp`.
#[test]
fn the_identity_groups_leave_what_they_do_not_rewrite() {
    let all = Groups::IDENTITIES;
    let x = E::var("x", 8);
    let y = E::var("y", 8);
    for term in [
        x.clone().bvlshr(E::bv_const(8, 8)),
        x.clone().bvshl(E::bv_const(9, 8)),
        x.clone().bvmul(E::bv_const(3, 8)),
        x.clone().bvmul(y.clone()).extract(7, 0),
        x.clone().bvult(y.clone()),
        x.clone().bvslt(y.clone()),
    ] {
        let normal = normal::normalized_term(&term, all).expect("in the vocabulary");
        let normal = match (&term, &normal) {
            // A full-width extract is its operand (OD-183), nothing more.
            (E::Extract { operand, .. }, _) => {
                assert_eq!(normal, *operand.as_ref(), "{term}");
                continue;
            }
            _ => normal,
        };
        assert_eq!(normal, term, "{term} is rewritten");
    }
    // A 64x64 signed product's sign test (65 top bits): left unrewritten.
    let (a, b) = (E::var("a", 64), E::var("b", 64));
    let product = a.clone().sign_ext(64).bvmul(b.clone().sign_ext(64));
    let test = a
        .clone()
        .bvmul(b.clone())
        .sign_ext(64)
        .eq_expr(product.clone());
    let normal = normal::normalized_term(&test, all).expect("in the vocabulary");
    assert!(
        matches!(&normal, E::Eq { .. }),
        "the 65-bit sign test is not rewritten: {normal}"
    );
    // A 32x32 one (33 top bits) is.
    let (a, b) = (E::var("a", 32), E::var("b", 32));
    let product = a.clone().sign_ext(32).bvmul(b.clone().sign_ext(32));
    let test = a.clone().bvmul(b.clone()).sign_ext(32).eq_expr(product);
    let normal = normal::normalized_term(&test, all).expect("in the vocabulary");
    assert!(
        matches!(&normal, E::Or { .. }),
        "the 33-bit sign test is rewritten: {normal}"
    );
}

// ---------------------------------------------------------------------------
// Random terms and random definitions, against evaluation
// ---------------------------------------------------------------------------

/// A seeded generator of the terms the canonical spelling rewrites.
struct Random(u64);

impl Random {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn constant(&mut self, width: u32) -> E {
        let value = match self.below(6) {
            0 => 0,
            1 => 1,
            2 => u64::MAX,
            3 => 1u64 << self.below(u64::from(width.min(64))),
            4 => self.below(u64::from(width) + 1),
            _ => self.next(),
        };
        E::bv_const(value, width.min(64)).zero_ext(width.saturating_sub(64))
    }

    fn leaf(&mut self, width: u32, vars: &[(String, u32)]) -> E {
        let fitting: Vec<&(String, u32)> = vars.iter().filter(|(_, w)| *w >= width).collect();
        if fitting.is_empty() || self.below(4) == 0 {
            return self.constant(width);
        }
        let (name, var_width) = fitting[self.below(fitting.len() as u64) as usize];
        let var = E::var(name.clone(), *var_width);
        if *var_width == width {
            return var;
        }
        let low = self.below(u64::from(var_width - width + 1)) as u32;
        var.extract(low + width - 1, low)
    }

    fn boolean(&mut self, depth: u32, vars: &[(String, u32)]) -> E {
        let width = [1u32, 8, 16, 32, 64][self.below(5) as usize];
        let a = self.term(width, depth, vars);
        let b = if self.below(3) == 0 {
            a.clone()
        } else {
            self.term(width, depth, vars)
        };
        match self.below(12) {
            0 => a.eq_expr(b),
            1 => a.bvult(b),
            2 => a.bvule(b),
            3 => a.bvugt(b),
            4 => a.bvuge(b),
            5 => a.bvslt(b),
            6 => a.bvsle(b),
            7 => a.bvsgt(b),
            8 => a.bvsge(b),
            9 => a.clone().bvult(b.clone()).or_expr(a.eq_expr(b)),
            10 => a.bvsub(b).eq_expr(E::bv_const(0, width)),
            _ => {
                let bit = E::ite(a.eq_expr(b), E::bv_const(1, 1), E::bv_const(0, 1));
                bit.eq_expr(E::bv_const(self.below(2), 1))
            }
        }
    }

    /// A random `width`-bit term (`width` 1 to 128) over `vars`.
    fn term(&mut self, width: u32, depth: u32, vars: &[(String, u32)]) -> E {
        if depth == 0 || self.below(6) == 0 {
            return self.leaf(width, vars);
        }
        let d = depth - 1;
        let narrower = |r: &mut Self| 1 + r.below(u64::from(width.max(2) - 1)) as u32;
        match self.below(16) {
            0 if width < 128 => {
                let wider = width + 1 + self.below(u64::from((128 - width).min(64))) as u32;
                let low = self.below(u64::from(wider - width + 1)) as u32;
                self.term(wider, d, vars).extract(low + width - 1, low)
            }
            1 if width > 1 => {
                let inner = narrower(self);
                let operand = self.term(inner, d, vars);
                if self.below(2) == 0 {
                    operand.zero_ext(width - inner)
                } else {
                    operand.sign_ext(width - inner)
                }
            }
            2 if width > 1 => {
                let high = narrower(self);
                let hi = self.term(high, d, vars);
                let lo = self.term(width - high, d, vars);
                hi.concat(lo)
            }
            3 => {
                let a = self.term(width, d, vars);
                let b = self.term(width, d, vars);
                [E::bvadd, E::bvsub, E::bvand, E::bvor, E::bvxor][self.below(5) as usize](a, b)
            }
            4 => self.term(width, d, vars).bvneg(),
            5 => {
                let a = self.term(width, d, vars);
                let b = if self.below(2) == 0 {
                    self.constant(width)
                } else {
                    self.term(width, d, vars)
                };
                a.bvmul(b)
            }
            6 => {
                let a = self.term(width, d, vars);
                let k = self.constant(width);
                [E::bvlshr, E::bvshl, E::bvashr][self.below(3) as usize](a, k)
            }
            7 => {
                let condition = self.boolean(d, vars);
                let (t, e) = if width > 1 && self.below(2) == 0 {
                    // Two equal extensions or extracts (`itepull`).
                    let inner = narrower(self);
                    let (a, b) = (self.term(inner, d, vars), self.term(inner, d, vars));
                    if self.below(2) == 0 {
                        (a.zero_ext(width - inner), b.zero_ext(width - inner))
                    } else {
                        (a.sign_ext(width - inner), b.sign_ext(width - inner))
                    }
                } else {
                    (self.term(width, d, vars), self.term(width, d, vars))
                };
                E::ite(condition, t, e)
            }
            8 if (2..=64).contains(&width) => {
                // A low-bits extract of a wider computation (`mullo`,
                // `addlo`).
                let wider = (width * 2).min(128);
                let a = self.term(wider, d, vars);
                let b = self.term(wider, d, vars);
                let op = [E::bvmul, E::bvadd, E::bvsub, E::bvand][self.below(4) as usize];
                op(a, b).extract(width - 1, 0)
            }
            9 => {
                let a = self.term(width, d, vars);
                let b = self.term(width, d, vars);
                [E::bvudiv, E::bvurem][self.below(2) as usize](a, b)
            }
            _ => self.term(width, d, vars),
        }
    }
}

/// Seeded inputs for `vars`.
fn inputs(random: &mut Random, vars: &[(String, u32)], count: usize) -> Vec<HashMap<String, u128>> {
    (0..count)
        .map(|_| {
            vars.iter()
                .map(|(name, width)| {
                    let value = match random.below(6) {
                        0 => 0,
                        1 => u128::MAX,
                        2 => 1,
                        3 => 1u128 << random.below(u64::from(*width)),
                        _ => (u128::from(random.next()) << 64) | u128::from(random.next()),
                    };
                    (name.clone(), fit(value, *width))
                })
                .collect()
        })
        .collect()
}

/// The normalizer with every identity group is exact on random terms: on
/// 4000 seeded terms of widths 1 to 128 over three variables (and 2000
/// Boolean ones), the normalized term has the width and, on 32 seeded inputs,
/// the value of the original; a share of them are rewritten.
#[test]
fn the_full_normalizer_is_exact_on_random_terms() {
    let vars = vec![
        ("x".to_owned(), 64),
        ("y".to_owned(), 64),
        ("z".to_owned(), 8),
    ];
    let mut random = Random(0x510e_527f_ade6_82d1);
    let mut rewritten = 0;
    let mut failures = Vec::new();
    for round in 0..6000u32 {
        let term = if round % 3 == 2 {
            random.boolean(3, &vars)
        } else {
            let width = [1, 7, 8, 16, 31, 32, 56, 64, 65, 96, 128][(round % 11) as usize];
            random.term(width, 4, &vars)
        };
        let Some(normal) = normal::normalized_term(&term, Groups::CANONICAL) else {
            failures.push(format!("{term} is outside the vocabulary"));
            continue;
        };
        if normal != term {
            rewritten += 1;
        }
        if normal.try_bv_width().ok() != term.try_bv_width().ok() {
            failures.push(format!("{term} -> {normal} changes the width"));
            continue;
        }
        for env in inputs(&mut random, &vars, 32) {
            let (mut a, mut b) = (HashMap::new(), HashMap::new());
            if exact_eval(&term, &env, &mut a) != exact_eval(&normal, &env, &mut b) {
                failures.push(format!("{term} -> {normal} differ at {env:?}"));
                break;
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(rewritten >= 2000, "{rewritten} terms rewritten");
}

/// The values of `definitions` (in order) and of `claims` on `env`.
fn evaluate(
    definitions: &[(String, E)],
    claims: &E,
    env: &HashMap<String, u128>,
) -> (bool, HashMap<String, u128>) {
    let mut values = env.clone();
    let mut memo = HashMap::new();
    for (name, expr) in definitions {
        let value = bv(expr, &values, &mut memo);
        values.insert(name.clone(), value);
    }
    let holds = match exact_eval(claims, &values, &mut memo) {
        Val::Bool(holds) => holds,
        Val::Bv(_) => panic!("{claims} is not Boolean"),
    };
    (holds, values)
}

/// The whole pipeline (`normal::spelled`) is exact on random theorems:
/// random definition lists over three variables and the earlier names
/// (renamings, repeated right-hand sides, extensions read back through their
/// low bits, products and their low bits, extracts of names) and random
/// claims (equations, Boolean literals and guarded items), spelled with every
/// identity group, keep the claims' value and every kept definition's value
/// on 32 seeded inputs; every kept name is an original name, every free
/// input an original one; an emptied theorem holds on every sample.
#[test]
fn the_full_spelling_is_exact_on_random_theorems() {
    let vars = vec![
        ("x".to_owned(), 64),
        ("y".to_owned(), 64),
        ("z".to_owned(), 8),
    ];
    let mut random = Random(0x9b05_688c_2b3e_6c1f);
    let (mut spelled, mut emptied) = (0, 0);
    let mut failures = Vec::new();
    for round in 0..800u32 {
        let mut scope = vars.clone();
        let mut definitions: Vec<(String, E)> = Vec::new();
        for k in 0..(4 + round % 9) {
            let width = [8u32, 16, 32, 64, 128][random.below(5) as usize];
            let expr = match random.below(7) {
                0 if !definitions.is_empty() => {
                    let (name, earlier) =
                        definitions[random.below(definitions.len() as u64) as usize].clone();
                    if random.below(2) == 0 {
                        E::var(name, earlier.bv_width())
                    } else {
                        earlier
                    }
                }
                1 if !definitions.is_empty() => {
                    // An extension of an earlier name, or of a term.
                    let (name, earlier) =
                        definitions[random.below(definitions.len() as u64) as usize].clone();
                    let inner = E::var(name, earlier.bv_width());
                    let w = inner.bv_width();
                    if w < 128 {
                        inner.zero_ext(128 - w)
                    } else {
                        random.term(width, 3, &scope)
                    }
                }
                2 if !definitions.is_empty() => {
                    // The low bits of an earlier name.
                    let (name, earlier) =
                        definitions[random.below(definitions.len() as u64) as usize].clone();
                    let w = earlier.bv_width();
                    let high = random.below(u64::from(w)) as u32;
                    E::var(name, w).extract(high, 0)
                }
                _ => random.term(width, 3, &scope),
            };
            let name = format!("d{k}");
            scope.push((name.clone(), expr.bv_width()));
            definitions.push((name, expr));
        }
        let mut items: Vec<E> = Vec::new();
        for _ in 0..1 + random.below(4) {
            let (name, width) = scope[random.below(scope.len() as u64) as usize].clone();
            let other = random.term(width, 2, &scope);
            let equation = E::var(name, width).eq_expr(other);
            items.push(match random.below(4) {
                0 => random.boolean(2, &scope).not_expr().or_expr(equation),
                1 => random.boolean(2, &scope),
                _ => equation,
            });
        }
        let claims = items
            .into_iter()
            .rev()
            .reduce(|tail, item| item.and_expr(tail))
            .expect("a claim");
        let samples = inputs(&mut random, &vars, 32);
        match normal::spelled(&definitions, &claims, Groups::CANONICAL) {
            normal::Normal::Declined => failures.push(format!("round {round} declined")),
            normal::Normal::Emptied => {
                emptied += 1;
                for env in &samples {
                    if !evaluate(&definitions, &claims, env).0 {
                        failures.push(format!("round {round} empties, yet fails at {env:?}"));
                        break;
                    }
                }
            }
            normal::Normal::Spelled((kept, rewritten)) => {
                spelled += 1;
                let names: HashSet<&str> =
                    definitions.iter().map(|(name, _)| name.as_str()).collect();
                if let Some((name, _)) =
                    kept.iter().find(|(name, _)| !names.contains(name.as_str()))
                {
                    failures.push(format!("round {round} keeps the new name {name}"));
                }
                let declared: HashSet<String> =
                    scope.iter().map(|(name, _)| name.clone()).collect();
                for name in kept
                    .iter()
                    .flat_map(|(_, expr)| expr.free_vars())
                    .chain(rewritten.free_vars())
                {
                    if !declared.contains(&name) {
                        failures.push(format!("round {round} reads the new input {name}"));
                    }
                }
                for env in &samples {
                    let (holds, values) = evaluate(&definitions, &claims, env);
                    let (spelled_holds, spelled_values) = evaluate(&kept, &rewritten, env);
                    if holds != spelled_holds
                        || kept
                            .iter()
                            .any(|(name, _)| values[name] != spelled_values[name])
                    {
                        failures.push(format!("round {round} changes a value at {env:?}"));
                        break;
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(
        spelled >= 600,
        "{spelled} theorems spelled, {emptied} emptied"
    );
}

/// `cse`, `look`, value numbering and inlining on a small theorem the
/// measurement's census queries show: the source's quotient `s := (bvudiv x
/// k)` and the machine's `m := (bvudiv x k)` behind a renaming, a sum read
/// through the low bits of its zero extension, a product spelled again
/// inside a later definition. Every claim becomes an identity: the theorem
/// empties.
#[test]
fn the_definition_steps_merge_one_value_behind_two_names() {
    let x = E::var("x", 64);
    let y = E::var("y", 64);
    let definitions = vec![
        ("s0".to_owned(), x.clone().bvadd(y.clone())),
        ("m1".to_owned(), x.clone().bvadd(y.clone()).zero_ext(64)),
        ("s2".to_owned(), E::var("s0", 64).bvmul(E::bv_const(10, 64))),
        (
            "m3".to_owned(),
            E::var("m1", 128).extract(63, 0).bvmul(E::bv_const(10, 64)),
        ),
    ];
    let claims = E::var("s2", 64)
        .eq_expr(E::var("m3", 64))
        .and_expr(E::var("s0", 64).eq_expr(E::var("m1", 128).extract(63, 0)));
    assert_eq!(
        normal::spelled(&definitions, &claims, Groups::CANONICAL),
        normal::Normal::Emptied,
        "every claim is an identity under the definitions"
    );
    // Without `look`/`peel` the low bits of `m1` stay a name.
    assert!(matches!(
        normal::spelled(
            &definitions,
            &claims,
            Groups::CANONICAL.without(Groups::LOOK.with(Groups::PEEL))
        ),
        normal::Normal::Emptied | normal::Normal::Spelled(_)
    ));
}

/// The one measured departure from the design's pipeline: a name defined as
/// bits of a term wider than 64 bits that holds no product is kept even when
/// used once. The shape
/// is `SubU128` (`i128::wrapping_sub`): the low half's claim is an identity
/// under the definitions, and the only claim left is the high half of the
/// 128-bit difference, which AY 13556 certifies named and not inlined. The
/// same theorem over a 64-bit difference inlines its name, and so does the
/// high half of a 128-bit product.
#[test]
fn a_single_use_name_for_bits_of_a_wide_term_is_kept() {
    let (a_lo, a_hi) = (E::var("e_rdi", 64), E::var("e_rsi", 64));
    let (b_lo, b_hi) = (E::var("e_rdx", 64), E::var("e_rcx", 64));
    let wide = a_hi
        .clone()
        .concat(a_lo.clone())
        .bvsub(b_hi.clone().concat(b_lo.clone()));
    let borrow = E::ite(
        a_lo.clone().bvult(b_lo.clone()),
        E::bv_const(1, 64),
        E::bv_const(0, 64),
    );
    let high = a_hi.clone().bvsub(b_hi.clone().bvadd(borrow));
    let definitions = vec![
        ("s0".to_owned(), wide.clone().extract(63, 0)),
        ("s1".to_owned(), wide.clone().extract(127, 64)),
    ];
    let pair = E::var("s1", 64).concat(E::var("s0", 64));
    let claims = pair
        .clone()
        .extract(63, 0)
        .eq_expr(a_lo.clone().bvsub(b_lo.clone()))
        .and_expr(pair.extract(127, 64).eq_expr(high.clone()));
    assert_eq!(
        normal::spelled(&definitions, &claims, Groups::CANONICAL),
        normal::Normal::Spelled((
            vec![("s1".to_owned(), wide.extract(127, 64))],
            E::var("s1", 64).eq_expr(high.clone())
        )),
        "the high half stays a name"
    );
    let narrow = a_lo.clone().bvsub(b_lo.clone());
    let definitions = vec![("s1".to_owned(), narrow.clone().extract(63, 32))];
    let claims = E::var("s1", 32).eq_expr(a_hi.extract(31, 0));
    assert_eq!(
        normal::spelled(&definitions, &claims, Groups::CANONICAL),
        normal::Normal::Spelled((
            Vec::new(),
            narrow
                .extract(63, 32)
                .eq_expr(E::var("e_rsi", 64).extract(31, 0))
        )),
        "bits of a 64-bit term are inlined"
    );
    // The high half of a 128-bit product is inlined too, as the design
    // does: kept, it would keep the product in the query (`magic` reads the
    // multiply-high it computes through the name either way).
    let product = E::var("e_rdi", 64)
        .zero_ext(64)
        .bvmul(E::var("e_rsi", 64).zero_ext(64));
    let definitions = vec![("s1".to_owned(), product.extract(127, 64))];
    let claims = E::var("s1", 64).eq_expr(E::var("e_rdx", 64));
    assert!(
        matches!(
            normal::spelled(&definitions, &claims, Groups::CANONICAL),
            normal::Normal::Spelled((kept, _)) if kept.is_empty()
        ),
        "the high half of a product is inlined"
    );
}

// ---------------------------------------------------------------------------
// Every fixture and every wrong lowering
// ---------------------------------------------------------------------------

/// THE sweep of OD-195: every fixture's and every wrong lowering's
/// single-query theorem in the canonical spelling against the plain
/// spelling of the same pair ([`sweep`]: equal claim values and equal kept
/// definitions on every sampled input); every theorem the canonical spelling
/// spells (conjunctive and one-path) passes the owner's structural check; a
/// wrong lowering falsified on a sample stays falsified there.
#[test]
fn the_full_spelling_preserves_every_fixture_theorem() {
    let mut failures: Vec<String> = Vec::new();
    let mut counts: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
    let mut cases: Vec<(String, Function, X86ISelFunction, bool)> = every_fixture()
        .into_iter()
        .map(|(label, source, machine)| (label, source, machine, false))
        .collect();
    let fixtures = cases.len();
    cases.extend(every_refutation());
    for (k, (label, source, machine, unbounded)) in cases.iter().enumerate() {
        let wrong = k >= fixtures;
        let Some(plain) = built(source, machine, PLAIN, *unbounded) else {
            continue;
        };
        let Some(spelled) = built(source, machine, PathEncoding::CANONICAL, *unbounded) else {
            failures.push(format!("{label}: the canonical spelling refuses"));
            continue;
        };
        let Some(slice18) = built(source, machine, SLICE18, *unbounded) else {
            failures.push(format!("{label}: slice 18's spelling refuses"));
            continue;
        };
        if spelled.2 != Spelling::Normal {
            *counts.entry("not re-spelled").or_default() += 1;
            if spelled.0 != slice18.0 {
                failures.push(format!(
                    "{label}: not re-spelled, yet not slice 18's theorem"
                ));
            }
            continue;
        }
        let one_path = spelled.0.trust_ir_expr != E::bool_const(true);
        let checked = if one_path {
            check_definitional(&spelled.0, &spelled.1)
        } else {
            check_definitional_part(&spelled.0, &spelled.1)
        };
        if let Err(why) = checked {
            failures.push(format!("{label}: {why}"));
        }
        match sweep(&format!("{label} (slice 19)"), &plain, &spelled) {
            Ok(falsified) => {
                *counts
                    .entry(match (wrong, one_path) {
                        (false, false) => "conjunctive swept",
                        (false, true) => "one-path swept",
                        (true, false) => "wrong conjunctive swept",
                        (true, true) => "wrong one-path swept",
                    })
                    .or_default() += 1;
                if falsified > 0 {
                    *counts.entry("falsified on a sample").or_default() += 1;
                }
                if spelled.0 != slice18.0 {
                    *counts.entry("changed against slice 18").or_default() += 1;
                }
            }
            Err(why) => failures.push(why),
        }
    }
    eprintln!("SLICE19_SWEEP {counts:?}");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    for (key, floor) in [
        ("conjunctive swept", 150),
        // Slice 23 (OD-205): `Mul/commuted`'s machine product is spelled as
        // the source's, so its one claim empties and it keeps slice 18's
        // spelling (40 before).
        ("one-path swept", 39),
        ("wrong conjunctive swept", 150),
        ("wrong one-path swept", 50),
        ("changed against slice 18", 300),
    ] {
        assert!(
            counts.get(key).copied().unwrap_or(0) >= floor,
            "{key} below {floor}: {counts:?}"
        );
    }
}

/// THE parts sweep of OD-195: every earlier fixture cut at every block
/// start and every slice-16 size shape, stated in parts in slice 18's
/// spelling and canonically: the canonical parts are exactly slice 18's
/// parts each spelled by `normal::spelled` (kept where that fails the part
/// check or declines, dropped where it empties), in order, unless every part
/// empties; each spelled part keeps the slice-18 part's claim value and
/// every definition it keeps on every sampled input, and an emptied one
/// holds on every sample; every inventory checks.
#[test]
fn every_part_spelled_canonically_is_its_slice_eighteen_part() {
    type PartCase = (
        String,
        Function,
        X86ISelFunction,
        Option<Vec<(Block, usize)>>,
    );
    let mut cases: Vec<PartCase> = Vec::new();
    for (label, source, machine) in super::slice16::earlier_fixtures() {
        let points = super::slice16::every_block(&source);
        cases.push((label, source, machine, Some(points)));
    }
    for shape in super::slice16::SLICE_SIXTEEN {
        let (source, machine) = super::slice16::slice16_pair(shape);
        cases.push((format!("s16 {shape:?}"), source, machine, None));
    }
    let mut failures: Vec<String> = Vec::new();
    let (mut parts, mut spelled_parts, mut emptied, mut changed) = (0usize, 0usize, 0usize, 0usize);
    for (label, source, machine, points) in &cases {
        let build = || match points {
            Some(points) => super::slice16::in_parts(source, machine, points.clone()),
            None => fixture_owner(source, machine),
        };
        // Slice 23's pairing (OD-205) is not this custody's question: a
        // spelling without the canonical groups pairs nothing, so the
        // canonical side is built without it too.
        let (Ok(canonical), Ok(slice18)) = (
            with_arithmetic_pairing(false, build),
            with_normal_groups(Groups::NONE, build),
        ) else {
            continue;
        };
        if !canonical.is_stated_in_parts() {
            continue;
        }
        if let Err(why) = canonical.check_parts() {
            failures.push(format!("{label}: the inventory does not check: {why}"));
        }
        let mut expected: Vec<ProofObligation> = Vec::new();
        for (k, part) in slice18.parts().iter().enumerate() {
            parts += 1;
            let definitions = part_definitions(part);
            let free = part_free(part);
            let plain: Built = (part.clone(), free.clone(), Spelling::Plain);
            match normal::spelled(&definitions, &part.aarch64_expr, Groups::CANONICAL) {
                normal::Normal::Emptied => {
                    emptied += 1;
                    let mut state = 0x9abc_def0u64 ^ k as u64;
                    for _ in 0..64 {
                        let inputs: HashMap<String, u128> = free
                            .iter()
                            .map(|(name, width)| (name.clone(), sample(*width, &mut state)))
                            .collect();
                        if !evaluate_theorem(part, &inputs).0 {
                            failures.push(format!(
                                "{label} part {}: its canonical spelling empties, yet it fails a sample",
                                k + 1
                            ));
                            break;
                        }
                    }
                }
                normal::Normal::Declined => expected.push(part.clone()),
                normal::Normal::Spelled((kept, claims)) => {
                    let candidate = split::part_obligation(part, &free, kept, claims);
                    let candidate_free = part_free(&candidate);
                    if check_definitional_part(&candidate, &candidate_free).is_ok() {
                        spelled_parts += 1;
                        let spelled: Built = (candidate.clone(), candidate_free, Spelling::Normal);
                        if let Err(why) =
                            sweep(&format!("{label} part {}", k + 1), &plain, &spelled)
                        {
                            failures.push(why);
                        }
                        expected.push(candidate);
                    } else {
                        expected.push(part.clone());
                    }
                }
            }
        }
        if expected.is_empty() {
            continue;
        }
        let names = |list: &[ProofObligation]| -> Vec<ProofObligation> {
            list.iter()
                .map(|part| ProofObligation {
                    name: String::new(),
                    ..part.clone()
                })
                .collect()
        };
        let unchanged = names(slice18.parts()) == names(canonical.parts());
        changed += usize::from(!unchanged);
        if names(&expected) != names(canonical.parts()) && !unchanged {
            failures.push(format!(
                "{label}: the canonical parts are not slice 18's spelled again ({} expected, {} stated)",
                expected.len(),
                canonical.parts().len()
            ));
        }
    }
    eprintln!(
        "SLICE19_PARTS parts={parts} spelled={spelled_parts} emptied={emptied} \
         functions_changed={changed}"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(spelled_parts >= 200, "{spelled_parts} parts spelled");
    assert!(
        changed >= 50,
        "the spelling changes {changed} functions' parts"
    );
}

// ---------------------------------------------------------------------------
// Historical custody of the goldens
// ---------------------------------------------------------------------------

/// Slice 18's spelling ([`with_normal_groups`] with no group) re-renders
/// every golden file as it was before slice 19, byte for byte (each digest
/// pinned here, as slice 18 pinned slice 17's); the canonical rendering is
/// the committed golden. Prints, per file, how many theorems slice 19
/// changes and how each canonical theorem is spelled.
#[test]
fn the_slice_eighteen_spelling_reproduces_every_golden_before_slice_nineteen() {
    use sha2::{Digest, Sha256};
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/x86_source_bound_body");
    let before: std::collections::BTreeMap<&str, &str> = SLICE18_DIGESTS.iter().copied().collect();
    // Every historical rendering selects as the selector did then, every
    // constant `I128` shift on the general path (OD-215 came later).
    let old = super::with_i128_const_shift_fold(false, || {
        with_normal_groups(Groups::NONE, super::slice16::slice_sixteen_parts_snapshots)
    });
    assert_eq!(
        format!("{:x}", Sha256::digest(old.as_bytes())),
        before["slice16_parts_snapshots.smt2"],
        "slice16_parts_snapshots.smt2: slice 18's spelling no longer renders its parts"
    );
    let canonical = super::slice16::slice_sixteen_parts_snapshots();
    let committed = std::fs::read_to_string(dir.join("slice16_parts_snapshots.smt2")).unwrap();
    assert_eq!(canonical, committed, "slice16_parts_snapshots.smt2 drifted");
    eprintln!(
        "SLICE19_CUSTODY file=slice16_parts_snapshots.smt2 changed={} canonical_sha256={:x}",
        old != canonical,
        Sha256::digest(canonical.as_bytes())
    );
    let old = super::with_i128_const_shift_fold(false, || {
        with_normal_groups(Groups::NONE, super::slice20::slice_twenty_snapshots)
    });
    assert_eq!(
        format!("{:x}", Sha256::digest(old.as_bytes())),
        before["slice20_snapshots.smt2"],
        "slice20_snapshots.smt2: slice 18's spelling no longer renders slice 20's golden"
    );
    let canonical = super::slice20::slice_twenty_snapshots();
    let committed = std::fs::read_to_string(dir.join("slice20_snapshots.smt2")).unwrap();
    assert_eq!(canonical, committed, "slice20_snapshots.smt2 drifted");
    eprintln!(
        "SLICE19_CUSTODY file=slice20_snapshots.smt2 changed={} canonical_sha256={:x}",
        old != canonical,
        Sha256::digest(canonical.as_bytes())
    );
    let old_files = super::with_i128_const_shift_fold(false, golden_files);
    for ((file, _, fixtures), (_, _, old_fixtures)) in golden_files().into_iter().zip(old_files) {
        let old = with_normal_groups(Groups::NONE, || render(&old_fixtures));
        assert_eq!(
            format!("{:x}", Sha256::digest(old.as_bytes())),
            before[file],
            "{file}: slice 18's spelling no longer renders the golden before slice 19"
        );
        let canonical = render(&fixtures);
        let committed = std::fs::read_to_string(dir.join(file)).unwrap();
        assert_eq!(
            canonical, committed,
            "{file}: the canonical rendering drifted"
        );
        let old_sections = super::snapshot_sections(&old);
        let new_sections = super::snapshot_sections(&canonical);
        let changed = old_sections
            .iter()
            .zip(&new_sections)
            .filter(|(a, b)| a != b)
            .count();
        let mut spellings: std::collections::BTreeMap<&str, usize> =
            std::collections::BTreeMap::new();
        for (label, source, machine) in &fixtures {
            let key = match single_theorem_with_encoding(
                source,
                machine,
                SYSV,
                PathEncoding::CANONICAL,
                false,
            ) {
                None => "in parts",
                Some(Err(refusal)) => panic!("{label}: {refusal}"),
                Some(Ok((obligation, _, spelling))) => {
                    let one_path = obligation.trust_ir_expr != E::bool_const(true);
                    match (spelling, one_path) {
                        (Spelling::Normal, false) => "normal",
                        (Spelling::Normal, true) => "normal one-path",
                        (Spelling::Folded, _) => "folded",
                        (Spelling::BitMoves, _) => "bit moves",
                        (Spelling::Numbered, _) => "parts spelling",
                        (Spelling::Plain, false) => "plain conjunctive",
                        (Spelling::Plain, true) => "one path",
                    }
                }
            };
            *spellings.entry(key).or_default() += 1;
        }
        eprintln!(
            "SLICE19_CUSTODY file={file} theorems={} changed={changed} spellings={spellings:?} \
             slice18_sha256={} canonical_sha256={:x}",
            new_sections.len(),
            before[file],
            Sha256::digest(canonical.as_bytes())
        );
    }
}

/// Every golden file's digest in slice 18's spelling (main `fc03f94f2`,
/// before slice 19; slice 20's golden as it landed).
const SLICE18_DIGESTS: &[(&str, &str)] = &[
    (
        "slice16_parts_snapshots.smt2",
        "3be10a8e747e1bb59670457fa5c1116d4b3a7ff8b40d1ccba7140c8f9b18aa59",
    ),
    (
        "slice20_snapshots.smt2",
        "72b649229806c7d1f018eecea0dd232377e51496d83150645783f6759fcb127d",
    ),
    (
        "snapshots.smt2",
        "a4e5c826cdc750a42aa190cc205c92196547c21ad22564c9d7829ad4d82acf7b",
    ),
    (
        "memory_snapshots.smt2",
        "b1b7b2a7e954e234bfb1add9ae507221c0721d5526cbb1295018c205ca8c6af2",
    ),
    (
        "slice5_snapshots.smt2",
        "16e1d2c778037e337aff622bf2f5810ae6c159f29d02bf017381fce632c1f6ef",
    ),
    (
        "slice6_snapshots.smt2",
        "d264c23281c27f4f94e791268df056b889225069f41992ab085bbb783c546cd8",
    ),
    (
        "slice7_snapshots.smt2",
        "6b3fdaed9079bf5ab671bc48bdc1b74dd367f12e00e1f1d77f93dc721c7c8991",
    ),
    (
        "slice8_snapshots.smt2",
        "2be134f07bbbafe0b2733748af49ee678936ba7eb68aaa490777051b80b6bc61",
    ),
    (
        "slice9_snapshots.smt2",
        "0a635a0af9062dca7e9166ebd759d96451251d6982acc0efb67d949ec3453a60",
    ),
    (
        "slice10_snapshots.smt2",
        "5447f01315e1cf3e7e0e151074b759816c30eb31fd24decb889d9890d662299f",
    ),
    (
        "slice11_snapshots.smt2",
        "91fbcb2c12ad1e6e7103404b02271bc7d24f06885858c3e925fa47a0971248a2",
    ),
    (
        "slice12_snapshots.smt2",
        "a006b6dc84f3db88cff4a4764d1e05703ee8a0d4d01d72a59f60c7e744d6a54c",
    ),
    (
        "slice13_snapshots.smt2",
        "7b8a48e3b34edf559ce1379077c0ac1f17f8e854b6223e74b7733e118d285c5f",
    ),
    (
        "slice14_snapshots.smt2",
        "2d9eea931477f4e200019012c29c60dccbffea3ee17c4d0c71a5a8f7fea5147e",
    ),
    (
        "slice15_snapshots.smt2",
        "7d037264e29d7784520ef3637b1a249ba054297eff203fbe88f76366d2780db9",
    ),
    (
        "arraygep_snapshots.smt2",
        "144a12d55cde752af8884e1e21d2d4b1e41aa58753e71c112138ea92b67679b4",
    ),
];

// ---------------------------------------------------------------------------
// OD-196: `magic`, the quotient range and `uremdef`
// ---------------------------------------------------------------------------

/// The `magic` groups over slice 18's "v18" groups (as the measurement
/// checked them).
const MAGIC: Groups = V18
    .with(Groups::MAGIC)
    .with(Groups::RANGE)
    .with(Groups::UREMDEF);

/// THE side condition against its definition: for every `n` in 1..=8, every
/// multiplier `m` below `2^(n+3)` and every shift `k` up to `2n + 3`,
/// `normal::magic_divisor(n, m, k)` is `Some(d)` exactly when `d = ceil(2^k /
/// m)` satisfies `1 <= d < 2^n` and `(2^n - 1) * (m d - 2^k) < 2^k`, computed
/// here directly in 128-bit integers (every value is small); and whenever it
/// is `Some(d)`, `floor(x m / 2^k) = floor(x / d)` for EVERY `x < 2^n`
/// (the theorem, checked on each instance). Counts the instances where the
/// equality holds for every `x` without the condition (the condition is
/// sufficient, not necessary: those are left unrewritten).
#[test]
fn the_magic_condition_is_the_granlund_montgomery_inequality() {
    let (mut admitted, mut exact_but_refused, mut checked) = (0usize, 0usize, 0usize);
    for n in 1..=8u32 {
        for m in 1..(1u128 << (n + 3)) {
            for k in 0..=(2 * n + 3) {
                let pow = 1u128 << k;
                let d = pow.div_ceil(m);
                let e = m * d - pow;
                let condition = d >= 1 && d < (1u128 << n) && ((1u128 << n) - 1) * e < pow;
                let got = normal::magic_divisor(n, m, k);
                assert_eq!(
                    got,
                    condition.then_some(d),
                    "n {n} m {m} k {k}: the condition is {condition} (d {d}, e {e})"
                );
                let exact = (0..1u128 << n).all(|x| (x * m) >> k == x / d);
                if let Some(d) = got {
                    admitted += 1;
                    for x in 0..1u128 << n {
                        assert_eq!((x * m) >> k, x / d, "n {n} m {m} k {k} x {x}");
                        checked += 1;
                    }
                } else if exact && d < (1u128 << n) {
                    exact_but_refused += 1;
                }
            }
        }
    }
    eprintln!(
        "SLICE19_MAGIC_CONDITION admitted={admitted} checked_inputs={checked} \
         exact_but_refused={exact_but_refused}"
    );
    assert!(admitted > 1000, "{admitted} instances admitted");
    // The extremes: a 64-bit dividend, `k` up to 128, a multiplier past 64
    // bits (the add shape's `2^64 + C`), and `m = 0` or `n` past the bound.
    for (n, m, k, want) in [
        (64, 0xcccc_cccc_cccc_cccd, 67, Some(10)),
        (64, 0xaaaa_aaaa_aaaa_aaab, 68, Some(24)),
        (64, 0xdbe6_fece_bded_d5bf, 97, Some(10_000_000_000)),
        (64, (1u128 << 64) + 0x47ae_147a_e147_ae15, 71, Some(100)),
        (64, (1u128 << 64) + 0x4f8b_588e_368f_0847, 81, Some(100_000)),
        (32, 0xcccc_cccd, 35, Some(10)),
        (32, (1u128 << 32) + 0x4f8b_588f, 49, Some(100_000)),
        (64, 0xcccc_cccc_cccc_cccc, 67, None),
        (64, 0xcccc_cccc_cccc_ccce, 67, None),
        (64, 0xcccc_cccc_cccc_cccd, 65, None),
        (64, 0xcccc_cccc_cccc_cccd, 64, None),
        // One shift less or more: still a quotient, by 5 and by 20.
        (64, 0xcccc_cccc_cccc_cccd, 66, Some(5)),
        (64, 0xcccc_cccc_cccc_cccd, 68, Some(20)),
        (64, 1, 128, None),
        (64, 3, 128, None),
        (0, 5, 3, None),
        (64, 0, 3, None),
        (128, 5, 3, None),
        (64, 5, 129, None),
    ] {
        assert_eq!(normal::magic_divisor(n, m, k), want, "n {n} m {m:#x} k {k}");
    }
}

/// Every census instance (the measurement's `magic_instances.txt`: the
/// eleven distinct multiply-high constants AY could not decide), the
/// replaced formula checked in exact integers independently of the rule:
/// `floor(x * C / 2^lo)` (plain) or `floor((h + floor((x - h) / 2)) /
/// 2^lo)` with `h = floor(x * C / 2^N)` (add), against `floor(x / d)`, on
/// 2^16 seeded inputs and every input within one of a multiple of `d` at
/// both ends of the range.
#[test]
fn every_census_magic_instance_computes_its_quotient() {
    // (shape, N, C, shift, d)
    let instances: [(&str, u32, u128, u32, u128); 11] = [
        ("add", 32, 0x4f8b_588f, 16, 100_000),
        ("add", 64, 0x47ae_147a_e147_ae15, 6, 100),
        ("add", 64, 0x4f8b_588e_368f_0847, 16, 100_000),
        ("plain", 32, 0x1062_4dd3, 38, 1000),
        ("plain", 32, 0x431b_de83, 50, 1_000_000),
        ("plain", 32, 0x51eb_851f, 37, 100),
        ("plain", 32, 0xcccc_cccd, 35, 10),
        ("plain", 64, 0x346d_c5d6_3886_594b, 75, 10_000),
        ("plain", 64, 0xaaaa_aaaa_aaaa_aaab, 68, 24),
        ("plain", 64, 0xcccc_cccc_cccc_cccd, 67, 10),
        ("plain", 64, 0xdbe6_fece_bded_d5bf, 97, 10_000_000_000),
    ];
    // The machine formula, in 256-bit arithmetic held as two 128-bit halves
    // (x * C needs up to 128 bits; the add form adds no more).
    let mul_high = |x: u128, c: u128, shift: u32| -> u128 {
        // x < 2^64, c < 2^64: the product fits 128 bits.
        (x * c) >> shift
    };
    let machine = |shape: &str, n: u32, c: u128, shift: u32, x: u128| -> u128 {
        if shape == "plain" {
            mul_high(x, c, shift)
        } else {
            let h = mul_high(x, c, n);
            (h + ((x - h) >> 1)) >> shift
        }
    };
    for (shape, n, c, shift, d) in instances {
        let (m, k) = if shape == "plain" {
            (c, shift)
        } else {
            ((1u128 << n) + c, n + 1 + shift)
        };
        assert_eq!(
            normal::magic_divisor(n, m, k),
            Some(d),
            "{shape} N {n} C {c:#x}"
        );
        let top = (1u128 << n) - 1;
        let mut state = (c as u64) ^ u64::from(n);
        let mut xs: Vec<u128> = (0..1 << 16)
            .map(|_| {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                u128::from(state) & top
            })
            .collect();
        for multiple in [0, 1, 2, 3, top / d - 2, top / d - 1, top / d] {
            for offset in [-1i128, 0, 1, d as i128 - 1] {
                let x = (multiple * d) as i128 + offset;
                if (0..=top as i128).contains(&x) {
                    xs.push(x as u128);
                }
            }
        }
        xs.extend([0, 1, top - 1, top]);
        for x in xs {
            assert_eq!(
                machine(shape, n, c, shift, x),
                x / d,
                "{shape} N {n} C {c:#x} shift {shift} x {x:#x}"
            );
        }
    }
}

/// `x` at width `n`, the plain multiply-high `extract[hi:lo](bvmul
/// (zero_extend_k x) C)`.
fn plain_high(n: u32, k: u32, c: u64, high: u32, low: u32) -> E {
    E::var("x", n)
        .zero_ext(k)
        .bvmul(E::bv_const(c, n + k))
        .extract(high, low)
}

/// The add-shape multiply-high of `x` (`n` bits) by `C`, shifted by `low`.
fn add_high(n: u32, low: u32, h: E) -> E {
    let x = E::var("x", n);
    let halved = x.bvsub(h.clone()).extract(n - 1, 1).zero_ext(1);
    h.bvadd(halved).extract(n - 1, low)
}

/// Whether `expr` holds a quotient by a constant.
fn has_quotient(expr: &E) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if matches!(node, E::BvUDiv { rhs, .. } if matches!(rhs.as_ref(), E::BvConst { .. })) {
            return true;
        }
        node.for_each_child(&mut |child| stack.push(child));
    }
    false
}

/// The add shape's subtraction must read the multiplied `x`: the same
/// shape with another input `y` in `y - h` keeps its value on every input
/// (exhaustive over `x` and `y`, widths 2 to 5, every constant and shift;
/// the sweep above only builds `x - h`, so a rewrite of it to the quotient
/// of `x` is caught only here). And every window `[hi:lo]`
/// of the sum below its top bit keeps its value (the add shape's own window
/// is `[n-1:lo]`).
#[test]
fn the_add_shape_reads_its_own_x() {
    let mut instances = 0usize;
    for n in 2..=5u32 {
        for c in 0..1u64 << n {
            let h = plain_high(n, n, c, 2 * n - 1, n);
            let other = E::var("y", n)
                .bvsub(h.clone())
                .extract(n - 1, 1)
                .zero_ext(1);
            let other_sum = h.clone().bvadd(other);
            for low in 0..n {
                // Its `h` alone may be a plain multiply-high `magic`
                // rewrites; the whole term keeps its value on every input.
                let term = other_sum.clone().extract(n - 1, low);
                exhaustive(&term, &[("x", n), ("y", n)], MAGIC);
                instances += 1;
            }
            let own = E::var("x", n)
                .bvsub(h.clone())
                .extract(n - 1, 1)
                .zero_ext(1);
            let own_sum = h.bvadd(own);
            for high in 0..n - 1 {
                for low in 0..=high {
                    exhaustive(&own_sum.clone().extract(high, low), &[("x", n)], MAGIC);
                    instances += 1;
                }
            }
        }
    }
    eprintln!("SLICE19_MAGIC_ADD_OTHER instances={instances}");
}

/// `magic`, the quotient range and `uremdef`, exhaustively at small widths
/// (the measurement's `magic_exhaustive.py`): every plain shape (`x` of 1 to
/// 6 bits, extensions by 1 to 5, EVERY constant and every extract window),
/// every add shape (`x` of 2 to 7 bits, every constant and shift), the add
/// shape with `h` behind a kept name read through its low bits, every
/// quotient range and every `bvurem` by a constant, normalized with the
/// groups and checked against the original on every input. Each rewrites
/// some instances.
#[test]
fn magic_is_exact_exhaustively_at_small_widths() {
    let mut tally = Tally::default();
    let check = |term: &E, n: u32, groups: Groups| -> Option<usize> {
        let normal = normal::normalized_term(term, groups).expect("in the vocabulary");
        if !has_quotient(&normal) || has_quotient(term) {
            if normal != *term {
                // Another identity applied: still exact.
                exhaustive(term, &[("x", n)], groups);
            }
            return None;
        }
        exhaustive(term, &[("x", n)], groups)
    };
    for n in 1..=6u32 {
        for k in 1..=5u32 {
            let wide = n + k;
            for c in 0..1u64 << wide {
                for low in 0..wide {
                    for high in low..wide {
                        let term = plain_high(n, k, c, high, low);
                        tally.add("magic-plain", check(&term, n, MAGIC));
                    }
                }
            }
        }
        let x = E::var("x", n);
        for c in 1..1u64 << n {
            let quotient = x.clone().bvudiv(E::bv_const(c, n));
            for r in 1..=n {
                for j in 1..=3u32 {
                    let term = quotient.clone().extract(r - 1, 0).zero_ext(j);
                    tally.add("magic-range", exhaustive(&term, &[("x", n)], MAGIC));
                }
            }
            let remainder = x.clone().bvurem(E::bv_const(c, n));
            let normal = normal::normalized_term(&remainder, MAGIC).expect("in the vocabulary");
            assert_ne!(normal, remainder, "uremdef rewrites {remainder}");
            tally.add("uremdef", exhaustive(&remainder, &[("x", n)], MAGIC));
        }
    }
    for n in 2..=7u32 {
        for c in 0..1u64 << n {
            let h = plain_high(n, n, c, 2 * n - 1, n);
            for low in 0..n {
                let term = add_high(n, low, h.clone());
                tally.add("magic-add", check(&term, n, MAGIC));
            }
        }
    }
    // `h` behind a kept name `hv := zext_n(h)`, read as `hv[n-1:0]`
    // (int_log10's spelling): through `normal::spelled`, the name a premise.
    // Where the condition holds, the claim equating the term with the
    // quotient empties; everywhere the spelling keeps every claim's value.
    for n in 2..=6u32 {
        for c in 0..1u64 << n {
            let h = plain_high(n, n, c, 2 * n - 1, n);
            for low in 0..n {
                let low_bits = E::var("hv", 2 * n).extract(n - 1, 0);
                let definitions = vec![
                    ("hv".to_owned(), h.clone().zero_ext(n)),
                    ("t".to_owned(), add_high(n, low, low_bits)),
                ];
                let d = normal::magic_divisor(n, (1u128 << n) + u128::from(c), n + 1 + low);
                let divisor = d.map_or(1, |d| d as u64);
                let quotient = E::var("x", n)
                    .bvudiv(E::bv_const(divisor, n))
                    .extract(n - low - 1, 0);
                let claim = E::var("t", n - low).eq_expr(quotient);
                let spelled = normal::spelled(&definitions, &claim, Groups::CANONICAL);
                let mut inputs = 0;
                for x in 0..1u128 << n {
                    let env: HashMap<String, u128> = [("x".to_owned(), x)].into_iter().collect();
                    let (holds, _) = evaluate(&definitions, &claim, &env);
                    match &spelled {
                        normal::Normal::Emptied => assert!(holds, "n {n} c {c} low {low} x {x}"),
                        normal::Normal::Spelled((kept, claims)) => assert_eq!(
                            evaluate(kept, claims, &env).0,
                            holds,
                            "n {n} c {c} low {low} x {x}"
                        ),
                        normal::Normal::Declined => panic!("declined"),
                    }
                    inputs += 1;
                }
                // Counted where the claim empties: the add shape through the
                // name reached `magic` (not where the extract is the whole sum,
                // `C` a power of two `mulpow2` made a shift, or `h` already a
                // quotient itself).
                tally.add(
                    "magic-add-peel",
                    (d.is_some() && matches!(spelled, normal::Normal::Emptied)).then_some(inputs),
                );
            }
        }
    }
    for (group, (instances, inputs)) in &tally.0 {
        eprintln!("SLICE19_MAGIC {group}: {instances} rewritten instances, {inputs} inputs");
    }
    for group in [
        "magic-plain",
        "magic-range",
        "uremdef",
        "magic-add",
        "magic-add-peel",
    ] {
        assert!(
            tally
                .0
                .get(group)
                .is_some_and(|(instances, _)| *instances > 0),
            "{group} rewrites no instance"
        );
    }
}

/// THE controls of the side condition: a multiply-high by a WRONG magic
/// constant (the right one for 10 plus or minus one) or with a WRONG shift
/// (two or three less), where the inequality fails, is never rewritten, and
/// a theorem that equates it with the quotient by 10 stays refuted: its
/// spelling keeps a claim, false on some input. The right constant and shift
/// are rewritten and the theorem empties; one shift less still computes a
/// quotient (by 5): it is rewritten to it, and the theorem stays refuted.
#[test]
fn a_wrong_magic_constant_or_shift_is_not_rewritten_and_stays_refuted() {
    let x = E::var("x", 64);
    let quotient = x.clone().bvudiv(E::bv_const(10, 64));
    let theorem = |c: u64, shift: u32| {
        let definitions = vec![
            ("s0".to_owned(), quotient.clone()),
            (
                "m0".to_owned(),
                x.clone()
                    .zero_ext(64)
                    .bvmul(E::bv_const(c, 128))
                    .extract(127, shift),
            ),
        ];
        let high = E::var("m0", 128 - shift);
        let high = if 128 - shift >= 64 {
            high.extract(63, 0)
        } else {
            high.zero_ext(shift - 64)
        };
        let claim = E::var("s0", 64).eq_expr(high);
        (definitions, claim)
    };
    let right = 0xcccc_cccc_cccc_cccdu64;
    let (definitions, claim) = theorem(right, 67);
    // The right constant and shift: the multiply-high is the quotient, and
    // the theorem holds (it may keep `(= s0 (zero_extend (s0[60:0])))`: the
    // quotient range reads `bvudiv`, not a name `cse` gave it).
    match normal::spelled(&definitions, &claim, Groups::CANONICAL) {
        normal::Normal::Emptied => {}
        normal::Normal::Spelled((kept, claims)) => {
            assert!(
                !claims.to_string().contains("bvmul")
                    && !kept
                        .iter()
                        .any(|(_, rhs)| rhs.to_string().contains("bvmul")),
                "the right constant and shift: rewritten: {claims}"
            );
            for x in [0u128, 9, 10, 11, u128::from(u64::MAX), 1 << 63] {
                let env: HashMap<String, u128> = [("x".to_owned(), x)].into_iter().collect();
                assert!(evaluate(&kept, &claims, &env).0, "x {x:#x}");
            }
        }
        normal::Normal::Declined => panic!("declined"),
    }
    for (c, shift) in [
        (right + 1, 67),
        (right - 1, 67),
        (right, 65),
        (right, 64),
        (right, 66),
    ] {
        let quotient_by = normal::magic_divisor(64, u128::from(c), shift);
        assert_eq!(
            quotient_by,
            (shift == 66).then_some(5),
            "C {c:#x} shift {shift}"
        );
        let (definitions, claim) = theorem(c, shift);
        let normal::Normal::Spelled((kept, claims)) =
            normal::spelled(&definitions, &claim, Groups::CANONICAL)
        else {
            panic!("C {c:#x} shift {shift}: the claim is kept");
        };
        let multiplied = claims.to_string().contains("bvmul")
            || kept
                .iter()
                .any(|(_, rhs)| rhs.to_string().contains("bvmul"));
        assert_eq!(
            multiplied,
            quotient_by.is_none(),
            "C {c:#x} shift {shift}: rewritten only when the inequality holds: {claims}"
        );
        // Refuted: some input falsifies the original and the spelled claim
        // alike (the inputs where the wrong formula and the quotient part).
        let mut refuted = false;
        let mut state = c ^ u64::from(shift);
        for round in 0..4096u64 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let value = match round % 4 {
                0 => u128::from(u64::MAX - (round >> 2)),
                1 => u128::from(round * 10 + 9),
                2 => u128::from(state >> (round % 64)),
                _ => u128::from(state),
            };
            let env: HashMap<String, u128> = [("x".to_owned(), value)].into_iter().collect();
            let (holds, _) = evaluate(&definitions, &claim, &env);
            assert_eq!(
                evaluate(&kept, &claims, &env).0,
                holds,
                "C {c:#x} shift {shift} x {value:#x}"
            );
            refuted |= !holds;
        }
        assert!(refuted, "C {c:#x} shift {shift}: refuted on a sample");
    }
}

// ---------------------------------------------------------------------------
// OD-197: a theorem or part replayed claim by claim
// ---------------------------------------------------------------------------

/// The right-nested conjuncts of `claims`.
fn conjuncts_of(claims: &E) -> Vec<E> {
    let mut out = Vec::new();
    let mut rest = claims;
    while let E::And { lhs, rhs } = rest {
        out.push(lhs.as_ref().clone());
        rest = rhs.as_ref();
    }
    out.push(rest.clone());
    out
}

/// THE claim split's sweep: every canonical single theorem stated against
/// `true` of every fixture and wrong lowering, and every part of every
/// earlier fixture cut at every block start, with two distinct claims or
/// more, split by `split::claim_parts`: one obligation per distinct claim,
/// in order, named `<name> | claim i of m`, each passing the part check,
/// each over a subset of the obligation's definitions (in order, at their
/// right-hand sides) and free inputs; and on 256 sampled inputs the
/// obligation holds exactly when every claim part does, each claim part's
/// value being its conjunct's.
#[test]
fn every_claim_split_is_the_conjunction_of_its_claims() {
    let mut obligations: Vec<(String, ProofObligation)> = Vec::new();
    let mut cases: Vec<(String, Function, X86ISelFunction, bool)> = every_fixture()
        .into_iter()
        .map(|(label, source, machine)| (label, source, machine, false))
        .collect();
    cases.extend(every_refutation());
    for (label, source, machine, unbounded) in &cases {
        if let Some(theorem) = built(source, machine, PathEncoding::CANONICAL, *unbounded)
            && theorem.0.trust_ir_expr == E::bool_const(true)
        {
            obligations.push((label.clone(), theorem.0));
        }
    }
    for (label, source, machine) in super::slice16::earlier_fixtures() {
        let points = super::slice16::every_block(&source);
        if let Ok(owner) = super::slice16::in_parts(&source, &machine, points) {
            for part in owner.parts() {
                obligations.push((format!("{label} {}", part.name), part.clone()));
            }
        }
    }
    let (mut split, mut refused, mut claims) = (0usize, 0usize, 0usize);
    let mut failures = Vec::new();
    for (label, obligation) in &obligations {
        let mut distinct: Vec<E> = Vec::new();
        for conjunct in conjuncts_of(&obligation.aarch64_expr) {
            if !distinct.contains(&conjunct) {
                distinct.push(conjunct);
            }
        }
        let parts = match split::claim_parts(obligation) {
            Ok(parts) => parts,
            Err(why) => {
                refused += 1;
                if distinct.len() >= 2 && distinct.len() <= 64 {
                    failures.push(format!("{label}: not split: {why}"));
                }
                continue;
            }
        };
        split += 1;
        claims += parts.len();
        if parts.len() != distinct.len() {
            failures.push(format!(
                "{label}: {} parts for {} claims",
                parts.len(),
                distinct.len()
            ));
            continue;
        }
        let definitions = definitions_of(obligation);
        let free = part_free(obligation);
        for (k, part) in parts.iter().enumerate() {
            let want = format!(
                "{}{X86_BODY_CLAIM_SEPARATOR}{} of {}",
                obligation.name,
                k + 1,
                parts.len()
            );
            if part.name != want || part.aarch64_expr != distinct[k] {
                failures.push(format!("{label}: claim {} is not the obligation's", k + 1));
            }
            if let Err(why) = check_definitional_part(part, &part_free(part)) {
                failures.push(format!("{label} claim {}: {why}", k + 1));
            }
            // A subsequence of the obligation's definitions, unchanged.
            let mut at = 0;
            for (name, rhs) in definitions_of(part) {
                match definitions[at..]
                    .iter()
                    .position(|(n, r)| *n == name && *r == rhs)
                {
                    Some(offset) => at += offset + 1,
                    None => {
                        failures.push(format!("{label} claim {}: {name} is no definition", k + 1))
                    }
                }
            }
            for (name, width) in part_free(part) {
                if !free.contains(&(name.clone(), width)) {
                    failures.push(format!("{label} claim {}: reads {name}", k + 1));
                }
            }
        }
        let mut state = label.bytes().fold(0x84222325u64, |h, b| {
            (h ^ u64::from(b)).wrapping_mul(0x01b3)
        });
        for _ in 0..256 {
            let inputs: HashMap<String, u128> = free
                .iter()
                .map(|(name, width)| (name.clone(), sample(*width, &mut state)))
                .collect();
            let (holds, _) = evaluate_theorem(obligation, &inputs);
            let each: Vec<bool> = parts
                .iter()
                .map(|part| evaluate_theorem(part, &inputs).0)
                .collect();
            if holds != each.iter().all(|claim| *claim) {
                failures.push(format!(
                    "{label}: the claims' conjunction differs at {inputs:?}"
                ));
                break;
            }
        }
    }
    eprintln!("SLICE19_CLAIMS split={split} claims={claims} refused={refused}");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(split >= 200, "{split} obligations split");
}

/// What has no claim split: a one-path theorem, a single claim (or one
/// claim repeated), and more than [`split::MAX_CLAIM_PARTS`] claims.
#[test]
fn a_claim_split_refuses_what_it_cannot_split() {
    let x = E::var("x", 8);
    let obligation = |source: E, machine: E| ProofObligation {
        name: X86_BODY_OBLIGATION_NAME.into(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![("x".into(), 8)],
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    let claim = |k: u64| {
        x.clone()
            .bvadd(E::bv_const(k, 8))
            .eq_expr(E::bv_const(k, 8))
    };
    assert!(
        split::claim_parts(&obligation(x.clone(), x.clone().bvadd(E::bv_const(0, 8)))).is_err()
    );
    assert!(split::claim_parts(&obligation(E::bool_const(true), claim(1))).is_err());
    assert!(
        split::claim_parts(&obligation(
            E::bool_const(true),
            claim(1).and_expr(claim(1))
        ))
        .is_err()
    );
    let many = (0..65u64)
        .map(claim)
        .rev()
        .reduce(|tail, c| c.and_expr(tail))
        .unwrap();
    assert!(split::claim_parts(&obligation(E::bool_const(true), many)).is_err());
    let two = split::claim_parts(&obligation(
        E::bool_const(true),
        claim(1).and_expr(claim(2)),
    ))
    .expect("two claims split");
    assert_eq!(two.len(), 2);
    assert!(is_x86_body_claim_name(&two[1].name), "{}", two[1].name);
}

/// THE credit rule of a claim-by-claim replay (`x86_claims_verdict`): it
/// runs only after a whole replay with no verdict and with two claims or
/// more; every claim Valid credits the obligation; a refuted claim refutes
/// it, naming the claim; the first claim without a verdict stops the replay
/// and keeps the whole replay's outcome.
#[test]
fn the_claim_by_claim_credit_rule() {
    use crate::function_request::x86_claims_verdict;
    use crate::verify::VerificationResult as V;
    let timeout = || V::Unknown {
        reason: "AY Timeout".into(),
    };
    let valid = |_| (Some(V::Valid), None);
    // A whole verdict is never replayed claim by claim.
    for whole in [
        Some(V::Valid),
        Some(V::Invalid {
            counterexample: "x".into(),
        }),
    ] {
        let valid = matches!(whole, Some(V::Valid));
        let (verdict, _, credited) = x86_claims_verdict((whole, None), 3, |_| panic!("replayed"));
        assert!(if valid {
            matches!(verdict, Some(V::Valid))
        } else {
            matches!(verdict, Some(V::Invalid { .. }))
        });
        assert!(!credited);
    }
    assert!(
        !x86_claims_verdict((None, Some("AY Timeout".into())), 1, |_| panic!("replayed")).2,
        "one claim is no split"
    );
    // Every claim Valid: Valid, credited claim by claim.
    let (verdict, why, credited) = x86_claims_verdict((Some(timeout()), None), 4, valid);
    assert!(matches!(verdict, Some(V::Valid)));
    assert!(credited && why.is_none());
    // A refuted claim refutes the obligation.
    let (verdict, _, credited) = x86_claims_verdict((None, None), 4, |k| {
        if k == 2 {
            (
                Some(V::Invalid {
                    counterexample: "x = 1".into(),
                }),
                None,
            )
        } else {
            (Some(V::Valid), None)
        }
    });
    assert!(
        matches!(&verdict, Some(V::Invalid { counterexample }) if counterexample == "claim 3 of 4: x = 1"),
        "{verdict:?}"
    );
    assert!(!credited);
    // A claim without a verdict stops the replay: the whole outcome stands.
    let mut replayed = Vec::new();
    let (verdict, why, credited) = x86_claims_verdict((Some(timeout()), None), 5, |k| {
        replayed.push(k);
        if k == 1 {
            (None, Some("AY Timeout".into()))
        } else {
            (Some(V::Valid), None)
        }
    });
    assert!(matches!(&verdict, Some(V::Unknown { reason }) if reason == "AY Timeout"));
    assert!(!credited);
    assert_eq!(
        replayed,
        vec![0, 1],
        "the replay stops at the first unproven claim"
    );
    assert!(why.is_some_and(|why| why.contains("claim 2 of 5")));
}

/// An export credited claim by claim publishes, for each obligation so
/// credited, exactly its claim split in its place, and the consumer's check
/// refuses a tampered record: claims of another obligation, a claim
/// missing, a record for an obligation that has no split, a record of the
/// wrong length.
#[test]
fn an_export_credited_claim_by_claim_publishes_its_claims() {
    let mut checked = 0;
    for shape in super::slice16::SLICE_SIXTEEN {
        let (source, machine) = super::slice16::slice16_pair(shape);
        let Ok(owner) = fixture_owner(&source, &machine) else {
            continue;
        };
        let units = owner.replayed_units();
        let Some((k, claims)) =
            (0..units.len()).find_map(|k| owner.replay_claims(k).ok().map(|claims| (k, claims)))
        else {
            continue;
        };
        let claims: Vec<ProofObligation> = claims
            .iter()
            .map(|claim| claim.obligation().clone())
            .collect();
        let mut record = vec![None; units.len()];
        record[k] = Some(claims.clone());
        let export =
            crate::function_request::SourceBoundArithmeticObligation::x86_body_export_for_tests(
                &owner,
            )
            .with_x86_body_claims(normal_claims(record.clone()));
        let published = export.replayed_obligations().expect("the record checks");
        assert_eq!(published.len(), units.len() - 1 + claims.len(), "{shape:?}");
        assert_eq!(
            published[k..k + claims.len()]
                .iter()
                .map(|o| (*o).clone())
                .collect::<Vec<_>>(),
            claims
        );
        // Tampered records.
        let mut missing = record.clone();
        missing[k].as_mut().unwrap().pop();
        let mut short = record.clone();
        short.pop();
        let mut foreign = record.clone();
        foreign[k].as_mut().unwrap()[0].aarch64_expr = E::bool_const(false);
        for (what, bad) in [
            ("a claim missing", missing),
            ("a short record", short),
            ("a foreign claim", foreign),
        ] {
            let export = export.with_x86_body_claims(normal_claims(bad));
            assert!(
                export.check_x86_body_claims().is_err(),
                "{shape:?}: {what} checks"
            );
            assert!(
                export.replayed_obligations().is_err(),
                "{shape:?}: {what} is published"
            );
        }
        checked += 1;
    }
    assert!(checked >= 2, "{checked} shapes checked");
}

fn normal_claims(units: Vec<Option<Vec<ProofObligation>>>) -> X86BodyClaims {
    X86BodyClaims::new(units)
}
