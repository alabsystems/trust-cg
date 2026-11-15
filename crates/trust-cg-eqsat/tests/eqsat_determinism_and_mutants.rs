// crates/trust-cg-eqsat/tests/eqsat_determinism_and_mutants.rs - PKG-U1 exit test: determinism, rule mutants, forged derivations, checker independence
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The exit test of PKG-U1 (docs/eqsat-tier-e.md). It runs the engine
//! (`trust-cg-eqsat`) and replays what it emits through the independent
//! checker (`trust-cg-eqsat-check`), which reads the derivation bytes with its
//! own code and never sees the engine.
//!
//! What a pass establishes:
//! * the engine is deterministic: two runs with separately parsed rule sets
//!   give byte-identical derivations and identical bodies, over the interim
//!   corpus (section 9) and over random total-operator functions;
//! * every committed rule mutant (`tests/wrong_rules/*.rules`) that is well formed
//!   actually fires in the engine and is then refused by the checker holding
//!   the honest registry, both as emitted (its statement digest is not the
//!   registered one) and with the digest forged to the honest rule's (the
//!   replayed statement does not conclude what the derivation claims); the
//!   two non-total mutants are refused by both rule parsers, and a hand-made
//!   derivation using one is refused by the checker;
//! * a division hoisted above its guard and two swapped stores are refused;
//! * every derivation the engine emits on the corpus and on random functions
//!   is accepted by the checker and the output validates;
//! * input and output agree on the reference interpreter at every sampled
//!   boundary and seeded random input where both runs are conclusive; for
//!   random functions every sampled run returns; for corpus functions with
//!   scalar parameters, agreement counts as shown only for a function whose
//!   input returns at one or more sampled inputs, and at least one
//!   rule-backed rewrite is executed and compared that way;
//! * every byte-level forgery of a real derivation tried here is refused;
//! * the checker shares no code with the engine: its manifest and lock name
//!   trust-ir only, no checker source names the engine crate or uses an
//!   include, environment or `path` mechanism (a token scan with its own
//!   self-test), no checker file is a copy of an engine file; neither crate's
//!   library source reads a clock or uses a hash-ordered collection.
//!
//! What it does NOT establish: interpreter agreement is differential testing
//! at sampled inputs, not a proof, and says nothing about a corpus function
//! whose input never returns at a sampled input (every sampled run fails
//! alike on both sides, for example at an unsupported call ahead of the
//! rewritten code, or hits the fuel limit): those are counted and listed as
//! vacuous; acceptance by the checker rests on the registry's stated
//! (unproved, PKG-U2) rule statements; the source scan is lexical (it is not
//! a Rust parser, so it refuses any use of the scanned identifiers, used or
//! not); the corpus is the interim one (section 9), not the PKG-C0 ladder
//! dump.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

mod engine_common;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use trust_cg_eqsat::derivation::{DerivationBuilder, ScalarTy, header_only};
use trust_cg_eqsat::rules::{self, INTEGER_IDENTITIES, RuleSet};
use trust_cg_eqsat::{EngineConfig, Optimized, optimize_function, round_trip};
use trust_cg_eqsat_check::{Body, Registry, Rejection, check};
use trust_ir::{
    Function, InterpretErrorCode, InterpretOptions, InterpretValue, Interpreter, Module, Ty,
};

// ---------------------------------------------------------------------------
// Shared support.

fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn workspace_root() -> PathBuf {
    crate_dir()
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .to_path_buf()
}

fn checker_dir() -> PathBuf {
    workspace_root().join("crates/trust-cg-eqsat-check")
}

fn honest_rules() -> RuleSet {
    RuleSet::parse(INTEGER_IDENTITIES).expect("honest rules parse")
}

fn honest_registry() -> Registry {
    Registry::parse(INTEGER_IDENTITIES).expect("honest registry parses")
}

/// Parse and validate trust-ir text.
fn parse_valid(text: &str) -> Module {
    let module = trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{e}\n{text}"));
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "does not validate: {errors:?}\n{text}");
    module
}

fn function_named<'m>(module: &'m Module, name: &str) -> &'m Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"))
}

/// `module` with `output` in place of the function with the same id.
fn substituted(module: &Module, output: &Function) -> Module {
    let mut out = module.clone();
    let slot = out
        .functions
        .iter_mut()
        .find(|f| f.id == output.id)
        .expect("function in module");
    *slot = output.clone();
    out
}

/// Asserts that `module` with `output` substituted validates.
fn assert_validates_with(module: &Module, output: &Function, what: &str) -> Module {
    let out = substituted(module, output);
    let errors = trust_ir_build::validate_module(&out);
    assert!(
        errors.is_empty(),
        "{what}: output of @{} does not validate: {errors:?}",
        output.name
    );
    out
}

/// The rule table of a derivation: `(name, digest, offset of the digest)`.
fn rule_table(bytes: &[u8]) -> Vec<(String, [u8; 32], usize)> {
    let u32_at = |at: usize| u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap()) as usize;
    assert_eq!(&bytes[..8], b"TCGEQSAT");
    let mut at = 12;
    let name_len = u32_at(at);
    at += 4 + name_len;
    let count = u32_at(at);
    at += 4;
    let mut out = Vec::new();
    for _ in 0..count {
        let len = u32_at(at);
        at += 4;
        let name = String::from_utf8(bytes[at..at + len].to_vec()).unwrap();
        at += len;
        let digest: [u8; 32] = bytes[at..at + 32].try_into().unwrap();
        out.push((name, digest, at));
        at += 32;
    }
    out
}

/// SplitMix64: a fixed-seed generator (no clock, no host entropy).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }
    fn wide(&mut self) -> u128 {
        (u128::from(self.next()) << 64) | u128::from(self.next())
    }
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Width and signedness of an integer or Bool type (`None` otherwise).
fn scalar_shape(ty: &Ty, pointer_bits: u32) -> Option<(u32, bool)> {
    Some(match ty {
        Ty::Bool => (1, false),
        Ty::I8 => (8, true),
        Ty::I16 => (16, true),
        Ty::I32 => (32, true),
        Ty::I64 => (64, true),
        Ty::I128 => (128, true),
        Ty::Isize => (pointer_bits, true),
        Ty::U8 => (8, false),
        Ty::U16 => (16, false),
        Ty::U32 => (32, false),
        Ty::U64 => (64, false),
        Ty::U128 => (128, false),
        Ty::Usize => (pointer_bits, false),
        _ => return None,
    })
}

/// Boundary residues of a width: 0, 1, -1, MIN, MAX, MIN+1, MAX-1 and every
/// power of two.
fn boundary_residues(width: u32) -> Vec<u128> {
    if width == 1 {
        return vec![0, 1];
    }
    let m = mask(width);
    let min = 1u128 << (width - 1);
    let mut out = vec![0, 1, m, min, min - 1, min + 1, min - 2];
    for k in 0..width {
        out.push(1u128 << k);
    }
    out.sort_unstable();
    out.dedup();
    out
}

fn interp_value(ty: &Ty, residue: u128, pointer_bits: u32) -> InterpretValue {
    if *ty == Ty::Bool {
        InterpretValue::bool(residue == 1)
    } else {
        InterpretValue::int_at(ty.clone(), residue as i128, pointer_bits).expect("integer value")
    }
}

/// Argument vectors for scalar parameters: the boundary diagonal, boundary
/// mixes and seeded random residues (at most `count` vectors).
fn argument_vectors(
    params: &[Ty],
    pointer_bits: u32,
    count: usize,
    seed: u64,
) -> Vec<Vec<InterpretValue>> {
    let shapes: Vec<(u32, bool)> = params
        .iter()
        .map(|ty| scalar_shape(ty, pointer_bits).expect("scalar parameter"))
        .collect();
    let bounds: Vec<Vec<u128>> = shapes.iter().map(|(w, _)| boundary_residues(*w)).collect();
    let mut rng = Rng(seed);
    let mut out = Vec::new();
    if params.is_empty() {
        return vec![Vec::new()];
    }
    for i in 0..count {
        let args = params
            .iter()
            .enumerate()
            .map(|(j, ty)| {
                let b = &bounds[j];
                let residue = if i < count / 3 {
                    // Diagonal and staggered boundaries.
                    b[(i + j * 3) % b.len()]
                } else if i < (2 * count) / 3 {
                    b[rng.below(b.len())]
                } else {
                    rng.wide() & mask(shapes[j].0)
                };
                interp_value(ty, residue, pointer_bits)
            })
            .collect();
        out.push(args);
    }
    out
}

/// One run's observable outcome. `Inconclusive` is a fuel or call-depth
/// limit: the two bodies execute different numbers of instructions, so a
/// limit says nothing about agreement.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Outcome {
    Returned(Vec<InterpretValue>),
    Failed(InterpretErrorCode, String),
    Inconclusive,
}

fn outcome(module: &Module, function: &Function, args: &[InterpretValue], fuel: u64) -> Outcome {
    let options = InterpretOptions {
        fuel,
        ..InterpretOptions::default()
    };
    match Interpreter::with_module(module)
        .with_options(options)
        .execute_func(function.id, args.iter().cloned())
    {
        Ok(done) => Outcome::Returned(done.returns),
        Err(error) if error.code == InterpretErrorCode::OutOfFuel => Outcome::Inconclusive,
        Err(error) => Outcome::Failed(error.code, format!("{:?}", error.panic())),
    }
}

fn scalar_params(module: &Module, function: &Function) -> Option<Vec<Ty>> {
    let params = module
        .func_types
        .get(function.ty.0 as usize)?
        .params
        .clone();
    let bits = module.pointer_bits();
    params
        .iter()
        .all(|ty| scalar_shape(ty, bits).is_some())
        .then_some(params)
}

/// The result of a differential comparison.
struct Comparison {
    /// Argument vectors on which both runs were conclusive.
    compared: usize,
    /// Of those, the ones on which the input returned normally.
    returned: usize,
    /// The argument vectors on which the outcomes differ.
    differing: Vec<(Vec<InterpretValue>, Outcome, Outcome)>,
}

/// Differential comparison of `input` and `output` (substituted into
/// `module`) at boundary and seeded random arguments.
fn compare_runs(
    module: &Module,
    input: &Function,
    output_module: &Module,
    count: usize,
    fuel: u64,
    seed: u64,
) -> Comparison {
    let mut result = Comparison {
        compared: 0,
        returned: 0,
        differing: Vec::new(),
    };
    let Some(params) = scalar_params(module, input) else {
        return result;
    };
    let bits = module.pointer_bits();
    for args in argument_vectors(&params, bits, count, seed) {
        let before = outcome(module, input, &args, fuel);
        let after = outcome(output_module, input, &args, fuel);
        if before == Outcome::Inconclusive || after == Outcome::Inconclusive {
            continue;
        }
        result.compared += 1;
        result.returned += usize::from(matches!(before, Outcome::Returned(_)));
        if before != after {
            result.differing.push((args, before, after));
        }
    }
    result
}

// ---------------------------------------------------------------------------
// The interim corpus (section 9): MANIFEST.tsv rows with status `taken`.

struct CorpusModule {
    file: String,
    module: Module,
}

fn corpus() -> &'static [CorpusModule] {
    static CORPUS: OnceLock<Vec<CorpusModule>> = OnceLock::new();
    CORPUS.get_or_init(|| {
        let dir = crate_dir().join("tests/corpus");
        let manifest = std::fs::read_to_string(dir.join("MANIFEST.tsv")).expect("MANIFEST.tsv");
        let mut lines = manifest.lines().filter(|l| !l.starts_with('#'));
        assert_eq!(lines.next(), Some("status\tfile\tsource\treason"));
        let mut out = Vec::new();
        for line in lines {
            let fields: Vec<&str> = line.split('\t').collect();
            assert_eq!(fields.len(), 4, "manifest row {line:?}");
            match fields[0] {
                "taken" => {
                    let text = std::fs::read_to_string(dir.join(fields[1]))
                        .unwrap_or_else(|e| panic!("{}: {e}", fields[1]));
                    let module = trust_ir::parser::parse_module(&text)
                        .unwrap_or_else(|e| panic!("{}: {e}", fields[1]));
                    out.push(CorpusModule {
                        file: fields[1].to_owned(),
                        module,
                    });
                }
                "left" => assert_eq!(fields[1], "-"),
                other => panic!("manifest status {other:?}"),
            }
        }
        assert!(!out.is_empty(), "the corpus takes no module");
        out
    })
}

// ---------------------------------------------------------------------------
// Random total-operator functions (case 8, also cases 1 and 11).

#[derive(Clone, Copy, PartialEq, Eq)]
struct TyInfo {
    name: &'static str,
    width: u32,
    signed: bool,
}

const INT_TYS: [TyInfo; 12] = [
    TyInfo {
        name: "i8",
        width: 8,
        signed: true,
    },
    TyInfo {
        name: "i16",
        width: 16,
        signed: true,
    },
    TyInfo {
        name: "i32",
        width: 32,
        signed: true,
    },
    TyInfo {
        name: "i64",
        width: 64,
        signed: true,
    },
    TyInfo {
        name: "i128",
        width: 128,
        signed: true,
    },
    TyInfo {
        name: "isize",
        width: 64,
        signed: true,
    },
    TyInfo {
        name: "u8",
        width: 8,
        signed: false,
    },
    TyInfo {
        name: "u16",
        width: 16,
        signed: false,
    },
    TyInfo {
        name: "u32",
        width: 32,
        signed: false,
    },
    TyInfo {
        name: "u64",
        width: 64,
        signed: false,
    },
    TyInfo {
        name: "u128",
        width: 128,
        signed: false,
    },
    TyInfo {
        name: "usize",
        width: 64,
        signed: false,
    },
];

const BOOL: TyInfo = TyInfo {
    name: "bool",
    width: 1,
    signed: false,
};

/// The text of a constant residue at a type.
fn const_text(ty: TyInfo, residue: u128) -> String {
    let r = residue & mask(ty.width);
    if ty.width == 1 {
        return if r == 1 { "true" } else { "false" }.to_owned();
    }
    if ty.signed && r >> (ty.width - 1) == 1 {
        // Negative: -(2^w - r).
        let magnitude = (mask(ty.width) - r) + 1;
        if magnitude == 1u128 << 127 {
            return "-170141183460469231731687303715884105728".to_owned();
        }
        return format!("-{magnitude}");
    }
    r.to_string()
}

/// Builds one random function body as trust-ir text.
struct Gen {
    rng: Rng,
    lines: Vec<String>,
    next: usize,
    /// Defined values (section 2.3) visible at the current point, by type name.
    pool: BTreeMap<&'static str, Vec<String>>,
    types: Vec<TyInfo>,
}

impl Gen {
    fn fresh(&mut self) -> String {
        let v = format!("%{}", self.next);
        self.next += 1;
        v
    }
    fn emit(&mut self, ty: TyInfo, rhs: String) -> String {
        let v = self.fresh();
        self.lines.push(format!("    {v} = {rhs}"));
        self.pool.entry(ty.name).or_default().push(v.clone());
        v
    }
    fn constant(&mut self, ty: TyInfo, residue: u128) -> String {
        let text = const_text(ty, residue);
        self.emit(ty, format!("const {} {text}", ty.name))
    }
    fn random_residue(&mut self, ty: TyInfo) -> u128 {
        let m = mask(ty.width);
        match self.rng.below(6) {
            0 => 0,
            1 => 1,
            2 => m,
            3 => 1u128 << (ty.width - 1),
            4 => u128::from(ty.width),
            _ => self.rng.wide() & m,
        }
    }
    fn random_const(&mut self, ty: TyInfo) -> String {
        let r = self.random_residue(ty);
        self.constant(ty, r)
    }
    /// A defined value of `ty` (made if none is visible).
    fn value(&mut self, ty: TyInfo) -> String {
        let n = self.pool.get(ty.name).map_or(0, Vec::len);
        if n == 0 || self.rng.chance(10) {
            if ty.width == 1 {
                let a = self.int_ty();
                let x = self.value(a);
                let y = self.value(a);
                return self.emit(BOOL, format!("icmp ult {} {x}, {y}", a.name));
            }
            return self.random_const(ty);
        }
        // Prefer recent values, so the DAG has depth.
        let pick = if self.rng.chance(60) {
            n - 1 - self.rng.below(n.min(3))
        } else {
            self.rng.below(n)
        };
        self.pool[ty.name][pick].clone()
    }
    fn int_ty(&mut self) -> TyInfo {
        let ints: Vec<TyInfo> = self.types.iter().copied().filter(|t| t.width > 1).collect();
        ints[self.rng.below(ints.len())]
    }
    fn any_ty(&mut self) -> TyInfo {
        self.types[self.rng.below(self.types.len())]
    }

    /// One random graph instruction.
    fn random_op(&mut self) {
        match self.rng.below(10) {
            0..=2 => {
                let t = self.int_ty();
                let op =
                    ["add", "sub", "mul", "and", "or", "xor", "rotl", "rotr"][self.rng.below(8)];
                let a = self.value(t);
                let b = self.value(t);
                self.emit(t, format!("{op} {} {a}, {b}", t.name));
            }
            3 => {
                let t = self.int_ty();
                let op = ["neg", "not", "ctpop", "ctlz", "cttz", "bswap", "bitreverse"]
                    [self.rng.below(7)];
                if op == "bswap" && t.width % 16 != 0 {
                    return;
                }
                let a = self.value(t);
                self.emit(t, format!("{op} {} {a}", t.name));
            }
            4 => {
                let t = self.int_ty();
                let pred = [
                    "eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge",
                ][self.rng.below(10)];
                let a = self.value(t);
                let b = self.value(t);
                self.emit(BOOL, format!("icmp {pred} {} {a}, {b}", t.name));
            }
            5 => {
                let op = ["and", "or", "xor", "band", "bor", "bxor"][self.rng.below(6)];
                let a = self.value(BOOL);
                let b = self.value(BOOL);
                if self.rng.chance(30) {
                    let pred = ["eq", "ne"][self.rng.below(2)];
                    self.emit(BOOL, format!("icmp {pred} bool {a}, {b}"));
                } else {
                    self.emit(BOOL, format!("{op} bool {a}, {b}"));
                }
            }
            6 => {
                let s = self.int_ty();
                let d = self.int_ty();
                let op = if d.width < s.width {
                    "trunc"
                } else if d.width > s.width {
                    if self.rng.chance(50) { "zext" } else { "sext" }
                } else {
                    return;
                };
                let a = self.value(s);
                self.emit(d, format!("{op} {} {a} to {}", s.name, d.name));
            }
            7 => {
                let t = self.any_ty();
                let c = self.value(BOOL);
                let a = self.value(t);
                let b = self.value(t);
                self.emit(t, format!("select {} {c}, {a}, {b}", t.name));
            }
            8 => {
                // A see-through copy of a defined value.
                let t = self.any_ty();
                let a = self.value(t);
                self.emit(t, format!("copy {} {a}", t.name));
            }
            _ => {
                let t = self.any_ty();
                self.random_const(t);
            }
        }
    }

    /// One instance of a rule's lhs shape, so that rules fire.
    fn seeded_shape(&mut self) {
        let t = self.int_ty();
        let n = t.name;
        let w = u128::from(t.width);
        match self.rng.below(24) {
            0 => {
                let x = self.value(t);
                let z = self.constant(t, 0);
                self.emit(t, format!("add {n} {x}, {z}"));
            }
            1 => {
                let x = self.value(t);
                let c = self.random_const(t);
                self.emit(t, format!("add {n} {c}, {x}"));
            }
            2 => {
                let x = self.value(t);
                let one = self.constant(t, 1);
                self.emit(t, format!("mul {n} {x}, {one}"));
            }
            3 => {
                let x = self.value(t);
                let z = self.constant(t, 0);
                self.emit(t, format!("mul {n} {x}, {z}"));
            }
            4 => {
                let x = self.value(t);
                let m = self.constant(t, u128::MAX);
                self.emit(t, format!("mul {n} {x}, {m}"));
            }
            5 => {
                let x = self.value(t);
                self.emit(t, format!("add {n} {x}, {x}"));
            }
            6 => {
                let x = self.value(t);
                let op = ["sub", "xor", "and", "or"][self.rng.below(4)];
                self.emit(t, format!("{op} {n} {x}, {x}"));
            }
            7 => {
                let x = self.value(t);
                let c = self.random_const(t);
                self.emit(t, format!("sub {n} {x}, {c}"));
            }
            8 => {
                let x = self.value(t);
                let z = self.constant(t, 0);
                self.emit(t, format!("sub {n} {z}, {x}"));
            }
            9 => {
                let x = self.value(t);
                let m = self.constant(t, u128::MAX);
                let op = ["or", "and"][self.rng.below(2)];
                self.emit(t, format!("{op} {n} {x}, {m}"));
            }
            10 => {
                let x = self.value(t);
                let op = ["neg", "not"][self.rng.below(2)];
                let a = self.emit(t, format!("{op} {n} {x}"));
                self.emit(t, format!("{op} {n} {a}"));
            }
            11 => {
                let x = self.value(t);
                let y = self.value(t);
                let ny = self.emit(t, format!("neg {n} {y}"));
                self.emit(t, format!("add {n} {x}, {ny}"));
            }
            12 => {
                let x = self.value(t);
                let k = self.rng.below(3) as u128;
                let c = self.constant(t, w * k);
                let op = ["rotl", "rotr"][self.rng.below(2)];
                self.emit(t, format!("{op} {n} {x}, {c}"));
            }
            13 => {
                let x = self.value(t);
                let op = ["add", "mul", "and", "or", "xor"][self.rng.below(5)];
                let a = self.random_const(t);
                let b = self.random_const(t);
                let inner = self.emit(t, format!("{op} {n} {x}, {a}"));
                self.emit(t, format!("{op} {n} {inner}, {b}"));
            }
            14 => {
                let x = self.value(t);
                let pred = ["eq", "ne", "ult", "ule", "slt", "sle"][self.rng.below(6)];
                self.emit(BOOL, format!("icmp {pred} {n} {x}, {x}"));
            }
            15 => {
                let c = self.value(BOOL);
                let x = self.value(t);
                self.emit(t, format!("select {n} {c}, {x}, {x}"));
            }
            16 => {
                let b = self.rng.below(2) as u128;
                let c = self.constant(BOOL, b);
                let x = self.value(t);
                let y = self.value(t);
                self.emit(t, format!("select {n} {c}, {x}, {y}"));
            }
            17 => {
                let op =
                    ["add", "sub", "mul", "and", "or", "xor", "rotl", "rotr"][self.rng.below(8)];
                let a = self.random_const(t);
                let b = self.random_const(t);
                self.emit(t, format!("{op} {n} {a}, {b}"));
            }
            18 => {
                let op = ["neg", "not", "ctpop", "ctlz", "cttz", "bitreverse"][self.rng.below(6)];
                let a = self.random_const(t);
                self.emit(t, format!("{op} {n} {a}"));
            }
            19 => {
                let pred = [
                    "eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge",
                ][self.rng.below(10)];
                let a = self.random_const(t);
                let b = self.random_const(t);
                self.emit(BOOL, format!("icmp {pred} {n} {a}, {b}"));
            }
            20 => {
                let b = self.value(BOOL);
                let k = self.rng.below(2) as u128;
                let c = self.constant(BOOL, k);
                let op = ["band", "bor", "bxor"][self.rng.below(3)];
                self.emit(BOOL, format!("{op} bool {b}, {c}"));
            }
            21 => {
                let b = self.value(BOOL);
                let t1 = self.constant(BOOL, 1);
                let inner = self.emit(BOOL, format!("bxor bool {b}, {t1}"));
                self.emit(BOOL, format!("bxor bool {inner}, {t1}"));
            }
            22 => {
                let op = ["band", "bor", "bxor", "and", "or", "xor"][self.rng.below(6)];
                let a = self.rng.below(2) as u128;
                let b = self.rng.below(2) as u128;
                let a = self.constant(BOOL, a);
                let b = self.constant(BOOL, b);
                self.emit(BOOL, format!("{op} bool {a}, {b}"));
            }
            _ => {
                let b = self.value(BOOL);
                let pred = ["eq", "ne"][self.rng.below(2)];
                let a = self.rng.below(2) as u128;
                let c = self.constant(BOOL, a);
                self.emit(BOOL, format!("icmp {pred} bool {b}, {c}"));
            }
        }
    }

    fn step(&mut self) {
        if self.rng.chance(45) {
            self.seeded_shape();
        } else {
            self.random_op();
        }
    }

    /// A frontier skeleton op over a maybe-poison value: its result is
    /// defined (section 2.3), so graph operators above it are total.
    /// Sometimes the value first passes through a skeleton `select` (whose
    /// result is still maybe-poison, a leaf).
    fn define(&mut self, ty: TyInfo, maybe_poison: &str) -> String {
        let mut source = maybe_poison.to_owned();
        if self.rng.chance(15) {
            // A copy of a maybe-poison value is maybe-poison too.
            let v = self.fresh();
            self.lines
                .push(format!("    {v} = copy {} {source}", ty.name));
            source = v;
        }
        if self.rng.chance(25) {
            let c = self.value(BOOL);
            let other = self.value(ty);
            let v = self.fresh();
            let (a, b) = if self.rng.chance(50) {
                (source.clone(), other)
            } else {
                (other, source.clone())
            };
            self.lines
                .push(format!("    {v} = select {} {c}, {a}, {b}", ty.name));
            source = v;
        }
        if ty.width == 1 {
            match self.rng.below(3) {
                0 => {
                    let f = self.constant(BOOL, 0);
                    self.emit(ty, format!("bxor bool {source}, {f}"))
                }
                1 => {
                    let t = self.constant(BOOL, 1);
                    self.emit(ty, format!("icmp eq bool {source}, {t}"))
                }
                _ => {
                    let o = self.value(BOOL);
                    self.emit(ty, format!("and bool {source}, {o}"))
                }
            }
        } else {
            let n = ty.name;
            match self.rng.below(4) {
                0 => {
                    let z = self.constant(ty, 0);
                    self.emit(ty, format!("xor {n} {source}, {z}"))
                }
                1 => {
                    let o = self.value(ty);
                    self.emit(ty, format!("add {n} {source}, {o}"))
                }
                2 => self.emit(ty, format!("neg {n} {source}")),
                _ => {
                    let o = self.value(ty);
                    self.emit(ty, format!("mul {n} {o}, {source}"))
                }
            }
        }
    }
}

/// The text of random function `index` (deterministic in `index`).
fn random_module_text(index: u64) -> String {
    let mut rng = Rng(0x5EED_0000_0000_0000 ^ index.wrapping_mul(0x1234_5678_9ABC_DEF1));
    // Every fourth module targets 32-bit pointers: isize and usize are then
    // 32 bits wide (section 2.1).
    let pointer32 = index % 4 == 3;
    let mut types = vec![BOOL];
    for _ in 0..=rng.below(2) {
        let mut t = INT_TYS[rng.below(INT_TYS.len())];
        if pointer32 && matches!(t.name, "isize" | "usize") {
            t.width = 32;
        }
        if !types.contains(&t) {
            types.push(t);
        }
    }
    let mut g = Gen {
        rng,
        lines: Vec::new(),
        next: 0,
        pool: BTreeMap::new(),
        types: types.clone(),
    };
    let nparams = 1 + g.rng.below(3);
    let params: Vec<TyInfo> = (0..nparams).map(|_| g.any_ty()).collect();
    let param_values: Vec<String> = params.iter().map(|_| g.fresh()).collect();
    let entry_params: Vec<String> = param_values
        .iter()
        .zip(&params)
        .map(|(v, t)| format!("{v}: {}", t.name))
        .collect();
    let mut blocks: Vec<String> = Vec::new();
    for (v, t) in param_values.iter().zip(&params) {
        g.define(*t, v);
    }
    let ops = 8 + g.rng.below(20);
    for _ in 0..ops {
        g.step();
    }
    let shape = g.rng.below(100);
    let mut current_header = format!("bb0({}):", entry_params.join(", "));
    if shape < 35 {
        let cond = g.value(BOOL);
        let join_ty = g.int_ty();
        g.lines
            .push("    condbr ".to_owned() + &cond + ", bb1, bb2");
        blocks.push(format!("{current_header}\n{}", g.lines.join("\n")));
        g.lines.clear();
        let saved = g.pool.clone();
        let mut arm_values = Vec::new();
        for arm in 1..=2 {
            for _ in 0..(2 + g.rng.below(6)) {
                g.step();
            }
            let v = g.value(join_ty);
            g.lines.push(format!("    br bb3({v})"));
            blocks.push(format!("bb{arm}:\n{}", g.lines.join("\n")));
            g.lines.clear();
            g.pool = saved.clone();
            arm_values.push(v);
        }
        let joined = g.fresh();
        current_header = format!("bb3({joined}: {}):", join_ty.name);
        g.define(join_ty, &joined);
        for _ in 0..(2 + g.rng.below(8)) {
            g.step();
        }
    } else if shape < 60 {
        // A counted loop: bb1 runs four times; graph nodes over bb0 values
        // only may be hoisted out of it, the rest stay in bb1.
        let counter = g.int_ty();
        let n = counter.name;
        let init = g.constant(counter, 0);
        g.lines.push(format!("    br bb1({init})"));
        blocks.push(format!("{current_header}\n{}", g.lines.join("\n")));
        g.lines.clear();
        let i = g.fresh();
        let header = format!("bb1({i}: {n}):");
        let z = g.constant(counter, 0);
        let di = g.emit(counter, format!("xor {n} {i}, {z}"));
        for _ in 0..(2 + g.rng.below(8)) {
            g.step();
        }
        let one = g.constant(counter, 1);
        let next = g.emit(counter, format!("add {n} {di}, {one}"));
        let limit = g.constant(counter, 4);
        let c = g.emit(BOOL, format!("icmp ult {n} {next}, {limit}"));
        g.lines.push(format!("    condbr {c}, bb1({next}), bb2"));
        blocks.push(format!("{header}\n{}", g.lines.join("\n")));
        g.lines.clear();
        current_header = "bb2:".to_owned();
        for _ in 0..(2 + g.rng.below(6)) {
            g.step();
        }
    }
    // Returns: the latest value of each type, plus one random one.
    let mut rets: Vec<(String, TyInfo)> = Vec::new();
    for t in types.clone() {
        if let Some(v) = g.pool.get(t.name).and_then(|vs| vs.last()).cloned()
            && g.rng.chance(70)
        {
            rets.push((v, t));
        }
    }
    let t = g.any_ty();
    let v = g.value(t);
    rets.push((v, t));
    let ret_values: Vec<String> = rets.iter().map(|(v, _)| v.clone()).collect();
    g.lines.push(format!("    ret {}", ret_values.join(", ")));
    blocks.push(format!("{current_header}\n{}", g.lines.join("\n")));
    let param_tys: Vec<&str> = params.iter().map(|t| t.name).collect();
    let ret_tys: Vec<&str> = rets.iter().map(|(_, t)| t.name).collect();
    format!(
        "; TrustIr text format v1\nmodule \"random{index}\"\n{}\nfuncty.0 = ({}) -> ({})\n\nfn @f(functy.0) {{\n{}\n}}\n",
        if pointer32 {
            "target \"wasm32-unknown-unknown\" 4 little\n"
        } else {
            ""
        },
        param_tys.join(", "),
        ret_tys.join(", "),
        blocks.join("\n")
    )
}

const RANDOM_FUNCTIONS: u64 = 320;

fn random_modules() -> &'static [(String, Module)] {
    static RANDOM: OnceLock<Vec<(String, Module)>> = OnceLock::new();
    RANDOM.get_or_init(|| {
        (0..RANDOM_FUNCTIONS)
            .map(|i| {
                let text = random_module_text(i);
                let module = parse_valid(&text);
                (text, module)
            })
            .collect()
    })
}

// ---------------------------------------------------------------------------
// Case 1: determinism.

fn assert_same_run(
    a: &Result<Optimized, trust_cg_eqsat::Decline>,
    b: &Result<Optimized, trust_cg_eqsat::Decline>,
    what: &str,
) {
    match (a, b) {
        (Err(x), Err(y)) => assert_eq!(x, y, "{what}: declines differ"),
        (Ok(x), Ok(y)) => {
            assert_eq!(x.derivation, y.derivation, "{what}: derivations differ");
            assert_eq!(x.function, y.function, "{what}: bodies differ");
            assert_eq!(
                format!("{:?}", x.function),
                format!("{:?}", y.function),
                "{what}: printed bodies differ"
            );
            assert_eq!(x.rewritten, y.rewritten, "{what}");
            assert_eq!(x.stats, y.stats, "{what}: stats differ");
        }
        _ => panic!("{what}: one run declined and the other did not"),
    }
}

#[test]
fn determinism_byte_identical_derivations() {
    let first = honest_rules();
    let second = honest_rules();
    let config = EngineConfig::default();
    let mut functions = 0usize;
    for entry in corpus() {
        let module = &entry.module;
        let mut out_a = module.clone();
        let mut out_b = module.clone();
        for (index, function) in module.functions.iter().enumerate() {
            let a = optimize_function(module, function, &first, &config);
            let b = optimize_function(module, function, &second, &config);
            let what = format!("{}:@{}", entry.file, function.name);
            assert_same_run(&a, &b, &what);
            if let (Ok(a), Ok(b)) = (a, b) {
                out_a.functions[index] = a.function;
                out_b.functions[index] = b.function;
            }
            functions += 1;
        }
        // The printed modules with every output substituted are identical.
        let text_a = trust_ir::format::text_checked(&out_a).expect("prints");
        let text_b = trust_ir::format::text_checked(&out_b).expect("prints");
        assert_eq!(text_a, text_b, "{}", entry.file);
    }
    for (text, module) in random_modules() {
        let function = function_named(module, "f");
        let a = optimize_function(module, function, &first, &config);
        let b = optimize_function(module, function, &second, &config);
        assert_same_run(&a, &b, text);
        functions += 1;
    }
    eprintln!("determinism: {functions} functions, two runs each, identical");
}

// ---------------------------------------------------------------------------
// Case 2 and 3: the rule mutants.

const MUTANTS: [&str; 10] = [
    "missing_side_condition.rules",
    "one_way_reversed.rules",
    "panic_only_sdiv_neg_one.rules",
    "panic_only_udiv_self.rules",
    "wrong_boolean_constant.rules",
    "wrong_constant.rules",
    "wrong_fold.rules",
    "wrong_operand_order.rules",
    "wrong_select_arm.rules",
    "wrong_width.rules",
];

#[test]
fn mutant_set_is_the_committed_set() {
    let dir = crate_dir().join("tests/wrong_rules");
    let mut found: Vec<String> = std::fs::read_dir(&dir)
        .expect("wrong_rules directory")
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect();
    found.sort();
    let expected: Vec<String> = MUTANTS.iter().map(|s| (*s).to_owned()).collect();
    assert_eq!(
        found, expected,
        "tests/wrong_rules differs from the committed set"
    );
}

/// A mutant file and its header comments.
struct Mutant {
    text: String,
    /// The rule's name (the same as the honest rule it mutates, if any).
    name: String,
    mutant_of: String,
    subject: String,
    consts: BTreeMap<String, i128>,
}

fn mutant(file: &str) -> Mutant {
    let text = std::fs::read_to_string(crate_dir().join("tests/wrong_rules").join(file))
        .unwrap_or_else(|e| panic!("{file}: {e}"));
    let mut mutant_of = None;
    let mut subject = None;
    let mut consts = BTreeMap::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("; mutant-of: ") {
            mutant_of = Some(rest.trim().to_owned());
        } else if let Some(rest) = line.strip_prefix("; subject: ") {
            subject = Some(rest.trim().to_owned());
        } else if let Some(rest) = line.strip_prefix("; const: ") {
            let (name, value) = rest.split_once('=').expect("const header");
            consts.insert(
                name.trim().to_owned(),
                value.trim().parse().expect("const value"),
            );
        }
    }
    let texts = rules::canonical_texts(&text).expect("mutant tokenizes");
    assert_eq!(texts.len(), 1, "{file}: one rule per mutant file");
    Mutant {
        name: texts[0].0.clone(),
        text,
        mutant_of: mutant_of.expect("mutant-of header"),
        subject: subject.expect("subject header"),
        consts,
    }
}

/// Patches the digest of rule `name` in a derivation's rule table.
fn forge_digest(derivation: &[u8], name: &str, digest: [u8; 32]) -> Vec<u8> {
    let mut out = derivation.to_vec();
    let (_, _, at) = rule_table(derivation)
        .into_iter()
        .find(|(n, _, _)| n == name)
        .expect("rule in table");
    out[at..at + 32].copy_from_slice(&digest);
    out
}

/// The classes a forged-digest derivation may be refused with: the replayed
/// honest statement does not conclude what is claimed, or its domain,
/// premises or side conditions do not fit.
const SEMANTIC: [&str; 7] = [
    "conclusion_mismatch",
    "claim_mismatch",
    "operand_unjustified",
    "side_condition_failed",
    "premise_mismatch",
    "type_not_in_domain",
    "binding_mismatch",
];

/// What the interpreter must show about a total mutant's rewrite.
#[derive(PartialEq, Eq)]
enum Wrongness {
    /// The rewritten body computes a different value on some input.
    Differs,
    /// The rewrite is semantically true; the wrongness is the direction.
    AgreesButDirectionIsWrong,
}

/// Runs the engine with the mutant alone on `subject_text` and checks every
/// claim of case 3 for a total-operator mutant. Returns the forged-digest
/// rejection class.
fn total_mutant(file: &str, subject_text: &str, wrongness: Wrongness) -> &'static str {
    let m = mutant(file);
    assert_eq!(
        m.mutant_of, m.name,
        "{file}: a mutant of a registered rule keeps its name"
    );
    let mutant_rules = RuleSet::parse(&m.text).unwrap_or_else(|e| panic!("{file}: {e:?}"));
    Registry::parse(&m.text).unwrap_or_else(|e| panic!("{file}: checker refuses: {e}"));
    let honest = honest_rules();
    let honest_rule = honest
        .rules()
        .iter()
        .find(|r| r.name() == m.name)
        .expect("honest rule of the same name");
    let mutant_rule = &mutant_rules.rules()[0];
    assert_ne!(
        mutant_rule.statement_digest(),
        honest_rule.statement_digest(),
        "{file}: the mutant states the same statement"
    );
    assert!(
        subject_text.contains(&format!(" {}", m.subject)),
        "{file}: subject type"
    );

    let module = parse_valid(subject_text);
    let input = function_named(&module, "f");
    let result = optimize_function(&module, input, &mutant_rules, &EngineConfig::default())
        .unwrap_or_else(|d| panic!("{file}: declined: {d}"));
    // A mutant that never fires proves nothing: it must be used.
    assert!(
        result.rewritten,
        "{file}: the mutant did not rewrite the subject: {:?}",
        result.stats
    );
    assert!(
        result.stats.rule_matches.get(&m.name).copied().unwrap_or(0) > 0,
        "{file}: no match recorded: {:?}",
        result.stats.rule_matches
    );
    let table = rule_table(&result.derivation);
    assert!(
        table
            .iter()
            .any(|(n, d, _)| *n == m.name && *d == mutant_rule.statement_digest()),
        "{file}: the derivation does not name the mutant: {table:?}"
    );
    let output_module = assert_validates_with(&module, &result.function, file);

    // (a) As emitted: the registry holds a different statement under the name.
    let registry = honest_registry();
    let emitted = check(
        &module,
        input,
        &result.function,
        &result.derivation,
        &registry,
    )
    .expect_err("the checker accepted a mutant derivation");
    assert!(
        matches!(
            emitted,
            Rejection::DigestMismatch { .. } | Rejection::UnknownRule { .. }
        ),
        "{file}: as emitted: {emitted:?}"
    );

    // (b) With the honest digest forged in: refused for the semantic reason.
    let forged = forge_digest(&result.derivation, &m.name, honest_rule.statement_digest());
    let refused = check(&module, input, &result.function, &forged, &registry)
        .expect_err("the checker accepted a forged-digest mutant derivation");
    assert!(
        SEMANTIC.contains(&refused.class()),
        "{file}: forged digest refused for a non-semantic reason: {refused:?}"
    );

    // The interpreter: is the rewrite really wrong?
    let Comparison {
        returned,
        differing,
        ..
    } = compare_runs(&module, input, &output_module, 64, 10_000, 7);
    assert!(returned > 0, "{file}: the subject never returned");
    match wrongness {
        Wrongness::Differs => assert!(
            !differing.is_empty(),
            "{file}: the mutant's rewrite agrees with the input on every sampled input"
        ),
        Wrongness::AgreesButDirectionIsWrong => assert!(
            differing.is_empty(),
            "{file}: the reversed refinement changed a value: {:?}",
            differing.first()
        ),
    }
    refused.class()
}

fn subject(template: &str, ty: &str) -> String {
    format!(
        "; TrustIr text format v1\nmodule \"m\"\n\n{}",
        template.replace("{T}", ty)
    )
}

/// mul_one stated as `x * 2 = x`: wrong at every x != 0 (x = 1 gives 2 vs 1).
#[test]
fn mutant_wrong_constant() {
    let m = mutant("wrong_constant.rules");
    let text = subject(
        "functy.0 = ({T}) -> ({T})

fn @f(functy.0) {
bb0(%0: {T}):
    %1 = const {T} 0
    %2 = xor {T} %0, %1
    %3 = const {T} 2
    %4 = mul {T} %2, %3
    ret %4
}
",
        &m.subject,
    );
    let class = total_mutant("wrong_constant.rules", &text, Wrongness::Differs);
    eprintln!("wrong_constant: forged digest refused as {class}");
}

/// mul_255_neg_i8 widened to i16: 255 is -1 only at width 8, so at i16
/// `x * 255` is not `-x` (x = 1 gives 255 vs 65535). The honest domain is
/// {i8, u8}: the forged derivation's instance type is outside it.
#[test]
fn mutant_wrong_width() {
    let m = mutant("wrong_width.rules");
    let text = subject(
        "functy.0 = ({T}) -> ({T})

fn @f(functy.0) {
bb0(%0: {T}):
    %1 = const {T} 0
    %2 = xor {T} %0, %1
    %3 = const {T} 255
    %4 = mul {T} %2, %3
    ret %4
}
",
        &m.subject,
    );
    let class = total_mutant("wrong_width.rules", &text, Wrongness::Differs);
    assert_eq!(class, "type_not_in_domain");
}

/// rotl_full without `(zero_mod_width ?c)`: rotating by c = 3 is not the
/// identity (x = 1 gives 8 vs 1). Replaying the honest rule re-evaluates the
/// side condition (or finds the missing premise).
#[test]
fn mutant_missing_side_condition() {
    let m = mutant("missing_side_condition.rules");
    let c = m.consts["c"];
    let text = subject(
        &format!(
            "functy.0 = ({{T}}) -> ({{T}})

fn @f(functy.0) {{
bb0(%0: {{T}}):
    %1 = const {{T}} 0
    %2 = xor {{T}} %0, %1
    %3 = const {{T}} {c}
    %4 = rotl {{T}} %2, %3
    ret %4
}}
"
        ),
        &m.subject,
    );
    let class = total_mutant("missing_side_condition.rules", &text, Wrongness::Differs);
    assert!(
        ["side_condition_failed", "premise_mismatch"].contains(&class),
        "{class}"
    );
}

/// double_to_mul is stated `refines` from `x + x` to `x * 2`; the mutant
/// states it from `x * 2` to `x + x`, the backwards use. The values agree
/// (the interpreter shows it), so the wrongness is the direction: the
/// checker refuses a conclusion the registered statement does not give, and
/// refuses a `Sym` of the registered refinement.
#[test]
fn mutant_one_way_reversed() {
    let m = mutant("one_way_reversed.rules");
    let text = subject(
        "functy.0 = ({T}) -> ({T})

fn @f(functy.0) {
bb0(%0: {T}):
    %1 = const {T} 0
    %2 = xor {T} %0, %1
    %3 = const {T} 2
    %4 = mul {T} %2, %3
    ret %4
}
",
        &m.subject,
    );
    let class = total_mutant(
        "one_way_reversed.rules",
        &text,
        Wrongness::AgreesButDirectionIsWrong,
    );
    assert!(
        [
            "conclusion_mismatch",
            "claim_mismatch",
            "operand_unjustified"
        ]
        .contains(&class),
        "{class}"
    );
    // The backwards use spelled as Sym of the honest refinement.
    let (module, input, output, derivation) = sym_of_refines_case();
    let refused = check(&module, &input, &output, &derivation, &honest_registry())
        .expect_err("Sym of a refines rule accepted");
    assert_eq!(refused.class(), "sym_of_refines", "{refused:?}");
}

/// add_neg with the sides of the subtraction swapped: `x + -y` is `x - y`,
/// not `y - x` (x = 1, y = 0 gives 1 vs -1).
#[test]
fn mutant_wrong_operand_order() {
    let m = mutant("wrong_operand_order.rules");
    let text = subject(
        "functy.0 = ({T}, {T}) -> ({T})

fn @f(functy.0) {
bb0(%0: {T}, %1: {T}):
    %2 = const {T} 0
    %3 = xor {T} %0, %2
    %4 = xor {T} %1, %2
    %5 = neg {T} %4
    %6 = add {T} %3, %5
    ret %6
}
",
        &m.subject,
    );
    let class = total_mutant("wrong_operand_order.rules", &text, Wrongness::Differs);
    eprintln!("wrong_operand_order: forged digest refused as {class}");
}

/// icmp_ult_self stated as `x <u x = true`: it is false at every x. The
/// subject defines `true` first so the extracted constant is shared and the
/// rewrite is strictly cheaper.
#[test]
fn mutant_wrong_boolean_constant() {
    let m = mutant("wrong_boolean_constant.rules");
    let text = subject(
        "functy.0 = ({T}) -> (bool, bool)

fn @f(functy.0) {
bb0(%0: {T}):
    %1 = const bool true
    %2 = const {T} 0
    %3 = xor {T} %0, %2
    %4 = icmp ult {T} %3, %3
    ret %1, %4
}
",
        &m.subject,
    );
    let class = total_mutant("wrong_boolean_constant.rules", &text, Wrongness::Differs);
    eprintln!("wrong_boolean_constant: forged digest refused as {class}");
}

/// select_true choosing the else arm: `select true x y` is x (x = 0, y = 1
/// gives 0 vs 1).
#[test]
fn mutant_wrong_select_arm() {
    let m = mutant("wrong_select_arm.rules");
    let text = subject(
        "functy.0 = ({T}, {T}) -> ({T})

fn @f(functy.0) {
bb0(%0: {T}, %1: {T}):
    %2 = const {T} 0
    %3 = xor {T} %0, %2
    %4 = xor {T} %1, %2
    %5 = const bool true
    %6 = select {T} %5, %3, %4
    ret %6
}
",
        &m.subject,
    );
    let class = total_mutant("wrong_select_arm.rules", &text, Wrongness::Differs);
    eprintln!("wrong_select_arm: forged digest refused as {class}");
}

/// fold_sub evaluating `a + b`: 7 - 5 is 2, the mutant folds it to 12.
#[test]
fn mutant_wrong_fold() {
    let m = mutant("wrong_fold.rules");
    let a = m.consts["a"];
    let b = m.consts["b"];
    let text = subject(
        &format!(
            "functy.0 = ({{T}}) -> ({{T}})

fn @f(functy.0) {{
bb0(%0: {{T}}):
    %1 = const {{T}} {a}
    %2 = const {{T}} {b}
    %3 = sub {{T}} %1, %2
    %4 = xor {{T}} %0, %3
    ret %4
}}
"
        ),
        &m.subject,
    );
    let class = total_mutant("wrong_fold.rules", &text, Wrongness::Differs);
    assert!(
        [
            "conclusion_mismatch",
            "claim_mismatch",
            "operand_unjustified"
        ]
        .contains(&class),
        "{class}"
    );
}

/// A non-total mutant: both rule parsers refuse it; the derivation an
/// unchecked engine would emit is refused by the checker (the rule is not in
/// the registry); and the interpreter shows the input has undefined
/// behaviour at `bad` where the rewritten body returns a value.
fn panic_only_mutant(
    file: &str,
    input_text: &str,
    kept_text: &str,
    removed_text: &str,
    claim: impl Fn(&mut DerivationBuilder, [u8; 32]) -> trust_cg_eqsat::derivation::ProofRef,
    bad: &[InterpretValue],
) {
    let m = mutant(file);
    assert!(m.mutant_of.starts_with("(none"), "{file}: {}", m.mutant_of);
    let engine_error = RuleSet::parse(&m.text).expect_err("the engine admitted a non-total rule");
    assert_eq!(
        engine_error.kind.as_str(),
        "non_total_operator",
        "{engine_error:?}"
    );
    Registry::parse(&m.text).expect_err("the checker admitted a non-total rule");
    assert!(
        honest_registry().statement_digest(&m.name).is_none(),
        "{file}: registered"
    );

    let texts = rules::canonical_texts(&m.text).unwrap();
    let digest = rules::statement_digest(&texts[0].1);
    let module = parse_valid(input_text);
    let input = function_named(&module, "f");
    let registry = honest_registry();

    // The derivation an unchecked engine would emit.
    let mut builder = DerivationBuilder::new("f");
    let proof = claim(&mut builder, digest);
    builder.claim(proof);
    let derivation = builder.finish();
    assert_eq!(rule_table(&derivation)[0].0, m.name);

    // (i) The division kept in the skeleton, its use replaced.
    let kept = parse_valid(kept_text);
    let kept_f = function_named(&kept, "f");
    let refused = check(&module, input, kept_f, &derivation, &registry)
        .expect_err("a non-total rule's derivation accepted");
    assert_eq!(refused.class(), "unknown_rule", "{refused:?}");

    // (ii) The division removed, as an engine treating it as pure would.
    let removed = parse_valid(removed_text);
    let removed_f = function_named(&removed, "f");
    let refused = check(&module, input, removed_f, &derivation, &registry)
        .expect_err("a removed division accepted");
    assert_eq!(refused.class(), "skeleton_count_mismatch", "{refused:?}");

    // The input has undefined behaviour at `bad`; the removed form returns.
    let before = outcome(&module, input, bad, 10_000);
    let after = outcome(&removed, removed_f, bad, 10_000);
    assert_eq!(
        before,
        Outcome::Failed(InterpretErrorCode::UndefinedBehavior, "None".to_owned()),
        "{file}: input at {bad:?}"
    );
    assert!(
        matches!(after, Outcome::Returned(_)),
        "{file}: output at {bad:?}: {after:?}"
    );
}

/// `x udiv x = 1` holds only where the division is defined: at x = 0 the
/// input is undefined behaviour and the rewrite returns 1.
#[test]
fn mutant_panic_only_udiv_self() {
    let m = mutant("panic_only_udiv_self.rules");
    let t = &m.subject;
    let head = format!(
        "; TrustIr text format v1\nmodule \"m\"\n\nfuncty.0 = ({t}) -> ({t})\n\nfn @f(functy.0) {{\nbb0(%0: {t}):\n    %1 = const {t} 0\n    %2 = xor {t} %0, %1\n"
    );
    let input = format!("{head}    %3 = udiv {t} %2, %2\n    ret %3\n}}\n");
    let kept = format!("{head}    %3 = udiv {t} %2, %2\n    %4 = const {t} 1\n    ret %4\n}}\n");
    let removed = format!("{head}    %4 = const {t} 1\n    ret %4\n}}\n");
    let ty = ScalarTy::from_name(t).unwrap();
    panic_only_mutant(
        "panic_only_udiv_self.rules",
        &input,
        &kept,
        &removed,
        |b, digest| {
            let rule = b.rule(&m.name, digest);
            let x = b.result(0, 0, 0);
            b.rule_step(rule, ty, &[("x", x)], 0)
        },
        &[InterpretValue::int(Ty::U32, 0).unwrap()],
    );
}

/// `x sdiv -1 = -x` holds only where the division is defined: at x = MIN
/// the input is undefined behaviour and the rewrite returns MIN.
#[test]
fn mutant_panic_only_sdiv_neg_one() {
    let m = mutant("panic_only_sdiv_neg_one.rules");
    let t = &m.subject;
    let head = format!(
        "; TrustIr text format v1\nmodule \"m\"\n\nfuncty.0 = ({t}) -> ({t})\n\nfn @f(functy.0) {{\nbb0(%0: {t}):\n    %1 = const {t} 0\n    %2 = xor {t} %0, %1\n    %3 = const {t} -1\n"
    );
    let input = format!("{head}    %4 = sdiv {t} %2, %3\n    ret %4\n}}\n");
    let kept = format!("{head}    %4 = sdiv {t} %2, %3\n    %5 = neg {t} %2\n    ret %5\n}}\n");
    let removed = format!("{head}    %5 = neg {t} %2\n    ret %5\n}}\n");
    let ty = ScalarTy::from_name(t).unwrap();
    panic_only_mutant(
        "panic_only_sdiv_neg_one.rules",
        &input,
        &kept,
        &removed,
        |b, digest| {
            let rule = b.rule(&m.name, digest);
            let x = b.result(0, 0, 0);
            b.rule_step(rule, ty, &[("x", x)], 0)
        },
        &[InterpretValue::int(Ty::I32, i128::from(i32::MIN)).unwrap()],
    );
}

// ---------------------------------------------------------------------------
// Cases 4 and 5: skeleton changes the checker must refuse.

/// A division guarded by `b != 0`, then the same body with the division
/// hoisted above the guard. A graph node may be hoisted (it is total); a
/// division is skeleton (zero divisor is undefined behaviour), so the hoist
/// adds undefined behaviour at b = 0, and the checker refuses it.
#[test]
fn hoisted_division_above_guard_is_rejected() {
    let input_text = "; TrustIr text format v1
module \"m\"

functy.0 = (u32, u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: u32):
    %2 = const u32 0
    %3 = icmp ne u32 %1, %2
    condbr %3, bb1, bb2
bb1:
    %4 = udiv u32 %0, %1
    br bb3(%4)
bb2:
    br bb3(%2)
bb3(%5: u32):
    ret %5
}
";
    let output_text = input_text
        .replace("    %4 = udiv u32 %0, %1\n", "")
        .replace("    condbr %3", "    %4 = udiv u32 %0, %1\n    condbr %3");
    assert_ne!(input_text, output_text);
    let module = parse_valid(input_text);
    let hoisted = parse_valid(&output_text);
    let input = function_named(&module, "f");
    let output = function_named(&hoisted, "f");
    let refused = check(
        &module,
        input,
        output,
        &header_only("f"),
        &honest_registry(),
    )
    .expect_err("hoisted division accepted");
    assert!(
        refused.class().starts_with("skeleton_"),
        "refused for another reason: {refused:?}"
    );
    // The engine never does this: it leaves the body alone.
    let result =
        optimize_function(&module, input, &honest_rules(), &EngineConfig::default()).unwrap();
    assert_eq!(result.function.blocks[1].body.len(), 2);

    let zero = [
        InterpretValue::int(Ty::U32, 7).unwrap(),
        InterpretValue::int(Ty::U32, 0).unwrap(),
    ];
    assert_eq!(
        outcome(&module, input, &zero, 1000),
        Outcome::Returned(vec![InterpretValue::int(Ty::U32, 0).unwrap()])
    );
    assert!(matches!(
        outcome(&hoisted, output, &zero, 1000),
        Outcome::Failed(InterpretErrorCode::UndefinedBehavior, _)
    ));
}

/// Two stores, the second through a pointer that aliases the first exactly
/// when `c` is true; the function loads the first address back. Swapping the
/// stores changes the loaded value when they alias, so store order is
/// observable and the checker must refuse the swap.
#[test]
fn swapped_stores_are_rejected() {
    let input_text = "; TrustIr text format v1
module \"m\"

functy.0 = (u32, u32, bool) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: u32, %2: bool):
    %3 = alloca u32
    %4 = alloca u32
    %5 = select ptr %2, %3, %4
    store u32 %0, ptr %3
    store u32 %1, ptr %5
    %6 = load u32, ptr %3
    ret %6
}
";
    let output_text = input_text.replace(
        "    store u32 %0, ptr %3\n    store u32 %1, ptr %5\n",
        "    store u32 %1, ptr %5\n    store u32 %0, ptr %3\n",
    );
    assert_ne!(input_text, output_text);
    let module = parse_valid(input_text);
    let swapped = parse_valid(&output_text);
    let input = function_named(&module, "f");
    let output = function_named(&swapped, "f");
    let refused = check(
        &module,
        input,
        output,
        &header_only("f"),
        &honest_registry(),
    )
    .expect_err("swapped stores accepted");
    eprintln!("swapped stores refused as {}", refused.class());

    let args = |c: bool| {
        [
            InterpretValue::int(Ty::U32, 1).unwrap(),
            InterpretValue::int(Ty::U32, 2).unwrap(),
            InterpretValue::bool(c),
        ]
    };
    // Aliasing: the order decides the loaded value.
    assert_eq!(
        outcome(&module, input, &args(true), 1000),
        Outcome::Returned(vec![InterpretValue::int(Ty::U32, 2).unwrap()])
    );
    assert_eq!(
        outcome(&swapped, output, &args(true), 1000),
        Outcome::Returned(vec![InterpretValue::int(Ty::U32, 1).unwrap()])
    );
    // Not aliasing: both return the first value.
    assert_eq!(
        outcome(&module, input, &args(false), 1000),
        outcome(&swapped, output, &args(false), 1000)
    );
}

// ---------------------------------------------------------------------------
// Case 6: the checker shares no code with the engine.

/// `(table, dependency name, line)` for every dependency entry of a manifest.
fn manifest_dependencies(toml: &str) -> Vec<(String, String, String)> {
    let is_dep_table = |segment: &str| {
        matches!(
            segment,
            "dependencies" | "dev-dependencies" | "build-dependencies"
        )
    };
    let mut out = Vec::new();
    let mut table = String::new();
    let mut sub_dependency: Option<String> = None;
    for raw in toml.lines() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') {
            table = line
                .trim_matches(|c| c == '[' || c == ']')
                .trim()
                .to_owned();
            let segments: Vec<&str> = table.split('.').collect();
            sub_dependency = None;
            if segments.len() >= 2 && is_dep_table(segments[segments.len() - 2]) {
                let name = segments[segments.len() - 1].trim_matches('"').to_owned();
                sub_dependency = Some(name.clone());
                out.push((table.clone(), name, line.to_owned()));
            }
            continue;
        }
        let last = table.rsplit('.').next().unwrap_or("");
        if is_dep_table(last) {
            if let Some((key, _)) = line.split_once('=') {
                out.push((
                    table.clone(),
                    key.trim().trim_matches('"').to_owned(),
                    line.to_owned(),
                ));
            }
        } else if let Some(name) = &sub_dependency {
            out.push((table.clone(), name.clone(), line.to_owned()));
        }
    }
    out
}

/// Whether `text` names the engine crate (and not the checker crate) as a
/// Rust path (`trust_cg_eqsat`), or also as a package name when `package`.
/// The hyphenated form in Rust code is only a string: section 5.2's digest
/// domain `trust-cg-eqsat.rule-statement.v1` is one, and path strings into
/// the engine's directory are checked separately.
fn names_engine(text: &str, package: bool) -> bool {
    let needles: &[&str] = if package {
        &["trust-cg-eqsat", "trust_cg_eqsat"]
    } else {
        &["trust_cg_eqsat"]
    };
    for needle in needles {
        let mut from = 0;
        while let Some(at) = text[from..].find(needle) {
            let end = from + at + needle.len();
            let rest = &text[end..];
            if !(rest.starts_with("-check") || rest.starts_with("_check")) {
                return true;
            }
            from = end;
        }
    }
    false
}

/// Every file under `dir`, skipping only the directory `skip` (a crate's own
/// build directory), never a nested directory that happens to share its
/// name. Symlinks are refused: a crate never reaches another one through a
/// link.
fn walk(dir: &Path, skip: Option<&Path>, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
        let path = entry.unwrap().path();
        let meta = std::fs::symlink_metadata(&path).unwrap();
        assert!(
            !meta.file_type().is_symlink(),
            "symlink in a crate: {}",
            path.display()
        );
        if meta.is_dir() {
            if skip == Some(path.as_path()) {
                continue;
            }
            walk(&path, skip, out);
        } else {
            out.push(path);
        }
    }
}

/// Every file of the crate at `root` but its `target` directory.
fn crate_files(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    walk(root, Some(&root.join("target")), &mut out);
    out.sort();
    out
}

/// A token of Rust source for the no-shared-code scan.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    /// An identifier or keyword; a raw identifier without its `r#`.
    Ident(String),
    /// A string, character or number literal, with its source text.
    Lit(String),
    /// One punctuation character.
    Punct(char),
}

/// Lexes Rust source: whitespace and comments (nested block comments
/// included) are dropped, literals are single tokens (so a `//` or a quote
/// inside one hides nothing), identifiers are maximal runs. A source this
/// lexer cannot read (an unterminated comment or literal) is an error, and
/// the scan flags it.
fn lex(text: &str) -> Result<Vec<Tok>, String> {
    let c: Vec<char> = text.chars().collect();
    let at = |i: usize| c.get(i).copied();
    let is_ident_start = |ch: char| ch == '_' || ch.is_alphabetic();
    let is_ident = |ch: char| ch == '_' || ch.is_alphanumeric();
    // A quoted literal from the quote at `i`; returns the index after it.
    let quoted = |mut i: usize, quote: char| -> Result<usize, String> {
        i += 1;
        while let Some(ch) = at(i) {
            if ch == '\\' {
                i += 2;
            } else if ch == quote {
                return Ok(i + 1);
            } else {
                i += 1;
            }
        }
        Err(format!("unterminated {quote} literal"))
    };
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(ch) = at(i) {
        if ch.is_whitespace() {
            i += 1;
        } else if ch == '/' && at(i + 1) == Some('/') {
            while at(i).is_some_and(|ch| ch != '\n') {
                i += 1;
            }
        } else if ch == '/' && at(i + 1) == Some('*') {
            let mut depth = 0usize;
            loop {
                match (at(i), at(i + 1)) {
                    (Some('/'), Some('*')) => {
                        depth += 1;
                        i += 2;
                    }
                    (Some('*'), Some('/')) => {
                        depth -= 1;
                        i += 2;
                        if depth == 0 {
                            break;
                        }
                    }
                    (Some(_), _) => i += 1,
                    (None, _) => return Err("unterminated block comment".to_owned()),
                }
            }
        } else if is_ident_start(ch) {
            let start = i;
            while at(i).is_some_and(is_ident) {
                i += 1;
            }
            let word: String = c[start..i].iter().collect();
            let mut hashes = 0;
            while at(i + hashes) == Some('#') {
                hashes += 1;
            }
            let raw_prefix = matches!(word.as_str(), "r" | "br" | "cr");
            if raw_prefix && at(i + hashes) == Some('"') {
                // A raw string: `"` then the same number of `#`.
                let mut j = i + hashes + 1;
                loop {
                    match at(j) {
                        Some('"') if (1..=hashes).all(|k| at(j + k) == Some('#')) => {
                            j += 1 + hashes;
                            break;
                        }
                        Some(_) => j += 1,
                        None => return Err("unterminated raw string".to_owned()),
                    }
                }
                out.push(Tok::Lit(c[start..j].iter().collect()));
                i = j;
            } else if word == "r" && hashes == 1 && at(i + 1).is_some_and(is_ident_start) {
                // A raw identifier.
                let s = i + 1;
                i = s;
                while at(i).is_some_and(is_ident) {
                    i += 1;
                }
                out.push(Tok::Ident(c[s..i].iter().collect()));
            } else if matches!(word.as_str(), "b" | "c") && at(i) == Some('"') {
                let end = quoted(i, '"')?;
                out.push(Tok::Lit(c[start..end].iter().collect()));
                i = end;
            } else if word == "b" && at(i) == Some('\'') {
                let end = quoted(i, '\'')?;
                out.push(Tok::Lit(c[start..end].iter().collect()));
                i = end;
            } else {
                out.push(Tok::Ident(word));
            }
        } else if ch.is_ascii_digit() {
            let start = i;
            while at(i).is_some_and(|ch| {
                is_ident(ch) || (ch == '.' && at(i + 1).is_some_and(|n| n.is_ascii_digit()))
            }) {
                i += 1;
            }
            out.push(Tok::Lit(c[start..i].iter().collect()));
        } else if ch == '"' {
            let end = quoted(i, '"')?;
            out.push(Tok::Lit(c[i..end].iter().collect()));
            i = end;
        } else if ch == '\'' {
            // A character literal (`'x'`, `'\n'`) or a lifetime or label.
            if at(i + 1) == Some('\\') || (at(i + 1).is_some() && at(i + 2) == Some('\'')) {
                let end = quoted(i, '\'')?;
                out.push(Tok::Lit(c[i..end].iter().collect()));
                i = end;
            } else {
                out.push(Tok::Punct('\''));
                i += 1;
            }
        } else {
            out.push(Tok::Punct(ch));
            i += 1;
        }
    }
    Ok(out)
}

/// Identifiers no checker source may contain, used or not: the include
/// macros (renamed imports need their name too), the engine crate's path,
/// the manifest-directory variable, and `path` (an attribute key, also when
/// a macro pastes it into an attribute).
const FORBIDDEN_IDENTS: [&str; 6] = [
    "include",
    "include_str",
    "include_bytes",
    "trust_cg_eqsat",
    "CARGO_MANIFEST_DIR",
    "path",
];

/// Why the no-shared-code scan flags a Rust source (empty: it does not).
fn scan_rust_source(text: &str) -> Vec<String> {
    let tokens = match lex(text) {
        Ok(tokens) => tokens,
        Err(error) => return vec![format!("unlexable: {error}")],
    };
    let mut reasons = Vec::new();
    for (i, token) in tokens.iter().enumerate() {
        match token {
            Tok::Ident(word) if FORBIDDEN_IDENTS.contains(&word.as_str()) => {
                reasons.push(format!("identifier `{word}`"));
            }
            Tok::Ident(word)
                if (word == "env" || word == "option_env")
                    && tokens.get(i + 1) == Some(&Tok::Punct('!')) =>
            {
                reasons.push(format!("`{word}!`"));
            }
            Tok::Lit(text) if text.contains("CARGO_MANIFEST_DIR") => {
                reasons.push("a literal naming CARGO_MANIFEST_DIR".to_owned());
            }
            Tok::Punct('#') => {
                // `#[...]` or `#![...]`: any attribute naming `path`.
                let mut j = i + 1;
                if tokens.get(j) == Some(&Tok::Punct('!')) {
                    j += 1;
                }
                if tokens.get(j) != Some(&Tok::Punct('[')) {
                    continue;
                }
                let mut depth = 0usize;
                for token in &tokens[j..] {
                    match token {
                        Tok::Punct('[') => depth += 1,
                        Tok::Punct(']') => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        Tok::Ident(word) if word == "path" => {
                            reasons.push("an attribute naming `path`".to_owned());
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
    reasons
}

/// The no-shared-code scan of every file of a crate tree at `root` (its own
/// `target` directory excepted): `(file, reason)` for each finding. Rust
/// sources get the token scan; every file but the manifest must not spell
/// a path into the engine's directory; a build script is refused (it could
/// write engine code into the tree before compilation).
fn scan_crate_tree(root: &Path) -> Vec<(PathBuf, String)> {
    let mut findings = Vec::new();
    for path in crate_files(root) {
        // Lossy: a non-UTF-8 file is still scanned, never skipped.
        let text = String::from_utf8_lossy(&std::fs::read(&path).unwrap()).into_owned();
        if path.extension().is_some_and(|e| e == "rs") {
            for reason in scan_rust_source(&text) {
                findings.push((path.clone(), reason));
            }
        }
        if path != root.join("Cargo.toml")
            && (text.contains("trust-cg-eqsat/") || text.contains("../trust-cg-eqsat"))
        {
            findings.push((
                path.clone(),
                "a path into the engine's directory".to_owned(),
            ));
        }
        if path == root.join("build.rs") {
            findings.push((path.clone(), "a build script".to_owned()));
        }
    }
    findings
}

/// The checker's manifest: the tables a library crate needs and nothing
/// that points Cargo at other sources (`[lib]`/`[[bin]]`/... `path`, a
/// `build` script, `[patch]`); its `[dependencies]` are trust-ir only and no
/// table of any kind (dev, build, target-specific) names the engine.
fn assert_checker_manifest(toml: &str) {
    let deps = manifest_dependencies(toml);
    let normal: BTreeSet<&str> = deps
        .iter()
        .filter(|(table, _, _)| table == "dependencies")
        .map(|(_, name, _)| name.as_str())
        .collect();
    assert_eq!(normal, BTreeSet::from(["trust-ir"]), "{deps:?}");
    for (table, name, line) in &deps {
        assert!(
            !names_engine(name, true) && !names_engine(line, true),
            "checker manifest [{table}] names the engine: {line}"
        );
    }
    let mut table = String::new();
    for raw in toml.lines() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.starts_with('[') {
            table = line
                .trim_matches(|c| c == '[' || c == ']')
                .trim()
                .to_owned();
            let last = table.rsplit('.').next().unwrap_or("");
            let dependency_table = matches!(
                last,
                "dependencies" | "dev-dependencies" | "build-dependencies"
            ) && (!table.contains('.') || table.starts_with("target."));
            assert!(
                matches!(table.as_str(), "package" | "lints" | "features") || dependency_table,
                "checker manifest table [{table}]"
            );
        } else if table == "package"
            && let Some((key, _)) = line.split_once('=')
        {
            assert!(
                !matches!(key.trim(), "build" | "links"),
                "checker manifest [package] {line}"
            );
        }
    }
}

#[test]
fn checker_shares_no_code_with_engine() {
    let toml = std::fs::read_to_string(checker_dir().join("Cargo.toml")).unwrap();
    assert_checker_manifest(&toml);

    // Every file of the checker crate: no symlink, no build script, no path
    // into the engine's directory, and no Rust source with an identifier or
    // attribute of the scan (`scan_rust_source`).
    let checker_files = crate_files(&checker_dir());
    assert!(checker_files.iter().any(|p| p.ends_with("src/lib.rs")));
    let rust_files = checker_files
        .iter()
        .filter(|p| p.extension().is_some_and(|e| e == "rs"))
        .count();
    let findings = scan_crate_tree(&checker_dir());
    assert!(findings.is_empty(), "checker sources: {findings:#?}");
    eprintln!(
        "no shared code: {} checker files ({rust_files} Rust) scanned",
        checker_files.len()
    );

    // No Rust file of the checker is byte-identical to one of the engine.
    let engine_sources: BTreeSet<Vec<u8>> = crate_files(&crate_dir())
        .iter()
        .filter(|p| p.extension().is_some_and(|e| e == "rs"))
        .map(|p| std::fs::read(p).unwrap())
        .collect();
    for path in checker_files
        .iter()
        .filter(|p| p.extension().is_some_and(|e| e == "rs"))
    {
        assert!(
            !engine_sources.contains(&std::fs::read(path).unwrap()),
            "{} is a copy of an engine source file",
            path.display()
        );
    }

    // Cargo.lock: the checker's package depends on trust-ir only.
    let lock = std::fs::read_to_string(workspace_root().join("Cargo.lock")).unwrap();
    let mut packages = lock.split("[[package]]");
    let block = packages
        .find(|b| {
            b.lines()
                .any(|l| l.trim() == "name = \"trust-cg-eqsat-check\"")
        })
        .expect("trust-cg-eqsat-check in Cargo.lock");
    let start = block.find("dependencies = [").expect("dependency list");
    let list = &block[start + "dependencies = [".len()..];
    let list = &list[..list.find(']').expect("closing bracket")];
    let names: BTreeSet<&str> = list
        .split(',')
        .map(|e| e.trim().trim_matches('"'))
        .filter(|e| !e.is_empty())
        .map(|e| e.split_whitespace().next().unwrap())
        .collect();
    assert_eq!(names, BTreeSet::from(["trust-ir"]), "Cargo.lock: {list}");

    // The reverse: the engine's library dependencies exclude the checker.
    let engine_toml = std::fs::read_to_string(crate_dir().join("Cargo.toml")).unwrap();
    for (table, name, _) in manifest_dependencies(&engine_toml) {
        if table == "dependencies" || table.ends_with(".dependencies") {
            assert_ne!(
                name, "trust-cg-eqsat-check",
                "the engine library depends on the checker"
            );
        }
    }
}

/// The scan of case 6 on a synthetic crate tree: every planted evasion is
/// flagged (a module under a nested `target` directory, a `cfg_attr` path
/// with escapes, renamed include macros, spaced and raw spellings, a path
/// pasted by a macro, environment macros, a build script, a source the lexer
/// cannot read), and nothing in the clean control file or in the crate's
/// own `target` directory is.
#[test]
fn no_shared_code_scan_flags_every_evasion() {
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("no_shared_code_scan");
    let _ = std::fs::remove_dir_all(&root);
    let evasions: [(&str, &str); 20] = [
        (
            "src/target/mod.rs",
            "include!(\"../../../trust-cg-eqsat/src/eval.rs\");\n",
        ),
        (
            "src/cfg_attr_escaped.rs",
            "#[cfg_attr(all(), path = \"..\\x2f..\\x2ftrust-cg-eqsat\\x2fsrc\\x2feval.rs\")]\nmod e;\n",
        ),
        (
            "src/renamed_include.rs",
            "use core::include as inc;\ninc!(concat!(env!(\"CARGO_MANIFEST_DIR\"), \"/../trust-cg-\", \"eqsat/src/eval.rs\"));\n",
        ),
        (
            "src/renamed_include_str.rs",
            "use core::include_str as s;\nconst T: &str = s!(concat!(\"..\", \"/x.rs\"));\n",
        ),
        (
            "src/renamed_include_bytes.rs",
            "pub use ::core::{include_bytes as b};\n",
        ),
        ("src/spaced_include.rs", "include ! ( \"x.rs\" ) ;\n"),
        (
            "src/spaced_path.rs",
            "# [\n  path\n  = \"x.rs\" ]\nmod e;\n",
        ),
        (
            "src/inner_attribute.rs",
            "#![cfg_attr(all(), path = \"x\")]\n",
        ),
        ("src/raw_identifier.rs", "r#include!(\"x.rs\");\n"),
        (
            "src/macro_pasted_path.rs",
            "macro_rules! m { ($k:ident) => { #[$k = \"x.rs\"] mod e; }; }\nm!(path);\n",
        ),
        (
            "src/env_macro.rs",
            "const D: &str = env ! (\"CARGO_MANIFEST_DIR\");\n",
        ),
        (
            "src/option_env_macro.rs",
            "const D: Option<&str> = option_env!(\"OUT_DIR\");\n",
        ),
        ("src/import.rs", "use trust_cg_eqsat :: eval;\n"),
        (
            "src/extern_crate.rs",
            "extern crate trust_cg_eqsat as engine;\n",
        ),
        (
            "src/doc_include.rs",
            "#[doc = include_bytes!(\"x\")]\nstruct S;\n",
        ),
        (
            "src/path_string.rs",
            "const P: &str = \"../trust-cg-eqsat/src/eval.rs\";\n",
        ),
        (
            "src/after_raw_string.rs",
            "const S: &str = r#\"a \" // b\"#; include!(\"x.rs\");\n",
        ),
        (
            "src/after_chars_and_lifetimes.rs",
            "fn f<'a>(x: &'a str) -> char { let _ = '\"'; '\\'' } include!(\"y.rs\");\n",
        ),
        (
            "src/unterminated.rs",
            "/* never closed /* include!(\"x\") */\n",
        ),
        ("build.rs", "fn main() {}\n"),
    ];
    let clean = "mod target;\n\
                 // include! path trust_cg_eqsat CARGO_MANIFEST_DIR in a comment\n\
                 /* nested /* include!(\"x\") */ path */\n\
                 use trust_cg_eqsat_check::check;\n\
                 fn display_path<'a>(x: &'a str) -> &'a str { let _ = '/'; x }\n\
                 const TEXT: &str = \"include! path trust_cg_eqsat\";\n\
                 const DOMAIN: &str = \"trust-cg-eqsat.rule-statement.v1\";\n\
                 #[derive(Debug)]\nstruct Paths;\n";
    for (file, text) in evasions.iter().chain(&[
        ("src/lib.rs", clean),
        ("target/debug/out.rs", "include!(\"skipped.rs\");\n"),
    ]) {
        let path = root.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, text).unwrap();
    }
    let findings = scan_crate_tree(&root);
    eprintln!("synthetic tree findings: {findings:#?}");
    for (file, _) in evasions {
        assert!(
            findings.iter().any(|(path, _)| *path == root.join(file)),
            "{file} is not flagged"
        );
    }
    for clean_file in ["src/lib.rs", "target/debug/out.rs"] {
        assert!(
            !findings
                .iter()
                .any(|(path, _)| *path == root.join(clean_file)),
            "{clean_file} is flagged: {findings:?}"
        );
    }
    std::fs::remove_dir_all(&root).unwrap();
}

// ---------------------------------------------------------------------------
// Case 7: corpus outputs pass the checker and the interpreter.

/// This test's own reading of section 2.5: every class that applies to
/// `function`. Both crates name the classes as section 2.5 does; when
/// several apply, each crate may report any one of them.
fn ineligibility(module: &Module, function: &Function) -> BTreeSet<&'static str> {
    let mut out = BTreeSet::new();
    if function.blocks.is_empty() {
        out.insert("no_body");
        return out;
    }
    if !function.proofs.is_empty() {
        out.insert("function_proofs");
    }
    if function
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .any(|n| !n.proofs.is_empty() || n.proof_context.is_some())
    {
        out.insert("instruction_proofs");
    }
    if function.summary.is_some() {
        out.insert("summary");
    }
    if function.body_gate.is_some() {
        out.insert("body_gate");
    }
    if function.source_provenance.is_some() {
        out.insert("source_provenance");
    }
    for obligation in &module.proof_obligations {
        if obligation.function == Some(function.id)
            || obligation.site.is_some_and(|s| s.function == function.id)
        {
            out.insert("module_obligation");
        }
        if obligation.function.is_none() && obligation.site.is_none() {
            out.insert("unscoped_obligation");
        }
    }
    if !module.spec_modules.is_empty() {
        out.insert("spec_modules");
    }
    let mut reached = BTreeSet::from([function.blocks[0].id]);
    let mut work = vec![function.blocks[0].id];
    while let Some(id) = work.pop() {
        let Some(block) = function.blocks.iter().find(|b| b.id == id) else {
            continue;
        };
        for node in &block.body {
            for edge in node.inst.successor_edges() {
                if reached.insert(edge.target) {
                    work.push(edge.target);
                }
            }
        }
    }
    if function.blocks.iter().any(|b| !reached.contains(&b.id)) {
        out.insert("unreachable_block");
    }
    out
}

#[derive(Default, Debug)]
struct CorpusCounts {
    functions: usize,
    declined: BTreeMap<String, usize>,
    unsupported: usize,
    rewritten: usize,
    unchanged: usize,
    /// Rewritten functions whose derivation names a rule.
    rule_justified: usize,
    /// Rewritten functions with scalar parameters (compared on the
    /// interpreter).
    rewritten_scalar: usize,
    /// Of those, the ones whose input returned at one or more sampled
    /// inputs.
    interpreted_functions: usize,
    /// Their conclusive runs.
    interpreted_runs: usize,
    /// Of `interpreted_functions`, the rule-justified ones.
    rule_justified_and_returned: usize,
    /// Vacuous comparisons: no sampled run conclusive on both sides.
    vacuous_all_inconclusive: Vec<String>,
    /// Vacuous comparisons: conclusive runs, but the input never returned
    /// (input and output fail alike on every sampled input).
    vacuous_never_returned: Vec<String>,
}

/// Where a corpus comparison leaves a function: its input returned at one or
/// more sampled inputs (with the conclusive runs), or one of the two vacuous
/// kinds.
enum Interpreted {
    Returned { runs: usize },
    AllInconclusive,
    NeverReturned,
}

fn interpreted(comparison: &Comparison) -> Interpreted {
    if comparison.returned > 0 {
        Interpreted::Returned {
            runs: comparison.compared,
        }
    } else if comparison.compared == 0 {
        Interpreted::AllInconclusive
    } else {
        Interpreted::NeverReturned
    }
}

#[test]
fn corpus_engine_outputs_pass_checker_and_interpreter() {
    let rules = honest_rules();
    let registry = honest_registry();
    let config = EngineConfig::default();
    let mut counts = CorpusCounts::default();
    for entry in corpus() {
        let module = &entry.module;
        for function in &module.functions {
            counts.functions += 1;
            let what = format!("{}:@{}", entry.file, function.name);
            match optimize_function(module, function, &rules, &config) {
                Err(decline) => {
                    let class = decline.class();
                    *counts.declined.entry(class.to_owned()).or_default() += 1;
                    if class == "unsupported" {
                        // A reader refusal is not a section 2.5 class; the
                        // engine leaves the function alone, which is safe.
                        counts.unsupported += 1;
                        eprintln!("unsupported: {what}: {decline}");
                        continue;
                    }
                    let applicable = ineligibility(module, function);
                    assert!(
                        applicable.contains(class),
                        "{what}: engine declines {class}, test reads {applicable:?}"
                    );
                    let refused = check(
                        module,
                        function,
                        function,
                        &header_only(&function.name),
                        &registry,
                    )
                    .expect_err("checker accepted an ineligible function");
                    match &refused {
                        Rejection::Ineligible { body, class, .. } => {
                            assert_eq!(*body, Body::Input, "{what}");
                            assert!(
                                applicable.contains(class),
                                "{what}: checker class {class}, test reads {applicable:?}"
                            );
                        }
                        other => panic!("{what}: declined {decline}, checker: {other:?}"),
                    }
                }
                Ok(result) => {
                    assert!(
                        ineligibility(module, function).is_empty(),
                        "{what}: the engine took an ineligible function"
                    );
                    let verdict = check(
                        module,
                        function,
                        &result.function,
                        &result.derivation,
                        &registry,
                    )
                    .unwrap_or_else(|r| {
                        panic!(
                            "{what}: checker refused the engine's output: {r}\n{r:?}\nrewritten {}",
                            result.rewritten
                        )
                    });
                    if !result.rewritten {
                        counts.unchanged += 1;
                        assert_eq!(&result.function, function, "{what}");
                        assert_eq!(verdict.claims, 0, "{what}");
                        continue;
                    }
                    counts.rewritten += 1;
                    let justified = !verdict.rules_used.is_empty();
                    counts.rule_justified += usize::from(justified);
                    assert!(result.stats.cost_after < result.stats.cost_before, "{what}");
                    let out_module = assert_validates_with(module, &result.function, &what);
                    if scalar_params(module, function).is_some() {
                        counts.rewritten_scalar += 1;
                        let comparison = compare_runs(module, function, &out_module, 16, 3000, 11);
                        assert!(
                            comparison.differing.is_empty(),
                            "{what}: input and output differ: {:?}",
                            comparison.differing.first()
                        );
                        let rules = &verdict.rules_used;
                        match interpreted(&comparison) {
                            Interpreted::Returned { runs } => {
                                counts.interpreted_functions += 1;
                                counts.interpreted_runs += runs;
                                counts.rule_justified_and_returned += usize::from(justified);
                            }
                            Interpreted::AllInconclusive => counts
                                .vacuous_all_inconclusive
                                .push(format!("{what} (rules {rules:?})")),
                            Interpreted::NeverReturned => {
                                counts.vacuous_never_returned.push(format!(
                                    "{what} (rules {rules:?}, {} runs)",
                                    comparison.compared
                                ));
                            }
                        }
                    }
                }
            }
        }
    }
    eprintln!("corpus case 7: {counts:#?}");
    eprintln!(
        "corpus case 7: {} rewritten, {} with scalar parameters: {} interpreted with a return \
         ({} rule-justified), {} vacuous (all inconclusive), {} vacuous (never returned)",
        counts.rewritten,
        counts.rewritten_scalar,
        counts.interpreted_functions,
        counts.rule_justified_and_returned,
        counts.vacuous_all_inconclusive.len(),
        counts.vacuous_never_returned.len()
    );
    let declined: usize = counts.declined.values().sum();
    assert_eq!(
        declined + counts.rewritten + counts.unchanged,
        counts.functions
    );
    assert_eq!(
        counts.interpreted_functions
            + counts.vacuous_all_inconclusive.len()
            + counts.vacuous_never_returned.len(),
        counts.rewritten_scalar
    );
    assert!(counts.rewritten > 0 && counts.interpreted_functions > 0);
    assert!(counts.interpreted_runs >= counts.interpreted_functions);
    // A rule-backed rewrite was executed and compared, not only checked.
    assert!(
        counts.rule_justified_and_returned > 0,
        "no rule-justified corpus rewrite returned at a sampled input"
    );
}

// ---------------------------------------------------------------------------
// Case 8: random total-operator functions.

#[test]
fn random_total_terms_differential() {
    let rules = honest_rules();
    let registry = honest_registry();
    let config = EngineConfig::default();
    let mut rewritten = 0usize;
    let mut rule_justified = 0usize;
    let mut matches = 0u64;
    let mut runs = 0usize;
    let mut fired: BTreeMap<String, u64> = BTreeMap::new();
    let mut budget_hits = 0u64;
    for (index, (text, module)) in random_modules().iter().enumerate() {
        let input = function_named(module, "f");
        let result = optimize_function(module, input, &rules, &config)
            .unwrap_or_else(|d| panic!("random {index} declined: {d}\n{text}"));
        for (rule, n) in &result.stats.rule_matches {
            matches += n;
            *fired.entry(rule.clone()).or_default() += n;
        }
        let verdict = check(
            module,
            input,
            &result.function,
            &result.derivation,
            &registry,
        )
        .unwrap_or_else(|r| panic!("random {index}: checker refused: {r}\n{r:?}\n{text}"));
        let seed = 1000 + index as u64;
        if result.rewritten {
            rewritten += 1;
            if !verdict.rules_used.is_empty() {
                rule_justified += 1;
            }
            let out_module = assert_validates_with(module, &result.function, text);
            let Comparison {
                compared,
                returned,
                differing,
            } = compare_runs(module, input, &out_module, 32, 10_000, seed);
            assert!(
                differing.is_empty(),
                "random {index}: input and output differ: {:?}\n{text}\n{}",
                differing.first(),
                trust_ir::format::text_checked(&out_module).unwrap_or_default()
            );
            // Total operators over defined arguments: every run returns, at
            // either pointer width (not a vacuous comparison of two refusals).
            assert_eq!(
                returned, 32,
                "random {index}: not every run returned\n{text}"
            );
            assert_eq!(compared, 32);
            runs += compared;
        } else {
            assert_eq!(&result.function, input);
        }
        // Tight budgets cut matching short; what is emitted must still check.
        let tight = EngineConfig {
            max_rewrite_depth: (index % 3) as u32,
            max_matches_per_node: 1 + (index % 4) as u32,
            max_ids_per_instruction: [0, 2, 8, 256][(index / 3) % 4],
        };
        let cut = optimize_function(module, input, &rules, &tight)
            .unwrap_or_else(|d| panic!("random {index} declined at {tight:?}: {d}"));
        budget_hits += cut.stats.budget_hits;
        check(module, input, &cut.function, &cut.derivation, &registry).unwrap_or_else(|r| {
            panic!("random {index} at {tight:?}: checker refused: {r}\n{r:?}\n{text}")
        });
        if cut.rewritten {
            let cut_module = assert_validates_with(module, &cut.function, text);
            let differing = compare_runs(module, input, &cut_module, 8, 10_000, seed).differing;
            assert!(differing.is_empty(), "random {index} at {tight:?}: differs");
        }
        let trip = round_trip(module, input)
            .unwrap_or_else(|d| panic!("random {index}: round trip declined: {d}"));
        // No rule: every skeleton operand keeps its term, so the header-only
        // derivation justifies the round trip.
        check(module, input, &trip, &header_only(&input.name), &registry).unwrap_or_else(|r| {
            panic!("random {index}: checker refused the round trip: {r}\n{r:?}\n{text}")
        });
        let trip_module = assert_validates_with(module, &trip, text);
        let differing = compare_runs(module, input, &trip_module, 16, 10_000, seed).differing;
        assert!(
            differing.is_empty(),
            "random {index}: round trip differs: {:?}\n{text}",
            differing.first()
        );
    }
    eprintln!(
        "random case 8: {} functions, {rewritten} rewritten ({rule_justified} naming a rule), {matches} rule matches, {runs} differential runs, {budget_hits} budget hits at tight budgets\n  rules fired: {fired:?}",
        random_modules().len()
    );
    assert!(matches > 0, "no rule fired on the random functions");
    assert!(budget_hits > 0, "the tight budgets never bound");
    assert!(rule_justified > 0);
}

// ---------------------------------------------------------------------------
// Case 9: no-rule round trip over the corpus.

#[test]
fn no_rule_round_trip_preserves_corpus() {
    let registry = honest_registry();
    let mut eligible = 0usize;
    let mut compared_functions = 0usize;
    let mut returned_functions = 0usize;
    let mut vacuous_all_inconclusive: Vec<String> = Vec::new();
    let mut vacuous_never_returned: Vec<String> = Vec::new();
    for entry in corpus() {
        let module = &entry.module;
        for function in &module.functions {
            let what = format!("{}:@{}", entry.file, function.name);
            let Ok(trip) = round_trip(module, function) else {
                continue;
            };
            eligible += 1;
            check(
                module,
                function,
                &trip,
                &header_only(&function.name),
                &registry,
            )
            .unwrap_or_else(|r| panic!("{what}: checker refused the round trip: {r}\n{r:?}"));
            let out_module = assert_validates_with(module, &trip, &what);
            if scalar_params(module, function).is_some() {
                compared_functions += 1;
                let comparison = compare_runs(module, function, &out_module, 12, 3000, 23);
                assert!(
                    comparison.differing.is_empty(),
                    "{what}: round trip differs: {:?}",
                    comparison.differing.first()
                );
                match interpreted(&comparison) {
                    Interpreted::Returned { .. } => returned_functions += 1,
                    Interpreted::AllInconclusive => vacuous_all_inconclusive.push(what),
                    Interpreted::NeverReturned => vacuous_never_returned.push(what),
                }
            }
        }
    }
    eprintln!(
        "round trip: {eligible} eligible functions, {compared_functions} with scalar parameters: \
         {returned_functions} interpreted with a return, {} vacuous (all inconclusive), \
         {} vacuous (never returned)\n  all inconclusive: {vacuous_all_inconclusive:?}\n  \
         never returned: {vacuous_never_returned:?}",
        vacuous_all_inconclusive.len(),
        vacuous_never_returned.len()
    );
    assert!(eligible > 0);
    assert_eq!(
        returned_functions + vacuous_all_inconclusive.len() + vacuous_never_returned.len(),
        compared_functions
    );
    assert!(returned_functions > 0);
}

// ---------------------------------------------------------------------------
// Case 10: engine and checker agree on rule identity.

#[test]
fn engine_and_checker_agree_on_rule_identity() {
    let engine = honest_rules();
    let checker = honest_registry();
    let engine_names: Vec<String> = engine.rules().iter().map(|r| r.name().to_owned()).collect();
    assert_eq!(engine_names, checker.names());
    assert_eq!(engine.rules().len(), checker.len());
    let texts = rules::canonical_texts(INTEGER_IDENTITIES).unwrap();
    for (rule, (name, text)) in engine.rules().iter().zip(&texts) {
        assert_eq!(rule.name(), name);
        assert_eq!(rule.canonical_text(), text);
        assert_eq!(
            checker.canonical_text(name).as_deref(),
            Some(rule.canonical_text()),
            "{name}"
        );
        assert_eq!(
            checker.statement_digest(name),
            Some(rule.statement_digest()),
            "{name}"
        );
        assert_eq!(rules::statement_digest(text), rule.statement_digest());
    }
    for file in MUTANTS.iter().filter(|f| f.starts_with("panic_only_")) {
        let m = mutant(file);
        assert!(RuleSet::parse(&m.text).is_err(), "{file}: engine admits it");
        assert!(
            Registry::parse(&m.text).is_err(),
            "{file}: checker admits it"
        );
    }
    // A well-formed mutant parses in both and gets the same identity.
    for file in MUTANTS.iter().filter(|f| !f.starts_with("panic_only_")) {
        let m = mutant(file);
        let e = RuleSet::parse(&m.text).unwrap();
        let c = Registry::parse(&m.text).unwrap();
        assert_eq!(
            c.statement_digest(&m.name),
            Some(e.rules()[0].statement_digest()),
            "{file}"
        );
    }
}

// ---------------------------------------------------------------------------
// Case 11: forged derivation bytes.

/// The section 7.2 encoding of a decoded derivation (for re-encoding after a
/// structural change).
fn encode(d: &engine_common::Decoded) -> Vec<u8> {
    use engine_common::{Proof, Term};
    fn put_u32(out: &mut Vec<u8>, v: u32) {
        out.extend_from_slice(&v.to_le_bytes());
    }
    fn put_str(out: &mut Vec<u8>, s: &str) {
        put_u32(out, s.len() as u32);
        out.extend_from_slice(s.as_bytes());
    }
    let mut out = b"TCGEQSAT".to_vec();
    put_u32(&mut out, 1);
    put_str(&mut out, &d.function);
    put_u32(&mut out, d.rules.len() as u32);
    for (name, digest) in &d.rules {
        put_str(&mut out, name);
        out.extend_from_slice(digest);
    }
    put_u32(&mut out, d.terms.len() as u32);
    for term in &d.terms {
        match term {
            Term::Param(b, i) => {
                out.push(1);
                put_u32(&mut out, *b);
                put_u32(&mut out, *i);
            }
            Term::Result(b, k, j) => {
                out.push(2);
                put_u32(&mut out, *b);
                put_u32(&mut out, *k);
                put_u32(&mut out, *j);
            }
            Term::Const(ty, r) => {
                out.push(3);
                out.push(ty.code());
                out.extend_from_slice(&r.to_le_bytes());
            }
            Term::Op(desc, args) => {
                out.push(4);
                desc.encode(&mut out);
                for a in args {
                    put_u32(&mut out, *a);
                }
            }
        }
    }
    put_u32(&mut out, d.proofs.len() as u32);
    for proof in &d.proofs {
        match proof {
            Proof::Refl(t) => {
                out.push(1);
                put_u32(&mut out, *t);
            }
            Proof::Sym(p) => {
                out.push(2);
                put_u32(&mut out, *p);
            }
            Proof::Trans(p, q) => {
                out.push(3);
                put_u32(&mut out, *p);
                put_u32(&mut out, *q);
            }
            Proof::Congr(desc, ps) => {
                out.push(4);
                desc.encode(&mut out);
                for p in ps {
                    put_u32(&mut out, *p);
                }
            }
            Proof::Rule {
                rule,
                ty,
                bindings,
                premises,
            } => {
                out.push(5);
                put_u32(&mut out, *rule);
                out.push(ty.code());
                put_u32(&mut out, bindings.len() as u32);
                for (name, t) in bindings {
                    put_str(&mut out, name);
                    put_u32(&mut out, *t);
                }
                put_u32(&mut out, premises.len() as u32);
                for p in premises {
                    put_u32(&mut out, *p);
                }
            }
        }
    }
    put_u32(&mut out, d.claims.len() as u32);
    for c in &d.claims {
        put_u32(&mut out, *c);
    }
    out
}

/// Terms `i` and `i + 1` swapped; references remapped iff `remap`.
fn swap_terms(d: &engine_common::Decoded, i: usize, remap: bool) -> engine_common::Decoded {
    use engine_common::{Proof, Term};
    let mut out = d.clone();
    out.terms.swap(i, i + 1);
    if remap {
        let fix = |t: &mut u32| {
            if *t as usize == i {
                *t += 1;
            } else if *t as usize == i + 1 {
                *t -= 1;
            }
        };
        for term in &mut out.terms {
            if let Term::Op(_, args) = term {
                args.iter_mut().for_each(fix);
            }
        }
        for proof in &mut out.proofs {
            match proof {
                Proof::Refl(t) => fix(t),
                Proof::Rule { bindings, .. } => bindings.iter_mut().for_each(|(_, t)| fix(t)),
                _ => {}
            }
        }
    }
    out
}

/// Input `x * 2` and output `x + x`, justified by `Sym` of the registered
/// refinement `double_to_mul: x + x ~> x * 2` (refused: a refinement may be
/// used forward only).
fn sym_of_refines_case() -> (Module, Function, Function, Vec<u8>) {
    let head = "; TrustIr text format v1\nmodule \"m\"\n\nfuncty.0 = (i64) -> (i64)\n\nfn @f(functy.0) {\nbb0(%0: i64):\n    %1 = const i64 0\n    %2 = xor i64 %0, %1\n";
    let input = parse_valid(&format!(
        "{head}    %3 = const i64 2\n    %4 = mul i64 %2, %3\n    ret %4\n}}\n"
    ));
    let output = parse_valid(&format!("{head}    %4 = add i64 %2, %2\n    ret %4\n}}\n"));
    let honest = honest_rules();
    let rule = honest
        .rules()
        .iter()
        .find(|r| r.name() == "double_to_mul")
        .expect("double_to_mul");
    assert!(!rule.is_equiv(), "double_to_mul is a refinement");
    let mut b = DerivationBuilder::new("f");
    let r = b.rule("double_to_mul", rule.statement_digest());
    let x = b.result(0, 0, 0);
    let step = b.rule_step(r, ScalarTy::I64, &[("x", x)], 0);
    let sym = b.sym(step);
    b.claim(sym);
    let f_in = function_named(&input, "f").clone();
    let f_out = function_named(&output, "f").clone();
    (input, f_in, f_out, b.finish())
}

#[test]
fn forged_derivation_bytes_are_rejected() {
    let rules = honest_rules();
    let registry = honest_registry();
    // The random function whose derivation has the most claims (ties: the
    // longest derivation, then the lowest index).
    let mut best: Option<(usize, usize, usize, Optimized)> = None;
    for (index, (_, module)) in random_modules().iter().enumerate() {
        let input = function_named(module, "f");
        let result = optimize_function(module, input, &rules, &EngineConfig::default()).unwrap();
        let decoded = engine_common::decode(&result.derivation).unwrap();
        if decoded.rules.is_empty() || decoded.claims.len() < 2 {
            continue;
        }
        let key = (decoded.claims.len(), result.derivation.len());
        if best.as_ref().is_none_or(|(c, l, _, _)| key > (*c, *l)) {
            best = Some((key.0, key.1, index, result));
        }
    }
    let (claims, len, index, result) =
        best.expect("a random derivation with two claims and a rule");
    let module = &random_modules()[index].1;
    let input = function_named(module, "f");
    let output = &result.function;
    let genuine = &result.derivation;
    check(module, input, output, genuine, &registry).expect("the genuine derivation is accepted");
    eprintln!("forgeries of random function {index}: {claims} claims, {len} bytes");

    let refuse = |bytes: &[u8], what: &str| {
        if let Ok(verdict) = check(module, input, output, bytes, &registry) {
            panic!("forged derivation accepted ({what}): {verdict:?}");
        }
    };

    // Every byte position, two different bit flips each (all positions when
    // short, else a deterministic sample of at least 400).
    let positions: Vec<usize> = if len <= 4000 {
        (0..len).collect()
    } else {
        (0..len).step_by(len / 400).collect()
    };
    assert!(positions.len() >= 200);
    for &at in &positions {
        for flip in [0x01u8, 0x80] {
            let mut bytes = genuine.clone();
            bytes[at] ^= flip;
            refuse(&bytes, &format!("byte {at} ^ {flip:#x}"));
        }
    }
    // Truncations and an appended byte.
    for cut in [1usize, 4, 33, len / 2] {
        refuse(&genuine[..len - cut], &format!("truncated by {cut}"));
    }
    refuse(&genuine[..12], "header only up to the version");
    let mut longer = genuine.clone();
    longer.push(0);
    refuse(&longer, "one byte appended");

    // Two claims swapped (claims must be strictly increasing).
    let decoded = engine_common::decode(genuine).unwrap();
    assert_eq!(
        &encode(&decoded),
        genuine,
        "test encoder reproduces the bytes"
    );
    let mut swapped = decoded.clone();
    let n = swapped.claims.len();
    swapped.claims.swap(n - 2, n - 1);
    refuse(&encode(&swapped), "two claims swapped");

    // Two adjacent terms reordered. Without remapping the references, the
    // meaning changes and the derivation must be refused. With remapping the
    // swap is a renumbering: refused unless it is semantically neutral and
    // still canonical by section 7.2's list; any such case is reported.
    let mut neutral_accepted = 0usize;
    let mut reorders = 0usize;
    for i in 0..decoded.terms.len().saturating_sub(1) {
        let independent = !matches!(
            &decoded.terms[i + 1],
            engine_common::Term::Op(_, args) if args.contains(&(i as u32))
        );
        if !independent {
            continue;
        }
        reorders += 1;
        refuse(
            &encode(&swap_terms(&decoded, i, false)),
            &format!("terms {i} and {} swapped, references kept", i + 1),
        );
        if check(
            module,
            input,
            output,
            &encode(&swap_terms(&decoded, i, true)),
            &registry,
        )
        .is_ok()
        {
            neutral_accepted += 1;
        }
    }
    assert!(reorders > 0);
    eprintln!(
        "term reorders: {reorders} tried; {neutral_accepted} renumberings (references remapped) were accepted as neutral"
    );

    // Sym of a refinement.
    let (m, i, o, d) = sym_of_refines_case();
    let refused = check(&m, &i, &o, &d, &registry).expect_err("Sym of refines accepted");
    assert_eq!(refused.class(), "sym_of_refines", "{refused:?}");
    // The forward use of the same refinement, the other way round, is fine.
    let mut b = DerivationBuilder::new("f");
    let rule = rules
        .rules()
        .iter()
        .find(|r| r.name() == "double_to_mul")
        .unwrap();
    let r = b.rule("double_to_mul", rule.statement_digest());
    let x = b.result(0, 0, 0);
    let step = b.rule_step(r, ScalarTy::I64, &[("x", x)], 0);
    b.claim(step);
    let forward = b.finish();
    check(&m, &o, &i, &forward, &registry).expect("forward refinement x + x ~> x * 2 accepted");
}

// ---------------------------------------------------------------------------
// Case 12: neither crate's library reads a clock or orders by hash.

#[test]
fn engine_src_reads_no_clock() {
    // The gate of section 6 (`git grep -n -E 'Instant|SystemTime'`), a
    // substring search, over the engine's `src` and the checker's `src`.
    for dir in [crate_dir().join("src"), checker_dir().join("src")] {
        let mut files = Vec::new();
        walk(&dir, None, &mut files);
        assert!(
            files.iter().any(|p| p.ends_with("lib.rs")),
            "{}",
            dir.display()
        );
        for path in files {
            let text = std::fs::read_to_string(&path).unwrap();
            for (number, line) in text.lines().enumerate() {
                for needle in ["Instant", "SystemTime", "HashMap", "HashSet"] {
                    assert!(
                        !line.contains(needle),
                        "{}:{}: {needle}: {line}",
                        path.display(),
                        number + 1
                    );
                }
            }
        }
    }
}
