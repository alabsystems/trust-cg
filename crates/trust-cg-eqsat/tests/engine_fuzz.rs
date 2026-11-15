// crates/trust-cg-eqsat/tests/engine_fuzz.rs - structured random modules through every engine contract
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A fixed-seed generator of valid trust-ir modules with the shapes the
//! hand-written tests lack: switches with case arguments, invokes with
//! landing pads (the result read in the normal successor, passed in the
//! invoke's own normal-edge arguments, or read in a normal successor that is
//! a loop header), loops with block parameters, early returns, unreachable
//! arms, `i128`/`u128` constants (canonical `U128` spellings above
//! `i128::MAX` included), `isize`/`usize` at 16-, 32- and 64-bit pointers,
//! every Bool operator, casts, nested selects, copies of copies,
//! overflow/undef/alloca/store/load/call, duplicate instructions in
//! sibling branches, and vector `extractelement`/`insertelement` whose lane
//! index is computed from constants, a copy of a constant or a constant
//! (in range on the main path, out of range in an arm that may be taken):
//! the literal-sensitive positions of sections 2.5 and 6, where a folded
//! index must stay behind a see-through copy for the output to validate; and
//! switches flagged `exhaustive` over the tag of an enum parameter whose
//! selector reaches the tag through `zext`, `sext`, equal-width `bitcast`,
//! copies and the graph identities `add 0`, `mul 1`, `or 0`, `xor 0`,
//! `sub 0`, with complete case sets and (only behind an identity, where the
//! validator does not hold the case set to the enum) incomplete ones: the
//! selector traces of section 2.5, which the engine must keep.
//!
//! Every module that validates goes through [`audit`]: no panic, no decline,
//! deterministic output, the output validates and the independent checker
//! (`trust-cg-eqsat-check`, a dev-dependency) accepts it, the reference
//! interpreter agrees on seeded arguments, the cost rule (a rewritten body is
//! strictly cheaper and its reported cost is its re-read cost; an unchanged
//! body is the input with the header-only derivation), the same under
//! several `EngineConfig`s including zero and one-entry budgets, and
//! `round_trip` likewise with the header-only derivation.
//!
//! Evidence boundary: random testing at a fixed seed. It finds faults in the
//! shapes it generates; it proves nothing about the others.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::panic::{AssertUnwindSafe, catch_unwind};

use trust_cg_eqsat::derivation::header_only;
use trust_cg_eqsat::rules::{INTEGER_IDENTITIES, RuleSet};
use trust_cg_eqsat::{Decline, EngineConfig, Optimized, optimize_function, round_trip};
use trust_cg_eqsat_check::{Registry, check};
use trust_ir::{
    Constant, Function, Inst, InterpretErrorCode, InterpretOptions, InterpretValue,
    InterpretValueKind, Interpreter, Module, Ty,
};

/// Generated modules (fixed seeds `0..MODULES`). Sized so the test runs in
/// well under a minute in a debug build.
const MODULES: u64 = 600;

// ---- support -----------------------------------------------------------------

/// SplitMix64.
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

fn rules() -> RuleSet {
    RuleSet::parse(INTEGER_IDENTITIES).expect("rules parse")
}

fn registry() -> Registry {
    Registry::parse(INTEGER_IDENTITIES).expect("registry parses")
}

fn parse(text: &str) -> Result<Module, String> {
    let module = trust_ir::parser::parse_module(text).map_err(|e| format!("parse: {e}"))?;
    let errors = trust_ir_build::validate_module(&module);
    if errors.is_empty() {
        Ok(module)
    } else {
        Err(format!("validate: {errors:?}"))
    }
}

fn function_named<'m>(module: &'m Module, name: &str) -> &'m Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"))
}

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

fn scalar_width(ty: &Ty, pointer_bits: u32) -> Option<u32> {
    Some(match ty {
        Ty::Bool => 1,
        Ty::I8 | Ty::U8 => 8,
        Ty::I16 | Ty::U16 => 16,
        Ty::I32 | Ty::U32 => 32,
        Ty::I64 | Ty::U64 => 64,
        Ty::I128 | Ty::U128 => 128,
        Ty::Isize | Ty::Usize => pointer_bits,
        _ => return None,
    })
}

fn interp_value(ty: &Ty, residue: u128, pointer_bits: u32) -> InterpretValue {
    if *ty == Ty::Bool {
        InterpretValue::bool(residue & 1 == 1)
    } else {
        InterpretValue::int_at(ty.clone(), residue as i128, pointer_bits).expect("integer value")
    }
}

/// How the differential makes an argument of one parameter type.
enum ArgKind {
    /// A scalar of this width.
    Scalar(u32),
    /// A field-less enum: its canonical tag type and every discriminant.
    Enum(Ty, Vec<i128>),
}

fn arg_kind(module: &Module, ty: &Ty) -> Option<ArgKind> {
    if let Ty::Enum(id) = ty {
        let def = module.enum_def(*id)?;
        if def.variants.iter().any(|v| !v.fields.is_empty()) {
            return None;
        }
        let tag = def.canonical_tag_repr()?.ty();
        return Some(ArgKind::Enum(tag, def.effective_discriminants()?));
    }
    scalar_width(ty, module.pointer_bits()).map(ArgKind::Scalar)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Outcome {
    Returned(String),
    Failed(InterpretErrorCode),
    Inconclusive,
}

fn outcome(module: &Module, function: &Function, args: &[InterpretValue]) -> Outcome {
    let options = InterpretOptions {
        fuel: 200_000,
        ..InterpretOptions::default()
    };
    match Interpreter::with_module(module)
        .with_options(options)
        .execute_func(function.id, args.iter().cloned())
    {
        Ok(done) => Outcome::Returned(format!("{:?}", done.returns)),
        Err(error) if error.code == InterpretErrorCode::OutOfFuel => Outcome::Inconclusive,
        Err(error) => Outcome::Failed(error.code),
    }
}

/// The first disagreement of the two modules on seeded arguments (boundary
/// residues and random ones). Running out of fuel on either side is
/// inconclusive, not a disagreement (section 8, "Not checked: resources").
fn differential(
    module: &Module,
    input: &Function,
    output_module: &Module,
    seed: u64,
) -> Option<String> {
    let bits = module.pointer_bits();
    let params = module.func_types.get(input.ty.0 as usize)?.params.clone();
    let kinds: Vec<ArgKind> = params
        .iter()
        .map(|t| arg_kind(module, t))
        .collect::<Option<_>>()?;
    let mut rng = Rng(seed);
    for i in 0..12 {
        let args: Vec<InterpretValue> = params
            .iter()
            .zip(&kinds)
            .map(|(ty, kind)| match kind {
                ArgKind::Scalar(w) => {
                    let r = match (i + rng.below(4)) % 5 {
                        0 => 0,
                        1 => 1,
                        2 => mask(*w),
                        3 => 1u128 << (w - 1),
                        _ => rng.wide() & mask(*w),
                    };
                    interp_value(ty, r, bits)
                }
                ArgKind::Enum(tag, discriminants) => {
                    let d =
                        discriminants[(i + rng.below(discriminants.len())) % discriminants.len()];
                    InterpretValue {
                        ty: ty.clone(),
                        kind: InterpretValueKind::Aggregate(vec![
                            InterpretValue::int_at(tag.clone(), d, bits).expect("tag value"),
                        ]),
                    }
                }
            })
            .collect();
        let before = outcome(module, input, &args);
        let after = outcome(output_module, input, &args);
        if before == Outcome::Inconclusive || after == Outcome::Inconclusive {
            continue;
        }
        if before != after {
            return Some(format!("args {args:?}: input {before:?}, output {after:?}"));
        }
    }
    None
}

fn panic_text(p: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = p.downcast_ref::<String>() {
        s.clone()
    } else if let Some(s) = p.downcast_ref::<&str>() {
        (*s).to_owned()
    } else {
        "non-string panic".to_owned()
    }
}

fn run_engine(
    module: &Module,
    function: &Function,
    rules: &RuleSet,
    config: &EngineConfig,
) -> Result<Result<Optimized, Decline>, String> {
    catch_unwind(AssertUnwindSafe(|| {
        optimize_function(module, function, rules, config)
    }))
    .map_err(|p| panic_text(&p))
}

/// The configurations every module also runs under: zero and one-entry
/// arena bounds, no rewrite depth, a single match, and wide budgets.
const CONFIGS: [EngineConfig; 5] = [
    EngineConfig {
        max_rewrite_depth: 0,
        max_matches_per_node: 1,
        max_ids_per_instruction: 256,
    },
    EngineConfig {
        max_rewrite_depth: 3,
        max_matches_per_node: 64,
        max_ids_per_instruction: 0,
    },
    EngineConfig {
        max_rewrite_depth: 3,
        max_matches_per_node: 64,
        max_ids_per_instruction: 1,
    },
    EngineConfig {
        max_rewrite_depth: 8,
        max_matches_per_node: 3,
        max_ids_per_instruction: 4,
    },
    EngineConfig {
        max_rewrite_depth: 6,
        max_matches_per_node: 400,
        max_ids_per_instruction: 1024,
    },
];

/// One optimized output against every contract that applies to it.
fn audit_output(
    module: &Module,
    function: &Function,
    out: &Optimized,
    registry: &Registry,
    what: &str,
    seed: u64,
    problems: &mut Vec<String>,
) {
    if out.rewritten {
        if out.stats.cost_after >= out.stats.cost_before {
            problems.push(format!(
                "{what}: rewritten but not cheaper ({} -> {})",
                out.stats.cost_before, out.stats.cost_after
            ));
        }
    } else {
        if out.function != *function {
            problems.push(format!("{what}: an unchanged result is not the input"));
        }
        if out.derivation != header_only(&function.name) {
            problems.push(format!(
                "{what}: an unchanged result has a non-header derivation"
            ));
        }
        if out.stats.cost_after != out.stats.cost_before {
            problems.push(format!("{what}: an unchanged result changed cost"));
        }
    }
    let out_module = substituted(module, &out.function);
    let errors = trust_ir_build::validate_module(&out_module);
    if !errors.is_empty() {
        problems.push(format!("{what}: the output does not validate: {errors:?}"));
        return;
    }
    if out.rewritten {
        match optimize_function(
            &out_module,
            &out.function,
            &RuleSet::empty(),
            &EngineConfig::default(),
        ) {
            Ok(again) if again.stats.cost_before != out.stats.cost_after => problems.push(format!(
                "{what}: cost_after {} but the returned body costs {}",
                out.stats.cost_after, again.stats.cost_before
            )),
            Ok(_) => {}
            Err(d) => problems.push(format!("{what}: re-reading the output declined: {d}")),
        }
    }
    if let Err(r) = check(module, function, &out.function, &out.derivation, registry) {
        problems.push(format!("{what}: the checker refuses the output: {r:?}"));
    }
    if let Some(d) = differential(module, function, &out_module, seed) {
        problems.push(format!("{what}: the interpreter disagrees: {d}"));
    }
}

/// Every contract on one function: the problems found, and whether the
/// default configuration rewrote it.
fn audit(module: &Module, name: &str, seed: u64) -> (Vec<String>, bool) {
    let mut problems = Vec::new();
    let function = function_named(module, name);
    let rules = rules();
    let registry = registry();
    let config = EngineConfig::default();
    let first = run_engine(module, function, &rules, &config);
    let second = run_engine(module, function, &rules, &config);
    let mut rewritten = false;
    match (&first, &second) {
        (Err(p), _) | (_, Err(p)) => problems.push(format!("optimize_function panicked: {p}")),
        (Ok(Err(a)), _) => problems.push(format!("declined: {a}")),
        (Ok(Ok(a)), Ok(Ok(b))) => {
            if a.derivation != b.derivation || a.function != b.function || a.stats != b.stats {
                problems.push("two runs differ".to_owned());
            }
            rewritten = a.rewritten;
            audit_output(
                module,
                function,
                a,
                &registry,
                "default",
                seed,
                &mut problems,
            );
        }
        (Ok(Ok(_)), Ok(Err(_))) => problems.push("one run declined, one did not".to_owned()),
    }
    for (index, config) in CONFIGS.iter().enumerate() {
        match run_engine(module, function, &rules, config) {
            Err(p) => problems.push(format!("optimize_function panicked at {config:?}: {p}")),
            Ok(Err(d)) => problems.push(format!("declined at {config:?}: {d}")),
            Ok(Ok(out)) => {
                if config.max_ids_per_instruction == 0 && !out.stats.rule_matches.is_empty() {
                    problems.push(format!(
                        "a rule fired under a zero arena bound: {:?}",
                        out.stats.rule_matches
                    ));
                }
                let what = format!("{config:?}");
                audit_output(
                    module,
                    function,
                    &out,
                    &registry,
                    &what,
                    seed ^ (index as u64 + 2),
                    &mut problems,
                );
            }
        }
    }
    match catch_unwind(AssertUnwindSafe(|| round_trip(module, function))) {
        Err(p) => problems.push(format!("round_trip panicked: {}", panic_text(&p))),
        Ok(Err(d)) => problems.push(format!("round_trip declined: {d}")),
        Ok(Ok(out)) => {
            if round_trip(module, function).as_ref() != Ok(&out) {
                problems.push("round_trip is not deterministic".to_owned());
            }
            let out_module = substituted(module, &out);
            let errors = trust_ir_build::validate_module(&out_module);
            if errors.is_empty() {
                if let Some(d) = differential(module, function, &out_module, seed ^ 1) {
                    problems.push(format!("round_trip: the interpreter disagrees: {d}"));
                }
            } else {
                problems.push(format!("round_trip output does not validate: {errors:?}"));
            }
            if let Err(r) = check(
                module,
                function,
                &out,
                &header_only(&function.name),
                &registry,
            ) {
                problems.push(format!("the checker refuses the round trip: {r:?}"));
            }
        }
    }
    (problems, rewritten)
}

// ---- structured random generator ---------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct TyInfo {
    name: &'static str,
    width: u32,
    signed: bool,
}

const BOOL: TyInfo = TyInfo {
    name: "bool",
    width: 1,
    signed: false,
};

const I64: TyInfo = TyInfo {
    name: "i64",
    width: 64,
    signed: true,
};

/// The defined and the maybe-poison value pools.
type Pools = (
    BTreeMap<&'static str, Vec<String>>,
    BTreeMap<&'static str, Vec<String>>,
);

fn int_tys(pointer_bits: u32) -> Vec<TyInfo> {
    let mut out = Vec::new();
    for (name, width, signed) in [
        ("i8", 8, true),
        ("i16", 16, true),
        ("i32", 32, true),
        ("i64", 64, true),
        ("i128", 128, true),
        ("isize", pointer_bits, true),
        ("u8", 8, false),
        ("u16", 16, false),
        ("u32", 32, false),
        ("u64", 64, false),
        ("u128", 128, false),
        ("usize", pointer_bits, false),
    ] {
        out.push(TyInfo {
            name,
            width,
            signed,
        });
    }
    out
}

fn const_text(ty: TyInfo, residue: u128) -> String {
    let r = residue & mask(ty.width);
    if ty.width == 1 {
        return if r == 1 { "true" } else { "false" }.to_owned();
    }
    if ty.signed && r >> (ty.width - 1) == 1 {
        let magnitude = (mask(ty.width) - r) + 1;
        if magnitude == 1u128 << 127 {
            return "-170141183460469231731687303715884105728".to_owned();
        }
        return format!("-{magnitude}");
    }
    r.to_string()
}

struct BlockText {
    header: String,
    lines: Vec<String>,
}

struct Gen {
    rng: Rng,
    next: usize,
    blocks: Vec<BlockText>,
    cur: usize,
    /// Defined values by type name (dominating the current block).
    pool: BTreeMap<&'static str, Vec<String>>,
    /// Maybe-poison values by type name (dominating the current block).
    raw: BTreeMap<&'static str, Vec<String>>,
    types: Vec<TyInfo>,
    rets: Vec<TyInfo>,
    budget: usize,
    use_invoke: bool,
    /// The enum parameter, when the function has one.
    tag: Option<TagEnum>,
    /// Whether an integer `bitcast` validates: trust-ir refuses one on a
    /// target outside its canonical scalar layouts (msp430,
    /// `CastLayoutUnsupported`).
    bitcast: bool,
}

/// The function's field-less enum parameter: its value, its tag type and its
/// discriminants (`0..variants`).
#[derive(Clone)]
struct TagEnum {
    param: String,
    tag_ty: TyInfo,
    variants: usize,
}

/// The tag types `enum @E` is declared with.
const TAG_TYS: [TyInfo; 4] = [
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
        name: "i8",
        width: 8,
        signed: true,
    },
    TyInfo {
        name: "i16",
        width: 16,
        signed: true,
    },
];

impl Gen {
    fn fresh(&mut self) -> String {
        let v = format!("%{}", self.next);
        self.next += 1;
        v
    }
    fn line(&mut self, text: String) {
        self.blocks[self.cur].lines.push(format!("    {text}"));
    }
    fn emit(&mut self, ty: TyInfo, rhs: String) -> String {
        let v = self.fresh();
        self.line(format!("{v} = {rhs}"));
        self.pool.entry(ty.name).or_default().push(v.clone());
        self.budget = self.budget.saturating_sub(1);
        v
    }
    fn new_block(&mut self, params: &[(String, TyInfo)]) -> usize {
        let id = self.blocks.len();
        let ps: Vec<String> = params
            .iter()
            .map(|(v, t)| format!("{v}: {}", t.name))
            .collect();
        let header = if ps.is_empty() {
            format!("bb{id}:")
        } else {
            format!("bb{id}({}):", ps.join(", "))
        };
        self.blocks.push(BlockText {
            header,
            lines: Vec::new(),
        });
        id
    }
    fn constant(&mut self, ty: TyInfo, residue: u128) -> String {
        let text = const_text(ty, residue);
        self.emit(ty, format!("const {} {text}", ty.name))
    }
    fn residue(&mut self, ty: TyInfo) -> u128 {
        let m = mask(ty.width);
        match self.rng.below(8) {
            0 => 0,
            1 => 1,
            2 => m,
            3 => 1u128 << (ty.width - 1),
            4 => (1u128 << (ty.width - 1)).wrapping_sub(1) & m,
            5 => u128::from(ty.width),
            _ => self.rng.wide() & m,
        }
    }
    fn random_const(&mut self, ty: TyInfo) -> String {
        let r = self.residue(ty);
        self.constant(ty, r)
    }
    fn int_ty(&mut self) -> TyInfo {
        let ints: Vec<TyInfo> = self.types.iter().copied().filter(|t| t.width > 1).collect();
        ints[self.rng.below(ints.len())]
    }
    fn any_ty(&mut self) -> TyInfo {
        self.types[self.rng.below(self.types.len())]
    }
    fn value(&mut self, ty: TyInfo) -> String {
        let n = self.pool.get(ty.name).map_or(0, Vec::len);
        if n == 0 || self.rng.chance(8) {
            if ty.width == 1 && self.rng.chance(60) {
                let a = self.int_ty();
                let x = self.value(a);
                let y = self.value(a);
                return self.emit(BOOL, format!("icmp ult {} {x}, {y}", a.name));
            }
            return self.random_const(ty);
        }
        let pick = if self.rng.chance(60) {
            n - 1 - self.rng.below(n.min(3))
        } else {
            self.rng.below(n)
        };
        self.pool[ty.name][pick].clone()
    }
    /// A value (defined or maybe-poison) of `ty`.
    fn any_value(&mut self, ty: TyInfo) -> String {
        let n = self.raw.get(ty.name).map_or(0, Vec::len);
        if n > 0 && self.rng.chance(30) {
            let i = self.rng.below(n);
            return self.raw[ty.name][i].clone();
        }
        self.value(ty)
    }
    /// A frontier op over a maybe-poison value.
    fn define(&mut self, ty: TyInfo, source: &str) -> String {
        self.raw.entry(ty.name).or_default().push(source.to_owned());
        let mut source = source.to_owned();
        if self.rng.chance(20) {
            // copy of copy of a maybe-poison value
            let a = self.fresh();
            self.line(format!("{a} = copy {} {source}", ty.name));
            let b = self.fresh();
            self.line(format!("{b} = copy {} {a}", ty.name));
            source = b;
        }
        if ty.width == 1 {
            let f = self.constant(BOOL, 0);
            self.emit(ty, format!("bxor bool {source}, {f}"))
        } else {
            let n = ty.name;
            match self.rng.below(3) {
                0 => {
                    let z = self.constant(ty, 0);
                    self.emit(ty, format!("xor {n} {source}, {z}"))
                }
                1 => self.emit(ty, format!("neg {n} {source}")),
                _ => {
                    let o = self.value(ty);
                    self.emit(ty, format!("add {n} {source}, {o}"))
                }
            }
        }
    }

    fn op(&mut self) {
        let t = self.int_ty();
        let n = t.name;
        match self.rng.below(28) {
            22 => {
                // two defined results, the second Bool
                let op = ["add.overflow", "sub.overflow", "mul.overflow"][self.rng.below(3)];
                let a = self.value(t);
                let b = self.value(t);
                let r0 = self.fresh();
                let r1 = self.fresh();
                self.line(format!("{r0}, {r1} = {op} {n} {a}, {b}"));
                self.pool.entry(t.name).or_default().push(r0);
                self.pool.entry("bool").or_default().push(r1);
            }
            23 => {
                // skeleton cast from Bool: defined result
                let b = self.value(BOOL);
                let op = ["zext", "sext"][self.rng.below(2)];
                let v = self.fresh();
                self.line(format!("{v} = {op} bool {b} to {n}"));
                self.pool.entry(t.name).or_default().push(v);
            }
            24 if self.rng.chance(30) => {
                let v = self.fresh();
                self.line(format!("{v} = undef {n}"));
                self.raw.entry(t.name).or_default().push(v);
            }
            25 => {
                // memory: alloca/store/load (loads may be poison)
                let p = self.fresh();
                self.line(format!("{p} = alloca {n}"));
                let v = self.value(t);
                self.line(format!("store {n} {v}, ptr {p}"));
                let l = self.fresh();
                self.line(format!("{l} = load {n}, ptr {p}"));
                self.raw.entry(t.name).or_default().push(l.clone());
                if self.rng.chance(50) {
                    self.define(t, &l);
                }
            }
            26 if self.use_invoke => {
                let a = self.value(I64);
                let r = self.fresh();
                self.line(format!("{r} = call @func.1({a})"));
                self.raw.entry("i64").or_default().push(r);
            }
            0..=2 => {
                let op =
                    ["add", "sub", "mul", "and", "or", "xor", "rotl", "rotr"][self.rng.below(8)];
                let a = self.value(t);
                let b = self.value(t);
                self.emit(t, format!("{op} {n} {a}, {b}"));
            }
            3 => {
                let op = ["neg", "not", "ctpop", "ctlz", "cttz", "bswap", "bitreverse"]
                    [self.rng.below(7)];
                let a = self.value(t);
                self.emit(t, format!("{op} {n} {a}"));
            }
            4 => {
                let pred = [
                    "eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge",
                ][self.rng.below(10)];
                let a = self.value(t);
                let b = self.value(t);
                self.emit(BOOL, format!("icmp {pred} {n} {a}, {b}"));
            }
            5 => {
                // every Bool operator kind
                let op = ["and", "or", "xor", "band", "bor", "bxor"][self.rng.below(6)];
                let a = self.value(BOOL);
                let b = self.value(BOOL);
                match self.rng.below(4) {
                    0 => {
                        let pred = ["eq", "ne"][self.rng.below(2)];
                        self.emit(BOOL, format!("icmp {pred} bool {a}, {b}"));
                    }
                    1 => {
                        let c = self.value(BOOL);
                        self.emit(BOOL, format!("select bool {c}, {a}, {b}"));
                    }
                    _ => {
                        self.emit(BOOL, format!("{op} bool {a}, {b}"));
                    }
                }
            }
            6 => {
                // casts between IT pairs
                let d = self.int_ty();
                let op = if d.width < t.width {
                    "trunc"
                } else if d.width > t.width {
                    if self.rng.chance(50) { "zext" } else { "sext" }
                } else {
                    return;
                };
                let a = self.value(t);
                self.emit(d, format!("{op} {n} {a} to {}", d.name));
            }
            7 => {
                // nested selects
                let ty = self.any_ty();
                let mut acc = self.value(ty);
                for _ in 0..(1 + self.rng.below(4)) {
                    let c = self.value(BOOL);
                    let other = self.value(ty);
                    let (a, b) = if self.rng.chance(50) {
                        (acc.clone(), other)
                    } else {
                        (other, acc.clone())
                    };
                    acc = self.emit(ty, format!("select {} {c}, {a}, {b}", ty.name));
                }
            }
            8 => {
                // copies of copies (defined)
                let ty = self.any_ty();
                let mut a = self.value(ty);
                for _ in 0..(1 + self.rng.below(3)) {
                    a = self.emit(ty, format!("copy {} {a}", ty.name));
                }
            }
            9 => {
                // duplicate equal instructions
                let op = ["add", "xor", "mul", "and"][self.rng.below(4)];
                let a = self.value(t);
                let b = self.value(t);
                self.emit(t, format!("{op} {n} {a}, {b}"));
                self.emit(t, format!("{op} {n} {a}, {b}"));
            }
            10 => {
                // a skeleton (non-total) op: leaf maker; nonzero divisor
                let a = self.value(t);
                let c = self.constant(t, 3);
                let op = ["udiv", "urem"][self.rng.below(2)];
                let v = self.fresh();
                self.line(format!("{v} = {op} {n} {a}, {c}"));
                self.pool.entry(t.name).or_default().push(v);
            }
            11 => {
                let x = self.value(t);
                let z = self.constant(t, 0);
                self.emit(t, format!("add {n} {x}, {z}"));
            }
            12 => {
                let x = self.value(t);
                let a = self.random_const(t);
                let b = self.random_const(t);
                let op = ["add", "mul", "and", "or", "xor"][self.rng.below(5)];
                let i = self.emit(t, format!("{op} {n} {x}, {a}"));
                self.emit(t, format!("{op} {n} {i}, {b}"));
            }
            13 => {
                let x = self.value(t);
                let op = ["sub", "xor", "and", "or"][self.rng.below(4)];
                self.emit(t, format!("{op} {n} {x}, {x}"));
            }
            14 => {
                let x = self.value(t);
                let c = self.random_const(t);
                self.emit(t, format!("sub {n} {x}, {c}"));
            }
            15 => {
                let b = self.rng.below(2) as u128;
                let c = self.constant(BOOL, b);
                let x = self.value(t);
                let y = self.value(t);
                self.emit(t, format!("select {n} {c}, {x}, {y}"));
            }
            16 => {
                let x = self.value(t);
                let op = ["neg", "not"][self.rng.below(2)];
                let a = self.emit(t, format!("{op} {n} {x}"));
                self.emit(t, format!("{op} {n} {a}"));
            }
            17 => {
                let a = self.random_const(t);
                let b = self.random_const(t);
                let op =
                    ["add", "sub", "mul", "and", "or", "xor", "rotl", "rotr"][self.rng.below(8)];
                self.emit(t, format!("{op} {n} {a}, {b}"));
            }
            18 => {
                let a = self.random_const(t);
                let op = ["neg", "not", "ctpop", "ctlz", "cttz", "bswap", "bitreverse"]
                    [self.rng.below(7)];
                self.emit(t, format!("{op} {n} {a}"));
            }
            19 => {
                let b = self.value(BOOL);
                let k = self.rng.below(2) as u128;
                let c = self.constant(BOOL, k);
                let op = ["band", "bor", "bxor", "and", "or", "xor"][self.rng.below(6)];
                self.emit(BOOL, format!("{op} bool {b}, {c}"));
            }
            27 => self.lanes(),
            20 => {
                let x = self.value(t);
                let w = u128::from(t.width) * (self.rng.below(3) as u128);
                let c = self.constant(t, w);
                let op = ["rotl", "rotr"][self.rng.below(2)];
                self.emit(t, format!("{op} {n} {x}, {c}"));
            }
            _ => {
                let ty = self.any_ty();
                self.random_const(ty);
            }
        }
    }

    /// A lane index of type `t` with value `target`: computed from two
    /// constants (the engine folds it to a `Const` the input does not have
    /// there), a copy of a constant, or (only when `in_range`: the validator
    /// range-checks a `Const` index) a constant.
    fn lane_index(&mut self, t: TyInfo, target: u128, in_range: bool) -> String {
        let n = t.name;
        let target = target & mask(t.width);
        match self.rng.below(if in_range { 5 } else { 4 }) {
            0 | 1 => {
                let a = self.residue(t);
                let ca = self.constant(t, a);
                let cb = self.constant(t, target.wrapping_sub(a));
                self.emit(t, format!("add {n} {ca}, {cb}"))
            }
            2 => {
                let a = self.residue(t);
                let ca = self.constant(t, a);
                let cb = self.constant(t, target ^ a);
                self.emit(t, format!("xor {n} {ca}, {cb}"))
            }
            3 => {
                let c = self.constant(t, target);
                self.emit(t, format!("copy {n} {c}"))
            }
            _ => self.constant(t, target),
        }
    }

    /// An element read or write of a constant four-lane vector at `index`;
    /// a read's result joins the defined pool (every lane is defined).
    fn element(&mut self, lane: TyInfo, vector: &str, index: &str) {
        let l = lane.name;
        if self.rng.chance(50) {
            self.emit(lane, format!("extractelement {l} {vector}, {index}"));
        } else {
            let x = self.value(lane);
            let w = self.fresh();
            self.line(format!(
                "{w} = insertelement <4 x {l}> {vector}, {index}, {x}"
            ));
            let t = self.int_ty();
            let k = self.rng.below(4) as u128;
            let read = self.lane_index(t, k, true);
            self.emit(lane, format!("extractelement {l} {w}, {read}"));
        }
    }

    /// Vector element ops at the literal-sensitive lane index position: in
    /// range on the current path, or out of range (`4..68`) in an arm taken
    /// on a maybe-poison condition, which traps there.
    fn lanes(&mut self) {
        // trust-ir vector lanes are fixed-width integers up to 64 bits
        // (`InvalidVectorType` otherwise): one of the function's own types
        // when it has one.
        let fixed =
            |t: &TyInfo| (8..=64).contains(&t.width) && !matches!(t.name, "isize" | "usize");
        let mut lanes: Vec<TyInfo> = self.types.iter().copied().filter(fixed).collect();
        if lanes.is_empty() {
            lanes = int_tys(64).into_iter().filter(fixed).collect();
        }
        let lane = lanes[self.rng.below(lanes.len())];
        let lanes: Vec<String> = (0..4)
            .map(|_| {
                let r = self.residue(lane);
                const_text(lane, r)
            })
            .collect();
        let vector = self.fresh();
        self.line(format!(
            "{vector} = const <4 x {}> vec[ {} ]",
            lane.name,
            lanes.join(", ")
        ));
        let t = self.int_ty();
        if self.rng.chance(20) {
            let cond = self.any_value(BOOL);
            let saved = self.snapshot();
            let tb = self.new_block(&[]);
            let cb = self.new_block(&[]);
            self.line(format!("condbr {cond}, bb{tb}, bb{cb}"));
            self.cur = tb;
            let target = 4 + self.rng.below(64) as u128;
            let index = self.lane_index(t, target, false);
            self.element(lane, &vector, &index);
            self.line("unreachable".to_owned());
            self.restore(&saved);
            self.cur = cb;
        } else {
            let target = self.rng.below(4) as u128;
            let index = self.lane_index(t, target, true);
            self.element(lane, &vector, &index);
        }
    }

    fn steps(&mut self, k: usize) {
        for _ in 0..k {
            if self.budget == 0 {
                return;
            }
            self.op();
        }
    }

    fn ret(&mut self) {
        let rets = self.rets.clone();
        let vals: Vec<String> = rets.iter().map(|t| self.any_value(*t)).collect();
        self.line(format!("ret {}", vals.join(", ")));
    }

    fn snapshot(&self) -> Pools {
        (self.pool.clone(), self.raw.clone())
    }
    fn restore(&mut self, s: &Pools) {
        self.pool = s.0.clone();
        self.raw = s.1.clone();
    }

    fn params_for(&mut self, k: usize) -> Vec<(String, TyInfo)> {
        (0..k)
            .map(|_| {
                let t = self.any_ty();
                (self.fresh(), t)
            })
            .collect()
    }
    fn args_for(&mut self, params: &[(String, TyInfo)]) -> String {
        let vals: Vec<String> = params.iter().map(|(_, t)| self.any_value(*t)).collect();
        if vals.is_empty() {
            String::new()
        } else {
            format!("({})", vals.join(", "))
        }
    }
    fn enter(&mut self, block: usize, params: &[(String, TyInfo)]) {
        self.cur = block;
        for (v, t) in params {
            if self.rng.chance(70) {
                self.define(*t, v);
            } else {
                self.raw.entry(t.name).or_default().push(v.clone());
            }
        }
    }

    /// Emit a region starting in the current block; returns with the
    /// current block open (not terminated). May terminate inner blocks.
    fn region(&mut self, depth: u32) {
        let k = 1 + self.rng.below(5);
        self.steps(k);
        if depth >= 6 || self.budget == 0 {
            return;
        }
        match self.rng.below(9) {
            0 | 1 => self.diamond(depth),
            2 if self.tag.is_some() && self.rng.chance(50) => self.tag_switch(depth),
            2 => self.switch(depth),
            3 => self.looped(depth),
            4 if self.use_invoke => self.invoke(depth),
            5 => self.early_return(),
            6 => self.unreachable_arm(),
            _ => self.trampoline(),
        }
        if self.rng.chance(50) {
            self.region(depth + 1);
        }
    }

    fn diamond(&mut self, depth: u32) {
        let cond = self.any_value(BOOL);
        let saved = self.snapshot();
        let k_tmp = self.rng.below(2);
        let tp = self.params_for(k_tmp);
        let k_tmp = self.rng.below(2);
        let ep = self.params_for(k_tmp);
        let jn = 1 + self.rng.below(4);
        let jp = self.params_for(jn);
        let tb = self.new_block(&tp);
        let eb = self.new_block(&ep);
        let jb = self.new_block(&jp);
        let targs = self.args_for(&tp);
        let eargs = self.args_for(&ep);
        // sibling duplicate over dominating values
        let t = self.int_ty();
        let dup_a = self.value(t);
        let dup_b = self.value(t);
        let after_dup = self.snapshot();
        self.line(format!("condbr {cond}, bb{tb}{targs}, bb{eb}{eargs}"));
        for (b, ps) in [(tb, tp.clone()), (eb, ep.clone())] {
            self.restore(&after_dup);
            self.enter(b, &ps);
            if self.rng.chance(60) {
                self.emit(t, format!("xor {} {dup_a}, {dup_b}", t.name));
                // a constant only in this branch
                self.constant(t, 0x1234);
            }
            self.region(depth + 1);
            let a = self.args_for(&jp);
            self.line(format!("br bb{jb}{a}"));
        }
        self.restore(&saved);
        self.enter(jb, &jp);
    }

    fn switch(&mut self, depth: u32) {
        let t = self.int_ty();
        let sel = self.any_value(t);
        let saved = self.snapshot();
        let k_tmp = 1 + self.rng.below(3);
        let jp = self.params_for(k_tmp);
        let ncases = 1 + self.rng.below(4);
        let mut arms = Vec::new();
        for _ in 0..=ncases {
            let k_tmp = self.rng.below(3);
            let ps = self.params_for(k_tmp);
            let b = self.new_block(&ps);
            arms.push((b, ps));
        }
        let jb = self.new_block(&jp);
        let mut text = format!("switch {sel} [");
        for (i, (b, ps)) in arms.iter().enumerate() {
            let a = self.args_for(ps);
            if i == ncases {
                let _ = write!(text, " default: bb{b}{a}");
            } else {
                let _ = write!(text, " {i}: bb{b}{a}");
            }
        }
        text.push_str(" ]");
        self.line(text);
        let after = self.snapshot();
        for (b, ps) in arms {
            self.restore(&after);
            self.enter(b, &ps);
            self.region(depth + 1);
            let a = self.args_for(&jp);
            self.line(format!("br bb{jb}{a}"));
        }
        self.restore(&saved);
        self.enter(jb, &jp);
    }

    /// A switch flagged `exhaustive` over the enum parameter's tag: the
    /// selector is the tag (`extractfield`, of the parameter or a copy of it)
    /// through 1-4 steps of `zext`/`sext` to a wider type, an equal-width
    /// `bitcast` flipping the signedness, a copy, or a graph identity (`add
    /// 0`, `mul 1`, `or 0`, `xor 0`, `sub 0`). Without an identity the
    /// validator holds the case set to the enum, so it is every discriminant;
    /// behind one it may also omit a discriminant or name a non-discriminant.
    /// The default block is `unreachable`, as the flag requires.
    fn tag_switch(&mut self, depth: u32) {
        let Some(e) = self.tag.clone() else {
            return self.switch(depth);
        };
        let mut source = e.param.clone();
        if self.rng.chance(20) {
            let c = self.fresh();
            self.line(format!("{c} = copy enum.0 {source}"));
            source = c;
        }
        let tag = self.fresh();
        self.line(format!(
            "{tag} = extractfield {} {source}, 0",
            e.tag_ty.name
        ));
        self.raw.entry(e.tag_ty.name).or_default().push(tag.clone());
        let mut cur = tag;
        let mut ty = e.tag_ty;
        let mut identity = false;
        let all = int_tys(64);
        for _ in 0..(1 + self.rng.below(4)) {
            match self.rng.below(6) {
                0 | 1 => {
                    let wider: Vec<TyInfo> = all
                        .iter()
                        .copied()
                        .filter(|t| t.width > ty.width && t.width <= 64)
                        .filter(|t| !matches!(t.name, "isize" | "usize"))
                        .collect();
                    if wider.is_empty() {
                        continue;
                    }
                    let to = wider[self.rng.below(wider.len())];
                    let op = if self.rng.chance(50) { "zext" } else { "sext" };
                    cur = self.emit(to, format!("{op} {} {cur} to {}", ty.name, to.name));
                    ty = to;
                }
                2 if self.bitcast => {
                    let Some(to) = all
                        .iter()
                        .copied()
                        .find(|t| t.width == ty.width && t.signed != ty.signed)
                        .filter(|t| !matches!(t.name, "isize" | "usize"))
                    else {
                        continue;
                    };
                    cur = self.emit(to, format!("bitcast {} {cur} to {}", ty.name, to.name));
                    ty = to;
                }
                2 | 3 => cur = self.emit(ty, format!("copy {} {cur}", ty.name)),
                _ => {
                    let (op, k) = [("add", 0), ("mul", 1), ("or", 0), ("xor", 0), ("sub", 0)]
                        [self.rng.below(5)];
                    let c = self.constant(ty, k);
                    cur = self.emit(ty, format!("{op} {} {cur}, {c}", ty.name));
                    identity = true;
                }
            }
        }
        let mut cases: Vec<usize> = (0..e.variants).collect();
        if identity && self.rng.chance(60) {
            if self.rng.chance(70) {
                let dropped = self.rng.below(cases.len());
                cases.remove(dropped);
            } else {
                cases.push(e.variants + 2);
            }
        }
        if cases.is_empty() {
            cases.push(0);
        }
        let saved = self.snapshot();
        let k_tmp = 1 + self.rng.below(2);
        let jp = self.params_for(k_tmp);
        let mut arms = Vec::new();
        for _ in &cases {
            let k_tmp = self.rng.below(2);
            let ps = self.params_for(k_tmp);
            let b = self.new_block(&ps);
            arms.push((b, ps));
        }
        let unreachable = self.new_block(&[]);
        let jb = self.new_block(&jp);
        let mut text = format!("switch {cur} [");
        for (case, (b, ps)) in cases.iter().zip(&arms) {
            let a = self.args_for(ps);
            let _ = write!(text, " {case}: bb{b}{a}");
        }
        let _ = write!(text, " default: bb{unreachable} ] exhaustive");
        self.line(text);
        self.cur = unreachable;
        self.line("unreachable".to_owned());
        let after = self.snapshot();
        for (b, ps) in arms {
            self.restore(&after);
            self.enter(b, &ps);
            self.region(depth + 1);
            let a = self.args_for(&jp);
            self.line(format!("br bb{jb}{a}"));
        }
        self.restore(&saved);
        self.enter(jb, &jp);
    }

    fn looped(&mut self, depth: u32) {
        let counter = self.int_ty();
        let n = counter.name;
        let mut hp = vec![(self.fresh(), counter)];
        let k_tmp = 1 + self.rng.below(6);
        hp.extend(self.params_for(k_tmp));
        let hb = self.new_block(&hp);
        let init = self.constant(counter, 0);
        let rest = self.args_for(&hp[1..]);
        let rest = rest
            .trim_start_matches('(')
            .trim_end_matches(')')
            .to_owned();
        let args = if rest.is_empty() {
            format!("({init})")
        } else {
            format!("({init}, {rest})")
        };
        self.line(format!("br bb{hb}{args}"));
        self.cur = hb;
        let i = hp[0].0.clone();
        let z = self.constant(counter, 0);
        let di = self.emit(counter, format!("xor {n} {i}, {z}"));
        self.enter(hb, &hp[1..]);
        // loop-invariant computations over pre-loop values
        self.region(depth + 1);
        let one = self.constant(counter, 1);
        let next = self.emit(counter, format!("add {n} {di}, {one}"));
        let limit = self.constant(counter, 3);
        let c = self.emit(BOOL, format!("icmp ult {n} {next}, {limit}"));
        let rest = self.args_for(&hp[1..]);
        let rest = rest
            .trim_start_matches('(')
            .trim_end_matches(')')
            .to_owned();
        let back = if rest.is_empty() {
            format!("({next})")
        } else {
            format!("({next}, {rest})")
        };
        let xb = self.new_block(&[]);
        self.line(format!("condbr {c}, bb{hb}{back}, bb{xb}"));
        // The exit block is dominated by the block that ends the loop body,
        // so the pools of the loop stay visible.
        self.cur = xb;
    }

    /// An invoke of `@inc`, in one of the shapes section 4 admits: its
    /// result read in the normal successor's region, passed in its own
    /// normal-edge arguments, or read in a normal successor that is a loop
    /// header (its back edge comes from itself). The unwind successor is a
    /// landing pad block that never reads the result.
    fn invoke(&mut self, depth: u32) {
        let a = self.any_value(I64);
        let saved = self.snapshot();
        let r = self.fresh();
        match self.rng.below(3) {
            0 => {
                let nb = self.new_block(&[]);
                let lb = self.new_block(&[]);
                self.line(format!(
                    "{r} = invoke @func.1({a}) to bb{nb}() unwind bb{lb}"
                ));
                self.landing_pad(lb, &saved);
                self.cur = nb;
                self.define(I64, &r);
                self.region(depth + 1);
            }
            1 => {
                let q = (self.fresh(), I64);
                let nb = self.new_block(std::slice::from_ref(&q));
                let lb = self.new_block(&[]);
                self.line(format!(
                    "{r} = invoke @func.1({a}) to bb{nb}({r}) unwind bb{lb}"
                ));
                self.landing_pad(lb, &saved);
                self.enter(nb, &[q]);
                if self.rng.chance(50) {
                    self.define(I64, &r);
                }
                self.region(depth + 1);
            }
            _ => {
                let init = self.constant(I64, 0);
                let saved = self.snapshot();
                let i = self.fresh();
                let hb = self.new_block(&[(i.clone(), I64)]);
                let lb = self.new_block(&[]);
                self.line(format!(
                    "{r} = invoke @func.1({a}) to bb{hb}({init}) unwind bb{lb}"
                ));
                self.landing_pad(lb, &saved);
                self.cur = hb;
                self.define(I64, &r);
                let z = self.constant(I64, 0);
                let di = self.emit(I64, format!("xor i64 {i}, {z}"));
                let k = 1 + self.rng.below(3);
                self.steps(k);
                let one = self.constant(I64, 1);
                let next = self.emit(I64, format!("add i64 {di}, {one}"));
                let limit = self.constant(I64, 3);
                let c = self.emit(BOOL, format!("icmp ult i64 {next}, {limit}"));
                let xb = self.new_block(&[]);
                self.line(format!("condbr {c}, bb{hb}({next}), bb{xb}"));
                self.cur = xb;
                self.region(depth + 1);
            }
        }
    }

    /// The unwind successor: a cleanup pad, a few instructions over values
    /// that dominate the invoke, and a return.
    fn landing_pad(&mut self, block: usize, saved: &Pools) {
        self.restore(saved);
        self.cur = block;
        let p0 = self.fresh();
        let p1 = self.fresh();
        self.line(format!("{p0}, {p1} = landingpad cleanup"));
        let k = 1 + self.rng.below(4);
        self.steps(k);
        self.ret();
        self.restore(saved);
    }

    fn unreachable_arm(&mut self) {
        let cond = self.any_value(BOOL);
        let ub = self.new_block(&[]);
        let cb = self.new_block(&[]);
        self.line(format!("condbr {cond}, bb{ub}, bb{cb}"));
        self.cur = ub;
        self.line("unreachable".to_owned());
        self.cur = cb;
    }

    /// Single-instruction blocks: `br` to a block that only branches on.
    fn trampoline(&mut self) {
        let k_tmp = self.rng.below(3);
        let tp = self.params_for(k_tmp);
        let k_tmp = self.rng.below(3);
        let np = self.params_for(k_tmp);
        let tb = self.new_block(&tp);
        let nb = self.new_block(&np);
        let a = self.args_for(&tp);
        let n = self.args_for(&np);
        self.line(format!("br bb{tb}{a}"));
        self.cur = tb;
        self.line(format!("br bb{nb}{n}"));
        self.enter(nb, &np);
    }

    fn early_return(&mut self) {
        let cond = self.any_value(BOOL);
        let saved = self.snapshot();
        let rb = self.new_block(&[]);
        let cb = self.new_block(&[]);
        self.line(format!("condbr {cond}, bb{rb}, bb{cb}"));
        self.cur = rb;
        let k_tmp = 1 + self.rng.below(3);
        self.steps(k_tmp);
        self.ret();
        self.restore(&saved);
        self.cur = cb;
    }
}

fn structured_module_text(index: u64) -> String {
    let mut rng = Rng(0xC0FF_EE00_0000_0000 ^ index.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    let pointer_bits = [64u32, 32, 16][rng.below(3)];
    let all = int_tys(pointer_bits);
    let mut types = vec![BOOL];
    let use_invoke = rng.chance(30);
    if use_invoke {
        types.push(I64);
    }
    for _ in 0..=rng.below(3) {
        let t = all[rng.below(all.len())];
        if !types.contains(&t) {
            types.push(t);
        }
    }
    let nrets = 1 + rng.below(2);
    let tag = rng.chance(40).then(|| {
        let tag_ty = TAG_TYS[rng.below(TAG_TYS.len())];
        let variants = 2 + rng.below(3);
        (tag_ty, variants)
    });
    let mut g = Gen {
        rng,
        next: 0,
        blocks: Vec::new(),
        cur: 0,
        pool: BTreeMap::new(),
        raw: BTreeMap::new(),
        types: types.clone(),
        rets: Vec::new(),
        budget: 150,
        use_invoke,
        tag: None,
        bitcast: pointer_bits != 16,
    };
    g.rets = (0..nrets).map(|_| g.any_ty()).collect();
    let np = 1 + g.rng.below(3);
    let params = g.params_for(np);
    let entry = g.new_block(&params);
    if let Some((tag_ty, variants)) = tag {
        let param = g.fresh();
        let header = &mut g.blocks[entry].header;
        if let Some(open) = header.strip_suffix("):") {
            *header = format!("{open}, {param}: enum.0):");
        }
        g.tag = Some(TagEnum {
            param,
            tag_ty,
            variants,
        });
    }
    g.enter(entry, &params);
    if g.tag.is_some() {
        let k = 1 + g.rng.below(3);
        g.steps(k);
        g.tag_switch(1);
    }
    g.region(0);
    g.ret();
    let mut body = String::new();
    for b in &g.blocks {
        body.push_str(&b.header);
        body.push('\n');
        for l in &b.lines {
            body.push_str(l);
            body.push('\n');
        }
    }
    let target = match pointer_bits {
        64 => String::new(),
        32 => "target \"wasm32-unknown-unknown\" 4 little\n".to_owned(),
        _ => "target \"msp430-none-elf\" 2 little\n".to_owned(),
    };
    let mut ptys: Vec<&str> = params.iter().map(|(_, t)| t.name).collect();
    let enum_decl = match tag {
        Some((tag_ty, variants)) => {
            ptys.push("enum.0");
            let names: Vec<String> = (0..variants).map(|v| format!("V{v}")).collect();
            format!(
                "enum @E repr({}) {{ {} }} id=0\n\n",
                tag_ty.name,
                names.join(", ")
            )
        }
        None => String::new(),
    };
    let rtys: Vec<&str> = g.rets.iter().map(|t| t.name).collect();
    let callee = if use_invoke {
        "\nfn @inc(functy.1) {\nbb0(%0: i64):\n    %1 = const i64 1\n    %2 = add i64 %0, %1\n    ret %2\n}\n"
    } else {
        ""
    };
    format!(
        "; TrustIr text format v1\nmodule \"s{index}\"\n{target}\n{enum_decl}functy.0 = ({}) -> ({})\nfuncty.1 = (i64) -> (i64)\n\nfn @f(functy.0) {{\n{body}}}\n{callee}",
        ptys.join(", "),
        rtys.join(", "),
    )
}

/// What the valid modules contain, by feature.
fn coverage(text: &str, module: &Module, counts: &mut BTreeMap<&'static str, usize>) {
    let mut see = |key: &'static str, present: bool| {
        if present {
            *counts.entry(key).or_default() += 1;
        }
    };
    for key in [
        "switch",
        "invoke",
        "landingpad",
        "unreachable",
        "condbr",
        "msp430",
        "wasm32",
        "i128",
        "u128",
        "isize",
        "usize",
        "select",
        "copy",
        "sext",
        "trunc",
        "zext",
        "band",
        "bor",
        "bxor",
        "overflow",
        "undef",
        "alloca",
        "call",
        "udiv",
        "extractelement",
        "insertelement",
    ] {
        see(key, text.contains(key));
    }
    let f = function_named(module, "f");
    let insts = || f.blocks.iter().flat_map(|b| &b.body);
    // A lane index the engine folds: an element op whose index a graph
    // operator over constants computes.
    let defs: BTreeMap<trust_ir::ValueId, &Inst> = insts()
        .flat_map(|n| n.results.iter().map(move |r| (*r, &n.inst)))
        .collect();
    see(
        "lane index computed from constants",
        insts().any(|n| match &n.inst {
            Inst::ExtractElement { index, .. } | Inst::InsertElement { index, .. } => {
                matches!(defs.get(index), Some(Inst::BinOp { .. }))
            }
            _ => false,
        }),
    );
    see(
        "u128 above i128::MAX",
        insts().any(|n| {
            matches!(
                n.inst,
                Inst::Const {
                    value: Constant::U128(_),
                    ..
                }
            )
        }),
    );
    see(
        "invoke result in its own normal-edge arguments",
        insts().any(|n| match &n.inst {
            Inst::Invoke { normal_args, .. } => n.results.iter().any(|r| normal_args.contains(r)),
            _ => false,
        }),
    );
    // Exhaustive switches over an enum tag: what lies on the selector's way
    // to the tag (identities seen through on their non-constant operand).
    let variants = module.enums.first().map_or(0, |e| e.variants.len());
    let mut steps: Vec<&'static str> = Vec::new();
    for node in insts() {
        let Inst::Switch {
            value,
            cases,
            exhaustive_enum_unreachable: true,
            ..
        } = &node.inst
        else {
            continue;
        };
        steps.push("exhaustive switch");
        let mut current = *value;
        let mut identity = false;
        for _ in 0..=defs.len() {
            match defs.get(&current).copied() {
                Some(Inst::Copy { operand, .. }) => {
                    steps.push("exhaustive switch through a copy");
                    current = *operand;
                }
                Some(Inst::Cast { op, operand, .. }) => {
                    steps.push(match op {
                        trust_ir::CastOp::ZExt => "exhaustive switch through zext",
                        trust_ir::CastOp::SExt => "exhaustive switch through sext",
                        trust_ir::CastOp::Bitcast => "exhaustive switch through bitcast",
                        _ => "exhaustive switch through another cast",
                    });
                    current = *operand;
                }
                Some(Inst::BinOp { lhs, rhs, .. })
                    if matches!(defs.get(rhs), Some(Inst::Const { .. })) =>
                {
                    identity = true;
                    steps.push("exhaustive switch through an identity");
                    current = *lhs;
                }
                Some(Inst::ExtractField { field: 0, .. }) => {
                    steps.push("exhaustive switch over an enum tag");
                    break;
                }
                _ => break,
            }
        }
        steps.push(if cases.len() < variants {
            "exhaustive switch with an incomplete case set"
        } else {
            "exhaustive switch with a complete case set"
        });
        if identity && cases.len() < variants {
            steps.push("exhaustive switch incomplete behind an identity");
        }
    }
    steps.sort_unstable();
    steps.dedup();
    for step in steps {
        see(step, true);
    }
    see(
        "invoke into a loop header",
        insts().any(|n| match &n.inst {
            Inst::Invoke { normal_dest, .. } => f.blocks.iter().any(|b| {
                b.id == *normal_dest
                    && b.body
                        .last()
                        .is_some_and(|t| t.inst.successor_edges().iter().any(|e| e.target == b.id))
            }),
            _ => false,
        }),
    );
}

#[test]
fn structured_random_modules_meet_every_engine_contract() {
    let mut invalid: BTreeMap<String, usize> = BTreeMap::new();
    let mut audited = 0usize;
    let mut rewritten = 0usize;
    let mut failures: Vec<(u64, Vec<String>, String)> = Vec::new();
    let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    for index in 0..MODULES {
        let text = structured_module_text(index);
        let module = match parse(&text) {
            Ok(m) => m,
            Err(e) => {
                let key: String = e.chars().take(160).collect();
                *invalid.entry(key).or_default() += 1;
                continue;
            }
        };
        audited += 1;
        coverage(&text, &module, &mut counts);
        let (problems, rw) = audit(&module, "f", index);
        rewritten += usize::from(rw);
        if rw && text.contains("] exhaustive") {
            *counts
                .entry("exhaustive switch in a rewritten function")
                .or_default() += 1;
        }
        if !problems.is_empty() {
            failures.push((index, problems, text));
        }
    }
    eprintln!("{MODULES} generated, {audited} valid, {rewritten} rewritten");
    eprintln!("coverage (valid modules containing): {counts:?}");
    for (k, v) in &invalid {
        eprintln!("  invalid x{v}: {k}");
    }
    for (index, problems, text) in failures.iter().take(3) {
        eprintln!("---- module {index}:");
        for p in problems {
            eprintln!("  {}", p.chars().take(600).collect::<String>());
        }
        eprintln!("{text}");
    }
    assert!(failures.is_empty(), "{} failing modules", failures.len());
    // The generator keeps generating what this test is for.
    assert!(
        audited * 10 >= MODULES as usize * 9,
        "too few valid modules"
    );
    assert!(
        rewritten * 4 >= audited,
        "too few rewrites: {rewritten}/{audited}"
    );
    for key in [
        "switch",
        "invoke",
        "landingpad",
        "msp430",
        "wasm32",
        "i128",
        "u128",
        "isize",
        "usize",
        "overflow",
        "undef",
        "alloca",
        "call",
        "u128 above i128::MAX",
        "invoke result in its own normal-edge arguments",
        "invoke into a loop header",
        "extractelement",
        "insertelement",
        "lane index computed from constants",
        "exhaustive switch",
        "exhaustive switch over an enum tag",
        "exhaustive switch through a copy",
        "exhaustive switch through zext",
        "exhaustive switch through sext",
        "exhaustive switch through bitcast",
        "exhaustive switch through an identity",
        "exhaustive switch with a complete case set",
        "exhaustive switch with an incomplete case set",
        "exhaustive switch incomplete behind an identity",
        "exhaustive switch in a rewritten function",
    ] {
        assert!(
            counts.get(key).copied().unwrap_or(0) > 0,
            "no module has {key}: {counts:?}"
        );
    }
}

/// The audit can fail: the checker refuses a rewritten output with the
/// header-only derivation, and the differential sees a wrong body.
#[test]
fn the_audit_is_not_vacuous() {
    let text = "; TrustIr text format v1\nmodule \"m\"\n\nfuncty.0 = (i32) -> (i32)\n\n\
                fn @f(functy.0) {\nbb0(%0: i32):\n    %1 = const i32 0\n    %2 = xor i32 %0, %1\n    \
                %3 = add i32 %2, %1\n    %4 = udiv i32 %3, %3\n    ret %4\n}\n";
    let module = parse(text).unwrap();
    let f = function_named(&module, "f");
    let out = optimize_function(&module, f, &rules(), &EngineConfig::default()).unwrap();
    assert!(out.rewritten);
    assert!(check(&module, f, &out.function, &out.derivation, &registry()).is_ok());
    assert!(
        check(
            &module,
            f,
            &out.function,
            &header_only(&f.name),
            &registry()
        )
        .is_err()
    );
    let wrong = parse(&text.replace("udiv i32 %3, %3", "add i32 %3, %3")).unwrap();
    let mut wrong_f = function_named(&wrong, "f").clone();
    wrong_f.id = f.id;
    assert!(differential(&module, f, &substituted(&module, &wrong_f), 1).is_some());
}
