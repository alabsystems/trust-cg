// trust_ir_interp_differential.rs — trust-ir -> native differential gate
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! WS7.2 (F-111, `crit.misw10`): the trust-ir -> LIR adapter sits OUTSIDE
//! every certificate trust-cg writes (`covered_span: "lir->machine"`), so an
//! adapter miscompile — an `InsertField` whose result aliased its base —
//! compiled silently and `--emit-proofs` still published `[VERIFIED]` rules
//! for it. Until an end-to-end trust-ir -> machine obligation exists (WS7.16),
//! this gate is the check on that step: every module of a corpus is
//! JIT-compiled at O0..O3, run natively, and compared, vector by vector, with
//! the trust-ir reference interpreter (`trust_ir::interpret::Interpreter`,
//! always on in trust-ir, so no new dependency).
//!
//! * **Vendored corpus** (`tests/fixtures/trust_ir_exec/`, `MANIFEST.tsv`:
//!   module, entry, argument vectors): the proof program's own miscompile
//!   witnesses (Part A-Lean `struct`, c13's shared/own seed and `shared_nomul`,
//!   the Rust tuple shape `c13c`) and the WS7.1 families (aggregate loop
//!   headers, block-parameter swaps, loop-carried aggregate `Load`s, parameter
//!   bases, `insertelement`, nested fields, packed structs, `select` bases).
//! * **Generated corpus**: a seeded generator of aggregate programs over the
//!   same families (insert chains off a shared base, extract-after-insert,
//!   aggregates carried around loops, loop-carried aggregate `Load`s,
//!   block-parameter swaps, parameter bases, nested aggregate fields, packed
//!   structs). Its seeds are FIXED and pinned (`GENERATOR_SEEDS`), so a run is
//!   reproducible; every generated module must be VALID trust-ir.
//!
//! **Vacuity rule.** A vector on which the interpreter reports
//! `UndefinedBehavior` is SKIPPED (any native result refines UB). Every other
//! interpreter error FAILS the test. Each corpus entry must compare at least
//! one vector: an entry whose every vector is skipped is a failure, not a
//! pass. Each run prints its compared/skipped counts.
//!
//! **Mutation control** (`--features mutation-knobs`): with
//! `legacy_in_place_insert` on (the historical F-111 lowering), the same gate
//! must report the c13 mismatches — `dotOf(1,2,3,4)` native 25 vs interpreter
//! 11, `two_inserts_sub(9,2)` native 0 vs 7 — and must catch the bug in the
//! generated corpus too. That is what makes the positive run discriminating.
//!
//! The differential is statistical, not a proof: it samples vectors and
//! programs. JIT host coverage is AArch64 (macOS, Linux/glibc) and x86-64
//! (Linux, macOS).
#![cfg(any(
    all(
        target_arch = "aarch64",
        any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
    ),
    all(
        target_arch = "x86_64",
        any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
    )
))]

use std::collections::HashMap;
use std::fmt::Write as _;
use std::sync::Mutex;

use trust_cg_codegen::compiler::JitValidationMode;
use trust_cg_codegen::{
    CodegenLicensePolicy, Compiler, CompilerConfig, CoreHostJitTarget, Target,
    UnlicensedBodyPolicy, jit::ExecutableBuffer, pipeline::OptLevel,
};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::{Module, Ty};

/// The mutation knob is process-global; every test that compiles holds this.
static KNOB: Mutex<()> = Mutex::new(());

const FIXTURES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/trust_ir_exec");

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// The pinned generator seeds. Changing this list changes the corpus; a seed
/// is never removed to make a run pass.
const GENERATOR_SEEDS: [u64; 24] = [
    0x5753_372e_3201,
    0x0000_0000_0001,
    0x0000_0000_0002,
    0x0000_0000_0003,
    0x0000_0000_0005,
    0x0000_0000_0008,
    0x0000_0000_000d,
    0x0000_0000_0015,
    0x0000_0000_0022,
    0x0000_0000_0037,
    0x0000_0000_0059,
    0x0000_0000_0090,
    0xdead_beef_0001,
    0xdead_beef_0002,
    0xc0ff_ee00_0013,
    0xf111_0000_0001,
    0xf111_0000_0002,
    0xf111_0000_0003,
    0x1234_5678_9abc,
    0x0bad_cafe_f00d,
    0x7777_7777_7777,
    0x0102_0304_0506,
    0x2026_1007_0072,
    0xffff_ffff_fffe,
];

// ---------------------------------------------------------------------------
// Corpus
// ---------------------------------------------------------------------------

/// One entry point of a corpus module and the argument vectors it runs.
#[derive(Debug, Clone)]
struct Entry {
    function: String,
    vectors: Vec<Vec<u64>>,
}

/// One corpus module.
struct CorpusModule {
    label: String,
    module: Module,
    entries: Vec<Entry>,
}

fn parse_valid(label: &str, text: &str) -> Module {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("parse {label}: {e:?}\n{text}"));
    assert_eq!(
        trust_ir_build::validate_module(&module),
        [],
        "{label} must be VALID trust-ir: a differential over input the format \
         refuses says nothing about the consumer\n{text}"
    );
    module
}

fn parse_u64(text: &str) -> u64 {
    let text = text.trim();
    let parsed = match text.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(&hex.replace('_', ""), 16),
        None => text.replace('_', "").parse::<u64>(),
    };
    parsed.unwrap_or_else(|e| panic!("bad manifest argument `{text}`: {e}"))
}

/// The host label a manifest row may restrict itself to.
fn host_label() -> &'static str {
    if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
        "aarch64-macos"
    } else if cfg!(all(target_arch = "aarch64", target_os = "linux")) {
        "aarch64-linux"
    } else if cfg!(all(target_arch = "x86_64", target_os = "macos")) {
        "x86_64-macos"
    } else {
        "x86_64-linux"
    }
}

/// The vendored corpus, read from `MANIFEST.tsv`: `module<TAB>entry<TAB>
/// vectors[<TAB>hosts]`, vectors `;`-separated, each a `,`-separated argument
/// list, optional hosts a `,`-separated list of [`host_label`]s.
fn vendored_corpus() -> Vec<CorpusModule> {
    let manifest = std::fs::read_to_string(format!("{FIXTURES}/MANIFEST.tsv"))
        .expect("read trust_ir_exec/MANIFEST.tsv");
    let mut order: Vec<String> = Vec::new();
    let mut rows: HashMap<String, Vec<Entry>> = HashMap::new();
    for (line_no, line) in manifest.lines().enumerate() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let columns: Vec<&str> = line.split('\t').collect();
        assert!(
            (3..=4).contains(&columns.len()),
            "MANIFEST.tsv:{}: expected 3 or 4 tab-separated columns: {line}",
            line_no + 1
        );
        if let Some(hosts) = columns.get(3)
            && !hosts.split(',').any(|host| host.trim() == host_label())
        {
            continue;
        }
        let vectors: Vec<Vec<u64>> = columns[2]
            .split(';')
            .map(|vector| {
                if vector.trim().is_empty() {
                    Vec::new()
                } else {
                    vector.split(',').map(parse_u64).collect()
                }
            })
            .collect();
        assert!(
            !vectors.is_empty(),
            "MANIFEST.tsv:{}: an entry needs at least one vector",
            line_no + 1
        );
        let module = columns[0].to_string();
        if !rows.contains_key(&module) {
            order.push(module.clone());
        }
        rows.entry(module).or_default().push(Entry {
            function: columns[1].to_string(),
            vectors,
        });
    }
    // Every vendored module is named by the manifest: a fixture nobody runs is
    // a corpus entry that silently compares nothing.
    let mut on_disk: Vec<String> = std::fs::read_dir(FIXTURES)
        .expect("list trust_ir_exec")
        .map(|entry| {
            entry
                .expect("dir entry")
                .file_name()
                .into_string()
                .expect("utf8")
        })
        .filter(|name| name.ends_with(".trust_ir"))
        .collect();
    on_disk.sort();
    let manifest_text = manifest.clone();
    for name in &on_disk {
        assert!(
            manifest_text
                .lines()
                .any(|line| line.split('\t').next() == Some(name.as_str())),
            "trust_ir_exec/{name} is not named by MANIFEST.tsv"
        );
    }
    order
        .into_iter()
        .map(|name| {
            let path = format!("{FIXTURES}/{name}");
            let text =
                std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
            let module = parse_valid(&name, &text);
            let entries = rows.remove(&name).expect("rows");
            CorpusModule {
                label: name,
                module,
                entries,
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Execution
// ---------------------------------------------------------------------------

fn license() -> CodegenLicensePolicy {
    // The vendored modules are licensed exactly as their producers stamped
    // them: the c13 repro's own authority name, the Rust direct lane's
    // structural authority, and `body_gate: None` (Permit, stated EXPLICITLY).
    CodegenLicensePolicy::default()
        .with_recognized_authority("c13-repro")
        .with_recognized_authority("trust-direct-lane-structural")
        .with_unlicensed(UnlicensedBodyPolicy::Permit)
}

fn compiler(opt: OptLevel) -> Compiler {
    let host = CoreHostJitTarget::detect().expect("supported native JIT test host");
    let target = if cfg!(target_arch = "aarch64") {
        Target::Aarch64
    } else {
        Target::X86_64
    };
    let mut config = CompilerConfig::jit_fast(target);
    config.opt_level = opt;
    // The differential IS the check on these bytes; it does not rest on JIT
    // certificate coverage (AArch64's default is already Unchecked).
    config.jit_validation_mode_override = Some(JitValidationMode::Unchecked);
    Compiler::new_for_target_spec(config, host.target_spec()).with_codegen_license(license())
}

fn jit(module: &Module, label: &str, opt: OptLevel) -> ExecutableBuffer {
    compiler(opt)
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|e| panic!("JIT compile of `{label}` at {opt:?}: {e}"))
        .buffer
}

/// An entry point's scalar signature: each parameter's and the result's
/// `(bits, signed)`.
struct ScalarSig {
    params: Vec<(Ty, u32, bool)>,
    ret: (Ty, u32, bool),
}

fn scalar_shape(ty: &Ty) -> Option<(u32, bool)> {
    Some(match ty {
        Ty::Bool => (1, false),
        Ty::U8 => (8, false),
        Ty::U16 => (16, false),
        Ty::U32 => (32, false),
        Ty::U64 => (64, false),
        Ty::I8 => (8, true),
        Ty::I16 => (16, true),
        Ty::I32 => (32, true),
        Ty::I64 => (64, true),
        _ => return None,
    })
}

fn entry_sig(module: &Module, label: &str, name: &str) -> ScalarSig {
    let function = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("{label}: no function `{name}`"));
    let fty = module
        .func_type(function.ty)
        .unwrap_or_else(|| panic!("{label}: `{name}` has no function type"));
    let shape = |ty: &Ty| {
        let (bits, signed) = scalar_shape(ty).unwrap_or_else(|| {
            panic!(
                "{label}: entry `{name}` must have scalar integer parameters and result, got {ty:?}"
            )
        });
        (ty.clone(), bits, signed)
    };
    assert!(
        fty.params.len() <= 6 && fty.returns.len() == 1 && !fty.is_vararg,
        "{label}: entry `{name}` must take at most six scalars and return one"
    );
    ScalarSig {
        params: fty.params.iter().map(shape).collect(),
        ret: shape(&fty.returns[0]),
    }
}

fn mask(value: u64, bits: u32) -> u64 {
    if bits >= 64 {
        value
    } else {
        value & ((1u64 << bits) - 1)
    }
}

/// The register image of `value` as an argument of `(bits, signed)`: zero-
/// or sign-extended to 64 bits, so both AAPCS64 (upper bits unspecified) and
/// Darwin (callers extend) read the same value.
fn register_image(value: u64, bits: u32, signed: bool) -> u64 {
    let narrow = mask(value, bits);
    if signed && bits < 64 && narrow >> (bits - 1) & 1 == 1 {
        narrow | !((1u64 << bits) - 1)
    } else {
        narrow
    }
}

/// Call `name` natively with register images of `args`; the raw x0/rax.
fn call_native(buffer: &ExecutableBuffer, name: &str, args: &[u64]) -> u64 {
    type F0 = extern "C" fn() -> u64;
    type F1 = extern "C" fn(u64) -> u64;
    type F2 = extern "C" fn(u64, u64) -> u64;
    type F3 = extern "C" fn(u64, u64, u64) -> u64;
    type F4 = extern "C" fn(u64, u64, u64, u64) -> u64;
    type F5 = extern "C" fn(u64, u64, u64, u64, u64) -> u64;
    type F6 = extern "C" fn(u64, u64, u64, u64, u64, u64) -> u64;
    // SAFETY: `entry_sig` checked that `name` takes exactly `args.len()`
    // integer scalars (<= 64 bits, passed in the first integer argument
    // registers under both the C and the Rust convention on these hosts) and
    // returns one integer scalar in the first return register; each argument
    // is already extended to its register image. `buffer` outlives the call.
    unsafe {
        match *args {
            [] => buffer.get_fn_bound::<F0>(name).expect(name).as_ref()(),
            [a] => buffer.get_fn_bound::<F1>(name).expect(name).as_ref()(a),
            [a, b] => buffer.get_fn_bound::<F2>(name).expect(name).as_ref()(a, b),
            [a, b, c] => buffer.get_fn_bound::<F3>(name).expect(name).as_ref()(a, b, c),
            [a, b, c, d] => buffer.get_fn_bound::<F4>(name).expect(name).as_ref()(a, b, c, d),
            [a, b, c, d, e] => buffer.get_fn_bound::<F5>(name).expect(name).as_ref()(a, b, c, d, e),
            [a, b, c, d, e, f] => {
                buffer.get_fn_bound::<F6>(name).expect(name).as_ref()(a, b, c, d, e, f)
            }
            _ => panic!("unsupported arity {}", args.len()),
        }
    }
}

/// The interpreter's verdict on one vector.
enum Oracle {
    /// The masked result.
    Value(u64),
    /// `UndefinedBehavior` (its message): any native result refines it.
    Undefined(String),
}

/// One entry point's oracle: its name, its scalar signature, and every input
/// vector with the interpreter's verdict on it.
type EntryOracle = (String, ScalarSig, Vec<(Vec<u64>, Oracle)>);

fn interpret(module: &Module, label: &str, name: &str, sig: &ScalarSig, args: &[u64]) -> Oracle {
    let function = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .expect("entry checked by entry_sig");
    let values = sig
        .params
        .iter()
        .zip(args)
        .map(|((ty, bits, signed), raw)| {
            if *ty == Ty::Bool {
                return InterpretValue::bool(raw & 1 == 1);
            }
            let narrow = mask(*raw, *bits);
            let value = if *signed && *bits < 64 && narrow >> (bits - 1) & 1 == 1 {
                i128::from(narrow) - (1i128 << bits)
            } else if *signed && *bits == 64 {
                i128::from(narrow as i64)
            } else {
                i128::from(narrow)
            };
            InterpretValue::int(ty.clone(), value).expect("integer argument")
        });
    match Interpreter::with_module(module).execute_function(function, values) {
        Ok(outcome) => {
            let [ret] = outcome.returns.as_slice() else {
                panic!(
                    "{label}: {name}{args:?}: expected one result, got {:?}",
                    outcome.returns
                )
            };
            let raw = if let Some(b) = ret.as_bool() {
                u64::from(b)
            } else {
                let int = ret.as_int().unwrap_or_else(|| {
                    panic!("{label}: {name}{args:?}: non-integer result {ret:?}")
                });
                int.as_unsigned() as u64
            };
            Oracle::Value(mask(raw, sig.ret.1))
        }
        Err(e) if e.code == InterpretErrorCode::UndefinedBehavior => Oracle::Undefined(e.message),
        Err(e) => panic!(
            "{label}: {name}{args:?}: the interpreter failed with `{}` ({}); only \
             UndefinedBehavior may skip a vector",
            e.code, e.message
        ),
    }
}

/// One native/interpreter disagreement.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Mismatch {
    module: String,
    function: String,
    args: Vec<u64>,
    opt: OptLevel,
    native: u64,
    interpreter: u64,
}

#[derive(Debug, Default)]
struct Report {
    compared: usize,
    skipped: usize,
    mismatches: Vec<Mismatch>,
    /// Entries whose every vector was skipped (a vacuity failure).
    vacuous: Vec<String>,
    /// Why vectors were skipped: the interpreter's UB message, with counts.
    skip_reasons: std::collections::BTreeMap<String, usize>,
}

impl Report {
    fn summary(&self, what: &str) -> String {
        let mut out = format!(
            "{what}: compared={} skipped={} mismatches={} vacuous-entries={}",
            self.compared,
            self.skipped,
            self.mismatches.len(),
            self.vacuous.len()
        );
        for m in self.mismatches.iter().take(20) {
            let _ = write!(
                out,
                "\n  MISMATCH {}::{}{:?} at {:?}: native {} interpreter {}",
                m.module, m.function, m.args, m.opt, m.native, m.interpreter
            );
        }
        for v in &self.vacuous {
            let _ = write!(out, "\n  VACUOUS {v}: every vector was skipped");
        }
        for (reason, count) in &self.skip_reasons {
            let _ = write!(out, "\n  skipped {count}x (undefined behaviour): {reason}");
        }
        out
    }
}

/// Run the differential over `corpus` at every opt level.
fn run(corpus: &[CorpusModule]) -> Report {
    let mut report = Report::default();
    for item in corpus {
        // The oracle is opt-independent: evaluate it once per vector.
        let mut oracle: Vec<EntryOracle> = Vec::new();
        for entry in &item.entries {
            let sig = entry_sig(&item.module, &item.label, &entry.function);
            let mut verdicts = Vec::new();
            for vector in &entry.vectors {
                assert_eq!(
                    vector.len(),
                    sig.params.len(),
                    "{}: {}{vector:?}: arity",
                    item.label,
                    entry.function
                );
                let verdict = interpret(&item.module, &item.label, &entry.function, &sig, vector);
                verdicts.push((vector.clone(), verdict));
            }
            if verdicts
                .iter()
                .all(|(_, verdict)| matches!(verdict, Oracle::Undefined(_)))
            {
                report
                    .vacuous
                    .push(format!("{}::{}", item.label, entry.function));
            }
            oracle.push((entry.function.clone(), sig, verdicts));
        }
        for opt in OPTS {
            let buffer = jit(&item.module, &item.label, opt);
            for (function, sig, verdicts) in &oracle {
                for (vector, verdict) in verdicts {
                    let want = match verdict {
                        Oracle::Value(want) => want,
                        Oracle::Undefined(reason) => {
                            report.skipped += 1;
                            *report.skip_reasons.entry(reason.clone()).or_default() += 1;
                            continue;
                        }
                    };
                    let images: Vec<u64> = sig
                        .params
                        .iter()
                        .zip(vector)
                        .map(|((_, bits, signed), raw)| register_image(*raw, *bits, *signed))
                        .collect();
                    let got = mask(call_native(&buffer, function, &images), sig.ret.1);
                    report.compared += 1;
                    if got != *want {
                        report.mismatches.push(Mismatch {
                            module: item.label.clone(),
                            function: function.clone(),
                            args: vector.clone(),
                            opt,
                            native: got,
                            interpreter: *want,
                        });
                    }
                }
            }
        }
    }
    report
}

/// The gate's verdict: no mismatch, no vacuous entry, something compared.
fn assert_agrees(report: &Report, what: &str) {
    let summary = report.summary(what);
    println!("{summary}");
    assert!(report.compared > 0, "{summary}\nthe gate compared nothing");
    assert!(report.vacuous.is_empty(), "{summary}");
    assert!(report.mismatches.is_empty(), "{summary}");
}

// ---------------------------------------------------------------------------
// The seeded generator
// ---------------------------------------------------------------------------

/// xorshift64*: deterministic, dependency-free, never seeded from the clock.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self((seed ^ 0x9e37_79b9_7f4a_7c15) | 1)
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
}

/// The aggregate types a generated program uses. Their definitions are the
/// fixed module header in [`GEN_HEADER`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Agg {
    /// `struct.0 { u64, u64 }`
    Pt,
    /// `struct.1 { u32, u64, u8 }` (mixed widths, natural padding)
    Mix,
    /// `struct.2 { u64, struct.0 }` (a nested aggregate field)
    Outer,
    /// `struct.3 { a: u8, b: u64, c: u16 } repr=packed(1)`
    Packed,
    /// `[u64 x 3]`
    Arr,
}

const ALL_AGGS: [Agg; 5] = [Agg::Pt, Agg::Mix, Agg::Outer, Agg::Packed, Agg::Arr];

const GEN_HEADER: &str = "; TrustIr text format v1
module \"ws7_2-generated\"

struct @Pt { u64, u64 } id=0

struct @Mix { u32, u64, u8 } id=1

struct @Outer { u64, struct.0 } id=2

struct @Packed { u8, u64, u16 } repr=packed(1) id=3

type ty.0 = u64

functy.0 = (u64, u64, u64) -> (u64)

functy.1 = (struct.1, u64) -> (u64)
";

impl Agg {
    fn spelling(self) -> &'static str {
        match self {
            Agg::Pt => "struct.0",
            Agg::Mix => "struct.1",
            Agg::Outer => "struct.2",
            Agg::Packed => "struct.3",
            Agg::Arr => "[ty.0 x 3]",
        }
    }

    /// The scalar lanes `(field index, scalar type)`; `Outer`'s second field
    /// is the nested `Pt`, handled separately.
    fn scalar_fields(self) -> &'static [(u32, &'static str)] {
        match self {
            Agg::Pt => &[(0, "u64"), (1, "u64")],
            Agg::Mix => &[(0, "u32"), (1, "u64"), (2, "u8")],
            Agg::Outer => &[(0, "u64")],
            Agg::Packed => &[(0, "u8"), (1, "u64"), (2, "u16")],
            Agg::Arr => &[],
        }
    }

    fn constant(self, rng: &mut Rng) -> String {
        let mut small = || rng.below(250) + 1;
        match self {
            Agg::Pt => format!("const struct.0 {{ {}, {} }}", small(), small()),
            Agg::Mix => format!("const struct.1 {{ {}, {}, {} }}", small(), small(), small()),
            Agg::Outer => format!(
                "const struct.2 {{ {}, {{ {}, {} }} }}",
                small(),
                small(),
                small()
            ),
            Agg::Packed => format!("const struct.3 {{ {}, {}, {} }}", small(), small(), small()),
            Agg::Arr => format!(
                "const [ty.0 x 3] array[ {}, {}, {} ]",
                small(),
                small(),
                small()
            ),
        }
    }
}

/// Text emission state for one function body.
struct Body {
    text: String,
    next: u32,
}

impl Body {
    fn new(first_free: u32) -> Self {
        Self {
            text: String::new(),
            next: first_free,
        }
    }

    fn fresh(&mut self) -> u32 {
        let v = self.next;
        self.next += 1;
        v
    }

    fn line(&mut self, line: &str) {
        self.text.push_str("    ");
        self.text.push_str(line);
        self.text.push('\n');
    }

    /// `%v = <rhs>`; returns `v`.
    fn def(&mut self, rhs: &str) -> u32 {
        let v = self.fresh();
        self.line(&format!("%{v} = {rhs}"));
        v
    }

    /// A `u64` value narrowed to `ty`.
    fn narrow(&mut self, value: u32, ty: &str) -> u32 {
        if ty == "u64" {
            value
        } else {
            self.def(&format!("trunc u64 %{value} to {ty}"))
        }
    }

    /// A `ty` value widened to `u64`.
    fn widen(&mut self, value: u32, ty: &str) -> u32 {
        if ty == "u64" {
            value
        } else {
            self.def(&format!("zext {ty} %{value} to u64"))
        }
    }

    /// `acc' = acc * K + x` (wrapping, defined for every input).
    fn fold(&mut self, acc: u32, x: u32, k: u32) -> u32 {
        let scaled = self.def(&format!("mul u64 %{acc}, %{k}"));
        self.def(&format!("add u64 %{scaled}, %{x}"))
    }

    /// Fold every lane of `agg` (nested and array lanes included) into `acc`.
    fn fold_all(&mut self, acc: u32, agg: Agg, value: u32, k: u32, index_consts: &[u32; 3]) -> u32 {
        let mut acc = acc;
        for &(field, ty) in agg.scalar_fields() {
            let lane = self.def(&format!("extractfield {ty} %{value}, {field}"));
            let wide = self.widen(lane, ty);
            acc = self.fold(acc, wide, k);
        }
        match agg {
            Agg::Outer => {
                let inner = self.def(&format!("extractfield struct.0 %{value}, 1"));
                acc = self.fold_all(acc, Agg::Pt, inner, k, index_consts);
            }
            Agg::Arr => {
                for index in index_consts {
                    let lane = self.def(&format!("extractelement u64 %{value}, %{index}"));
                    acc = self.fold(acc, lane, k);
                }
            }
            _ => {}
        }
        acc
    }
}

/// Insert a fresh scalar derived from `source` into one lane of `base`
/// (a nested lane of `Outer` goes through extract / insert / insert).
fn emit_insert(
    body: &mut Body,
    rng: &mut Rng,
    agg: Agg,
    base: u32,
    source: u32,
    index_consts: &[u32; 3],
    arg_index: u32,
) -> u32 {
    match agg {
        Agg::Arr => {
            let index = index_consts[rng.below(3) as usize];
            let index = if rng.chance(30) { arg_index } else { index };
            // trust-ir spells `insertelement TY %arr, %idx, %val` (parser and
            // display agree), the same order as `extractelement`.
            body.def(&format!(
                "insertelement [ty.0 x 3] %{base}, %{index}, %{source}"
            ))
        }
        Agg::Outer if rng.chance(60) => {
            let inner = body.def(&format!("extractfield struct.0 %{base}, 1"));
            let field = rng.below(2);
            let updated = body.def(&format!(
                "insertfield struct.0 %{inner}, {field}, %{source}"
            ));
            body.def(&format!("insertfield struct.2 %{base}, 1, %{updated}"))
        }
        _ => {
            let fields = agg.scalar_fields();
            let (field, ty) = fields[rng.below(fields.len() as u64) as usize];
            let lane = body.narrow(source, ty);
            body.def(&format!(
                "insertfield {} %{base}, {field}, %{lane}",
                agg.spelling()
            ))
        }
    }
}

/// One generated program: a parameter-base helper (`func.0`) and the entry
/// `gen(a, b, c)` (`func.1`), with a straight-line aggregate section and,
/// by seed, an aggregate-carrying loop.
fn generate(seed: u64) -> String {
    let mut rng = Rng::new(seed);
    let mut module = String::from(GEN_HEADER);

    // func.0: an insert into a by-value PARAMETER, which is read again after.
    module.push_str(
        "
rustcc fn @take_mix(functy.1) {
bb0(%0: struct.1, %1: u64):
    %2 = trunc u64 %1 to u32
    %3 = insertfield struct.1 %0, 0, %2
    %4 = extractfield u32 %3, 0
    %5 = zext u32 %4 to u64
    %6 = extractfield u32 %0, 0
    %7 = zext u32 %6 to u64
    %8 = extractfield u64 %0, 1
    %9 = const u64 1000003
    %10 = mul u64 %5, %9
    %11 = add u64 %10, %7
    %12 = mul u64 %11, %9
    %13 = add u64 %12, %8
    ret %13
}
",
    );

    let mut body = Body::new(3);
    let k = body.def("const u64 1000003");
    let zero = body.def("const u64 0");
    let index_consts = [zero, body.def("const u64 1"), body.def("const u64 2")];
    let three = body.def("const u64 3");
    // An in-range index from argument c.
    let arg_index = body.def(&format!("urem u64 %2, %{three}"));
    let args = [0u32, 1, 2];

    // The pool of live aggregate values; inserts never remove their base.
    let mut pool: Vec<(Agg, u32)> = Vec::new();
    for agg in ALL_AGGS {
        if rng.chance(70) || pool.is_empty() {
            let c = agg.constant(&mut rng);
            let v = body.def(&c);
            pool.push((agg, v));
        }
    }
    let mut acc = zero;
    let steps = 4 + rng.below(10);
    for _ in 0..steps {
        let pick = rng.below(pool.len() as u64) as usize;
        let (agg, base) = pool[pick];
        match rng.below(10) {
            // Insert chains off a shared base (the base stays in the pool).
            0..=4 => {
                let source = args[rng.below(3) as usize];
                let chain = 1 + rng.below(3);
                let mut value = base;
                for _ in 0..chain {
                    value = emit_insert(
                        &mut body,
                        &mut rng,
                        agg,
                        value,
                        source,
                        &index_consts,
                        arg_index,
                    );
                    if rng.chance(50) {
                        pool.push((agg, value));
                    }
                }
                pool.push((agg, value));
            }
            // Extract-after-insert: read the OLD base right away.
            5 | 6 => {
                let source = args[rng.below(3) as usize];
                let new = emit_insert(
                    &mut body,
                    &mut rng,
                    agg,
                    base,
                    source,
                    &index_consts,
                    arg_index,
                );
                acc = body.fold_all(acc, agg, base, k, &index_consts);
                acc = body.fold_all(acc, agg, new, k, &index_consts);
                pool.push((agg, new));
            }
            // A select of two values of one type becomes a new base.
            7 => {
                if let Some(&(_, other)) = pool.iter().find(|(a, v)| *a == agg && *v != base) {
                    let cond = body.def(&format!("icmp ult u64 %0, %{}", args[1]));
                    let chosen = body.def(&format!(
                        "select {} %{cond}, %{base}, %{other}",
                        agg.spelling()
                    ));
                    pool.push((agg, chosen));
                }
            }
            // A parameter base: pass a Mix by value, read it after the call.
            8 => {
                if let Some(&(_, mix)) = pool.iter().find(|(a, _)| *a == Agg::Mix) {
                    let source = args[rng.below(3) as usize];
                    let result = body.def(&format!("call @func.0(%{mix}, %{source})"));
                    acc = body.fold(acc, result, k);
                    acc = body.fold_all(acc, Agg::Mix, mix, k, &index_consts);
                }
            }
            // A copy that must stay independent of later inserts on the source.
            _ => {
                let copy = body.def(&format!("copy {} %{base}", agg.spelling()));
                pool.push((agg, copy));
            }
        }
    }

    let looped = rng.chance(65);
    // `gen` uses the Rust convention like `take_mix`: a cross-convention call
    // edge needs target info the module does not carry (`TargetInfoRequired`).
    // For three u64 arguments and a u64 result it is the C register
    // convention on every JIT host this gate runs on.
    let mut entry = String::from("\nrustcc fn @gen(functy.0) {\nbb0(%0: u64, %1: u64, %2: u64):\n");
    if looped {
        // An aggregate-carrying loop: a header parameter updated by an insert
        // whose OLD value is read afterwards, a swap of two same-typed
        // parameters, and (by seed) a loop-carried aggregate Load whose slot is
        // stored to in the body.
        let (agg_a, a0) = pool[rng.below(pool.len() as u64) as usize];
        let same: Vec<u32> = pool
            .iter()
            .filter(|(a, _)| *a == agg_a)
            .map(|(_, v)| *v)
            .collect();
        let b0 = same[rng.below(same.len() as u64) as usize];
        let swap = rng.chance(60);
        let carried_load = rng.chance(50);
        let one = body.def("const u64 1");
        let mask3 = body.def("const u64 3");
        let low = body.def(&format!("and u64 %0, %{mask3}"));
        let trips = body.def(&format!("add u64 %{low}, %{one}"));
        let (slot, l0) = if carried_load {
            let slot = body.def("alloca struct.0");
            let seed_value = body.def(&Agg::Pt.constant(&mut rng));
            body.line(&format!("store struct.0 %{seed_value}, ptr %{slot}"));
            let l0 = body.def(&format!("load struct.0, ptr %{slot}"));
            (Some(slot), Some(l0))
        } else {
            (None, None)
        };
        // Fold every pool value before the loop, so a corruption of any of
        // them by a later insert is observed both here and after the loop.
        for &(agg, value) in &pool.clone() {
            acc = body.fold_all(acc, agg, value, k, &index_consts);
        }
        let mut header_args = vec![a0, b0, zero, acc];
        if let Some(l0) = l0 {
            header_args.push(l0);
        }
        let ty = agg_a.spelling();
        let list = |values: &[u32]| {
            values
                .iter()
                .map(|v| format!("%{v}"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        body.line(&format!("br bb1({})", list(&header_args)));
        entry.push_str(&body.text);
        body.text.clear();

        let pa = body.fresh();
        let pb = body.fresh();
        let pi = body.fresh();
        let pacc = body.fresh();
        let pl = l0.map(|_| body.fresh());
        let mut params = format!("bb1(%{pa}: {ty}, %{pb}: {ty}, %{pi}: u64, %{pacc}: u64");
        if let Some(pl) = pl {
            let _ = write!(params, ", %{pl}: struct.0");
        }
        params.push_str("):\n");
        entry.push_str(&params);
        let updated = emit_insert(&mut body, &mut rng, agg_a, pa, pi, &index_consts, arg_index);
        let mut lacc = body.fold_all(pacc, agg_a, pa, k, &index_consts);
        lacc = body.fold_all(lacc, agg_a, updated, k, &index_consts);
        let mut next_load = None;
        if let (Some(slot), Some(pl)) = (slot, pl) {
            let reloaded = body.def(&format!("load struct.0, ptr %{slot}"));
            body.line(&format!("store u64 %{pi}, ptr %{slot}"));
            lacc = body.fold_all(lacc, Agg::Pt, pl, k, &index_consts);
            next_load = Some(reloaded);
        }
        let ni = body.def(&format!("add u64 %{pi}, %{one}"));
        let again = body.def(&format!("icmp ult u64 %{ni}, %{trips}"));
        let (next_a, next_b) = if swap { (pb, updated) } else { (updated, pb) };
        let mut back = vec![next_a, next_b, ni, lacc];
        if let Some(r) = next_load {
            back.push(r);
        }
        body.line(&format!(
            "condbr %{again}, bb1({}), bb2(%{next_a}, %{next_b}, %{lacc})",
            list(&back)
        ));
        entry.push_str(&body.text);
        body.text.clear();

        let ea = body.fresh();
        let eb = body.fresh();
        let eacc = body.fresh();
        let _ = writeln!(entry, "bb2(%{ea}: {ty}, %{eb}: {ty}, %{eacc}: u64):");
        let mut facc = body.fold_all(eacc, agg_a, ea, k, &index_consts);
        facc = body.fold_all(facc, agg_a, eb, k, &index_consts);
        // Values defined in bb0 dominate bb2: re-read every pool value.
        for &(agg, value) in &pool {
            facc = body.fold_all(facc, agg, value, k, &index_consts);
        }
        body.line(&format!("ret %{facc}"));
        entry.push_str(&body.text);
    } else {
        for &(agg, value) in &pool.clone() {
            acc = body.fold_all(acc, agg, value, k, &index_consts);
        }
        body.line(&format!("ret %{acc}"));
        entry.push_str(&body.text);
    }
    entry.push_str("}\n");
    module.push_str(&entry);
    module
}

/// The generated corpus: one module per pinned seed, each with fixed vectors
/// plus seed-derived ones.
fn generated_corpus() -> Vec<CorpusModule> {
    GENERATOR_SEEDS
        .iter()
        .map(|&seed| {
            let text = generate(seed);
            let label = format!("generated seed {seed:#x}");
            let module = parse_valid(&label, &text);
            let mut rng = Rng::new(seed.rotate_left(17));
            let mut vectors = vec![
                vec![0, 0, 0],
                vec![1, 2, 3],
                vec![3, 5, 7],
                vec![u64::MAX, 1 << 40, 0x0123_4567_89ab_cdef],
            ];
            for _ in 0..4 {
                vectors.push(vec![rng.next(), rng.next(), rng.next()]);
            }
            CorpusModule {
                label,
                module,
                entries: vec![Entry {
                    function: "gen".to_string(),
                    vectors,
                }],
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// POSITIVE: the vendored corpus — the proof program's miscompile witnesses
/// and the WS7.1 families — agrees with the reference interpreter on every
/// compared vector at O0..O3, and no entry is vacuous.
#[test]
fn vendored_corpus_agrees_with_the_interpreter() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let corpus = vendored_corpus();
    assert!(
        corpus
            .iter()
            .any(|m| m.label == "c13_shared_nomul.trust_ir"),
        "the corpus must carry the c13 gate module"
    );
    assert_agrees(&run(&corpus), "vendored trust_ir_exec corpus");
}

/// ADVERSARIAL: the seeded generator's programs (pinned seeds) agree with the
/// interpreter at O0..O3.
#[test]
fn generated_aggregate_programs_agree_with_the_interpreter() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    assert_agrees(
        &run(&generated_corpus()),
        &format!("generated corpus ({} pinned seeds)", GENERATOR_SEEDS.len()),
    );
}

/// The generator is deterministic: one seed, one program, byte for byte. A
/// pinned seed that drifted would make a failure unreproducible.
#[test]
fn generator_is_deterministic_and_covers_every_family() {
    for &seed in &GENERATOR_SEEDS {
        assert_eq!(generate(seed), generate(seed), "seed {seed:#x}");
    }
    let all: String = GENERATOR_SEEDS.iter().map(|&s| generate(s)).collect();
    for (family, needle) in [
        ("insert chain", "insertfield struct."),
        ("insertelement", "insertelement [ty.0 x 3]"),
        ("aggregate loop header", "bb1(%"),
        ("loop-carried aggregate load", "load struct.0, ptr"),
        ("parameter base", "call @func.0("),
        ("nested aggregate field", "insertfield struct.2"),
        ("packed struct", "insertfield struct.3"),
        ("select base", "select struct."),
    ] {
        assert!(all.contains(needle), "no pinned seed generates a {family}");
    }
    assert!(
        GENERATOR_SEEDS
            .iter()
            .any(|&s| generate(s).contains("bb2(%") && generate(s).contains(", %")),
        "no pinned seed generates a loop"
    );
    // Every generated element index is in range by construction: the index
    // operand (the second) of each `insertelement` / `extractelement` is a
    // `const u64 0|1|2` or the `urem` of an argument by 3, never a raw
    // argument or an inserted value (the operand-swap defect made 41% of the
    // generated vectors out-of-bounds UB, skipped).
    let mut dynamic = false;
    for &seed in &GENERATOR_SEEDS {
        let text = generate(seed);
        let defs: std::collections::HashMap<&str, &str> = text
            .lines()
            .filter_map(|line| line.trim().split_once(" = "))
            .collect();
        for line in text.lines().map(str::trim) {
            let Some((_, rhs)) = line.split_once(" = ") else {
                continue;
            };
            if !(rhs.starts_with("insertelement ") || rhs.starts_with("extractelement ")) {
                continue;
            }
            let operands: Vec<&str> = rhs.split(", ").collect();
            let index = operands.get(1).copied().unwrap_or("");
            let def = defs.get(index).copied().unwrap_or("");
            let in_range = ["const u64 0", "const u64 1", "const u64 2"].contains(&def)
                || (def.starts_with("urem u64 %") && rhs.starts_with("insertelement "));
            dynamic |= def.starts_with("urem u64 %");
            assert!(
                in_range,
                "seed {seed:#x}: element index {index} is `{def}` in `{line}`"
            );
        }
    }
    assert!(dynamic, "no pinned seed generates a dynamic in-range index");
}

/// Row `crit.misw10` (the critic: re-measure before calling it real): the
/// gate RE-MEASURES the c13 shapes natively on every run, so the F-111 claim
/// stays a measurement — and every c13 entry compares, never vacuously.
#[test]
fn crit_misw10_the_gate_remeasures_the_c13_shapes() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let corpus: Vec<CorpusModule> = vendored_corpus()
        .into_iter()
        .filter(|m| m.label.starts_with("c13") || m.label.starts_with("parta_lean_struct"))
        .collect();
    assert!(
        corpus.len() >= 4,
        "the c13 / Part A-Lean witnesses are vendored"
    );
    let report = run(&corpus);
    assert_eq!(report.skipped, 0, "{}", report.summary("c13 shapes"));
    assert_agrees(&report, "c13 shapes");
}

/// The vacuity rule is enforced, not assumed: an entry whose every vector is
/// UB is reported vacuous (a failure), and a UB vector beside a defined one is
/// skipped while the defined one is still compared.
#[test]
fn vacuity_rule_fails_an_all_skipped_entry() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let text = "; TrustIr text format v1
module \"ws7_2-vacuity\"

type ty.0 = u64

functy.0 = (u64) -> (u64)

fn @pick(functy.0) {
bb0(%0: u64):
    %1 = const [ty.0 x 2] array[ 7, 8 ]
    %2 = extractelement u64 %1, %0
    ret %2
}
";
    let module = parse_valid("vacuity", text);
    let all_ub = CorpusModule {
        label: "vacuity".into(),
        module: module.clone(),
        entries: vec![Entry {
            function: "pick".into(),
            vectors: vec![vec![5], vec![9]],
        }],
    };
    let report = run(&[all_ub]);
    assert_eq!(
        report.vacuous,
        ["vacuity::pick"],
        "{}",
        report.summary("all-UB")
    );
    assert_eq!(report.compared, 0);
    let mixed = CorpusModule {
        label: "vacuity".into(),
        module,
        entries: vec![Entry {
            function: "pick".into(),
            vectors: vec![vec![5], vec![1]],
        }],
    };
    let report = run(&[mixed]);
    assert!(report.vacuous.is_empty(), "{}", report.summary("mixed"));
    assert_eq!(report.compared, OPTS.len());
    assert_eq!(report.skipped, OPTS.len());
    assert!(report.mismatches.is_empty(), "{}", report.summary("mixed"));
}

/// A default build carries no mutation knob.
#[test]
fn default_build_has_no_mutation_knobs() {
    assert_eq!(
        trust_cg_lower::MUTATION_KNOBS,
        cfg!(feature = "mutation-knobs")
    );
}

/// The shared adapter must express aggregate storage offsets as addresses on
/// both selectors. This inventories all 240 object attempts. It never loads
/// foreign code and supplies neither native x86 nor proof evidence.
///
/// **The x86 Select refusal table is retired (2026-10-20).** Until then 52 of
/// the 240 rows — thirteen modules at four opt levels — refused with
/// `unsupported opcode for x86-64 ISel: Select NotEqual cond=B1
/// true=Struct(..) false=Struct(..)`, and this census pinned each one's exact
/// first refusal so the gap could not be mistaken for a compilation. x86-64
/// ISel now selects an aggregate `Select` whose arms it knows to be addresses
/// (`X86InstructionSelector::select_select`), so every row compiles and the
/// inventory is 240/240 with no refusal. The correctness check on those bytes
/// is NOT this census, which only inspects the ELF header: it is the two
/// differential tests above, which JIT and RUN each program at O0-O3 against
/// the trust-ir reference interpreter.
#[cfg(target_os = "linux")]
#[test]
fn aggregate_corpora_linux_object_census_preserves_every_outcome() {
    use trust_cg_codegen::target::TargetSpec;

    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let mut corpus = vendored_corpus();
    corpus.extend(generated_corpus());
    assert_eq!(corpus.len(), 30);
    let mut problems = Vec::new();
    let mut compiled = 0;
    let mut refused = 0;
    for (target, triple, machine) in [
        (Target::Aarch64, "aarch64-unknown-linux-gnu", 183u16),
        (Target::X86_64, "x86_64-unknown-linux-gnu", 62u16),
    ] {
        for opt in OPTS {
            let mut config = CompilerConfig::jit_fast(target);
            config.opt_level = opt;
            let compiler =
                Compiler::new_for_target_spec(config, TargetSpec::parse(triple).unwrap())
                    .with_codegen_license(license());
            for case in &corpus {
                match compiler.compile(&case.module) {
                    Ok(result) => {
                        let bytes = &result.object_code;
                        assert!(
                            bytes.len() > 64,
                            "{} {triple} {opt:?}: empty object",
                            case.label
                        );
                        assert_eq!(&bytes[..6], b"\x7fELF\x02\x01");
                        assert_eq!(u16::from_le_bytes([bytes[16], bytes[17]]), 1);
                        assert_eq!(u16::from_le_bytes([bytes[18], bytes[19]]), machine);
                        compiled += 1;
                    }
                    Err(error) => {
                        // No row of this corpus is allowed to refuse on either
                        // selector. A refusal here is the gap reopening, and
                        // it is named rather than counted.
                        refused += 1;
                        problems.push(format!("{} {triple} {opt:?}: {error}", case.label));
                    }
                }
            }
        }
    }
    let required = corpus.len() * OPTS.len() * 2;
    println!(
        "AGGREGATE_OBJECT_CORPUS modules={} targets=2 opts=4 required={required} compiled={compiled} refused={refused}",
        corpus.len()
    );
    assert!(problems.is_empty(), "{}", problems.join("\n"));
    assert_eq!(required, 240);
    assert_eq!(
        (compiled, refused),
        (240, 0),
        "every aggregate corpus module must produce an object on both selectors at every opt \
         level; this read (188, 52) until x86-64 ISel learned the aggregate Select"
    );
    assert_eq!(compiled + refused, required);
}

/// NEGATIVE TWIN / mutation control: with the historical in-place insert
/// lowering switched back on, the SAME gate reports the c13 mismatches —
/// `dotOf(1,2,3,4)`: native 25, interpreter 11; `two_inserts_sub(9,2)`: native
/// 0, interpreter 7 — and catches the bug in the generated corpus as well.
#[cfg(feature = "mutation-knobs")]
#[test]
fn legacy_in_place_insert_is_caught_by_the_differential() {
    use trust_cg_lower::mutation_knobs::set_legacy_in_place_insert;
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            set_legacy_in_place_insert(false);
        }
    }
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    set_legacy_in_place_insert(true);
    let _reset = Reset;

    let report = run(&vendored_corpus());
    println!(
        "{}",
        report.summary("vendored corpus, legacy_in_place_insert ON")
    );
    assert!(report.vacuous.is_empty());
    for (module, function, args, native, interpreter) in [
        (
            "parta_lean_struct.trust_ir",
            "dotOf",
            vec![1, 2, 3, 4],
            25,
            11,
        ),
        (
            "c13_shared_nomul.trust_ir",
            "two_inserts_sub",
            vec![9, 2],
            0,
            7,
        ),
    ] {
        let expected = Mismatch {
            module: module.into(),
            function: function.into(),
            args,
            opt: OptLevel::O0,
            native,
            interpreter,
        };
        assert!(
            report.mismatches.contains(&expected),
            "the gate must report {expected:?}\n{}",
            report.summary("legacy")
        );
    }
    for opt in OPTS {
        assert!(
            report.mismatches.iter().any(|m| m.opt == opt),
            "the legacy insert went undetected at {opt:?}\n{}",
            report.summary("legacy")
        );
    }
    let generated = run(&generated_corpus());
    println!(
        "{}",
        generated.summary("generated corpus, legacy_in_place_insert ON")
    );
    assert!(
        !generated.mismatches.is_empty(),
        "the generated corpus must catch the legacy insert"
    );
}

/// The blind spot itself, re-measured (c13, `crit.misw10`). c13 measured the
/// legacy insert lowering's proof-required AOT compile PROMOTING with every
/// certificate verified while the JIT computes `two_inserts_sub(9, 2) = 0`
/// (want 7). On main the promotion gate now refuses that object, but only
/// because an opcode of it (`MovI`) has no checked certificate: an
/// opcode-inventory refusal, not a check of the trust-ir -> LIR adapter. This
/// pins that exact reason (ratchet): when the opcode earns complete evidence
/// the miscompiled object promotes again and this test must return to
/// asserting every certificate verified. No certificate span covers the
/// adapter; only the differential above sees its error.
#[cfg(feature = "mutation-knobs")]
#[test]
fn legacy_in_place_insert_is_refused_only_by_an_opcode_inventory_gap() {
    use trust_cg_codegen::target::TargetSpec;
    use trust_cg_lower::mutation_knobs::set_legacy_in_place_insert;
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            set_legacy_in_place_insert(false);
        }
    }
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    set_legacy_in_place_insert(true);
    let _reset = Reset;

    let path = format!("{FIXTURES}/c13_shared_nomul.trust_ir");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let module = parse_valid("c13_shared_nomul.trust_ir", &text);
    let buffer = jit(&module, "c13_shared_nomul.trust_ir", OptLevel::O2);
    assert_eq!(
        call_native(&buffer, "two_inserts_sub", &[9, 2]),
        0,
        "the legacy insert must reproduce the c13 object"
    );

    let config = CompilerConfig {
        emit_proofs: true,
        ..CompilerConfig::default()
    };
    let spec = TargetSpec::parse("aarch64-apple-darwin").expect("target");
    let refusal = match Compiler::new_for_target_spec(config, spec)
        .with_codegen_license(license())
        .compile(&module)
    {
        Ok(result) => panic!(
            "the miscompiled object promoted: the opcode-inventory gap closed, so this \
             ratchet must return to asserting every certificate verified: {:?}",
            result.proofs
        ),
        Err(e) => e.to_string(),
    };
    assert!(
        refusal.contains("proof promotion rejected for target Aarch64")
            && refusal.contains("opcode_inventory_instruction")
            && refusal.contains("two_inserts_sub")
            && refusal.contains("no checked certificate"),
        "the miscompiled object is refused by an opcode-inventory gap, by name: {refusal}"
    );
    assert!(
        !trust_cg_verify::proof_certificate::CoveredSpan::LirToMachine.covers_trust_ir_to_lir(),
        "no certificate span covers the adapter"
    );
}
