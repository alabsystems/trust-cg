// trust-cg-codegen/tests/e2e_aarch64_pass_validation.rs
//
// Production per-pass translation validation (L10-P3) through the public
// `Pipeline`, on trust-ir kernels whose optimization exercises every
// dedicated validator (`trust_cg_opt::pass_validation`): the list schedulers
// (dependence preservation), mem-pair formation and if-conversion (symbolic
// region equivalence) and LICM (code-motion side conditions).
//
// * Every kernel compiles at O1, O2 and O3 under the refusing policy
//   (`PassValidationConfig::enforce()`, what proof-grade and certified
//   pipelines run) with no refusal, and under `off`; the two objects must be
//   byte-identical (validation observes, it never rewrites).
// * Non-vacuity: over the corpus each dedicated validator validated at least
//   one changed run, and no covered run was refuted or left unproved.
// * Native: the enforce-built kernels run against a C reference on fixed
//   inputs (macOS and Linux GNU AArch64 hosts).
// * The guarded-pair regression: `a[0] + a[1]` with an `in_bounds` carrier
//   before the second load. mem-pair formation used to pair the two loads
//   into an LDP ahead of the carrier (found by the region validator); with
//   a one-element array ending at an unmapped page the program then died of
//   SIGSEGV/SIGBUS instead of the carrier's SIGTRAP. The kernel must trap
//   with SIGTRAP at O2 and O3 and return the sum for two elements.
//
// Evidence strength: the verdicts are translation validation of these runs
// under the validators' machine model, and the native rows are a bounded
// differential on the listed inputs. Neither is a proof of the passes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeMap;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_opt::{PassValidationConfig, PassValidationSummary, ValidatorKind};

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
#[path = "common/native_host.rs"]
mod native_host;

/// One kernel: its trust-ir function type and body.
struct Kernel {
    name: &'static str,
    functy: &'static str,
    body: &'static str,
}

/// `x*y` is invariant in the loop (LICM); the loop body schedules.
const LICM_SUM: Kernel = Kernel {
    name: "licm_sum",
    functy: "(i64, i64, i64) -> (i64)",
    body: "bb0(%0: i64, %1: i64, %2: i64):
    %3 = const i64 0
    %4 = const i64 1
    br bb1(%3, %3)
bb1(%10: i64, %11: i64):
    %12 = icmp ult i64 %10, %2
    condbr %12, bb2, bb3
bb2:
    %13 = mul i64 %0, %1
    %14 = add i64 %13, %10
    %15 = xor i64 %11, %14
    %16 = add i64 %10, %4
    br bb1(%16, %15)
bb3:
    ret %11
",
};

/// Two adjacent loads off one pointer (mem-pair), and independent products
/// (scheduling).
const PAIR_POLY: Kernel = Kernel {
    name: "pair_poly",
    functy: "(ptr) -> (i64)",
    body: "bb0(%0: ptr):
    %1 = const i64 0
    %2 = const i64 1
    %3 = const i64 2
    %4 = const i64 3
    %5 = gep i64, ptr %0, %1
    %6 = load i64, ptr %5
    %7 = gep i64, ptr %0, %2
    %8 = load i64, ptr %7
    %9 = gep i64, ptr %0, %3
    %10 = load i64, ptr %9
    %11 = gep i64, ptr %0, %4
    %12 = load i64, ptr %11
    %13 = const i64 3
    %14 = const i64 5
    %15 = const i64 7
    %16 = const i64 11
    %17 = mul i64 %6, %13
    %18 = mul i64 %8, %14
    %19 = mul i64 %10, %15
    %20 = mul i64 %12, %16
    %21 = add i64 %17, %18
    %22 = add i64 %19, %20
    %23 = xor i64 %21, %22
    ret %23
",
};

/// A small value diamond (if-conversion).
const SELECT: Kernel = Kernel {
    name: "select_step",
    functy: "(i64, i64) -> (i64)",
    body: "bb0(%0: i64, %1: i64):
    %2 = icmp slt i64 %0, %1
    condbr %2, bb1, bb2
bb1:
    %3 = const i64 1
    %4 = add i64 %0, %3
    br bb3(%4)
bb2:
    br bb3(%1)
bb3(%5: i64):
    ret %5
",
};

/// `a < b` materialized through a `{1, 0}` diamond (if-conversion's boolean
/// admission), and a guarded division diamond.
const BOOL_DIV: Kernel = Kernel {
    name: "bool_div",
    functy: "(i64, i64) -> (i64)",
    body: "bb0(%0: i64, %1: i64):
    %2 = icmp slt i64 %0, %1
    condbr %2, bb1, bb2
bb1:
    %3 = const i64 1
    br bb3(%3)
bb2:
    %4 = const i64 0
    br bb3(%4)
bb3(%5: i64):
    %6 = const i64 0
    %7 = icmp ne i64 %1, %6
    condbr %7, bb4, bb5
bb4:
    %8 = udiv i64 %0, %1
    br bb6(%8)
bb5:
    br bb6(%6)
bb6(%9: i64):
    %10 = add i64 %5, %9
    ret %10
",
};

/// A loop over a pointer pair stream: loads, an invariant product and a
/// diamond in the body.
const STREAM: Kernel = Kernel {
    name: "stream_mix",
    functy: "(ptr, i64, i64) -> (i64)",
    body: "bb0(%0: ptr, %1: i64, %2: i64):
    %3 = const i64 0
    %4 = const i64 1
    %5 = const i64 2
    br bb1(%3, %3)
bb1(%10: i64, %11: i64):
    %12 = icmp ult i64 %10, %1
    condbr %12, bb2, bb5
bb2:
    %13 = mul i64 %10, %5
    %14 = gep i64, ptr %0, %13
    %15 = load i64, ptr %14
    %16 = add i64 %13, %4
    %17 = gep i64, ptr %0, %16
    %18 = load i64, ptr %17
    %19 = mul i64 %2, %2
    %20 = icmp ult i64 %15, %18
    condbr %20, bb3, bb4(%18)
bb3:
    %21 = add i64 %15, %19
    br bb4(%21)
bb4(%22: i64):
    %23 = add i64 %11, %22
    %24 = add i64 %10, %4
    br bb1(%24, %23)
bb5:
    ret %11
",
};

/// `a[0] + a[1]`, each index checked against `len` by an `in_bounds`
/// carrier; the second word is addressed by a byte offset, so both loads
/// are base-plus-immediate (`ldr [a]`, `ldr [a, #8]`) with the second check
/// between them.
const GUARDED_PAIR: Kernel = Kernel {
    name: "guarded_pair",
    functy: "(ptr, i64) -> (i64)",
    body: "bb0(%0: ptr, %1: i64):
    %2 = const i64 0
    %3 = const i64 1
    %20 = const i64 8
    %4 = icmp ult i64 %2, %1  ; #proof: in_bounds
    %6 = load i64, ptr %0
    %7 = icmp ult i64 %3, %1  ; #proof: in_bounds
    %8 = gep i8, ptr %0, %20
    %9 = load i64, ptr %8
    %10 = add i64 %6, %9
    ret %10
",
};

const KERNELS: [&Kernel; 6] = [
    &LICM_SUM,
    &PAIR_POLY,
    &SELECT,
    &BOOL_DIV,
    &STREAM,
    &GUARDED_PAIR,
];
const LEVELS: [OptLevel; 3] = [OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn level_tag(opt: OptLevel) -> &'static str {
    match opt {
        OptLevel::O0 => "o0",
        OptLevel::O1 => "o1",
        OptLevel::O2 => "o2",
        OptLevel::O3 => "o3",
    }
}

fn module(kernel: &Kernel, symbol: &str) -> trust_ir::Module {
    let text = format!(
        "; TrustIr text format v1\nmodule \"pv\"\ntarget \"{}\" 8 little abi=\"aapcs64\"\n\
         functy.0 = {}\nfn @{symbol}(functy.0) {{\n{}}}\n",
        native_host::TRIPLE,
        kernel.functy,
        kernel.body
    );
    trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("{symbol}: trust-ir parse: {error:?}\n{text}"))
}

/// One build: the object and its functions' validation summary.
struct Built {
    object: Vec<u8>,
    validation: PassValidationSummary,
}

fn build(kernel: &Kernel, symbol: &str, opt: OptLevel, validation: PassValidationConfig) -> Built {
    let module = module(kernel, symbol);
    let lowered = permit_translate_module(&module)
        .unwrap_or_else(|error| panic!("{symbol}: lowering: {error}"));
    let globals = trust_cg_codegen::compiler::module_object_globals(&module)
        .unwrap_or_else(|error| panic!("{symbol}: globals: {error}"));
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: opt,
        target_triple: native_host::TRIPLE.into(),
        disabled_passes_override: Some(String::new()),
        ..PipelineConfig::default()
    })
    .with_pass_validation(validation);
    assert_eq!(pipeline.pass_validation_config(), validation);
    let mut prepared = Vec::new();
    let mut summary = PassValidationSummary::new(validation);
    for (function, _) in &lowered {
        let (function, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .unwrap_or_else(|error| panic!("{symbol} {opt:?} {validation:?}: {error}"));
        summary.merge(&metrics.pass_validation);
        prepared.push(function);
    }
    let object = pipeline
        .compile_module_with_globals(&prepared, &globals)
        .unwrap_or_else(|error| panic!("{symbol} {opt:?}: {error}"));
    native_host::assert_native_object(&object);
    Built {
        object,
        validation: summary,
    }
}

/// Every kernel at every level under enforce, checked byte-for-byte against
/// the same build with validation off. Returns the enforce builds by symbol
/// and the corpus-wide summary.
fn build_corpus() -> (Vec<(String, Built)>, PassValidationSummary) {
    let mut builds = Vec::new();
    let mut corpus = PassValidationSummary::new(PassValidationConfig::enforce());
    for kernel in KERNELS {
        for opt in LEVELS {
            let symbol = format!("{}_{}", kernel.name, level_tag(opt));
            let enforced = build(kernel, &symbol, opt, PassValidationConfig::enforce());
            let off = build(kernel, &symbol, opt, PassValidationConfig::off());
            assert_eq!(
                enforced.object, off.object,
                "{symbol}: validation must not change the emitted object"
            );
            assert!(
                off.validation.passes.is_empty(),
                "{symbol}: the off policy records nothing"
            );
            assert!(
                enforced
                    .validation
                    .failures
                    .iter()
                    .all(|r| r.validator.is_none()),
                "{symbol}: a covered run failed validation: {:?}",
                enforced.validation.failures
            );
            corpus.merge(&enforced.validation);
            builds.push((symbol, enforced));
        }
    }
    (builds, corpus)
}

fn validated_runs(summary: &PassValidationSummary, pass: &str) -> u32 {
    summary
        .passes
        .iter()
        .filter(|c| c.pass_name == pass)
        .map(|c| c.validated)
        .sum()
}

/// Under enforce every kernel compiles, emits the bytes it emits with
/// validation off, and every dedicated validator checks real changed runs.
#[test]
fn enforced_validation_compiles_the_corpus_and_keeps_bytes_identical() {
    let (_, corpus) = build_corpus();
    let mut table = BTreeMap::new();
    for counts in &corpus.passes {
        table.insert(
            counts.pass_name.clone(),
            (
                counts.changed_runs,
                counts.validated,
                counts.unproved + counts.refuted,
                counts.uncovered,
            ),
        );
    }
    eprintln!("pass: (changed runs, validated, failed, uncovered)");
    for (pass, row) in &table {
        eprintln!("  {pass}: {row:?}");
    }
    assert_eq!(corpus.refuted(), 0, "{:?}", corpus.failures);
    assert_eq!(corpus.unproved(), 0, "{:?}", corpus.failures);
    for (pass, validator) in [
        (
            "instruction-scheduler",
            ValidatorKind::DependencePreservation,
        ),
        (
            "pressure-aware-scheduler",
            ValidatorKind::DependencePreservation,
        ),
        (
            "mem-pair-formation",
            ValidatorKind::SymbolicRegionEquivalence,
        ),
        ("licm", ValidatorKind::HoistConditions),
    ] {
        assert_eq!(
            trust_cg_opt::pass_validation::dedicated_validator(pass),
            Some(validator)
        );
        assert!(
            validated_runs(&corpus, pass) >= 1,
            "{pass}: no changed run was validated, so the corpus does not exercise it"
        );
    }
    assert!(
        validated_runs(&corpus, "if-convert")
            + validated_runs(&corpus, "late-boolean-diamond")
            + validated_runs(&corpus, "tiny-loop-diamond")
            >= 1,
        "no if-conversion run was validated"
    );
    assert!(
        corpus.examined_instructions > 0,
        "the validators report their work"
    );
}

/// The proof-grade publication and certified pipelines run at least
/// `enforce` over the dedicated validators, whatever they are asked for; an
/// explicit request otherwise stands, and the default is the diagnostic
/// schedulers tier.
#[test]
fn proof_grade_pipelines_cannot_lower_the_policy() {
    use trust_cg_opt::{PassValidationPolicy, PassValidationScope};
    let config = || PipelineConfig {
        opt_level: OptLevel::O2,
        target_triple: native_host::TRIPLE.into(),
        ..PipelineConfig::default()
    };
    let proof = Pipeline::new(config())
        .with_proof_grade_aarch64_publication()
        .with_pass_validation(PassValidationConfig::off());
    assert_eq!(
        proof.pass_validation_config(),
        PassValidationConfig::enforce(),
        "proof grade enforces the dedicated validators"
    );
    let certified = Pipeline::new(config())
        .with_certified_pass_execution()
        .with_pass_validation(PassValidationConfig::diagnostic());
    assert_eq!(
        certified.pass_validation_config(),
        PassValidationConfig::enforce()
    );
    let wider = PassValidationConfig::enforce().with_scope(PassValidationScope::AllPasses);
    assert_eq!(
        Pipeline::new(config())
            .with_proof_grade_aarch64_publication()
            .with_pass_validation(wider)
            .pass_validation_config(),
        wider,
        "a wider request is kept"
    );
    let explicit = Pipeline::new(config()).with_pass_validation(PassValidationConfig::off());
    assert_eq!(
        explicit.pass_validation_config().policy,
        PassValidationPolicy::Off
    );
    assert_eq!(
        PassValidationConfig::diagnostic(),
        PassValidationConfig {
            policy: PassValidationPolicy::Diagnostic,
            scope: PassValidationScope::Schedulers,
        }
    );
}

/// The refusal is wired into the real preparation path: under
/// `require-coverage` a changed run of a pass no validator covers refuses the
/// compile by name at the optimizer's own enforcement point. The codegen
/// scheduler step is disabled here, so no later check stands in for that
/// one. The same function prepares under `enforce`.
#[test]
fn require_coverage_refuses_an_uncovered_run_through_preparation() {
    use trust_cg_codegen::pipeline::PipelineError;
    use trust_cg_opt::PassValidationPolicy;
    let symbol = "licm_sum_coverage";
    let module = module(&LICM_SUM, symbol);
    let lowered = permit_translate_module(&module)
        .unwrap_or_else(|error| panic!("{symbol}: lowering: {error}"));
    let (function, _) = lowered.first().expect("one function");
    let pipeline = |validation: PassValidationConfig| {
        Pipeline::new(PipelineConfig {
            opt_level: OptLevel::O2,
            target_triple: native_host::TRIPLE.into(),
            disabled_passes_override: Some("sched".to_string()),
            ..PipelineConfig::default()
        })
        .with_pass_validation(validation)
    };
    let require = PassValidationConfig {
        policy: PassValidationPolicy::RequireCoverage,
        ..PassValidationConfig::enforce()
    };
    match pipeline(require).prepare_function_with_metrics(function, None) {
        Err(PipelineError::PassValidationFailed {
            function,
            pass,
            validator,
            verdict,
            reason,
        }) => {
            assert_eq!(function, symbol);
            assert!(
                trust_cg_opt::pass_validation::dedicated_validator(&pass).is_none(),
                "{pass} has a validator"
            );
            assert_eq!(validator, "none");
            assert_eq!(verdict, "uncovered");
            assert!(!reason.is_empty());
        }
        other => panic!(
            "require-coverage refuses an uncovered run, got {:?}",
            other.err()
        ),
    }
    let (_, metrics) = pipeline(PassValidationConfig::enforce())
        .prepare_function_with_metrics(function, None)
        .unwrap_or_else(|error| panic!("{symbol} under enforce: {error}"));
    assert!(metrics.pass_validation.uncovered() > 0);
    assert_eq!(
        metrics.pass_validation.refuted() + metrics.pass_validation.unproved(),
        0
    );
}

/// A whole-module compile through `Compiler` hands the merged verdicts to
/// the caller (`CompilationMetrics::pass_validation`): the default
/// diagnostic tier's evidence is not confined to per-function preparation
/// metrics. Post-allocation branch layout, which no validator covers, is
/// recorded as uncovered when it changes a function.
#[test]
fn compiler_results_carry_the_pass_validation_summary() {
    use trust_cg_codegen::{Compiler, CompilerConfig, target::TargetSpec};
    use trust_cg_opt::PassValidationPolicy;
    let module = module(&STREAM, "stream_mix_summary");
    let result = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            ..Default::default()
        },
        TargetSpec::parse(native_host::TRIPLE).expect("host triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    .unwrap_or_else(|error| panic!("compile: {error}"));
    let summary = &result.metrics.pass_validation;
    if summary.config.policy == PassValidationPolicy::Off {
        // `TRUST_CG_PASS_VALIDATION=off` in the environment: nothing runs.
        assert!(summary.passes.is_empty());
        return;
    }
    assert!(
        summary
            .passes
            .iter()
            .any(|c| c.pass_name == "pressure-aware-scheduler"
                && c.changed_runs + c.unchanged_checked >= 1),
        "the default tier's scheduler verdicts reach the compile result: {summary:?}"
    );
    assert_eq!(summary.refuted() + summary.unproved(), 0, "{summary:?}");
    assert!(
        summary
            .passes
            .iter()
            .any(|c| c.pass_name == "branch-layout" && c.uncovered >= 1),
        "a changed branch layout is recorded as uncovered: {summary:?}"
    );
}

// ---------------------------------------------------------------------------
// Native rows (AArch64 Linux GNU and macOS hosts)
// ---------------------------------------------------------------------------

#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
const DRIVER: &str = r#"
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#define DECL(L) \
  uint64_t licm_sum_##L(uint64_t, uint64_t, uint64_t); \
  uint64_t pair_poly_##L(const uint64_t*); \
  uint64_t select_step_##L(int64_t, int64_t); \
  uint64_t bool_div_##L(int64_t, int64_t); \
  uint64_t stream_mix_##L(const uint64_t*, uint64_t, uint64_t); \
  uint64_t guarded_pair_##L(const uint64_t*, uint64_t);
DECL(o1) DECL(o2) DECL(o3)

static uint64_t r_licm_sum(uint64_t x, uint64_t y, uint64_t n) {
  uint64_t acc = 0;
  for (uint64_t i = 0; i < n; i++) acc ^= x * y + i;
  return acc;
}
static uint64_t r_pair_poly(const uint64_t* a) {
  return (a[0] * 3 + a[1] * 5) ^ (a[2] * 7 + a[3] * 11);
}
static uint64_t r_select_step(int64_t a, int64_t b) { return a < b ? (uint64_t)a + 1 : (uint64_t)b; }
static uint64_t r_bool_div(int64_t a, int64_t b) {
  return (uint64_t)(a < b) + (b != 0 ? (uint64_t)a / (uint64_t)b : 0);
}
static uint64_t r_stream_mix(const uint64_t* a, uint64_t n, uint64_t k) {
  uint64_t acc = 0;
  for (uint64_t i = 0; i < n; i++) {
    uint64_t x = a[2 * i], y = a[2 * i + 1];
    acc += x < y ? x + k * k : y;
  }
  return acc;
}

static uint64_t word(uint64_t* s) {
  *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17;
  switch (*s % 7) { case 0: return 0; case 1: return ~0ull; case 2: return 1ull << 63; default: return *s; }
}

static int bad = 0;
#define CHECK(what, got, want) do { uint64_t g_ = (got), w_ = (want); \
  if (g_ != w_) { printf("MISMATCH %s: got %llu want %llu\n", what, \
    (unsigned long long)g_, (unsigned long long)w_); bad = 1; } } while (0)

/* Run `f(a, len)` in a child; return its termination signal, or 0 after
   comparing a normal return with `want`. */
static int guarded_child(uint64_t (*f)(const uint64_t*, uint64_t), const uint64_t* a,
                         uint64_t len, uint64_t want) {
  fflush(stdout);
  pid_t pid = fork();
  if (pid == 0) _exit(f(a, len) == want ? 0 : 3);
  int status = 0;
  waitpid(pid, &status, 0);
  if (WIFSIGNALED(status)) return WTERMSIG(status);
  return WEXITSTATUS(status) == 0 ? 0 : -1;
}

int main(void) {
  uint64_t s = 0x9e3779b97f4a7c15ull;
  static uint64_t buf[64];
  for (int round = 0; round < 64; round++) {
    for (int i = 0; i < 64; i++) buf[i] = word(&s);
    uint64_t x = word(&s), y = word(&s), n = word(&s) % 40, k = word(&s);
    int64_t a = (int64_t)word(&s), b = (int64_t)word(&s);
    if (round % 4 == 0) b = a;
#define ROW(L) \
    CHECK("licm_sum_" #L, licm_sum_##L(x, y, n), r_licm_sum(x, y, n)); \
    CHECK("pair_poly_" #L, pair_poly_##L(buf), r_pair_poly(buf)); \
    CHECK("select_step_" #L, select_step_##L(a, b), r_select_step(a, b)); \
    CHECK("bool_div_" #L, bool_div_##L(a, b), r_bool_div(a, b)); \
    CHECK("bool_div_" #L "_zero", bool_div_##L(a, 0), r_bool_div(a, 0)); \
    CHECK("stream_mix_" #L, stream_mix_##L(buf, n % 32, k), r_stream_mix(buf, n % 32, k)); \
    CHECK("guarded_pair_" #L, guarded_pair_##L(buf, 2 + n), buf[0] + buf[1]);
    ROW(o1) ROW(o2) ROW(o3)
  }
  /* The guarded pair over a one-element array ending at an unmapped page:
     the second check must trap before the second load runs. */
  long page = sysconf(_SC_PAGESIZE);
  uint8_t* map = mmap(NULL, 2 * page, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
  if (map == MAP_FAILED || mprotect(map + page, page, PROT_NONE) != 0) { printf("mmap failed\n"); return 2; }
  uint64_t* last = (uint64_t*)(map + page) - 1;
  *last = 41;
  uint64_t (*guarded[3])(const uint64_t*, uint64_t) = {guarded_pair_o1, guarded_pair_o2, guarded_pair_o3};
  for (int l = 0; l < 3; l++) {
    int sig = guarded_child(guarded[l], last, 1, 0);
    if (sig != SIGTRAP) { printf("MISMATCH guarded_pair level %d: one element at a page end ended with signal %d, want SIGTRAP\n", l + 1, sig); bad = 1; }
    uint64_t* two = last - 1;
    two[0] = 1; two[1] = 41;
    if (guarded_child(guarded[l], two, 2, 42) != 0) { printf("MISMATCH guarded_pair level %d: two elements\n", l + 1); bad = 1; }
    *last = 41;
  }
  printf("pass-validation native rows: %s\n", bad ? "MISMATCH" : "all equal");
  return bad;
}
"#;

/// The enforce-built kernels agree with the C reference, and the guarded
/// pair traps (not faults) one element short at a page end.
#[cfg_attr(
    any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    ),
    test
)]
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn enforce_built_kernels_match_the_c_reference_natively() {
    use std::process::Command;

    let (builds, _) = build_corpus();
    // Owned scratch: removed when it drops, on success and failure alike
    // (kept only when `TRUST_CG_KEEP_TEST_OBJECTS` is set).
    let dir = fresh_dir::create("trust_cg_pv_");
    let mut objects = Vec::new();
    for (symbol, built) in &builds {
        let path = dir.join(format!("{symbol}.o"));
        std::fs::write(&path, &built.object).expect("write object");
        objects.push(path);
    }
    let driver_c = dir.join("driver.c");
    let binary = dir.join("pass_validation_rows");
    std::fs::write(&driver_c, DRIVER).expect("write driver");
    let link = Command::new(native_host::C_COMPILER)
        .arg("-O1")
        .arg(&driver_c)
        .args(&objects)
        .args(native_host::link_hardening_args())
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run the linker");
    assert!(
        link.status.success(),
        "link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&binary).output().expect("run the rows");
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success(),
        "native rows failed in {} (kept only with {} set):\n{stdout}{}",
        dir.display(),
        fresh_dir::KEEP_ON_FAILURE,
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(stdout.contains("all equal"), "{stdout}");
    eprintln!("{} builds on {}: {stdout}", builds.len(), native_host::HOST);
}

/// This file's kernels are parsed from text and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
