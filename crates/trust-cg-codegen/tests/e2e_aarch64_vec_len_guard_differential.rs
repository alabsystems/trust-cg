// trust-cg-codegen/tests/e2e_aarch64_vec_len_guard_differential.rs
//
// Native on/off/reference differential for the two O2/O3 transforms behind
// the Darwin h1_vec_push_sum fix (2026-09-28):
//
// * LICM's dereferenceable-frame speculation (`licmframespec`): a loop-
//   invariant load that is not guaranteed to execute (it sits behind the
//   loop's exit test) is hoisted when it reads inside one fixed-size stack
//   slot;
// * aarch64-bounds-check-elim's register-bound trap-branch fold
//   (`bcetrapbranch`): an explicit `cmp idx, len ; b.hs trap` whose loop
//   header already tested `idx <u len` becomes an unconditional branch.
//
// Every kernel is a trust-ir function `k(ptr hdr, i64 passes, ptr escape) ->
// i64` in the shape the rustc bridge emits for `while k < v.len() { acc +=
// v[k]; k += 1 }` over a `Vec` whose header lives in an escaped stack slot:
// it copies the caller's `{ptr, cap, len}` header into a local 24-byte slot,
// stores the slot's address through `escape` (so the slot stays in memory),
// then runs `passes` passes whose inner loop reloads the length in its
// header and the pointer and length again in the bounds-check block, as the
// bridge's `Index` lowering does, with the failing edge ending in
// `unreachable` (BRK).
//
// Each kernel is compiled four ways through the public `Pipeline`: O2 and O3,
// transforms ON (an explicit empty disable list, so the ambient
// `TRUST_CG_DISABLE_PASSES` cannot switch them off) and OFF (the in-process
// list `licmframespec,bcetrapbranch`). A C driver runs all four builds and a
// C reference on the same fixed-seed data (lengths 0 to 4099, 0 to 3 passes,
// adversarial words) and compares the returned sums; the kernels whose check
// must fire run in a forked child that must die by SIGTRAP exactly when the
// reference says the access is out of bounds.
//
// Non-vacuity, per build (`PreparationMetrics::optimization_pass_changes`):
// the admitted shapes report at least one aarch64-bounds-check-elim change
// when ON (none of these kernels has a carrier, so the change is the fold)
// and none when OFF; the Vec-sum shape also reports exactly one neon-array
// rewrite ON at O2 and O3 and none OFF, and the ON code carries the `ADD
// Vd.2D` of the vector body. Each transform is also switched off alone
// (compile-only): without the frame speculation the check reloads stay in
// the loop and nothing folds or vectorizes; without the fold the loop stays
// scalar. The negative controls (a loop that stores the slot, a check
// against another field, a check of `k+1`, a non-strict `k <= len` guard)
// must report zero folds, and the last two must trap.
//
// Preheader-writer rows pin where LICM puts a hoisted load. Each is a
// trust-ir function `k(x, n) -> i64` over a zeroed four-word stack array `a`
// whose preheader writes `a[j] = x + 4` right before the loop, which then
// sums `a[2]` `n` times: after a mid-block `TrapBoundsCheckExact` carrier
// (an `in_bounds`-annotated `a[x & 3]` store, with the load behind the exit
// test or in the header), or as the preheader's last instruction before its
// branch (`a[2]` or `a[x & 3]`, loop state in two other slots). The load must
// read the stored value, so it has to land after the store. The same four
// builds and a C reference run over a grid of `x` and `n`; ON, LICM must
// report a hoist in every row, and OFF in exactly the header-load row (a
// load that runs every iteration needs no frame speculation).
//
// Evidence strength: a bounded native differential on the shapes, lengths
// and seeds listed here, plus unit tests of each recognizer's guards. It is
// testing, not a proof that either transform preserves semantics.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fmt::Write as _;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
#[path = "common/native_host.rs"]
mod native_host;

/// The disable-list keys of the two transforms.
const OFF_KEYS: &str = "licmframespec,bcetrapbranch";
const BCE_PASS: &str = "aarch64-bounds-check-elim";
const NEON_ARRAY_PASS: &str = "neon-array";
const LICM_PASS: &str = "licm";

/// The four native builds, in the driver's column order after the reference.
const BUILDS: [(OptLevel, bool, &str); 4] = [
    (OptLevel::O2, true, "on_o2"),
    (OptLevel::O2, false, "off_o2"),
    (OptLevel::O3, true, "on_o3"),
    (OptLevel::O3, false, "off_o3"),
];

/// The kernel shapes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Shape {
    /// `acc += v[k]` (h1_vec_push_sum's sum phase).
    VecSum,
    /// `acc += *v[k]` over boxed elements (h3_box_leak's sum phase).
    BoxSum,
    /// Negative control: the loop stores the length back into the slot every
    /// iteration, so no load of the slot is loop-invariant.
    StoresSlot,
    /// Negative control: the check compares against the capacity field.
    ChecksCap,
    /// Negative control that traps: the body reads `v[k+1]` checked against
    /// the length.
    NextIndex,
    /// Negative control that traps: the header tests `k <=u len`.
    NonStrictGuard,
}

impl Shape {
    fn name(self) -> &'static str {
        match self {
            Shape::VecSum => "vec_sum",
            Shape::BoxSum => "box_sum",
            Shape::StoresSlot => "stores_slot",
            Shape::ChecksCap => "checks_cap",
            Shape::NextIndex => "next_index",
            Shape::NonStrictGuard => "nonstrict_guard",
        }
    }

    /// The fold must fire (ON) for this shape.
    fn folds(self) -> bool {
        matches!(self, Shape::VecSum | Shape::BoxSum)
    }

    /// The vector body must be formed (ON) for this shape.
    fn vectorizes(self) -> bool {
        self == Shape::VecSum
    }

    /// The kernel can reach its BRK on the driver's inputs.
    fn may_trap(self) -> bool {
        matches!(self, Shape::NextIndex | Shape::NonStrictGuard)
    }

    fn all() -> [Shape; 6] {
        [
            Shape::VecSum,
            Shape::BoxSum,
            Shape::StoresSlot,
            Shape::ChecksCap,
            Shape::NextIndex,
            Shape::NonStrictGuard,
        ]
    }
}

/// The trust-ir text of one kernel, named `symbol`.
fn kernel_ir(shape: Shape, symbol: &str) -> String {
    let guard = if shape == Shape::NonStrictGuard {
        "ule"
    } else {
        "ult"
    };
    // The bounds-check block: reload the data pointer and the checked field,
    // then compare the checked index.
    let (check_field, check_index) = match shape {
        Shape::ChecksCap => ("%4", "%30"),
        Shape::NextIndex => ("%5", "%45"),
        _ => ("%5", "%30"),
    };
    let next_index = if shape == Shape::NextIndex {
        "    %45 = add i64 %30, %4\n"
    } else {
        ""
    };
    // The element load and the reduction.
    let element = match shape {
        Shape::BoxSum => {
            "    %50 = gep i64, ptr %41, %30\n\
    %56 = load ptr, ptr %50\n\
    %51 = load i64, ptr %56\n"
        }
        Shape::NextIndex => {
            "    %50 = gep i64, ptr %41, %45\n\
    %51 = load i64, ptr %50\n"
        }
        _ => {
            "    %50 = gep i64, ptr %41, %30\n\
    %51 = load i64, ptr %50\n"
        }
    };
    let store_slot = if shape == Shape::StoresSlot {
        "    store i64 %43, ptr %42\n"
    } else {
        ""
    };
    format!(
        "fn @{symbol}(functy.0) {{\n\
bb0(%0: ptr, %1: i64, %2: ptr):\n\
    %3 = const i64 0\n\
    %4 = const i64 1\n\
    %5 = const i64 2\n\
    %6 = const i64 3\n\
    %7 = alloca i64, %6\n\
    %8 = gep i64, ptr %0, %3\n\
    %9 = load ptr, ptr %8\n\
    %10 = gep i64, ptr %7, %3\n\
    store ptr %9, ptr %10\n\
    %11 = gep i64, ptr %0, %4\n\
    %12 = load i64, ptr %11\n\
    %13 = gep i64, ptr %7, %4\n\
    store i64 %12, ptr %13\n\
    %14 = gep i64, ptr %0, %5\n\
    %15 = load i64, ptr %14\n\
    %16 = gep i64, ptr %7, %5\n\
    store i64 %15, ptr %16\n\
    store ptr %7, ptr %2\n\
    br bb1(%3, %3)\n\
bb1(%20: i64, %21: i64):\n\
    %22 = icmp ult i64 %20, %1\n\
    condbr %22, bb2(%3, %21), bb9\n\
bb2(%30: i64, %31: i64):\n\
    %32 = gep i64, ptr %7, %5\n\
    %33 = load i64, ptr %32\n\
    %34 = icmp {guard} i64 %30, %33\n\
    condbr %34, bb3, bb4\n\
bb3:\n\
    %40 = gep i64, ptr %7, %3\n\
    %41 = load ptr, ptr %40\n\
    %42 = gep i64, ptr %7, {check_field}\n\
    %43 = load i64, ptr %42\n\
{next_index}\
    %44 = icmp ult i64 {check_index}, %43\n\
    condbr %44, bb5, bb8\n\
bb5:\n\
{element}\
{store_slot}\
    %52 = add i64 %31, %51\n\
    %53 = add i64 %30, %4\n\
    br bb2(%53, %52)\n\
bb4:\n\
    %60 = add i64 %20, %4\n\
    br bb1(%60, %31)\n\
bb8:\n\
    unreachable\n\
bb9:\n\
    ret %21\n\
}}\n"
    )
}

/// A one-function module holding `shape` under `symbol`.
fn module(shape: Shape, symbol: &str) -> trust_ir::Module {
    let text = format!(
        "; TrustIr text format v1\nmodule \"vlg\"\ntarget \"{}\" 8 little abi=\"aapcs64\"\n\
         functy.0 = (ptr, i64, ptr) -> (i64)\n{}",
        native_host::TRIPLE,
        kernel_ir(shape, symbol)
    );
    trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("{symbol}: trust-ir parse: {error:?}\n{text}"))
}

/// One compiled build of one kernel.
struct Compiled {
    object: Vec<u8>,
    /// Changing runs of aarch64-bounds-check-elim, neon-array and licm.
    bce_changes: u32,
    neon_array_changes: u32,
    licm_changes: u32,
}

fn compile(shape: Shape, symbol: &str, opt: OptLevel, disabled: &str) -> Compiled {
    compile_module(&module(shape, symbol), symbol, opt, disabled)
}

fn compile_module(
    module: &trust_ir::Module,
    symbol: &str,
    opt: OptLevel,
    disabled: &str,
) -> Compiled {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{symbol}: lowering: {error}"));
    let globals = trust_cg_codegen::compiler::module_object_globals(module)
        .unwrap_or_else(|error| panic!("{symbol}: globals: {error}"));
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: opt,
        target_triple: native_host::TRIPLE.into(),
        disabled_passes_override: Some(disabled.to_string()),
        ..PipelineConfig::default()
    });
    let mut prepared = Vec::new();
    let (mut bce_changes, mut neon_array_changes, mut licm_changes) = (0, 0, 0);
    for (function, _) in &lowered {
        let (function, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .unwrap_or_else(|error| panic!("{symbol} {opt:?} disabled={disabled:?}: {error}"));
        for (name, count) in &metrics.optimization_pass_changes {
            match name.as_str() {
                BCE_PASS => bce_changes += count,
                NEON_ARRAY_PASS => neon_array_changes += count,
                LICM_PASS => licm_changes += count,
                _ => {}
            }
        }
        prepared.push(function);
    }
    let object = pipeline
        .compile_module_with_globals(&prepared, &globals)
        .unwrap_or_else(|error| panic!("{symbol} {opt:?} disabled={disabled:?}: {error}"));
    native_host::assert_native_object(&object);
    Compiled {
        object,
        bce_changes,
        neon_array_changes,
        licm_changes,
    }
}

/// `ADD Vd.2D, Vn.2D, Vm.2D` (Advanced SIMD three same, size 11, U 0).
fn is_add_2d(word: u32) -> bool {
    word & 0xffe0_fc00 == 0x4ee0_8400
}

/// All four native builds of `shape`, checked against its firing contract.
fn compile_all_builds(shape: Shape) -> Vec<(String, Compiled)> {
    let builds: Vec<(String, Compiled)> = BUILDS
        .iter()
        .map(|&(opt, on, tag)| {
            let symbol = format!("{}_{tag}", shape.name());
            let disabled = if on { "" } else { OFF_KEYS };
            let compiled = compile(shape, &symbol, opt, disabled);
            (symbol, compiled)
        })
        .collect();
    for ((opt, on, tag), (_, compiled)) in BUILDS.iter().zip(&builds) {
        let label = format!("{} {tag} ({opt:?})", shape.name());
        if *on && shape.folds() {
            assert!(
                compiled.bce_changes >= 1,
                "{label}: the register-bound check must fold"
            );
        } else {
            assert_eq!(compiled.bce_changes, 0, "{label}: no check may fold");
        }
        let expected_vector = u32::from(*on && shape.vectorizes());
        assert_eq!(
            compiled.neon_array_changes, expected_vector,
            "{label}: neon-array must rewrite exactly {expected_vector} loop(s)"
        );
        let words = native_host::text_words(&compiled.object);
        assert_eq!(
            words.iter().any(|&w| is_add_2d(w)),
            expected_vector == 1,
            "{label}: the `add v.2d` vector body must be present exactly when neon-array fired"
        );
    }
    builds
}

// ---------------------------------------------------------------------------
// C reference and driver
// ---------------------------------------------------------------------------

/// The C reference for `shape`: the same passes, loop, check and reduction in
/// unsigned wrapping arithmetic. A check that would fail returns the TRAP
/// marker through `*trapped` instead of reading out of bounds.
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn c_reference(shape: Shape) -> String {
    let name = shape.name();
    let (loop_test, check, element) = match shape {
        Shape::VecSum | Shape::StoresSlot => ("k < len", "k < len", "d[k]"),
        Shape::BoxSum => ("k < len", "k < len", "*(const uint64_t*)(uintptr_t)d[k]"),
        Shape::ChecksCap => ("k < len", "k < cap", "d[k]"),
        Shape::NextIndex => ("k < len", "k + 1 < len", "d[k + 1]"),
        Shape::NonStrictGuard => ("k <= len", "k < len", "d[k]"),
    };
    format!(
        "uint64_t ref_{name}(const uint64_t* hdr, uint64_t passes, int* trapped) {{\n\
           const uint64_t* d = (const uint64_t*)(uintptr_t)hdr[0];\n\
           uint64_t cap = hdr[1], len = hdr[2], acc = 0;\n\
           (void)cap;\n\
           *trapped = 0;\n\
           for (uint64_t p = 0; p < passes; p++)\n\
             for (uint64_t k = 0; {loop_test}; k++) {{\n\
               if (!({check})) {{ *trapped = 1; return 0; }}\n\
               acc += {element};\n\
             }}\n\
           return acc;\n\
         }}\n"
    )
}

#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
const DRIVER_PRELUDE: &str = r#"
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

typedef uint64_t (*kfn)(const uint64_t*, uint64_t, void**);
typedef uint64_t (*rfn)(const uint64_t*, uint64_t, int*);
typedef struct { const char* name; int boxed; int may_trap; rfn ref; kfn f[4]; } kcase;
static const char* COLUMN[4] = {"on_o2", "off_o2", "on_o3", "off_o3"};

static uint64_t word(uint64_t* s, uint64_t i) {
    *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17;
    switch ((i * 5 + *s % 11) % 11) {
    case 0: return 0;
    case 1: return ~0ull;
    case 2: return 1ull << 63;
    case 3: return 1;
    default: return *s;
    }
}

/* One run of build `f` on `hdr`; forked when the kernel may trap. Returns 0
   when the build agrees with the reference (the same sum, or SIGTRAP where
   the reference traps). */
static int check_build(const kcase* k, int col, const uint64_t* hdr, uint64_t passes,
                       uint64_t expect, int trapped) {
    void* escape = 0;
    if (!k->may_trap) {
        uint64_t got = k->f[col](hdr, passes, &escape);
        if (got != expect) {
            printf("MISMATCH %s %s len=%llu passes=%llu: %llu vs reference %llu\n", k->name,
                   COLUMN[col], (unsigned long long)hdr[2], (unsigned long long)passes,
                   (unsigned long long)got, (unsigned long long)expect);
            return 1;
        }
        return 0;
    }
    fflush(stdout);
    pid_t pid = fork();
    if (pid < 0) { perror("fork"); exit(2); }
    if (pid == 0) _exit(k->f[col](hdr, passes, &escape) == expect ? 0 : 1);
    int status = 0;
    if (waitpid(pid, &status, 0) != pid) { perror("waitpid"); exit(2); }
    int ok = trapped ? (WIFSIGNALED(status) && WTERMSIG(status) == SIGTRAP)
                     : (WIFEXITED(status) && WEXITSTATUS(status) == 0);
    if (!ok) {
        printf("MISMATCH %s %s len=%llu passes=%llu: status 0x%x, reference %s\n", k->name,
               COLUMN[col], (unsigned long long)hdr[2], (unsigned long long)passes, status,
               trapped ? "traps" : "returns");
        return 1;
    }
    return 0;
}

static int run_case(const kcase* k, uint64_t len, uint64_t passes, uint64_t seed) {
    /* One spare element past the data so a wrong k+1 read stays mapped; the
       boxed shape points each element at its own cell. */
    uint64_t* data = malloc((len + 1) * sizeof(uint64_t));
    uint64_t* cells = malloc((len + 1) * sizeof(uint64_t));
    if (!data || !cells) { perror("malloc"); exit(2); }
    uint64_t s = seed | 1;
    for (uint64_t i = 0; i <= len; i++) {
        cells[i] = word(&s, i);
        data[i] = k->boxed ? (uint64_t)(uintptr_t)&cells[i] : word(&s, i);
    }
    uint64_t hdr[3] = {(uint64_t)(uintptr_t)data, len + (seed % 3), len};
    int trapped = 0;
    uint64_t expect = k->ref(hdr, passes, &trapped);
    int bad = 0;
    for (int col = 0; col < 4; col++) bad |= check_build(k, col, hdr, passes, expect, trapped);
    free(data);
    free(cells);
    return bad;
}
"#;

/// The C driver running every kernel's four builds against its reference
/// over the length, pass and seed grid.
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn c_driver(shapes: &[Shape]) -> String {
    let mut s = String::from(DRIVER_PRELUDE);
    for shape in shapes {
        let name = shape.name();
        let _ = writeln!(s, "uint64_t ref_{name}(const uint64_t*, uint64_t, int*);");
        for (_, _, tag) in BUILDS {
            let _ = writeln!(
                s,
                "uint64_t {name}_{tag}(const uint64_t*, uint64_t, void**);"
            );
        }
    }
    s.push_str("static const kcase CASES[] = {\n");
    for shape in shapes {
        let _ = writeln!(
            s,
            "  {{\"{n}\", {boxed}, {trap}, ref_{n}, {{{n}_on_o2, {n}_off_o2, {n}_on_o3, {n}_off_o3}}}},",
            n = shape.name(),
            boxed = i32::from(*shape == Shape::BoxSum),
            trap = i32::from(shape.may_trap()),
        );
    }
    s.push_str(
        "};\n\
         int main(void) {\n\
           static const uint64_t LENS[] = {0, 1, 2, 7, 8, 9, 15, 16, 17, 31, 63, 64, 65, 1000, 4099};\n\
           static const uint64_t PASSES[] = {0, 1, 3};\n\
           static const uint64_t SEEDS[2] = {0x9e3779b97f4a7c15ull, 0x243f6a8885a308d3ull};\n\
           int bad = 0; unsigned runs = 0;\n\
           for (unsigned i = 0; i < sizeof CASES / sizeof CASES[0]; i++)\n\
             for (unsigned l = 0; l < sizeof LENS / sizeof LENS[0]; l++)\n\
               for (unsigned p = 0; p < sizeof PASSES / sizeof PASSES[0]; p++)\n\
                 for (unsigned s = 0; s < 2; s++) { bad |= run_case(&CASES[i], LENS[l], PASSES[p], SEEDS[s]); runs++; }\n\
           printf(\"vec-len-guard differential: %u kernel runs x 4 builds, %s\\n\", runs, bad ? \"MISMATCH\" : \"all equal\");\n\
           return bad;\n\
         }\n",
    );
    s
}

/// Compile every kernel (checking the firing contract), link the objects
/// with the C reference and driver, run it, and require every build to agree
/// with the reference.
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn run_differential(shapes: &[Shape]) {
    use std::process::Command;

    let dir = fresh_dir::create("trust_cg_vlg_");
    let mut objects = Vec::new();
    let mut reference = String::from("#include <stdint.h>\n");
    for &shape in shapes {
        for (symbol, compiled) in compile_all_builds(shape) {
            let path = dir.join(format!("{symbol}.o"));
            std::fs::write(&path, &compiled.object).expect("write object");
            objects.push(path);
        }
        reference.push_str(&c_reference(shape));
    }
    let ref_c = dir.join("reference.c");
    let ref_o = dir.join("reference.o");
    let driver_c = dir.join("driver.c");
    let binary = dir.join("differential");
    std::fs::write(&ref_c, reference).expect("write reference");
    std::fs::write(&driver_c, c_driver(shapes)).expect("write driver");
    let cc = Command::new(native_host::C_COMPILER)
        .args(["-O2", "-c"])
        .arg(&ref_c)
        .arg("-o")
        .arg(&ref_o)
        .output()
        .expect("run the C compiler");
    assert!(
        cc.status.success(),
        "C reference:\n{}",
        String::from_utf8_lossy(&cc.stderr)
    );
    let link = Command::new(native_host::C_COMPILER)
        .arg("-O1")
        .arg(&driver_c)
        .arg(&ref_o)
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
    let run = Command::new(&binary)
        .output()
        .expect("run the differential");
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success(),
        "native results differ from the C reference (scratch kept at {}):\n{stdout}{}",
        dir.display(),
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(stdout.contains("all equal"), "{stdout}");
    eprintln!(
        "{} kernels on {}: {stdout}",
        shapes.len(),
        native_host::HOST
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Host-neutral compile checks (every host, native-triple objects)
// ---------------------------------------------------------------------------

/// The admitted shapes fold ON at O2 and O3 (and the Vec sum vectorizes);
/// OFF, nothing folds or vectorizes.
#[test]
fn admitted_shapes_fold_on_and_stay_scalar_off() {
    for shape in [Shape::VecSum, Shape::BoxSum] {
        compile_all_builds(shape);
    }
}

/// Every negative control keeps its check ON and OFF.
#[test]
fn negative_controls_keep_their_checks() {
    for shape in [
        Shape::StoresSlot,
        Shape::ChecksCap,
        Shape::NextIndex,
        Shape::NonStrictGuard,
    ] {
        compile_all_builds(shape);
    }
}

/// Each transform switched off alone: without the frame speculation the
/// pointer and length reloads stay behind the exit test, so the check's
/// length is not the header's and nothing folds or vectorizes; without the
/// fold the hoisted loads alone leave the check (and a scalar loop) in place.
#[test]
fn each_transform_is_needed_for_the_vec_sum_fix() {
    for opt in [OptLevel::O2, OptLevel::O3] {
        let no_spec = compile(Shape::VecSum, "vec_sum_nospec", opt, "licmframespec");
        assert_eq!(no_spec.bce_changes, 0, "{opt:?}: no fold without the hoist");
        assert_eq!(
            no_spec.neon_array_changes, 0,
            "{opt:?}: scalar without the hoist"
        );
        let no_fold = compile(Shape::VecSum, "vec_sum_nofold", opt, "bcetrapbranch");
        assert_eq!(no_fold.bce_changes, 0, "{opt:?}: fold switched off");
        assert_eq!(
            no_fold.neon_array_changes, 0,
            "{opt:?}: scalar without the fold"
        );
        let on = compile(Shape::VecSum, "vec_sum_on", opt, "");
        let off = compile(Shape::VecSum, "vec_sum_off", opt, OFF_KEYS);
        let words = |c: &Compiled| native_host::text_words(&c.object);
        assert_ne!(
            words(&no_fold),
            words(&off),
            "{opt:?}: the hoist alone changes the code"
        );
        assert_ne!(
            words(&on),
            words(&no_fold),
            "{opt:?}: the fold changes the code"
        );
    }
}

// ---------------------------------------------------------------------------
// Native differential (AArch64 Linux GNU and macOS hosts)
// ---------------------------------------------------------------------------

/// Every shape, transforms ON and OFF at O2 and O3, agrees with the C
/// reference (sums, and SIGTRAP exactly where the reference traps).
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
fn every_build_matches_the_c_reference() {
    run_differential(&Shape::all());
}

// ---------------------------------------------------------------------------
// Preheader writers: a hoisted load reads the state the loop is entered with
// ---------------------------------------------------------------------------

/// The preheader-writer kernels `k(x, n) -> i64` (see the file header).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum WriterShape {
    /// `in_bounds` carrier then `a[x & 3] = x + 4`; `a[2]` loaded behind the
    /// exit test (the frame-speculation tier).
    CarrierBody,
    /// The same preheader; `a[2]` loaded in the loop header, before the exit
    /// test, so it runs every iteration (the guaranteed-to-execute tier).
    CarrierHeader,
    /// `a[2] = x + 4` is the preheader's last instruction before its branch.
    StoreLastConst,
    /// `a[x & 3] = x + 4` is the preheader's last instruction before its branch.
    StoreLastIndex,
}

impl WriterShape {
    fn name(self) -> &'static str {
        match self {
            WriterShape::CarrierBody => "carrier_body",
            WriterShape::CarrierHeader => "carrier_header",
            WriterShape::StoreLastConst => "store_last_const",
            WriterShape::StoreLastIndex => "store_last_index",
        }
    }

    /// LICM hoists the `a[2]` load with the frame speculation off too.
    fn hoists_off(self) -> bool {
        self == WriterShape::CarrierHeader
    }

    /// The preheader stores to `a[2]` whatever `x` is (else to `a[x & 3]`).
    fn stores_const_index(self) -> bool {
        self == WriterShape::StoreLastConst
    }

    fn all() -> [WriterShape; 4] {
        [
            WriterShape::CarrierBody,
            WriterShape::CarrierHeader,
            WriterShape::StoreLastConst,
            WriterShape::StoreLastIndex,
        ]
    }
}

/// The zeroed four-word array `%7` (constants `%3`..`%6`, `%60`), shared by
/// every preheader-writer kernel.
const WRITER_PROLOGUE: &str = "    %3 = const i64 0\n\
    %4 = const i64 1\n\
    %5 = const i64 2\n\
    %6 = const i64 4\n\
    %60 = const i64 3\n\
    %7 = alloca i64, %6\n\
    %40 = gep i64, ptr %7, %3\n\
    store i64 %3, ptr %40\n\
    %41 = gep i64, ptr %7, %4\n\
    store i64 %3, ptr %41\n\
    %42 = gep i64, ptr %7, %5\n\
    store i64 %3, ptr %42\n\
    %43 = gep i64, ptr %7, %60\n\
    store i64 %3, ptr %43\n";

/// The trust-ir text of one preheader-writer kernel, named `symbol`.
fn writer_kernel_ir(shape: WriterShape, symbol: &str) -> String {
    match shape {
        WriterShape::CarrierBody | WriterShape::CarrierHeader => {
            let load = "    %30 = gep i64, ptr %7, %5\n    %31 = load i64, ptr %30\n";
            let (header_load, body_load) = if shape == WriterShape::CarrierHeader {
                (load, "")
            } else {
                ("", load)
            };
            format!(
                "fn @{symbol}(functy.0) {{\n\
bb0(%0: i64, %1: i64):\n\
{WRITER_PROLOGUE}\
    %8 = and i64 %0, %60\n\
    %9 = icmp ult i64 %8, %6  ; #proof: in_bounds\n\
    %10 = gep i64, ptr %7, %8\n\
    %11 = add i64 %0, %6\n\
    store i64 %11, ptr %10\n\
    br bb1(%3, %3)\n\
bb1(%20: i64, %21: i64):\n\
{header_load}\
    %22 = icmp ult i64 %20, %1\n\
    condbr %22, bb2, bb9\n\
bb2:\n\
{body_load}\
    %32 = add i64 %21, %31\n\
    %33 = add i64 %20, %4\n\
    br bb1(%33, %32)\n\
bb9:\n\
    ret %21\n\
}}\n"
            )
        }
        WriterShape::StoreLastConst | WriterShape::StoreLastIndex => {
            let index = if shape.stores_const_index() {
                "%5"
            } else {
                "%8"
            };
            format!(
                "fn @{symbol}(functy.0) {{\n\
bb0(%0: i64, %1: i64):\n\
{WRITER_PROLOGUE}\
    %70 = alloca i64, %4\n\
    %71 = alloca i64, %4\n\
    store i64 %3, ptr %70\n\
    store i64 %3, ptr %71\n\
    %8 = and i64 %0, %60\n\
    %11 = add i64 %0, %6\n\
    %10 = gep i64, ptr %7, {index}\n\
    store i64 %11, ptr %10\n\
    br bb1\n\
bb1:\n\
    %20 = load i64, ptr %70\n\
    %22 = icmp ult i64 %20, %1\n\
    condbr %22, bb2, bb9\n\
bb2:\n\
    %30 = gep i64, ptr %7, %5\n\
    %31 = load i64, ptr %30\n\
    %21 = load i64, ptr %71\n\
    %32 = add i64 %21, %31\n\
    store i64 %32, ptr %71\n\
    %33 = add i64 %20, %4\n\
    store i64 %33, ptr %70\n\
    br bb1\n\
bb9:\n\
    %50 = load i64, ptr %71\n\
    ret %50\n\
}}\n"
            )
        }
    }
}

/// A one-function module holding the preheader-writer kernel `shape`.
fn writer_module(shape: WriterShape, symbol: &str) -> trust_ir::Module {
    let text = format!(
        "; TrustIr text format v1\nmodule \"vlgw\"\ntarget \"{}\" 8 little abi=\"aapcs64\"\n\
         functy.0 = (i64, i64) -> (i64)\n{}",
        native_host::TRIPLE,
        writer_kernel_ir(shape, symbol)
    );
    trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("{symbol}: trust-ir parse: {error:?}\n{text}"))
}

/// All four native builds of a preheader-writer kernel, checked against its
/// LICM firing contract: a hoist ON in every row, OFF only in the
/// header-load row.
fn compile_writer_builds(shape: WriterShape) -> Vec<(String, Compiled)> {
    BUILDS
        .iter()
        .map(|&(opt, on, tag)| {
            let symbol = format!("{}_{tag}", shape.name());
            let disabled = if on { "" } else { OFF_KEYS };
            let compiled = compile_module(&writer_module(shape, &symbol), &symbol, opt, disabled);
            let label = format!("{} {tag} ({opt:?})", shape.name());
            if on || shape.hoists_off() {
                assert!(
                    compiled.licm_changes >= 1,
                    "{label}: LICM must hoist the a[2] load"
                );
            } else {
                assert_eq!(
                    compiled.licm_changes, 0,
                    "{label}: without the frame speculation nothing hoists"
                );
            }
            (symbol, compiled)
        })
        .collect()
}

/// The C driver comparing every preheader-writer build with the reference
/// `a[j] = x + 4; for k < n: acc += a[2]` over a grid of `x` and `n`.
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn writer_c_driver(shapes: &[WriterShape]) -> String {
    let mut s = String::from(
        "#include <stdint.h>\n\
         #include <stdio.h>\n\
         typedef uint64_t (*wfn)(uint64_t, uint64_t);\n\
         typedef struct { const char* name; int const_index; wfn f[4]; } wcase;\n\
         static const char* COLUMN[4] = {\"on_o2\", \"off_o2\", \"on_o3\", \"off_o3\"};\n\
         static uint64_t reference(int const_index, uint64_t x, uint64_t n) {\n\
           volatile uint64_t a[4] = {0, 0, 0, 0};\n\
           a[const_index ? 2 : (x & 3)] = x + 4;\n\
           uint64_t acc = 0;\n\
           for (uint64_t k = 0; k < n; k++) acc += a[2];\n\
           return acc;\n\
         }\n",
    );
    for shape in shapes {
        for (_, _, tag) in BUILDS {
            let _ = writeln!(s, "uint64_t {}_{tag}(uint64_t, uint64_t);", shape.name());
        }
    }
    s.push_str("static const wcase CASES[] = {\n");
    for shape in shapes {
        let _ = writeln!(
            s,
            "  {{\"{n}\", {c}, {{{n}_on_o2, {n}_off_o2, {n}_on_o3, {n}_off_o3}}}},",
            n = shape.name(),
            c = i32::from(shape.stores_const_index()),
        );
    }
    s.push_str(
        "};\n\
         int main(void) {\n\
           static const uint64_t XS[] = {0, 1, 2, 3, 4, 5, 6, 7, 10, 0x8000000000000002ull,\n\
                                         0xfffffffffffffffeull, 0xffffffffffffffffull};\n\
           static const uint64_t NS[] = {0, 1, 2, 3, 7, 100};\n\
           int bad = 0; unsigned runs = 0;\n\
           for (unsigned i = 0; i < sizeof CASES / sizeof CASES[0]; i++)\n\
             for (unsigned xi = 0; xi < sizeof XS / sizeof XS[0]; xi++)\n\
               for (unsigned ni = 0; ni < sizeof NS / sizeof NS[0]; ni++) {\n\
                 uint64_t x = XS[xi], n = NS[ni];\n\
                 uint64_t want = reference(CASES[i].const_index, x, n);\n\
                 for (int col = 0; col < 4; col++) {\n\
                   uint64_t got = CASES[i].f[col](x, n);\n\
                   if (got != want) {\n\
                     printf(\"MISMATCH %s %s x=%llu n=%llu: %llu vs reference %llu\\n\",\n\
                            CASES[i].name, COLUMN[col], (unsigned long long)x,\n\
                            (unsigned long long)n, (unsigned long long)got,\n\
                            (unsigned long long)want);\n\
                     bad = 1;\n\
                   }\n\
                 }\n\
                 runs++;\n\
               }\n\
           printf(\"preheader-writer differential: %u kernel runs x 4 builds, %s\\n\", runs,\n\
                  bad ? \"MISMATCH\" : \"all equal\");\n\
           return bad;\n\
         }\n",
    );
    s
}

/// The preheader-writer rows compile to the expected LICM firing pattern at
/// O2 and O3 with the transforms on and off.
#[test]
fn preheader_writer_kernels_hoist_as_expected() {
    for shape in WriterShape::all() {
        compile_writer_builds(shape);
    }
}

/// Every preheader-writer build agrees with the C reference: the hoisted
/// `a[2]` load reads the value the preheader stored.
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
fn preheader_writer_builds_match_the_c_reference() {
    use std::process::Command;

    let shapes = WriterShape::all();
    let dir = fresh_dir::create("trust_cg_vlgw_");
    let mut objects = Vec::new();
    for shape in shapes {
        for (symbol, compiled) in compile_writer_builds(shape) {
            let path = dir.join(format!("{symbol}.o"));
            std::fs::write(&path, &compiled.object).expect("write object");
            objects.push(path);
        }
    }
    let driver_c = dir.join("driver.c");
    let binary = dir.join("differential");
    std::fs::write(&driver_c, writer_c_driver(&shapes)).expect("write driver");
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
    let run = Command::new(&binary)
        .output()
        .expect("run the differential");
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success(),
        "native results differ from the C reference (scratch kept at {}):\n{stdout}{}",
        dir.display(),
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(stdout.contains("all equal"), "{stdout}");
    eprintln!(
        "{} kernels on {}: {stdout}",
        shapes.len(),
        native_host::HOST
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
