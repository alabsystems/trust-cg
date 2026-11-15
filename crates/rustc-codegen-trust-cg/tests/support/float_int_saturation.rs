//! The float -> integer conversion differential behind
//! `tests/float_to_int_saturating_differential.rs`, which states the claims.
//!
//! Kept apart from that test so the identical code also runs where the build
//! compiler cannot load the backend (a host whose bridge links another
//! `librustc_driver` than its build compiler): the caller passes the compiler
//! commands, and a report that drives it outside Cargo names the compiler it
//! used. Nothing here selects a backend or a compiler.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates
//! License: Apache-2.0

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::{CastOp, Inst, Module, Ty};

include!("float_int_saturation/spec.rs");

/// The conversions, one exported function per (float, integer) pair.
pub const CASTS: &str = include_str!("float_int_saturation/casts.rs");
/// The LLVM-built driver; [`SPEC`] is appended to it.
pub const DRIVER: &str = include_str!("float_int_saturation/driver.rs");
/// The reference semantics, shared by this harness and the driver.
pub const SPEC: &str = include_str!("float_int_saturation/spec.rs");
/// The 128-bit rows linked against the platform's runtime by the C driver.
pub const SYSTEM_RUNTIME: &str = include_str!("float_int_saturation/system_runtime.c");
/// Every optimization level the bridge maps.
pub const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];

const FLOATS: [Ty; 2] = [Ty::F32, Ty::F64];
const INTS: [Ty; 12] = [
    Ty::I8,
    Ty::I16,
    Ty::I32,
    Ty::I64,
    Ty::I128,
    Ty::Isize,
    Ty::U8,
    Ty::U16,
    Ty::U32,
    Ty::U64,
    Ty::U128,
    Ty::Usize,
];

/// One (float, integer) pair and the names casts.rs exports it under.
pub struct Conversion {
    pub float: Ty,
    pub int: Ty,
    pub as_name: String,
    pub unchecked_name: String,
}

fn rust_name(ty: &Ty) -> &'static str {
    match ty {
        Ty::F32 => "f32",
        Ty::F64 => "f64",
        Ty::I8 => "i8",
        Ty::I16 => "i16",
        Ty::I32 => "i32",
        Ty::I64 => "i64",
        Ty::I128 => "i128",
        Ty::Isize => "isize",
        Ty::U8 => "u8",
        Ty::U16 => "u16",
        Ty::U32 => "u32",
        Ty::U64 => "u64",
        Ty::U128 => "u128",
        Ty::Usize => "usize",
        other => panic!("no Rust spelling for {other:?} in this fixture"),
    }
}

/// Every pair casts.rs exports, in its order.
pub fn conversions() -> Vec<Conversion> {
    let mut all = Vec::new();
    for float in FLOATS {
        for int in INTS {
            let pair = format!("{}_{}", rust_name(&float), rust_name(&int));
            all.push(Conversion {
                float: float.clone(),
                int,
                as_name: format!("as_{pair}"),
                unchecked_name: format!("unchecked_{pair}"),
            });
        }
    }
    all
}

/// Width and signedness. Pointer-width integers are 64-bit: the bridge's
/// native hosts are 64-bit.
fn int_shape(ty: &Ty) -> (u32, bool) {
    match ty {
        Ty::I8 => (8, true),
        Ty::I16 => (16, true),
        Ty::I32 => (32, true),
        Ty::I64 | Ty::Isize => (64, true),
        Ty::I128 => (128, true),
        Ty::U8 => (8, false),
        Ty::U16 => (16, false),
        Ty::U32 => (32, false),
        Ty::U64 | Ty::Usize => (64, false),
        Ty::U128 => (128, false),
        other => panic!("{other:?} is not an integer of this fixture"),
    }
}

fn float_format(ty: &Ty) -> (u32, u32) {
    match ty {
        Ty::F32 => (8, 23),
        Ty::F64 => (11, 52),
        other => panic!("{other:?} is not a float of this fixture"),
    }
}

/// The inputs of `float` (encodings), as the driver uses them.
pub fn inputs(float: &Ty) -> Vec<u64> {
    match float {
        Ty::F32 => spec_inputs_f32(),
        _ => spec_inputs_f64(),
    }
}

/// What the dumped trust-ir says about the conversions.
#[derive(Default)]
pub struct TrustIrFindings {
    /// Each finding names its function; empty when the claim holds.
    pub failures: Vec<String>,
    /// Float -> integer casts that are the saturating op.
    pub saturating_casts: usize,
    /// Reference-interpreter executions compared with the spec.
    pub interpreted_calls: usize,
    /// The text of every exported conversion function, for the record.
    pub listing: String,
}

/// Hold the modules the backend handed to trust-cg to Rust's semantics:
///
/// 1. every float -> integer conversion `Cast` in them is `fptosi.sat` /
///    `fptoui.sat` of the destination's signedness, never the raw `fptosi` /
///    `fptoui`, which trust-ir leaves undefined for NaN and out-of-range
///    values;
/// 2. trust-ir's own reference interpreter, run on each exported function
///    and each input, returns what spec.rs says Rust returns (for
///    `to_int_unchecked`, on the inputs where Rust defines it).
pub fn check_trust_ir(modules: &[Module]) -> TrustIrFindings {
    let mut findings = TrustIrFindings::default();
    for module in modules {
        for function in &module.functions {
            for block in &function.blocks {
                for node in &block.body {
                    let Inst::Cast {
                        op, src_ty, dst_ty, ..
                    } = &node.inst
                    else {
                        continue;
                    };
                    if !matches!(
                        op,
                        CastOp::FPToSI | CastOp::FPToUI | CastOp::FPToSISat | CastOp::FPToUISat
                    ) {
                        continue;
                    }
                    let want = if dst_ty.is_signed() {
                        CastOp::FPToSISat
                    } else {
                        CastOp::FPToUISat
                    };
                    if *op == want {
                        findings.saturating_casts += 1;
                    } else {
                        findings.failures.push(format!(
                            "`{}`: `{op}` {src_ty} -> {dst_ty} where Rust's conversion is `{want}`",
                            function.name
                        ));
                    }
                }
            }
        }
    }
    for conversion in conversions() {
        let (exp_bits, man_bits) = float_format(&conversion.float);
        let (bits, signed) = int_shape(&conversion.int);
        for (name, unchecked) in [
            (&conversion.as_name, false),
            (&conversion.unchecked_name, true),
        ] {
            let Some((module, function)) = modules.iter().find_map(|module| {
                module
                    .functions
                    .iter()
                    .find(|function| function.name == *name)
                    .map(|function| (module, function))
            }) else {
                findings
                    .failures
                    .push(format!("`{name}`: no dumped module defines it"));
                continue;
            };
            findings.listing.push_str(&format!("{function}\n"));
            let interpreter = Interpreter::with_module(module);
            let mut wrong = 0usize;
            let mut first = None;
            for input in inputs(&conversion.float) {
                let truncated = spec_trunc(input, exp_bits, man_bits);
                if unchecked && !spec_unchecked_defined(truncated, bits, signed) {
                    continue;
                }
                let want = spec_saturating(truncated, bits, signed);
                let argument = InterpretValue {
                    ty: conversion.float.clone(),
                    kind: InterpretValueKind::FloatBits(input),
                };
                findings.interpreted_calls += 1;
                let got = match interpreter.execute_function(function, [argument]) {
                    Ok(outcome) => match outcome.returns.as_slice() {
                        [value] => value
                            .as_int()
                            .map(|int| format!("{:#x}", int.as_unsigned()))
                            .unwrap_or_else(|| format!("non-integer {value:?}")),
                        other => format!("{} returned values", other.len()),
                    },
                    // The interpreter prints a float's full decimal expansion;
                    // the code and the head of the message identify the case.
                    Err(error) => format!(
                        "{:?}: {}",
                        error.code,
                        error.message.chars().take(96).collect::<String>()
                    ),
                };
                if got != format!("{want:#x}") {
                    wrong += 1;
                    first.get_or_insert(format!("({input:#x}) = {got}, Rust gives {want:#x}"));
                }
            }
            if let Some(first) = first {
                findings.failures.push(format!(
                    "`{name}`: the reference interpreter disagrees with Rust on {wrong} \
                     input(s), first {first}"
                ));
            }
        }
    }
    findings
}

/// The `.trust_irbin` modules a `dump-trust-ir=<dir>` compile wrote, decoded.
pub fn dumped_modules(dir: &Path) -> Result<Vec<Module>, String> {
    let mut paths: Vec<PathBuf> = std::fs::read_dir(dir)
        .map_err(|error| format!("read {}: {error}", dir.display()))?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "trust_irbin"))
        .collect();
    paths.sort();
    if paths.is_empty() {
        return Err(format!("no .trust_irbin module under {}", dir.display()));
    }
    paths
        .iter()
        .map(|path| {
            let bytes = std::fs::read(path).map_err(|error| format!("read {path:?}: {error}"))?;
            trust_ir::binary::deserialize_module(&bytes)
                .map_err(|error| format!("{}: does not decode: {error:?}", path.display()))
        })
        .collect()
}

/// Compile casts.rs at `opt` with `compiler` into `dir`; the objects it wrote.
pub fn compile_casts(mut compiler: Command, dir: &Path, opt: &str) -> Result<Vec<PathBuf>, String> {
    std::fs::create_dir_all(dir).map_err(|error| error.to_string())?;
    let source = dir.join("casts.rs");
    std::fs::write(&source, CASTS).map_err(|error| error.to_string())?;
    let output = compiler
        .args(["--crate-type", "lib", "--crate-name", "casts", "--emit=obj"])
        .args(["-Cpanic=abort", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--out-dir")
        .arg(dir)
        .arg(&source)
        .output()
        .map_err(|error| format!("spawn the compiler: {error}"))?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let mut objects: Vec<PathBuf> = std::fs::read_dir(dir)
        .map_err(|error| error.to_string())?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    objects.sort();
    if objects.is_empty() {
        return Err(format!("no object under {}", dir.display()));
    }
    Ok(objects)
}

/// A finished run: exit code (`None` = killed by a signal) and stdout.
pub struct Run {
    pub code: Option<i32>,
    pub stdout: String,
}

/// Run `binary`; its stdout is also kept beside it as `<binary>.out`.
fn run(binary: &Path) -> Result<Run, String> {
    let output = Command::new(binary)
        .output()
        .map_err(|error| format!("run {}: {error}", binary.display()))?;
    let _ = std::fs::write(binary.with_extension("out"), &output.stdout);
    Ok(Run {
        code: output.status.code(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
    })
}

/// Link `objects` into the Rust driver (built by `llvm`, no backend) and run it.
pub fn run_rust_driver(mut llvm: Command, dir: &Path, objects: &[PathBuf]) -> Result<Run, String> {
    let source = dir.join("driver.rs");
    std::fs::write(&source, format!("{DRIVER}\n{SPEC}")).map_err(|error| error.to_string())?;
    let binary = dir.join("driver");
    llvm.args(["--crate-type", "bin", "-Copt-level=0"]);
    for object in objects {
        let mut arg = std::ffi::OsString::from("-Clink-arg=");
        arg.push(object);
        llvm.arg(arg);
    }
    let output = llvm
        .arg("-o")
        .arg(&binary)
        .arg(&source)
        .output()
        .map_err(|error| format!("spawn the compiler: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "the driver did not build: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    run(&binary)
}

/// Link `objects` into the C driver with the C compiler driver, so the
/// platform runtime supplies every `__fix*ti`, and run it.
pub fn run_system_runtime_driver(dir: &Path, objects: &[PathBuf]) -> Result<Run, String> {
    let source = dir.join("system_runtime.c");
    std::fs::write(&source, SYSTEM_RUNTIME).map_err(|error| error.to_string())?;
    let binary = dir.join("system_runtime");
    let output = Command::new("cc")
        .arg("-O0")
        .arg("-o")
        .arg(&binary)
        .arg(&source)
        .args(objects)
        .output()
        .map_err(|error| format!("spawn cc: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "the C driver did not link: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    run(&binary)
}

/// The native half at one optimization level: casts.rs built by LLVM and by
/// trust-cg (`cg`, which must compile it), each linked into both drivers.
/// The LLVM build must match the spec everywhere (else the oracle itself is
/// wrong); trust-cg's must print exactly LLVM's lines and pass the C driver.
pub fn native_differential(
    llvm: &dyn Fn() -> Command,
    cg: &dyn Fn() -> Command,
    root: &Path,
    opt: &str,
) -> Result<String, Vec<String>> {
    let mut failures = Vec::new();
    let mut runs = Vec::new();
    for (side, compiler) in [("llvm", llvm()), ("trust-cg", cg())] {
        let dir = root.join(format!("O{opt}-{side}"));
        let objects = match compile_casts(compiler, &dir, opt) {
            Ok(objects) => objects,
            Err(stderr) => {
                failures.push(format!(
                    "O{opt} {side}: casts.rs did not compile:\n{stderr}"
                ));
                continue;
            }
        };
        let rust = run_rust_driver(llvm(), &dir, &objects);
        let system = run_system_runtime_driver(&dir, &objects);
        runs.push((side, rust, system));
    }
    let summary = |run: &Run| {
        run.stdout
            .lines()
            .last()
            .unwrap_or("<no output>")
            .to_owned()
    };
    let mut report = Vec::new();
    for (side, rust, system) in &runs {
        match rust {
            Ok(run) if run.code == Some(0) => {
                report.push(format!("O{opt} {side}: {}", summary(run)))
            }
            Ok(run) => {
                let lines: Vec<&str> = run
                    .stdout
                    .lines()
                    .filter(|line| line.contains("MISMATCH"))
                    .take(8)
                    .collect();
                failures.push(format!(
                    "O{opt} {side}: the Rust driver exited {:?}, {}; first:\n  {}",
                    run.code,
                    summary(run),
                    lines.join("\n  ")
                ));
            }
            Err(error) => failures.push(format!("O{opt} {side}: {error}")),
        }
        match system {
            Ok(run) if run.code == Some(0) => {
                report.push(format!("O{opt} {side}: {}", summary(run)))
            }
            Ok(run) => failures.push(format!(
                "O{opt} {side}: the system-runtime driver exited {:?}:\n{}",
                run.code, run.stdout
            )),
            Err(error) => failures.push(format!("O{opt} {side}: {error}")),
        }
    }
    // Equal lines, not only equal summaries: the two builds must agree on
    // every call even where the spec column could be wrong.
    if let [(_, Ok(llvm_run), _), (_, Ok(cg_run), _)] = runs.as_slice() {
        let differing: Vec<String> = llvm_run
            .stdout
            .lines()
            .zip(cg_run.stdout.lines())
            .filter(|(a, b)| a != b)
            .take(8)
            .map(|(a, b)| format!("llvm {a}\n  cg   {b}"))
            .collect();
        if !differing.is_empty() || llvm_run.stdout.lines().count() != cg_run.stdout.lines().count()
        {
            failures.push(format!(
                "O{opt}: trust-cg's results differ from LLVM's; first:\n  {}",
                differing.join("\n  ")
            ));
        }
    }
    if failures.is_empty() {
        Ok(report.join("\n"))
    } else {
        Err(failures)
    }
}
