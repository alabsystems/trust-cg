// trust-cg-fuzz/src/jit_diff.rs - Core JIT-differential-harness logic.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use std::collections::HashMap;
use std::panic;
use std::time::Duration;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::interpreter::{InterpreterConfig, InterpreterValue, interpret_with_config};
use trust_cg_codegen::pipeline::OptLevel;

use crate::trust_ir_gen::{CONSUMER_STATUS_BYTES, FUZZ_FN_NAME};

/// Per-invocation soft deadline for a single JIT call. Random trust_ir can
/// generate genuine infinite loops via adversarial branches; do not let a
/// single program stall the driver.
pub const PER_INVOKE_TIMEOUT_MS: u64 = 1_500;

/// Outcome of one Path B (compile + JIT-execute) attempt.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum JitOutcome {
    /// Runtime produced this i64.
    Value(i64),
    /// Pipeline / JIT cannot handle this trust_ir at this opt level; skip.
    Unsupported(String),
    /// Pipeline / JIT call panicked.
    Panic(String),
    /// Call did not return within `PER_INVOKE_TIMEOUT_MS`.
    Timeout,
    /// The JIT'd code executed a HARDWARE trap at run time — e.g. `idiv` #DE on
    /// divide-by-zero or INT_MIN / -1 (SIGFPE), a bad load (SIGSEGV/SIGBUS), or
    /// an illegal instruction (SIGILL). Carries the terminating signal number.
    /// This is NOT a panic: it is the JIT producing no value because the CPU
    /// faulted. The classifier compares it against whether the oracle had a
    /// defined value: both-no-value is OK, JIT-trap-while-oracle-has-value (or
    /// one opt-level traps while another returns a value) is a finding.
    Trapped(i32),
}

/// Pointer-buffer consumer lane result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsumerSnapshot {
    pub ret: i64,
    pub bytes: [u8; CONSUMER_STATUS_BYTES],
}

/// Outcome of one consumer-shape JIT attempt.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum ConsumerJitOutcome {
    Value(ConsumerSnapshot),
    Unsupported(String),
    Panic(String),
    Timeout,
    /// JIT'd code executed a hardware trap at run time (see [`JitOutcome::Trapped`]).
    Trapped(i32),
}

/// Run the trust_ir interpreter on `(module, args)`. Returns the first i64 return
/// value, or an error string on panic / divide-by-zero / fuel exhaustion.
pub fn run_oracle_one(module: &trust_ir::Module, args: &[i64]) -> Result<i64, String> {
    let ivals: Vec<InterpreterValue> = args
        .iter()
        .map(|&x| InterpreterValue::Int(x as i128))
        .collect();
    let cfg = InterpreterConfig {
        fuel: 200_000,
        max_call_depth: 32,
    };
    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        interpret_with_config(module, FUZZ_FN_NAME, &ivals, cfg)
    }));
    match result {
        Ok(Ok(vs)) => match vs.into_iter().next() {
            Some(InterpreterValue::Int(x)) => Ok(x as i64),
            Some(InterpreterValue::Bool(b)) => Ok(if b { 1 } else { 0 }),
            Some(_) | None => Err("interp_unsupported_ret".to_string()),
        },
        Ok(Err(e)) => Err(format!("interp_err: {}", e)),
        Err(_) => Err("interp_panic".to_string()),
    }
}

/// The interpreter's `sext Bool -> i64` result, if it is in the domain of a
/// one-bit sign extension: `0` for false, all ones (`-1`) for true.
///
/// This is trust-ir's meaning (its reference interpreter widens
/// `as_signed()` of the 1-bit value, `interpret.rs` `eval_cast`) and LLVM's
/// `sext i1`. Since `1d65e8e64` the interpreter computes it directly;
/// before, it returned the raw Bool `1`, which a harness projected to `-1`.
/// Every other value, the retired `1` included, is refused, so neither a
/// return of that model nor any other change to the interpreter can be
/// silently normalized into agreement.
pub fn bool_sext_i64_oracle_result(raw: i64) -> Option<i64> {
    match raw {
        0 | -1 => Some(raw),
        _ => None,
    }
}

/// Compile `module` at `opt` and JIT-execute `FUZZ_FN_NAME` with `args`.
/// The generator guarantees a 4 x i64 -> i64 signature.
#[allow(clippy::result_large_err)] // The unwind boundary preserves the compiler's diagnostic.
pub fn compile_and_run(module: &trust_ir::Module, opt: OptLevel, args: &[i64; 4]) -> JitOutcome {
    let externs: HashMap<String, *const u8> = HashMap::new();
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = opt;
    let compiler = Compiler::new(config).with_codegen_license(crate::fuzz_license());
    let buf_result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        compiler.compile_module_to_jit(module, &externs)
    }));
    let buf = match buf_result {
        Ok(Ok(result)) => result.buffer,
        Ok(Err(e)) => return JitOutcome::Unsupported(format!("compile_jit_err: {:?}", e)),
        Err(_) => return JitOutcome::Panic("compile_jit_panic".to_string()),
    };

    type Fn4 = extern "C" fn(i64, i64, i64, i64) -> i64;
    // Safety: the JIT's calling-convention contract is extern "C".
    let fptr_opt = unsafe { buf.get_fn_bound::<Fn4>(FUZZ_FN_NAME) };
    let fptr = match fptr_opt {
        Some(p) => p.into_inner(),
        None => return JitOutcome::Unsupported("symbol_not_found".to_string()),
    };

    let a = *args;
    let fptr_usize = fptr as usize;
    // Run the JIT'd call in a forked child so a hardware trap (SIGFPE on idiv
    // #DE for div-by-zero or INT_MIN/-1, SIGSEGV on a bad load, ...) kills only
    // the child instead of the campaign. `buf` stays mapped in the parent (and,
    // via copy-on-write, in the child) for the whole `run_sandboxed` call.
    let deadline = Duration::from_millis(PER_INVOKE_TIMEOUT_MS);
    // Safety: `fptr_usize` came from the typed JIT symbol lookup above; `buf`
    // (and thus the executable memory it points at) is kept live below until
    // after the child has been reaped, and the closure does only an extern "C"
    // call plus a scalar copy — async-signal-safe in the post-fork child.
    let result = unsafe {
        crate::sandbox::run_sandboxed(0, deadline, move |_payload: &mut [u8]| {
            let f: Fn4 = std::mem::transmute(fptr_usize);
            f(a[0], a[1], a[2], a[3])
        })
    };
    // Buffer must outlive the child; explicit drop documents that ordering.
    drop(buf);
    match result {
        crate::sandbox::SandboxResult::Value((v, _)) => JitOutcome::Value(v),
        crate::sandbox::SandboxResult::Trapped(sig) => JitOutcome::Trapped(sig),
        crate::sandbox::SandboxResult::Timeout => JitOutcome::Timeout,
        crate::sandbox::SandboxResult::SandboxError(e) => {
            JitOutcome::Unsupported(format!("sandbox: {}", e))
        }
    }
}

/// Compile the consumer-shaped `FUZZ_FN_NAME` and execute it with a writable
/// status buffer. Signature: `(i64, i64, i64, i64, *mut u8) -> i64`.
#[allow(clippy::result_large_err)] // The unwind boundary preserves the compiler's diagnostic.
pub fn compile_and_run_consumer_shape(
    module: &trust_ir::Module,
    opt: OptLevel,
    args: &[i64; 4],
) -> ConsumerJitOutcome {
    let externs: HashMap<String, *const u8> = HashMap::new();
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = opt;
    let compiler = Compiler::new(config).with_codegen_license(crate::fuzz_license());
    let buf_result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        compiler.compile_module_to_jit(module, &externs)
    }));
    let buf = match buf_result {
        Ok(Ok(result)) => result.buffer,
        Ok(Err(e)) => return ConsumerJitOutcome::Unsupported(format!("compile_jit_err: {:?}", e)),
        Err(_) => return ConsumerJitOutcome::Panic("compile_jit_panic".to_string()),
    };

    type ConsumerFn = extern "C" fn(i64, i64, i64, i64, *mut u8) -> i64;
    // Safety: the JIT's calling-convention contract is extern "C".
    let fptr_opt = unsafe { buf.get_fn_bound::<ConsumerFn>(FUZZ_FN_NAME) };
    let fptr = match fptr_opt {
        Some(p) => p.into_inner(),
        None => return ConsumerJitOutcome::Unsupported("symbol_not_found".to_string()),
    };

    let a = *args;
    let fptr_usize = fptr as usize;
    // Run in a forked child (see `compile_and_run`). The child supplies its own
    // status buffer (in its COW copy of the address space), invokes the JIT'd
    // function, then publishes the 24 status bytes as the sandbox payload so the
    // parent can read them back after reaping. A trap aborts only the child.
    let deadline = Duration::from_millis(PER_INVOKE_TIMEOUT_MS);
    // Safety: `fptr_usize` is the typed JIT symbol; `buf` is kept live below
    // until after the child is reaped. The closure runs post-fork and only does
    // a stack write, an extern "C" call, and scalar copies — async-signal-safe.
    let result = unsafe {
        crate::sandbox::run_sandboxed(
            CONSUMER_STATUS_BYTES,
            deadline,
            move |payload: &mut [u8]| {
                let f: ConsumerFn = std::mem::transmute(fptr_usize);
                // Seed the status buffer with the 0xAA sentinel, then let the JIT'd
                // function write through it; the scratch IS the published payload.
                for b in payload.iter_mut() {
                    *b = 0xAA;
                }
                f(a[0], a[1], a[2], a[3], payload.as_mut_ptr())
            },
        )
    };
    drop(buf);
    match result {
        crate::sandbox::SandboxResult::Value((ret, payload)) => {
            let mut bytes = [0u8; CONSUMER_STATUS_BYTES];
            let n = payload.len().min(CONSUMER_STATUS_BYTES);
            bytes[..n].copy_from_slice(&payload[..n]);
            ConsumerJitOutcome::Value(ConsumerSnapshot { ret, bytes })
        }
        crate::sandbox::SandboxResult::Trapped(sig) => ConsumerJitOutcome::Trapped(sig),
        crate::sandbox::SandboxResult::Timeout => ConsumerJitOutcome::Timeout,
        crate::sandbox::SandboxResult::SandboxError(e) => {
            ConsumerJitOutcome::Unsupported(format!("sandbox: {}", e))
        }
    }
}

/// Pure diff logic: classify three outputs into no defect, miscompile, crash,
/// or timeout.
pub fn classify_outputs(
    oracle: Option<Result<i64, String>>,
    o0: &JitOutcome,
    o2: &JitOutcome,
    padded_args: &[i64; 4],
) -> Option<(&'static str, String)> {
    if let JitOutcome::Panic(msg) = o0 {
        return Some(("crash", format!("O0 JIT panic: {}", msg)));
    }
    if let JitOutcome::Panic(msg) = o2 {
        return Some(("crash", format!("O2 JIT panic: {}", msg)));
    }
    if matches!(o0, JitOutcome::Timeout) {
        return Some(("timeout", "O0 JIT timed out".to_string()));
    }
    if matches!(o2, JitOutcome::Timeout) {
        return Some(("timeout", "O2 JIT timed out".to_string()));
    }

    let o0_val = if let JitOutcome::Value(v) = o0 {
        Some(*v)
    } else {
        None
    };
    let o2_val = if let JitOutcome::Value(v) = o2 {
        Some(*v)
    } else {
        None
    };
    let oracle_val = match oracle {
        Some(Ok(v)) => Some(v),
        _ => None,
    };

    // A hardware trap (idiv #DE, bad load, ...) means the JIT produced NO value.
    // It is a finding only relative to a side that DID have a defined value:
    //   - oracle has a value but the JIT trapped, or
    //   - one opt level returns a value while another traps.
    // Both-trapped (or trapped while the oracle also lacked a value) is NOT a
    // defect — the program's behavior is genuinely "trap" on those inputs (e.g.
    // an unguarded divide-by-zero the interpreter also rejected). This is the
    // ONLY place a trap is excused, and never when a concrete value disagrees.
    if let Some(a) = oracle_val {
        if let Some(d) = trap_vs_value(o0, "O0", "interp", a, padded_args) {
            return Some(d);
        }
        if let Some(d) = trap_vs_value(o2, "O2", "interp", a, padded_args) {
            return Some(d);
        }
    }
    // Cross-opt: a value on one level and a trap on the other is a real
    // divergence in the compiled program's observable behavior.
    if let (Some(a), JitOutcome::Trapped(sig)) = (o0_val, o2) {
        return Some((
            "miscompile",
            format!(
                "O0_jit={} O2_jit=TRAP(sig={}) args={:?}",
                a, sig, padded_args
            ),
        ));
    }
    if let (Some(b), JitOutcome::Trapped(sig)) = (o2_val, o0) {
        return Some((
            "miscompile",
            format!(
                "O0_jit=TRAP(sig={}) O2_jit={} args={:?}",
                sig, b, padded_args
            ),
        ));
    }

    if let (Some(a), Some(b)) = (oracle_val, o0_val)
        && a != b
    {
        return Some((
            "miscompile",
            format!("interp={} O0_jit={} args={:?}", a, b, padded_args),
        ));
    }
    if let (Some(a), Some(b)) = (oracle_val, o2_val)
        && a != b
    {
        return Some((
            "miscompile",
            format!("interp={} O2_jit={} args={:?}", a, b, padded_args),
        ));
    }
    if let (Some(a), Some(b)) = (o0_val, o2_val)
        && a != b
    {
        return Some((
            "miscompile",
            format!("O0_jit={} O2_jit={} args={:?}", a, b, padded_args),
        ));
    }
    None
}

/// If `outcome` is a hardware trap while `ref_val` is a defined value from
/// `ref_label`, report a miscompile (the JIT trapped where a value was
/// expected). Returns None for any non-trap outcome.
fn trap_vs_value(
    outcome: &JitOutcome,
    jit_label: &str,
    ref_label: &str,
    ref_val: i64,
    padded_args: &[i64; 4],
) -> Option<(&'static str, String)> {
    if let JitOutcome::Trapped(sig) = outcome {
        return Some((
            "miscompile",
            format!(
                "{ref_label}={} {jit_label}_jit=TRAP(sig={}) args={:?}",
                ref_val, sig, padded_args
            ),
        ));
    }
    None
}

/// O0/O2/O3 scalar JIT diff classifier.
pub fn classify_outputs_o0_o2_o3(
    oracle: Option<Result<i64, String>>,
    o0: &JitOutcome,
    o2: &JitOutcome,
    o3: &JitOutcome,
    padded_args: &[i64; 4],
) -> Option<(&'static str, String)> {
    if let Some(defect) = classify_outputs(oracle.clone(), o0, o2, padded_args) {
        return Some(defect);
    }
    if let JitOutcome::Panic(msg) = o3 {
        return Some(("crash", format!("O3 JIT panic: {}", msg)));
    }
    if matches!(o3, JitOutcome::Timeout) {
        return Some(("timeout", "O3 JIT timed out".to_string()));
    }

    let o3_val = if let JitOutcome::Value(v) = o3 {
        Some(*v)
    } else {
        None
    };
    let oracle_val = match oracle {
        Some(Ok(v)) => Some(v),
        _ => None,
    };
    // O3 trapped while the oracle had a defined value => finding (see
    // `classify_outputs`); both-trapped / oracle-no-value is excused.
    if let Some(a) = oracle_val
        && let Some(d) = trap_vs_value(o3, "O3", "interp", a, padded_args)
    {
        return Some(d);
    }
    if let (Some(a), Some(b)) = (oracle_val, o3_val)
        && a != b
    {
        return Some((
            "miscompile",
            format!("interp={} O3_jit={} args={:?}", a, b, padded_args),
        ));
    }
    for (name, outcome) in [("O0", o0), ("O2", o2)] {
        // A value at O0/O2 vs a trap at O3 (or vice versa) is a cross-opt
        // behavioral divergence in the compiled program.
        if let (JitOutcome::Value(a), JitOutcome::Trapped(sig)) = (outcome, o3) {
            return Some((
                "miscompile",
                format!(
                    "{name}_jit={} O3_jit=TRAP(sig={}) args={:?}",
                    a, sig, padded_args
                ),
            ));
        }
        if let (JitOutcome::Trapped(sig), Some(b)) = (outcome, o3_val) {
            return Some((
                "miscompile",
                format!(
                    "{name}_jit=TRAP(sig={}) O3_jit={} args={:?}",
                    sig, b, padded_args
                ),
            ));
        }
        if let (JitOutcome::Value(a), Some(b)) = (outcome, o3_val)
            && *a != b
        {
            return Some((
                "miscompile",
                format!("{name}_jit={} O3_jit={} args={:?}", a, b, padded_args),
            ));
        }
    }
    None
}

/// Scalar oracle for `gen_consumer_shape_module`.
pub fn run_consumer_shape_oracle(args: &[i64; 4]) -> ConsumerSnapshot {
    let mut bytes = [0xAAu8; CONSUMER_STATUS_BYTES];
    let (ret, status, deopt, value, detail) = if args[3] != 7 {
        (-3, 3u8, 3u8, args[3], 7)
    } else if args[2] > 4 {
        (-1, 1u8, 1u8, args[2], 4)
    } else {
        let value = args[0]
            .wrapping_mul(3)
            .wrapping_add(args[1])
            .wrapping_sub(args[2]);
        (value ^ args[2], 0u8, 0u8, value, args[2])
    };
    bytes[0] = status;
    bytes[1] = deopt;
    bytes[8..16].copy_from_slice(&value.to_ne_bytes());
    bytes[16..24].copy_from_slice(&detail.to_ne_bytes());
    ConsumerSnapshot { ret, bytes }
}

fn classify_consumer_one(
    name: &str,
    oracle: &ConsumerSnapshot,
    outcome: &ConsumerJitOutcome,
    args: &[i64; 4],
) -> Option<(&'static str, String)> {
    match outcome {
        ConsumerJitOutcome::Value(actual) => {
            if actual != oracle {
                Some((
                    "miscompile",
                    format!(
                        "consumer {name} expected={:?} actual={:?} args={:?}",
                        oracle, actual, args
                    ),
                ))
            } else {
                None
            }
        }
        ConsumerJitOutcome::Panic(msg) => {
            Some(("crash", format!("consumer {name} JIT panic: {msg}")))
        }
        ConsumerJitOutcome::Timeout => Some(("timeout", format!("consumer {name} JIT timed out"))),
        // The consumer oracle (`run_consumer_shape_oracle`) always produces a
        // defined snapshot — it never traps. So a JIT trap here is always a
        // divergence from a side that had a value: a real finding.
        ConsumerJitOutcome::Trapped(sig) => Some((
            "miscompile",
            format!(
                "consumer {name} expected={:?} actual=TRAP(sig={}) args={:?}",
                oracle, sig, args
            ),
        )),
        ConsumerJitOutcome::Unsupported(_) => None,
    }
}

/// What one row check actually executed, beside its verdict. A JIT level
/// that was refused (`Unsupported`: a compile error, a missing symbol or an
/// unavailable sandbox) compared nothing, so a campaign must count it rather
/// than let the row pass silently.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RowExecution {
    /// JIT levels (of O0, O2, O3) whose call ran to a value or a hardware trap.
    pub executed_levels: u8,
    /// JIT levels that were refused.
    pub refused_levels: u8,
    /// The first refusal's reason.
    pub refusal: Option<String>,
    /// Whether the reference model (the trust-ir interpreter, or the
    /// consumer shape's closed-form oracle) produced a value the JIT levels
    /// were compared against. Without one (an interpreter error such as a
    /// division by zero) the row only compares the levels with each other.
    pub oracle_compared: bool,
    /// The reference model's error when it produced no value.
    pub oracle_error: Option<String>,
}

impl RowExecution {
    fn record(&mut self, refusal: Option<&str>, executed: bool) {
        if executed {
            self.executed_levels += 1;
        }
        if let Some(reason) = refusal {
            self.refused_levels += 1;
            self.refusal.get_or_insert_with(|| reason.to_string());
        }
    }

    fn of_scalar(outcomes: [&JitOutcome; 3]) -> Self {
        let mut execution = Self::default();
        for outcome in outcomes {
            let refusal = match outcome {
                JitOutcome::Unsupported(reason) => Some(reason.as_str()),
                _ => None,
            };
            let executed = matches!(outcome, JitOutcome::Value(_) | JitOutcome::Trapped(_));
            execution.record(refusal, executed);
        }
        execution
    }

    fn of_consumer(outcomes: [&ConsumerJitOutcome; 3]) -> Self {
        let mut execution = Self::default();
        for outcome in outcomes {
            let refusal = match outcome {
                ConsumerJitOutcome::Unsupported(reason) => Some(reason.as_str()),
                _ => None,
            };
            let executed = matches!(
                outcome,
                ConsumerJitOutcome::Value(_) | ConsumerJitOutcome::Trapped(_)
            );
            execution.record(refusal, executed);
        }
        execution
    }
}

/// One full differential check for a consumer-shaped pointer-buffer module.
pub fn diff_consumer_shape_row(
    module: &trust_ir::Module,
    row: &[i64; 4],
) -> Option<(&'static str, String)> {
    diff_consumer_shape_row_executed(module, row).0
}

/// [`diff_consumer_shape_row`] with what the row executed.
pub fn diff_consumer_shape_row_executed(
    module: &trust_ir::Module,
    row: &[i64; 4],
) -> (Option<(&'static str, String)>, RowExecution) {
    let oracle = run_consumer_shape_oracle(row);
    let o0 = compile_and_run_consumer_shape(module, OptLevel::O0, row);
    let o2 = compile_and_run_consumer_shape(module, OptLevel::O2, row);
    let o3 = compile_and_run_consumer_shape(module, OptLevel::O3, row);
    let mut execution = RowExecution::of_consumer([&o0, &o2, &o3]);
    // The consumer oracle is closed-form and always defines a snapshot.
    execution.oracle_compared = true;
    (consumer_verdict(row, &oracle, &o0, &o2, &o3), execution)
}

fn consumer_verdict(
    row: &[i64; 4],
    oracle: &ConsumerSnapshot,
    o0: &ConsumerJitOutcome,
    o2: &ConsumerJitOutcome,
    o3: &ConsumerJitOutcome,
) -> Option<(&'static str, String)> {
    for (name, outcome) in [("O0", o0), ("O2", o2), ("O3", o3)] {
        if let Some(defect) = classify_consumer_one(name, oracle, outcome, row) {
            return Some(defect);
        }
    }

    let values = [("O0", o0), ("O2", o2), ("O3", o3)];
    for i in 0..values.len() {
        for j in (i + 1)..values.len() {
            if let (ConsumerJitOutcome::Value(a), ConsumerJitOutcome::Value(b)) =
                (values[i].1, values[j].1)
                && a != b
            {
                return Some((
                    "miscompile",
                    format!(
                        "consumer {}={:?} {}={:?} args={:?}",
                        values[i].0, a, values[j].0, b, row
                    ),
                ));
            }
        }
    }
    None
}

/// One full differential check for a single `(module, args)` row.
pub fn diff_one_row(module: &trust_ir::Module, row: &[i64]) -> Option<(&'static str, String)> {
    diff_one_row_executed(module, row, false).0
}

/// The negative control of a campaign lane: [`diff_one_row`] with the O2 JIT
/// value perturbed by one after it executes, so the classifier must report a
/// miscompile whenever O2 returns a value. A row where O2 returns no value
/// (a trap, a refusal) plants nothing and is checked as usual.
pub fn diff_one_row_planted_miscompile(
    module: &trust_ir::Module,
    row: &[i64],
) -> Option<(&'static str, String)> {
    diff_one_row_executed(module, row, true).0
}

/// [`diff_one_row`] (or, with `plant`, [`diff_one_row_planted_miscompile`])
/// with what the row executed.
pub fn diff_one_row_executed(
    module: &trust_ir::Module,
    row: &[i64],
    plant: bool,
) -> (Option<(&'static str, String)>, RowExecution) {
    diff_row_against(module, row, plant, run_oracle_one(module, row))
}

/// Run trust-ir's reference interpreter (`trust_ir::interpret`) on
/// [`FUZZ_FN_NAME`]. Unlike [`run_oracle_one`], whose integer casts are
/// width-free, it models every integer at its width, so it is the oracle for
/// programs with narrow integers ([`crate::control_gen`]).
pub fn run_reference_oracle_one(module: &trust_ir::Module, args: &[i64]) -> Result<i64, String> {
    use trust_ir::interpret::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter};
    let function = module
        .functions
        .iter()
        .find(|function| function.name == FUZZ_FN_NAME)
        .ok_or_else(|| "reference_interp: no fuzz function".to_string())?;
    let values = args
        .iter()
        .map(|&x| InterpretValue::int(trust_ir::Ty::I64, i128::from(x)))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("reference_interp_args: {error}"))?;
    let outcome = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        Interpreter::with_module(module)
            .with_options(InterpretOptions {
                fuel: 200_000,
                max_call_depth: 32,
                panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
            })
            .execute_function(function, values)
    }))
    .map_err(|_| "reference_interp_panic".to_string())?
    .map_err(|error| format!("reference_interp_err: {error}"))?;
    match outcome.returns.first().map(|value| &value.kind) {
        Some(InterpretValueKind::Int(int)) => Ok(int.as_signed() as i64),
        Some(InterpretValueKind::Bool(b)) => Ok(i64::from(*b)),
        _ => Err("reference_interp_unsupported_ret".to_string()),
    }
}

/// [`diff_one_row_executed`] for a [`crate::control_gen`] module, judged by
/// [`run_reference_oracle_one`].
pub fn diff_control_row_executed(
    module: &trust_ir::Module,
    row: &[i64],
) -> (Option<(&'static str, String)>, RowExecution) {
    diff_row_against(module, row, false, run_reference_oracle_one(module, row))
}

fn diff_row_against(
    module: &trust_ir::Module,
    row: &[i64],
    plant: bool,
    oracle: Result<i64, String>,
) -> (Option<(&'static str, String)>, RowExecution) {
    let mut padded = [0i64; 4];
    for (i, v) in row.iter().take(4).enumerate() {
        padded[i] = *v;
    }

    let o0 = compile_and_run(module, OptLevel::O0, &padded);
    let o2 = match compile_and_run(module, OptLevel::O2, &padded) {
        JitOutcome::Value(value) if plant => JitOutcome::Value(value.wrapping_add(1)),
        other => other,
    };
    let o3 = compile_and_run(module, OptLevel::O3, &padded);
    let mut execution = RowExecution::of_scalar([&o0, &o2, &o3]);
    match &oracle {
        Ok(_) => execution.oracle_compared = true,
        Err(error) => execution.oracle_error = Some(error.clone()),
    }

    (
        classify_outputs_o0_o2_o3(Some(oracle), &o0, &o2, &o3, &padded),
        execution,
    )
}

#[cfg(test)]
mod tests {
    use super::bool_sext_i64_oracle_result;

    #[test]
    fn bool_sext_oracle_result_is_domain_checked() {
        assert_eq!(bool_sext_i64_oracle_result(0), Some(0));
        assert_eq!(bool_sext_i64_oracle_result(-1), Some(-1));
        // The retired widthless model's `true`.
        assert_eq!(bool_sext_i64_oracle_result(1), None);
        assert_eq!(bool_sext_i64_oracle_result(2), None);
        assert_eq!(bool_sext_i64_oracle_result(i64::MIN), None);
    }
}
