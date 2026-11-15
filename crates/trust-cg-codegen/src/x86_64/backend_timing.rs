// trust-cg-codegen/src/x86_64/backend_timing.rs - per-stage, per-function wall
// time inside the x86-64 backend's `x86_compile_module` phase.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHY THIS EXISTS. `CompilerTraceLevel::Full` reports `x86_compile_module` as a
// SINGLE row, and on the Clean-kernel corpus that row is 99.9% of the compile
// (measured 2026-09-27, `clean_lazy_delta.gate.trust.tir` at O1: 258.97s of
// 259.18s). `TCG_TIME_X86PM` splits the machine-pass phase, which is 0.1s of
// the same compile, so it cannot attribute this one. This splits the module
// phase into its per-function stages instead.
//
// INERT BY DEFAULT and PURELY OBSERVATIONAL, exactly like
// `trust_cg_opt::x86_pass_timing_report`: every entry point is a no-op unless
// `TCG_TIME_X86FN` is set, the timers never read or write the IR, and no stage
// verdict, allocation, byte or refusal depends on them. It is a diagnostic, not
// evidence: a stage that fails closed still fails closed, and the report is
// written to stderr by the caller that asks for it.

use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::time::Duration;
use std::time::Instant;

/// True when `TCG_TIME_X86FN` requests per-stage backend attribution.
/// Evaluated once and cached, so the timers cost one atomic load when off.
pub(crate) fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TCG_TIME_X86FN").is_some())
}

/// `stage -> (total nanos, call count)`.
static STAGE_TIMES: Mutex<BTreeMap<&'static str, (u128, u64)>> = Mutex::new(BTreeMap::new());

/// `(function, stage) -> total nanos`, kept only for the per-function ranking.
static FUNC_TIMES: Mutex<BTreeMap<(String, &'static str), u128>> = Mutex::new(BTreeMap::new());

/// Time `body`, recording its duration under `stage` for `function`.
///
/// When disabled this is `body()` and nothing else.
pub(crate) fn timed<T>(stage: &'static str, function: &str, body: impl FnOnce() -> T) -> T {
    if !enabled() {
        return body();
    }
    let start = Instant::now();
    let out = body();
    record(stage, function, start.elapsed());
    out
}

fn record(stage: &'static str, function: &str, elapsed: Duration) {
    let nanos = elapsed.as_nanos();
    if let Ok(mut table) = STAGE_TIMES.lock() {
        let entry = table.entry(stage).or_insert((0, 0));
        entry.0 += nanos;
        entry.1 += 1;
    }
    if let Ok(mut table) = FUNC_TIMES.lock() {
        *table.entry((function.to_string(), stage)).or_insert(0) += nanos;
    }
}

/// Ranked per-stage report plus the slowest functions, or `None` unless
/// `TCG_TIME_X86FN` is set.
///
/// `TCG_TIME_X86FN_TOP` (default 15) caps the per-function rows.
pub fn report() -> Option<String> {
    if !enabled() {
        return None;
    }
    let stages = STAGE_TIMES.lock().ok()?;
    let mut rows: Vec<(&'static str, u128, u64)> =
        stages.iter().map(|(k, (ns, n))| (*k, *ns, *n)).collect();
    rows.sort_by_key(|row| std::cmp::Reverse(row.1));
    // `fn_total` brackets every other stage, so it is the denominator rather
    // than a summand; summing all rows would double-count it.
    let total: u128 = rows
        .iter()
        .find(|r| r.0 == "fn_total")
        .map(|r| r.1)
        .unwrap_or_else(|| rows.iter().map(|r| r.1).sum());
    let denom = total.max(1) as f64;
    let mut out = format!(
        "TCG_TIME_X86FN fn_total={:.1}ms over {} stages\n",
        total as f64 / 1e6,
        rows.len()
    );
    for (name, ns, runs) in rows {
        out.push_str(&format!(
            "  {name:<38} {:>10.1}ms {:>5.1}%  runs={runs}\n",
            ns as f64 / 1e6,
            100.0 * ns as f64 / denom,
        ));
    }
    let top: usize = std::env::var("TCG_TIME_X86FN_TOP")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(15);
    let funcs = FUNC_TIMES.lock().ok()?;
    let mut per_fn: Vec<(&String, &'static str, u128)> = funcs
        .iter()
        .filter(|((_, stage), _)| *stage == "fn_total")
        .map(|((f, stage), ns)| (f, *stage, *ns))
        .collect();
    per_fn.sort_by_key(|row| std::cmp::Reverse(row.2));
    out.push_str(&format!("  --- slowest {top} functions (fn_total) ---\n"));
    for (name, _, ns) in per_fn.into_iter().take(top) {
        out.push_str(&format!("  {:>10.1}ms  {name}\n", ns as f64 / 1e6));
    }
    Some(out)
}
