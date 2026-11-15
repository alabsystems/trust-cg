// trust-cg-fuzz/src/bin/trust_ir_jit_diff.rs - JIT-based differential harness for trust_ir.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Part of #436 (WS3 differential fuzzing).

use std::process;

const DEFAULT_OUT_DIR: &str = "evals/results/fuzz/unknown";
const USAGE: &str = "Usage: trust-ir-jit-diff [--duration <secs>] [--out <dir>] [--seed-start <seed>] [--runs <n>] [--plant-miscompile-seed <seed>]\n\nOptions:\n  -h, --help             Print this help and exit\n      --duration <secs>  Fuzz campaign duration in seconds (default: 300)\n      --out <dir>        Output directory (default: evals/results/fuzz/unknown)\n      --seed-start <n>   First generated seed (default: 1)\n      --runs <n>         Stop after n seeds: the fixed range seed-start..seed-start+n\n                         (the duration still bounds the run; runs < n means it expired)\n      --plant-miscompile-seed <n>\n                         Negative control: perturb seed n's O2 JIT value after it runs,\n                         so that seed must be reported as a miscompile\n";

/// Prefix of a planted negative-control repro summary; scripts/run_linux_fuzz_lane.py
/// requires it (JIT_CONTROL_TAG) to tell the planted defect from a genuine one.
#[cfg_attr(
    not(all(unix, any(target_arch = "aarch64", target_arch = "x86_64"))),
    allow(dead_code)
)]
const PLANTED_MISCOMPILE_TAG: &str = "planted-negative-control";

struct Options {
    duration_secs: u64,
    out_dir: String,
    seed_start: u64,
    runs: Option<u64>,
    plant_miscompile_seed: Option<u64>,
}

enum ParseResult {
    Help,
    Run(Options),
}

fn parse_value<T: std::str::FromStr>(
    args: &[String],
    index: &mut usize,
    flag: &str,
) -> Result<T, String>
where
    T::Err: std::fmt::Display,
{
    *index += 1;
    let Some(value) = args.get(*index) else {
        return Err(format!("missing value for {flag}"));
    };
    if value.starts_with('-') {
        return Err(format!("missing value for {flag}"));
    }
    value
        .parse()
        .map_err(|err| format!("bad value for {flag}: {value}: {err}"))
}

fn parse_args(args: &[String]) -> Result<ParseResult, String> {
    let mut options = Options {
        duration_secs: 300,
        out_dir: DEFAULT_OUT_DIR.to_string(),
        seed_start: 1,
        runs: None,
        plant_miscompile_seed: None,
    };

    let mut index = 1;
    while index < args.len() {
        match args[index].as_str() {
            "-h" | "--help" => return Ok(ParseResult::Help),
            "--duration" => {
                options.duration_secs = parse_value(args, &mut index, "--duration")?;
            }
            "--out" => {
                options.out_dir = parse_value(args, &mut index, "--out")?;
            }
            "--seed-start" => {
                options.seed_start = parse_value(args, &mut index, "--seed-start")?;
            }
            "--runs" => {
                options.runs = Some(parse_value(args, &mut index, "--runs")?);
            }
            "--plant-miscompile-seed" => {
                options.plant_miscompile_seed =
                    Some(parse_value(args, &mut index, "--plant-miscompile-seed")?);
            }
            flag => return Err(format!("unknown argument: {flag}")),
        }
        index += 1;
    }

    Ok(ParseResult::Run(options))
}

fn parse_or_exit(args: &[String]) -> Option<Options> {
    match parse_args(args) {
        Ok(ParseResult::Help) => {
            print!("{USAGE}");
            None
        }
        Ok(ParseResult::Run(options)) => Some(options),
        Err(err) => {
            eprintln!("{err}\n\n{USAGE}");
            process::exit(2);
        }
    }
}

#[cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]
mod imp {
    use std::env;
    use std::fs;
    use std::panic;
    use std::path::{Path, PathBuf};
    use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

    use trust_cg_fuzz::control_gen::gen_control_module;
    use trust_cg_fuzz::jit_diff::{
        RowExecution, diff_consumer_shape_row_executed, diff_control_row_executed,
        diff_one_row_executed,
    };
    use trust_cg_fuzz::runlog::{Repro, RunLog, campaign_deadline};
    use trust_cg_fuzz::trust_ir_gen::{
        GenConfig, gen_consumer_shape_module, gen_module, sample_inputs,
    };

    const MAX_REPROS_RECORDED: usize = 32;
    /// Sample input rows each seed's scalar module is checked on.
    const SCALAR_ROWS_PER_SEED: u32 = 6;
    const MAX_INCOMPLETE_SEED_SAMPLES: usize = 8;

    /// A seed that checked fewer than every scalar row is incomplete.
    fn count_seed(log: &mut RunLog, seed: u64, scalar_rows: usize) {
        if scalar_rows < SCALAR_ROWS_PER_SEED as usize {
            *log.seeds_incomplete.get_or_insert(0) += 1;
            if log.incomplete_seed_samples.len() < MAX_INCOMPLETE_SEED_SAMPLES {
                log.incomplete_seed_samples.push(seed);
            }
        }
    }
    const MAX_REFUSAL_SAMPLES: usize = 8;
    const REFUSAL_SAMPLE_CHARS: usize = 240;

    /// Keep the first few distinct samples, truncated.
    fn push_sample(samples: &mut Vec<String>, reason: &str) {
        let sample: String = reason.chars().take(REFUSAL_SAMPLE_CHARS).collect();
        if samples.len() < MAX_REFUSAL_SAMPLES && !samples.contains(&sample) {
            samples.push(sample);
        }
    }

    /// Count what one row executed, and against which reference.
    fn count_row(log: &mut RunLog, execution: RowExecution) {
        *log.rows_checked.get_or_insert(0) += 1;
        if execution.refused_levels > 0 {
            *log.rows_refused.get_or_insert(0) += 1;
        } else if execution.executed_levels == 3 {
            *log.rows_executed.get_or_insert(0) += 1;
        }
        if let Some(reason) = &execution.refusal {
            push_sample(&mut log.refusal_samples, reason);
        }
        if execution.oracle_compared {
            *log.rows_oracle_compared.get_or_insert(0) += 1;
        } else {
            *log.rows_cross_level_only.get_or_insert(0) += 1;
            if let Some(error) = &execution.oracle_error {
                push_sample(&mut log.oracle_error_samples, error);
            }
        }
    }

    fn iso_now() -> String {
        let secs = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        let (year, month, day, hh, mm, ss) = decompose_unix(secs);
        format!(
            "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z",
            year, month, day, hh, mm, ss
        )
    }

    fn decompose_unix(secs: u64) -> (u32, u32, u32, u32, u32, u32) {
        let days = (secs / 86_400) as i64;
        let ss = (secs % 60) as u32;
        let mm = ((secs / 60) % 60) as u32;
        let hh = ((secs / 3600) % 24) as u32;

        let z = days + 719_468;
        let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
        let doe = (z - era * 146_097) as u32;
        let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
        let y = (yoe as i64) + era * 400;
        let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
        let mp = (5 * doy + 2) / 153;
        let d = doy - (153 * mp + 2) / 5 + 1;
        let m = if mp < 10 { mp + 3 } else { mp - 9 };
        let y = y + if m <= 2 { 1 } else { 0 };
        (y as u32, m, d, hh, mm, ss)
    }

    fn save_repro(out_dir: &Path, seed: u64, module: &trust_ir::Module) -> Option<String> {
        let path = out_dir.join(format!("repro-trust-ir-jit-diff-seed-{}.json", seed));
        let json = match serde_json::to_string_pretty(module) {
            Ok(s) => s,
            Err(_) => return None,
        };
        fs::write(&path, json).ok()?;
        Some(path.to_string_lossy().into_owned())
    }

    pub(crate) fn run() -> Result<(), String> {
        let args: Vec<String> = env::args().collect();
        let Some(options) = crate::parse_or_exit(&args) else {
            return Ok(());
        };

        let out_path = PathBuf::from(&options.out_dir);
        let deadline = campaign_deadline(options.duration_secs)?;
        fs::create_dir_all(&out_path).map_err(|error| {
            format!(
                "cannot create output directory '{}': {error}",
                out_path.display()
            )
        })?;

        let started_at = iso_now();

        let mut log = RunLog {
            driver: "trust-ir-jit-diff".to_string(),
            status: "ok".to_string(),
            reason: None,
            duration_secs: options.duration_secs,
            runs: 0,
            timeouts: 0,
            crashes: 0,
            miscompiles: 0,
            repros: Vec::new(),
            started_at: started_at.clone(),
            finished_at: String::new(),
            seed_start: Some(options.seed_start),
            requested_runs: options.runs,
            planted_miscompile_seed: options.plant_miscompile_seed,
            rows_checked: Some(0),
            rows_executed: Some(0),
            rows_refused: Some(0),
            refusal_samples: Vec::new(),
            rows_oracle_compared: Some(0),
            rows_cross_level_only: Some(0),
            oracle_error_samples: Vec::new(),
            scalar_rows_per_seed: Some(u64::from(SCALAR_ROWS_PER_SEED)),
            seeds_incomplete: Some(0),
            incomplete_seed_samples: Vec::new(),
        };

        let cfg = GenConfig::default();
        let mut seed = options.seed_start;
        let mut last_progress = Instant::now();

        while Instant::now() < deadline && options.runs.is_none_or(|runs| log.runs < runs) {
            log.runs += 1;

            let module =
                match panic::catch_unwind(panic::AssertUnwindSafe(|| gen_module(seed, &cfg))) {
                    Ok(Ok(m)) => m,
                    failed => {
                        log.crashes += 1;
                        if log.repros.len() < MAX_REPROS_RECORDED {
                            log.repros.push(Repro {
                                seed,
                                minimized_input_path: None,
                                summary: match failed {
                                    Ok(Err(refusal)) => {
                                        format!("gen_module's builder refused: {refusal}")
                                    }
                                    _ => "gen_module panicked".to_string(),
                                },
                            });
                        }
                        count_seed(&mut log, seed, 0);
                        seed = seed.wrapping_add(1);
                        continue;
                    }
                };

            let inputs = sample_inputs(seed, cfg.num_params, SCALAR_ROWS_PER_SEED);
            let planted = options.plant_miscompile_seed == Some(seed);
            let mut defect: Option<(&'static str, String)> = None;
            let mut scalar_rows = 0;
            for row in &inputs {
                let (found, execution) = diff_one_row_executed(&module, row, planted);
                count_row(&mut log, execution);
                scalar_rows += 1;
                if let Some(d) = found {
                    defect = Some(d);
                    break;
                }
            }
            count_seed(&mut log, seed, scalar_rows);

            if let Some((category, summary)) = defect {
                let summary = if planted {
                    format!("{} {summary}", crate::PLANTED_MISCOMPILE_TAG)
                } else {
                    summary
                };
                match category {
                    "miscompile" => log.miscompiles += 1,
                    "crash" => log.crashes += 1,
                    "timeout" => log.timeouts += 1,
                    _ => {}
                }
                if log.repros.len() < MAX_REPROS_RECORDED {
                    let saved = save_repro(&out_path, seed, &module);
                    log.repros.push(Repro {
                        seed,
                        minimized_input_path: saved,
                        summary: format!("{} seed={} {}", category, seed, summary),
                    });
                }
            }

            if seed % 8 == 0 {
                let module = match panic::catch_unwind(panic::AssertUnwindSafe(|| {
                    gen_consumer_shape_module(seed)
                })) {
                    Ok(Ok(m)) => m,
                    Ok(Err(_)) | Err(_) => {
                        log.crashes += 1;
                        if log.repros.len() < MAX_REPROS_RECORDED {
                            log.repros.push(Repro {
                                seed,
                                minimized_input_path: None,
                                summary:
                                    "gen_consumer_shape_module panicked or its builder refused"
                                        .to_string(),
                            });
                        }
                        seed = seed.wrapping_add(1);
                        continue;
                    }
                };

                let consumer_rows: [[i64; 4]; 4] =
                    [[3, 4, 0, 7], [-5, 9, 4, 7], [11, -2, 5, 7], [1, 2, 3, 6]];
                let mut defect: Option<(&'static str, String)> = None;
                for row in &consumer_rows {
                    let (found, execution) = diff_consumer_shape_row_executed(&module, row);
                    count_row(&mut log, execution);
                    if let Some(d) = found {
                        defect = Some(d);
                        break;
                    }
                }

                if let Some((category, summary)) = defect {
                    match category {
                        "miscompile" => log.miscompiles += 1,
                        "crash" => log.crashes += 1,
                        "timeout" => log.timeouts += 1,
                        _ => {}
                    }
                    if log.repros.len() < MAX_REPROS_RECORDED {
                        let saved = save_repro(&out_path, seed, &module);
                        log.repros.push(Repro {
                            seed,
                            minimized_input_path: saved,
                            summary: format!(
                                "consumer-shape {} seed={} {}",
                                category, seed, summary
                            ),
                        });
                    }
                }
            }

            // The multi-block control shapes (diamonds, counted loops, calls,
            // compares reused by selects and branches) for every seed.
            match panic::catch_unwind(panic::AssertUnwindSafe(|| gen_control_module(seed))) {
                Ok(Ok(module)) => {
                    let mut defect: Option<(&'static str, String)> = None;
                    for row in &inputs {
                        let (found, execution) = diff_control_row_executed(&module, row);
                        count_row(&mut log, execution);
                        if let Some(d) = found {
                            defect = Some(d);
                            break;
                        }
                    }
                    if let Some((category, summary)) = defect {
                        match category {
                            "miscompile" => log.miscompiles += 1,
                            "crash" => log.crashes += 1,
                            "timeout" => log.timeouts += 1,
                            _ => {}
                        }
                        if log.repros.len() < MAX_REPROS_RECORDED {
                            let saved = save_repro(&out_path, seed, &module);
                            log.repros.push(Repro {
                                seed,
                                minimized_input_path: saved,
                                summary: format!(
                                    "control-shape {} seed={} {}",
                                    category, seed, summary
                                ),
                            });
                        }
                    }
                }
                Ok(Err(_)) | Err(_) => {
                    log.crashes += 1;
                    if log.repros.len() < MAX_REPROS_RECORDED {
                        log.repros.push(Repro {
                            seed,
                            minimized_input_path: None,
                            summary: "gen_control_module panicked or its builder refused"
                                .to_string(),
                        });
                    }
                }
            }

            if last_progress.elapsed() >= Duration::from_secs(15) {
                eprintln!(
                    "[trust-ir-jit-diff] runs={} miscompiles={} crashes={} timeouts={}",
                    log.runs, log.miscompiles, log.crashes, log.timeouts
                );
                last_progress = Instant::now();
            }

            seed = seed.wrapping_add(1);
        }

        log.finished_at = iso_now();

        let json_path = out_path.join("trust-ir-jit-diff.json");
        log.write_to(&json_path)
            .map_err(|error| error.to_string())?;
        eprintln!(
            "[trust-ir-jit-diff] wrote {} runs={} miscompiles={} crashes={} timeouts={} rows={} executed={} refused={} oracle_compared={} cross_level_only={} incomplete_seeds={}",
            json_path.display(),
            log.runs,
            log.miscompiles,
            log.crashes,
            log.timeouts,
            log.rows_checked.unwrap_or(0),
            log.rows_executed.unwrap_or(0),
            log.rows_refused.unwrap_or(0),
            log.rows_oracle_compared.unwrap_or(0),
            log.rows_cross_level_only.unwrap_or(0),
            log.seeds_incomplete.unwrap_or(0),
        );
        Ok(())
    }
}

#[cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]
fn main() -> Result<(), String> {
    imp::run()
}

#[cfg(not(all(unix, any(target_arch = "aarch64", target_arch = "x86_64"))))]
fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    let Some(options) = parse_or_exit(&args) else {
        return Ok(());
    };
    let out_path = std::path::PathBuf::from(&options.out_dir);
    trust_cg_fuzz::runlog::campaign_deadline(options.duration_secs)?;
    std::fs::create_dir_all(&out_path).map_err(|error| {
        format!(
            "cannot create output directory '{}': {error}",
            out_path.display()
        )
    })?;
    let log = trust_cg_fuzz::runlog::RunLog {
        driver: "trust-ir-jit-diff".to_string(),
        status: "unavailable".to_string(),
        reason: Some("JIT only supported on aarch64/x86_64 hosts".to_string()),
        duration_secs: options.duration_secs,
        runs: 0,
        timeouts: 0,
        crashes: 0,
        miscompiles: 0,
        repros: Vec::new(),
        started_at: String::new(),
        finished_at: String::new(),
        seed_start: Some(options.seed_start),
        requested_runs: options.runs,
        planted_miscompile_seed: options.plant_miscompile_seed,
        rows_checked: None,
        rows_executed: None,
        rows_refused: None,
        refusal_samples: Vec::new(),
        rows_oracle_compared: None,
        rows_cross_level_only: None,
        oracle_error_samples: Vec::new(),
        scalar_rows_per_seed: None,
        seeds_incomplete: None,
        incomplete_seed_samples: Vec::new(),
    };
    let json_path = out_path.join("trust-ir-jit-diff.json");
    log.write_to(&json_path).map_err(|error| error.to_string())
}
