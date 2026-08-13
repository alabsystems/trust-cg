// trust-cg-fuzz/src/bin/trust_ir_jit_diff.rs - JIT-based differential harness for trust_ir.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Part of #436 (WS3 differential fuzzing).

use std::process;

const DEFAULT_OUT_DIR: &str = "evals/results/fuzz/unknown";
const USAGE: &str = "Usage: trust-ir-jit-diff [--duration <secs>] [--out <dir>] [--seed-start <seed>]\n\nOptions:\n  -h, --help             Print this help and exit\n      --duration <secs>  Fuzz campaign duration in seconds (default: 300)\n      --out <dir>        Output directory (default: evals/results/fuzz/unknown)\n      --seed-start <n>   First generated seed (default: 1)\n";

struct Options {
    duration_secs: u64,
    out_dir: String,
    seed_start: u64,
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

    use trust_cg_fuzz::jit_diff::{diff_consumer_shape_row, diff_one_row};
    use trust_cg_fuzz::runlog::{Repro, RunLog};
    use trust_cg_fuzz::trust_ir_gen::{
        GenConfig, gen_consumer_shape_module, gen_module, sample_inputs,
    };

    const MAX_REPROS_RECORDED: usize = 32;

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

    pub(crate) fn run() {
        let args: Vec<String> = env::args().collect();
        let Some(options) = crate::parse_or_exit(&args) else {
            return;
        };

        let out_path = PathBuf::from(&options.out_dir);
        fs::create_dir_all(&out_path).expect("create out_dir");

        let started_at = iso_now();
        let deadline = Instant::now() + Duration::from_secs(options.duration_secs);

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
        };

        let cfg = GenConfig::default();
        let mut seed = options.seed_start;
        let mut last_progress = Instant::now();

        while Instant::now() < deadline {
            log.runs += 1;

            let module =
                match panic::catch_unwind(panic::AssertUnwindSafe(|| gen_module(seed, &cfg))) {
                    Ok(m) => m,
                    Err(_) => {
                        log.crashes += 1;
                        if log.repros.len() < MAX_REPROS_RECORDED {
                            log.repros.push(Repro {
                                seed,
                                minimized_input_path: None,
                                summary: "gen_module panicked".to_string(),
                            });
                        }
                        seed = seed.wrapping_add(1);
                        continue;
                    }
                };

            let inputs = sample_inputs(seed, cfg.num_params, 6);
            let mut defect: Option<(&'static str, String)> = None;
            for row in &inputs {
                if let Some(d) = diff_one_row(&module, row) {
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
                        summary: format!("{} seed={} {}", category, seed, summary),
                    });
                }
            }

            if seed % 8 == 0 {
                let module = match panic::catch_unwind(panic::AssertUnwindSafe(|| {
                    gen_consumer_shape_module(seed)
                })) {
                    Ok(m) => m,
                    Err(_) => {
                        log.crashes += 1;
                        if log.repros.len() < MAX_REPROS_RECORDED {
                            log.repros.push(Repro {
                                seed,
                                minimized_input_path: None,
                                summary: "gen_consumer_shape_module panicked".to_string(),
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
                    if let Some(d) = diff_consumer_shape_row(&module, row) {
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
        let json = serde_json::to_string_pretty(&log).expect("serialize RunLog");
        fs::write(&json_path, json).expect("write trust-ir-jit-diff.json");
        eprintln!(
            "[trust-ir-jit-diff] wrote {} runs={} miscompiles={} crashes={} timeouts={}",
            json_path.display(),
            log.runs,
            log.miscompiles,
            log.crashes,
            log.timeouts,
        );
    }
}

#[cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]
fn main() {
    imp::run();
}

#[cfg(not(all(unix, any(target_arch = "aarch64", target_arch = "x86_64"))))]
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let Some(options) = parse_or_exit(&args) else {
        return;
    };
    let out_path = std::path::PathBuf::from(&options.out_dir);
    std::fs::create_dir_all(&out_path).expect("create out_dir");
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
    };
    let json_path = out_path.join("trust-ir-jit-diff.json");
    let json = serde_json::to_string_pretty(&log).expect("serialize RunLog");
    std::fs::write(&json_path, json).expect("write trust-ir-jit-diff.json");
}
