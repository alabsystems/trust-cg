//! Real LLVM-created map images reach the dyn drop-origin guard directly.
//! The LLVM provider and callback oracle retain ownership/layout authority;
//! only the executable consumer varies backend. CG must refuse the unsupported
//! real-map image at its owning or borrowed unsize, not at synthetic map storage.
use super::{TARGET, backend_arg, toolchain_support};
use std::io::Write;
use std::path::Path;
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

const PROVIDER: &str = include_str!("real_map_dyn_origin/provider.rs");
const CALLEE: &str = include_str!("real_map_dyn_origin/callee.rs");
const ORACLE: &str = include_str!("real_map_dyn_origin/oracle.rs");
const REFUSAL: &str = "[TCG-HEAP-IMAGE-VTABLE]";

fn run(command: &mut Command, log: &Path, limit: Duration) -> ExitStatus {
    let mut output = std::fs::File::create(log).expect("create real-map origin log");
    writeln!(output, "{command:?}").expect("record real-map command");
    command
        .stdout(Stdio::from(output.try_clone().expect("clone real-map log")))
        .stderr(Stdio::from(output.try_clone().expect("clone real-map log")));
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    let mut child = command.spawn().expect("spawn real-map origin command");
    let start = Instant::now();
    loop {
        match child.try_wait().expect("poll real-map origin command") {
            Some(status) => {
                writeln!(output, "status={status:?}").expect("record real-map status");
                return status;
            }
            None if start.elapsed() >= limit => {
                #[cfg(unix)]
                {
                    unsafe extern "C" {
                        fn kill(pid: i32, sig: i32) -> i32;
                    }
                    let pid = i32::try_from(child.id()).expect("real-map child pid fits i32");
                    unsafe {
                        kill(-pid, 9);
                    }
                }
                let _ = child.kill();
                let _ = child.wait();
                panic!("real-map origin timeout after {limit:?}; {}", log.display());
            }
            None => std::thread::sleep(Duration::from_millis(5)),
        }
    }
}

fn command(
    dir: &Path,
    name: &str,
    source: &Path,
    output: &Path,
    backend: Option<(&Path, &str)>,
    opt: &str,
    externs: &[(&str, &Path)],
) -> Command {
    let mut cmd = toolchain_support::rustc_command_with_edition("2021");
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg(format!("--crate-name={name}"))
    .arg(format!("-Copt-level={opt}"))
    .arg(format!("-Ldependency={}", dir.display()));
    if output.extension().is_some_and(|ext| ext == "rlib") {
        cmd.arg("--crate-type=rlib");
    }
    if let Some((backend, knobs)) = backend {
        cmd.arg(backend_arg(backend)).arg(knobs);
    }
    for (name, path) in externs {
        cmd.arg("--extern")
            .arg(format!("{name}={}", path.display()));
    }
    for (key, _) in std::env::vars_os() {
        let name = key.to_string_lossy();
        if name.starts_with("TCG_") || name.starts_with("AY_") || name.starts_with("TRUST_IR_CG_") {
            cmd.env_remove(key);
        }
    }
    cmd.env_remove("CARGO_MAKEFLAGS")
        .current_dir(dir)
        .arg(source)
        .arg("-o")
        .arg(output);
    cmd
}

/// Keep each O0–O3 expected-refusal cell paired with a real LLVM native oracle.
/// Returns the number of exact named CG refusals, never accepting a native CG
/// binary or an earlier generic compile refusal as origin-boundary evidence.
pub(super) fn qualify(
    dir: &Path,
    backend: &Path,
    owned: bool,
    opts: &[&str],
    knobs: &str,
) -> usize {
    let kind = if owned { "owned" } else { "borrowed" };
    let root = if owned {
        "consume_owned"
    } else {
        "consume_borrowed"
    };
    let cfg = if owned {
        "real_map_owned"
    } else {
        "real_map_borrowed"
    };
    let backend_before = std::fs::read(backend).expect("read real-map backend");
    let compiler =
        std::path::PathBuf::from(toolchain_support::rustc_driver_command().get_program());
    let compiler_before = std::fs::read(&compiler).expect("read real-map compiler");
    let provider_source = dir.join("real_map_provider.rs");
    let callee_source = dir.join("real_map_consumer.rs");
    let oracle_source = dir.join("real_map_oracle.rs");
    for (path, source) in [
        (&provider_source, PROVIDER),
        (&callee_source, CALLEE),
        (&oracle_source, ORACLE),
    ] {
        std::fs::write(path, source).expect("write exact real-map fixture");
    }
    let provider = dir.join("libreal_map_provider.rlib");
    let oracle = dir.join("libreal_map_oracle.rlib");
    let mut provider_cmd = command(
        dir,
        "real_map_provider",
        &provider_source,
        &provider,
        None,
        "0",
        &[],
    );
    assert!(
        run(
            &mut provider_cmd,
            &dir.join("real-map-provider.log"),
            Duration::from_secs(240)
        )
        .success(),
        "independent LLVM map provider failed; {}",
        dir.display()
    );
    let mut oracle_cmd = command(
        dir,
        "real_map_oracle",
        &oracle_source,
        &oracle,
        None,
        "0",
        &[("real_map_provider", provider.as_path())],
    );
    assert!(
        run(
            &mut oracle_cmd,
            &dir.join("real-map-oracle.log"),
            Duration::from_secs(240)
        )
        .success(),
        "independent LLVM map oracle failed; {}",
        dir.display()
    );
    let provider_before = std::fs::read(&provider).expect("read LLVM provider artifact");
    let oracle_before = std::fs::read(&oracle).expect("read LLVM oracle artifact");
    let marker = format!(
        "REAL_MAP_DYN_ORIGIN|kind={kind}|scenarios=2|outer_frees=2|bad_layout=0|provider=LLVM|oracle=LLVM"
    );
    let mut refused = 0;
    for opt in opts {
        for cg in [false, true] {
            let binary = dir.join(format!("real-map-{kind}-O{opt}-{cg}"));
            let log = binary.with_extension("compile.log");
            let mut cmd = command(
                dir,
                "real_map_consumer",
                &callee_source,
                &binary,
                cg.then_some((backend, knobs)),
                opt,
                &[
                    ("real_map_provider", provider.as_path()),
                    ("real_map_oracle", oracle.as_path()),
                ],
            );
            cmd.arg(format!("--cfg={cfg}"));
            let status = run(&mut cmd, &log, Duration::from_secs(240));
            let text = std::fs::read_to_string(&log).expect("read real-map compiler log");
            if cg {
                assert!(
                    !status.success() && !binary.exists(),
                    "CG real-map {kind} O{opt} must refuse, not build; {}",
                    log.display()
                );
                assert!(
                    text.lines().any(|line| line.contains(" - ")
                        && line.contains(root)
                        && line.contains(REFUSAL)),
                    "required {root} must reach exact {REFUSAL}, not an earlier storage/capability gate; {}",
                    log.display()
                );
                refused += 1;
            } else {
                assert!(
                    status.success() && binary.exists(),
                    "LLVM map control failed; {}",
                    log.display()
                );
                let binary_before = std::fs::read(&binary).expect("read LLVM native control");
                let run_log = binary.with_extension("run.log");
                assert!(
                    run(
                        &mut Command::new(&binary),
                        &run_log,
                        Duration::from_secs(30)
                    )
                    .success(),
                    "LLVM real-map native oracle failed; {}",
                    run_log.display()
                );
                let text = std::fs::read_to_string(&run_log).expect("read real-map native log");
                let markers: Vec<_> = text
                    .lines()
                    .filter(|line| line.starts_with("REAL_MAP_DYN_ORIGIN|"))
                    .collect();
                assert_eq!(
                    markers,
                    [marker.as_str()],
                    "real-map ownership/layout oracle must execute; {}",
                    run_log.display()
                );
                assert!(
                    !text
                        .lines()
                        .any(|line| line.trim_start().starts_with("SKIP")),
                    "real-map oracle skipped"
                );
                assert_eq!(
                    std::fs::read(&binary).expect("reread LLVM native control"),
                    binary_before
                );
            }
            assert_eq!(
                std::fs::read(&provider).expect("reread LLVM provider artifact"),
                provider_before
            );
            assert_eq!(
                std::fs::read(&oracle).expect("reread LLVM oracle artifact"),
                oracle_before
            );
            assert_eq!(
                std::fs::read(backend).expect("reread backend"),
                backend_before
            );
            assert_eq!(
                std::fs::read(&compiler).expect("reread compiler"),
                compiler_before
            );
            for (path, source) in [
                (&provider_source, PROVIDER),
                (&callee_source, CALLEE),
                (&oracle_source, ORACLE),
            ] {
                assert_eq!(
                    std::fs::read(path).expect("reread fixture"),
                    source.as_bytes()
                );
            }
        }
    }
    assert_eq!(refused, opts.len(), "every real-map origin cell must close");
    eprintln!(
        "REAL_MAP_DYN_ORIGIN_REFUSAL kind={kind} llvm_native={} cg_refused={refused}",
        opts.len()
    );
    refused
}
