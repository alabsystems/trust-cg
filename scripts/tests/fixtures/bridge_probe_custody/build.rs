//! Genuine inherited-custody regression for the bridge's actual probe helper.
//! Compilation remains explicitly unverified; no new scheduler is constructed.

#[allow(dead_code)]
#[path = "../../../../crates/rustc-codegen-trust-cg/build_support/probe.rs"]
mod probe;

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

fn write(name: &str, bytes: &[u8]) {
    let output = PathBuf::from(env::var_os("BRIDGE_PROBE_CUSTODY_RECORD").unwrap());
    std::fs::write(output.join(name), bytes).unwrap();
}

fn main() {
    println!(
        "cargo:rerun-if-changed=../../../../crates/rustc-codegen-trust-cg/build_support/probe.rs"
    );
    println!("cargo:rerun-if-env-changed=BRIDGE_PROBE_CUSTODY_CASE");
    println!("cargo:rerun-if-env-changed=BRIDGE_PROBE_CUSTODY_RECORD");
    println!("cargo:rerun-if-env-changed=BRIDGE_PROBE_ARTIFACTS");
    let case = env::var("BRIDGE_PROBE_CUSTODY_CASE").unwrap();
    let compiler = PathBuf::from(env::var_os("RUSTC").unwrap());
    assert!(compiler.is_absolute());
    // These must come from the actual native Targo invocation. In particular,
    // a standalone compiler process with no inherited custody is not positive
    // evidence that the original transport survived the helper.
    assert!(env::var_os("CARGO_JOBSERVER_HANDOFF").is_some());
    assert!(
        env::var("CARGO_MAKEFLAGS")
            .unwrap()
            .contains("--jobserver-auth=")
    );
    if case == "process-contracts" {
        // The unchanged process-contract suite also discovers the real sysroot.
        // Run it as this ordinary build-script descendant so that query retains
        // genuine Cargo custody, rather than running it from an SDK-only shell.
        let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../test_bridge_build_probe.py");
        assert!(
            Command::new("python3")
                .arg(script)
                .status()
                .unwrap()
                .success()
        );
        return;
    }
    let mut command = Command::new(&compiler);
    command.arg("-vV");
    match case.as_str() {
        "genuine" => {}
        "missing-gnu" => {
            for name in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"] {
                command.env_remove(name);
            }
        }
        "mismatched-gnu" | "malformed-handoff" => {
            for name in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"] {
                command.env(name, "-j --jobserver-auth=999996,999997");
            }
            if case == "malformed-handoff" {
                command.env("CARGO_JOBSERVER_HANDOFF", "invalid-handoff");
            }
        }
        _ => panic!("unknown custody case"),
    }
    let output = probe::capture(&mut command, probe::PROBE_TIMEOUT).unwrap();
    write("version.stdout", &output.stdout);
    write("version.stderr", &output.stderr);
    let record = serde_json::json!({
        "case": case,
        "compiler": compiler,
        "parent_native_handoff": true,
        "parent_gnu_auth": true,
        "version_status": output.status.code(),
        "ordinary_metadata_compile": false,
    });
    write("result.json", &serde_json::to_vec_pretty(&record).unwrap());
    if case != "genuine" {
        assert!(!output.status.success());
        let error = String::from_utf8(output.stderr).unwrap();
        assert!(
            error.contains("inherited compiler resource custody unavailable"),
            "{error}"
        );
        let reason = match case.as_str() {
            "missing-gnu" => "native/scoped compiler custody has no inherited GNU scheduler",
            "mismatched-gnu" => "jobserver handoff does not bind the advertised pool",
            "malformed-handoff" => "unsupported jobserver handoff advertisement",
            _ => unreachable!(),
        };
        assert!(error.contains(reason), "{error}");
        println!("cargo:warning=BRIDGE_PROBE_CUSTODY refused={case}");
        return;
    }
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    assert!(String::from_utf8_lossy(&output.stdout).contains("commit-hash:"));
    let target = env::var_os("TARGET").unwrap();
    let sysroot = probe::capture(
        Command::new(&compiler)
            .args(["--print", "sysroot", "--target"])
            .arg(target),
        probe::PROBE_TIMEOUT,
    )
    .unwrap();
    assert!(sysroot.status.success() && sysroot.stderr.is_empty());
    let sysroot = String::from_utf8(sysroot.stdout).unwrap();
    assert!(Path::new(sysroot.trim()).is_absolute());
    probe::set_probe_sysroot(PathBuf::from(sysroot.trim()));
    let options = probe::probe_options(&compiler);
    assert!(probe::compile_probe(
        &compiler,
        &options.flags,
        "native_custody_consumer",
        "pub fn ordinary_consumer() -> u64 { 41 }",
        None,
    ));
    let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    for suffix in ["rs", "command", "stdout", "stderr", "status", "rmeta"] {
        let name = format!("probe_native_custody_consumer.{suffix}");
        write(&name, &std::fs::read(out.join(&name)).unwrap());
    }
    let mut record = record;
    record["ordinary_metadata_compile"] = true.into();
    write("result.json", &serde_json::to_vec_pretty(&record).unwrap());
    println!("cargo:warning=BRIDGE_PROBE_CUSTODY genuine-version-and-metadata");
}
