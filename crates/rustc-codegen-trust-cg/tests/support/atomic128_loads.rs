//! Linux AArch64 128-bit loads, stores and fetch-adds preserve values and
//! whole-pair observations; 128-bit compare-exchange stays refused.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-atomic128-loads.XXXXXX"])
        .output()
        .expect("mktemp atomic128 load artifacts");
    assert!(temp.status.success());
    Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ))
}

fn valid_load_loop(name: &str, instructions: &[(u64, u32)]) -> bool {
    let loads: Vec<_> = instructions
        .iter()
        .enumerate()
        .filter(|(_, (_, word))| word & 0xffff0000 == 0xc87f0000)
        .collect();
    let stores: Vec<_> = instructions
        .iter()
        .enumerate()
        .filter(|(_, (_, word))| word & 0xffe00000 == 0xc8200000)
        .collect();
    if loads.len() != 1 || stores.len() != 1 {
        return false;
    }
    let (index, &(address, load)) = loads[0];
    let (store_index, &(_, store)) = stores[0];
    if store_index != index + 1 || index + 2 >= instructions.len() {
        return false;
    }
    let (branch_address, branch) = instructions[index + 2];
    let registers = |word: u32| [word & 31, (word >> 10) & 31, (word >> 5) & 31];
    let status = (store >> 16) & 31;
    if registers(load) != registers(store)
        || status == 31
        || registers(store).contains(&status)
        || branch & 0xff000000 != 0x35000000
        || branch & 31 != status
    {
        return false;
    }
    let mut immediate = i64::from((branch >> 5) & 0x7ffff);
    if immediate & 0x40000 != 0 {
        immediate -= 0x80000;
    }
    branch_address.checked_add_signed(immediate * 4) == Some(address)
        && (load & 0x8000 != 0) == !name.ends_with("_relaxed")
        && (store & 0x8000 != 0) == name.ends_with("_seqcst")
}

/// The (address, word) instruction list of every function in `objects`.
fn disassemble(
    objects: &[PathBuf],
    log: &Path,
) -> (String, std::collections::BTreeMap<String, Vec<(u64, u32)>>) {
    let output = checked(Command::new("objdump").arg("-d").args(objects), 30, log);
    let text = String::from_utf8(output.stdout).unwrap();
    let mut functions: std::collections::BTreeMap<String, Vec<(u64, u32)>> =
        std::collections::BTreeMap::new();
    let mut current = String::new();
    for line in text.lines() {
        if let Some((_, name)) = line.split_once('<') {
            if let Some(name) = name.strip_suffix(">:") {
                current = name.to_owned();
                functions.entry(current.clone()).or_default();
                continue;
            }
        }
        let fields: Vec<_> = line.split_whitespace().collect();
        if !current.is_empty()
            && fields.len() >= 3
            && fields[0].ends_with(':')
            && fields[1].len() == 8
        {
            if let (Ok(address), Ok(word)) = (
                u64::from_str_radix(fields[0].trim_end_matches(':'), 16),
                u32::from_str_radix(fields[1], 16),
            ) {
                functions.get_mut(&current).unwrap().push((address, word));
            }
        }
    }
    (text, functions)
}

fn inspect_load_loops(objects: &[PathBuf], log: &Path) {
    let (text, functions) = disassemble(objects, log);
    assert_eq!(
        functions.keys().map(String::as_str).collect::<Vec<_>>(),
        [
            "load_i128_acquire",
            "load_i128_relaxed",
            "load_i128_seqcst",
            "load_u128_acquire",
            "load_u128_relaxed",
            "load_u128_seqcst",
        ]
    );
    for (name, instructions) in functions {
        assert!(
            valid_load_loop(&name, &instructions),
            "invalid atomic load loop {name}: {text}"
        );
        let index = instructions
            .iter()
            .position(|(_, word)| word & 0xffff0000 == 0xc87f0000)
            .unwrap();
        // Wrong ordering, a different store-back data pair, or a retry on the
        // wrong status register must each fail this structural check.
        for (at, bit) in [(index, 0x8000), (index + 1, 1 << 10), (index + 2, 1)] {
            let mut damaged = instructions.clone();
            damaged[at].1 ^= bit;
            assert!(
                !valid_load_loop(&name, &damaged),
                "inspector accepted mutant of {name}"
            );
        }
    }
}

/// One exclusive-pair loop per 128-bit store or fetch-add: exactly one
/// `LDXP`/`LDAXP` and one later `STXP`/`STLXP` on the same base register, the
/// store writing a pair other than the one just loaded, and a `CBNZ` on the
/// store's status register straight after it that retries from the load. The
/// ordering bits are the intrinsic's: acquire on the load for SeqCst/AcqRel,
/// release on the store for Release/SeqCst/AcqRel (the AArch64 mapping LLVM
/// uses without FEAT_LSE2).
fn valid_rmw_loop(name: &str, instructions: &[(u64, u32)]) -> bool {
    let find = |mask: u32, value: u32| -> Vec<usize> {
        (0..instructions.len())
            .filter(|&i| instructions[i].1 & mask == value)
            .collect()
    };
    let (loads, stores) = (find(0xffff0000, 0xc87f0000), find(0xffe00000, 0xc8200000));
    if loads.len() != 1 || stores.len() != 1 {
        return false;
    }
    let (index, store_index) = (loads[0], stores[0]);
    if store_index <= index || store_index + 1 >= instructions.len() {
        return false;
    }
    let (address, load) = instructions[index];
    let store = instructions[store_index].1;
    let (branch_address, branch) = instructions[store_index + 1];
    let base = |word: u32| (word >> 5) & 31;
    let pair = |word: u32| [word & 31, (word >> 10) & 31];
    let status = (store >> 16) & 31;
    if base(load) != base(store)
        || pair(store) == pair(load)
        || status == 31
        || status == base(store)
        || pair(store).contains(&status)
        || branch & 0xff000000 != 0x35000000
        || branch & 31 != status
    {
        return false;
    }
    let mut immediate = i64::from((branch >> 5) & 0x7ffff);
    if immediate & 0x40000 != 0 {
        immediate -= 0x80000;
    }
    let acquire = matches!(name, "store_i128" | "add_u128");
    let release = matches!(name, "store_u128" | "store_i128" | "add_u128");
    branch_address.checked_add_signed(immediate * 4) == Some(address)
        && (load & 0x8000 != 0) == acquire
        && (store & 0x8000 != 0) == release
}

fn inspect_rmw_loops(objects: &[PathBuf], log: &Path) {
    let (text, functions) = disassemble(objects, log);
    assert_eq!(
        functions.keys().map(String::as_str).collect::<Vec<_>>(),
        [
            "add_i128",
            "add_u128",
            "load_u128_acquire",
            "store_i128",
            "store_u128"
        ]
    );
    for (name, instructions) in functions {
        if name == "load_u128_acquire" {
            assert!(
                valid_load_loop(&name, &instructions),
                "invalid atomic load loop {name}: {text}"
            );
            continue;
        }
        assert!(
            valid_rmw_loop(&name, &instructions),
            "invalid atomic store/add loop {name}: {text}"
        );
        let load = instructions
            .iter()
            .position(|(_, word)| word & 0xffff0000 == 0xc87f0000)
            .unwrap();
        let store = instructions
            .iter()
            .position(|(_, word)| word & 0xffe00000 == 0xc8200000)
            .unwrap();
        // Wrong load or store ordering, another base register, a retry on the
        // wrong status register or to the wrong place must each fail.
        for (at, bit) in [
            (load, 0x8000),
            (store, 0x8000),
            (store, 1 << 5),
            (store + 1, 1),
            (store + 1, 1 << 5),
        ] {
            let mut damaged = instructions.clone();
            damaged[at].1 ^= bit;
            assert!(
                !valid_rmw_loop(&name, &damaged),
                "inspector accepted mutant of {name}"
            );
        }
    }
}

/// What a case's CG lane must show: the 128-bit load loops, the store/add
/// loops, or the named refusal of the operations still unsupported.
#[derive(Clone, Copy, PartialEq)]
enum Mode {
    Loads,
    StoreAdd,
    Refusal,
}

fn native_case(
    root: &Path,
    backend: &Path,
    digest: &str,
    rust: &str,
    driver: &str,
    expected: &str,
    mode: Mode,
) {
    std::fs::create_dir(root).unwrap();
    std::fs::write(root.join("corpus.rs"), rust).unwrap();
    std::fs::write(root.join("driver.rs"), driver).unwrap();
    for opt in 0..=3 {
        for lane in ["llvm", "cg"] {
            let stem = format!("{lane}-O{opt}");
            let dir = root.join(&stem);
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "-Ccodegen-units=1",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
            }
            command
                .arg(root.join("corpus.rs"))
                .arg("--out-dir")
                .arg(&dir);
            if lane == "cg" && mode == Mode::Refusal {
                let (output, transcript) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                assert_eq!(output.status.code(), Some(1), "{transcript}");
                let diagnostics: Vec<serde_json::Value> = String::from_utf8(output.stderr)
                    .unwrap()
                    .lines()
                    .filter_map(|line| serde_json::from_str(line).ok())
                    .filter(|row: &serde_json::Value| row["code"] == "TCG-MIR-UNSUPPORTED")
                    .collect();
                assert_eq!(diagnostics.len(), 1, "{transcript}");
                let fields = &diagnostics[0]["fields"];
                assert_eq!(fields["failed_root_count"], "2", "{transcript}");
                let failures: Vec<_> = fields["failed_roots"]
                    .as_str()
                    .unwrap()
                    .split("\n  - ")
                    .collect();
                assert_eq!(failures.len(), 2, "{transcript}");
                assert!(
                    failures
                        .iter()
                        .all(|v| v.contains("atomic compare_exchange over I128 (T=i128)")
                            || v.contains("atomic compare_exchange over U128 (T=u128)")),
                    "{transcript}"
                );
                let mut names: Vec<_> = failures
                    .iter()
                    .map(|v| v.split(": ").next().unwrap())
                    .collect();
                names.sort();
                assert_eq!(names, ["cas_i128", "cas_u128"], "{transcript}");
                assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
                continue;
            }
            checked(&mut command, 180, &dir.join("compile.log"));
            if mode == Mode::Refusal {
                assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
                continue;
            }
            let mut objects: Vec<_> = std::fs::read_dir(&dir)
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                .collect();
            objects.sort();
            assert!(!objects.is_empty(), "no objects from {stem}");
            if lane == "cg" {
                match mode {
                    Mode::Loads => inspect_load_loops(&objects, &dir.join("atomic-loop.asm")),
                    Mode::StoreAdd => inspect_rmw_loops(&objects, &dir.join("atomic-loop.asm")),
                    Mode::Refusal => unreachable!(),
                }
            }
            checked(
                Command::new("ar")
                    .arg("crs")
                    .arg(dir.join("libatomic_loads.a"))
                    .args(&objects),
                60,
                &dir.join("archive.log"),
            );
            let executable = dir.join("native.elf");
            checked(
                rustc_command()
                    .args(["--target", TARGET, "-Cpanic=abort"])
                    .arg(root.join("driver.rs"))
                    .arg("-L")
                    .arg(&dir)
                    .arg("-lstatic=atomic_loads")
                    .arg("-o")
                    .arg(&executable),
                180,
                &dir.join("link.log"),
            );
            let output = checked(&mut Command::new(&executable), 20, &dir.join("native.log"));
            assert_eq!(output.stdout, expected.as_bytes());
            assert!(output.stderr.is_empty());
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
}

#[test]
fn no_proof_atomic128_loads_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("values"),
        &backend,
        &digest,
        include_str!("atomic128_loads/corpus.rs"),
        include_str!("atomic128_loads/values_driver.rs"),
        "PASS atomic128_load checks=49152\n",
        Mode::Loads,
    );
    native_case(
        &artifacts.0.join("contention"),
        &backend,
        &digest,
        include_str!("atomic128_loads/corpus.rs"),
        include_str!("atomic128_loads/contention_driver.rs"),
        "PASS atomic128_load_contention checks=196608\n",
        Mode::Loads,
    );
    println!(
        "TCG_ATOMIC128_LOAD_DIAGNOSTIC executions=16 checks=1966080 inspected_loops=48 inspector_mutants=144 backend_sha256={digest}"
    );
}

/// 128-bit atomic store and fetch-add reach the isel since the 128-bit element
/// admission (68c67a6fd, merged by 817cd8753) and lower to exclusive-pair
/// loops. The driver checks every value against u128/i128 arithmetic, sums a
/// contended fetch-add (a lost update or torn carry changes the total) and
/// watches contended stores of equal-halves pairs for tearing.
#[test]
fn no_proof_atomic128_store_add_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("store-add"),
        &backend,
        &digest,
        include_str!("atomic128_loads/store_add.rs"),
        include_str!("atomic128_loads/store_add_driver.rs"),
        "PASS atomic128_store_add checks=200487\n",
        Mode::StoreAdd,
    );
    println!(
        "TCG_ATOMIC128_STORE_ADD executions=8 checks=1603896 inspected_loops=20 inspector_mutants=80 backend_sha256={digest}"
    );
}

/// 128-bit compare-exchange still has no AArch64 lowering here and fails
/// closed at the bridge's width gate.
#[test]
fn atomic128_compare_exchange_retains_refusal() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("refusals"),
        &backend,
        &digest,
        include_str!("atomic128_loads/refusals.rs"),
        "",
        "",
        Mode::Refusal,
    );
    println!(
        "TCG_ATOMIC128_CAS_REFUSAL llvm_accepted=4 cg_refused=4 roots=2 backend_sha256={digest}"
    );
}
