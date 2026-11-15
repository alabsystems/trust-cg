// Copyright 2026 Andrew Yates | Apache-2.0
//! Regenerate untrusted context DATA from the complete original Lean cone.
//! This does not render CG goals, grant a certificate, or select a theory.

use clean_kernel::env::ENV_SCHEMA_FINGERPRINT;
use clean_kernel::level::LeanLevelProfile;
use clean_kernel::{Environment, Expr, Name};
use clean_olean::recheck_closed::reference_base::{ReferenceBase, reference_base_closed};
use clean_olean::{ClosedRecheckOptions, load_module_with_deps};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

const ROOTS: [&str; 3] = [
    "Trust.Cert.CheckedMulI128Raw.original_unsigned",
    "Trust.Cert.CheckedMulI128Raw.original_signed",
    "Trust.Cert.CheckedMulI128Raw.original_constant",
];
const LOCK: &str = include_str!("../../../Cargo.lock");
const BUNDLE_SCHEMA: u32 = 3;
const ENVIRONMENT_DAG_FORMAT: &str = "CLENEDG2";

fn sha(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn write_new(out: &Path, name: &str, bytes: &[u8]) -> Result<(), String> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(out.join(name))
        .map_err(|error| error.to_string())?;
    file.write_all(bytes).map_err(|error| error.to_string())?;
    file.sync_all().map_err(|error| error.to_string())
}

fn save<T: serde::Serialize>(out: &Path, name: &str, value: &T) -> Result<(), String> {
    write_new(
        out,
        name,
        &serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?,
    )
}

fn producer_revision() -> Result<String, String> {
    let lock: toml::Value = toml::from_str(LOCK).map_err(|error| error.to_string())?;
    let rows: Vec<_> = lock
        .get("package")
        .and_then(toml::Value::as_array)
        .ok_or("locked package array missing")?
        .iter()
        .filter(|row| row.get("name").and_then(toml::Value::as_str) == Some("clean-kernel"))
        .collect();
    if rows.len() != 1 {
        return Err("producer needs one exact locked Clean kernel source".into());
    }
    let source = rows[0]
        .get("source")
        .and_then(toml::Value::as_str)
        .ok_or("producer cannot label a path-patched Clean kernel")?;
    let tail = source
        .strip_prefix("git+https://github.com/alabsystems/clean.git?rev=")
        .ok_or("unexpected locked Clean source")?;
    let (revision, object) = tail.split_once('#').ok_or("locked Clean object missing")?;
    if revision.len() != 40
        || revision != object
        || !revision
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("locked Clean source is not an exact immutable revision".into());
    }
    Ok(revision.to_owned())
}

fn ready(checked: &ReferenceBase, roots: &BTreeSet<Name>) -> bool {
    let env = checked.kernel().environment();
    let axioms = ["propext", "Classical.choice", "Quot.sound"];
    checked.report.passed()
        && checked.report.extension_bindings_pinned
        && checked.entry_refusals.is_empty()
        && env.lean_level_profile() == LeanLevelProfile::Lean430
        && checked.report.axioms_admitted.len() == axioms.len()
        && checked.report.axioms_admitted.iter().all(|name| {
            axioms.contains(&name.as_str())
                && env.is_canonical_foundational_axiom(&Name::from_string(name))
        })
        && roots.iter().all(|name| {
            checked.admitted.contains(name)
                && env
                    .get_const(name)
                    .is_some_and(|info| info.value.is_some() && info.level_params.is_empty())
        })
}

fn run() -> Result<(), String> {
    let args: Vec<_> = std::env::args_os().collect();
    if args.len() != 4 {
        return Err("MODULE_ROOT LEAN430_LIB NEW_OUTPUT required".into());
    }
    let out = PathBuf::from(&args[3]);
    // A failed generation remains an immutable attempt, never overwritten.
    fs::create_dir(&out).map_err(|error| error.to_string())?;
    let clean_source = producer_revision()?;
    let search = vec![PathBuf::from(&args[1]), PathBuf::from(&args[2])];
    let mut source = Environment::default();
    let started = Instant::now();
    let imports = load_module_with_deps(&mut source, "Trust.Cert.CheckedMulI128Raw", &search)
        .map_err(|error| format!("actual source import refused: {error:?}"))?;
    let imported_modules: Vec<_> = imports
        .iter()
        .map(|row| {
            row.module_name
                .clone()
                .ok_or("imported module identity missing")
        })
        .collect::<Result<_, _>>()?;
    save(
        &out,
        "IMPORT.json",
        &json!({"modules":imports.len(),"module_names":imported_modules,"constants":source.constants().count(),
            "seconds":started.elapsed().as_secs_f64(),
            "source_lean_level_profile":source.lean_level_profile()}),
    )?;
    if source.lean_level_profile() != LeanLevelProfile::Lean430 {
        return Err("actual imported source has a different Lean level profile".into());
    }
    let roots: BTreeSet<_> = ROOTS.iter().map(|name| Name::from_string(name)).collect();
    let started = Instant::now();
    let checked = reference_base_closed(&source, &roots, &ClosedRecheckOptions::default())
        .map_err(|error| format!("fenced empty replay refused: {error}"))?;
    let closed_seconds = started.elapsed().as_secs_f64();
    save(&out, "CLOSED-REPORT.json", &checked.report)?;
    if !ready(&checked, &roots) {
        return Err("complete original source cone refused fresh replay".into());
    }
    let kernel = checked
        .into_kernel()
        .map_err(|report| format!("fenced replay refused: {report:?}"))?;
    let env = kernel.environment();
    let mut controls = Vec::new();
    for (index, name) in ROOTS.iter().enumerate() {
        let info = kernel
            .environment()
            .get_const(&Name::from_string(name))
            .ok_or("root missing")?;
        let proof = info.value.as_ref().ok_or("root proof missing")?;
        let other = kernel
            .environment()
            .get_const(&Name::from_string(ROOTS[(index + 1) % ROOTS.len()]))
            .ok_or("cross-root goal missing")?;
        let positive = kernel.check_closed_term(&info.type_, proof);
        let wrong = kernel.check_closed_term(&other.type_, proof);
        let open = kernel.check_closed_term(&info.type_, &Expr::bvar(0));
        let pass = positive.is_ok() && wrong.is_err() && open.is_err();
        controls.push(json!({"root":name,"positive":format!("{positive:?}"),
            "wrong_goal":format!("{wrong:?}"),"open_proof":format!("{open:?}"),"pass":pass}));
    }
    save(&out, "TYPECHECKS.json", &controls)?;
    if controls.iter().any(|row| row["pass"] != true) {
        return Err("original three-root proof controls failed".into());
    }
    drop(source);
    let bytes = env.to_dag_bincode().map_err(|error| error.to_string())?;
    if !bytes.starts_with(ENVIRONMENT_DAG_FORMAT.as_bytes()) {
        return Err("maintained writer did not produce the current owned DAG format".into());
    }
    let compressed =
        zstd::stream::encode_all(bytes.as_slice(), 9).map_err(|error| error.to_string())?;
    // Bind both the owned graph envelope and snapshot schema. Historical G1
    // data is not reinterpreted or allowed to select a legacy checker policy.
    let manifest = json!({"schema":BUNDLE_SCHEMA,"clean_source":clean_source,"roots":ROOTS,
        "environment_dag_format":ENVIRONMENT_DAG_FORMAT,
        "environment_schema":ENV_SCHEMA_FINGERPRINT,"source_lean_level_profile":LeanLevelProfile::Lean430,
        "raw_bytes":bytes.len(),"raw_sha256":sha(&bytes),"zstd_bytes":compressed.len(),
        "zstd_sha256":sha(&compressed),"closed_cone_seconds":closed_seconds,
        "scope":"untrusted retained mathematical context; must freshly recheck before use"});
    write_new(&out, "closed-environment.dag.zst", &compressed)?;
    save(&out, "BUNDLE.json", &manifest)?;
    let retained_compressed =
        fs::read(out.join("closed-environment.dag.zst")).map_err(|error| error.to_string())?;
    let retained_bytes = zstd::stream::decode_all(retained_compressed.as_slice())
        .map_err(|error| error.to_string())?;
    if retained_compressed != compressed || retained_bytes != bytes {
        return Err("written context bytes differ from the produced data".into());
    }
    let restored =
        Environment::from_dag_bincode(&retained_bytes).map_err(|error| error.to_string())?;
    let constants_exact = restored.constants().count() == env.constants().count()
        && kernel
            .environment()
            .constants()
            .all(|info| restored.get_const(&info.name) == Some(info));
    let inductives_exact = restored.inductives().count() == env.inductives().count()
        && kernel
            .environment()
            .inductives()
            .all(|info| restored.get_inductive(&info.name) == Some(info));
    let constructors_exact = restored.constructors().count() == env.constructors().count()
        && kernel
            .environment()
            .constructors()
            .all(|info| restored.get_constructor(&info.name) == Some(info));
    let recursors_exact = restored.recursors().count() == env.recursors().count()
        && kernel
            .environment()
            .recursors()
            .all(|info| restored.get_recursor(&info.name) == Some(info));
    let quotients_exact = restored.quotients().count() == env.quotients().count()
        && kernel
            .environment()
            .quotients()
            .all(|info| restored.quotients().any(|other| other == info));
    let no_stamps = restored
        .constants()
        .all(|info| restored.declaration_verification(&info.name).is_none());
    let profile_exact = restored.lean_level_profile() == env.lean_level_profile();
    save(
        &out,
        "ROUNDTRIP-DATA.json",
        &json!({"constants_exact":constants_exact,
        "inductives_exact":inductives_exact,"constructors_exact":constructors_exact,
        "recursors_exact":recursors_exact,"quotients_exact":quotients_exact,
        "profile_exact":profile_exact,"no_inherited_verification":no_stamps}),
    )?;
    if !(constants_exact
        && inductives_exact
        && constructors_exact
        && recursors_exact
        && quotients_exact
        && profile_exact
        && no_stamps)
    {
        return Err("serialized declaration data changed or inherited verification".into());
    }
    drop(kernel);
    let replay = reference_base_closed(&restored, &roots, &ClosedRecheckOptions::default())
        .map_err(|error| format!("restored fenced replay refused: {error}"))?;
    save(&out, "RESTORED-CLOSED-REPORT.json", &replay.report)?;
    if !ready(&replay, &roots) {
        return Err("restored complete context refused fresh replay".into());
    }
    let replay = replay
        .into_kernel()
        .map_err(|report| format!("restored fenced cone refused: {report:?}"))?;
    let mut retained = Vec::new();
    for name in ROOTS {
        let info = replay
            .environment()
            .get_const(&Name::from_string(name))
            .ok_or("restored root absent")?;
        let result =
            replay.check_closed_term(&info.type_, &Expr::const_(info.name.clone(), Vec::new()));
        retained.push(json!({"root":name,"check":format!("{result:?}"),"pass":result.is_ok()}));
    }
    save(&out, "RESTORED-TYPECHECKS.json", &retained)?;
    if retained.iter().any(|row| row["pass"] != true) {
        return Err("restored root proof reference refused".into());
    }
    save(
        &out,
        "FINAL.json",
        &json!({"pass":true,"actual_roots":ROOTS.len(),
        "environment_schema":ENV_SCHEMA_FINGERPRINT,"locked_source_manifest_sha256":sha(LOCK.as_bytes()),
        "scope":"fresh three-root mathematical DATA producer; no CG or machine-code grade"}),
    )
}

fn main() {
    let result = std::thread::Builder::new()
        .name("retained-i128-context-producer".into())
        .stack_size(256 * 1024 * 1024)
        .spawn(run)
        .expect("owned producer worker")
        .join();
    match result {
        Ok(Ok(())) => (),
        Ok(Err(error)) => {
            eprintln!("REFUSED: {error}");
            std::process::exit(2);
        }
        Err(_) => {
            eprintln!("REFUSED: owned producer worker panicked");
            std::process::exit(3);
        }
    }
}
