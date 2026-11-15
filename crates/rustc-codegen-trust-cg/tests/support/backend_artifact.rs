//! Locate the backend produced by the current Cargo integration-test build.
//!
//! Older Cargo builds put the package's dylib beside the test in `deps`.
//! Current Targo isolates each unit in `build/<package>/<unit>/out`; its test
//! fingerprint names the exact library dependency. Select that edge, including
//! its compiler/configuration identity, rather than the profile's mutable
//! top-level library or a newest cached artifact. Unknown layouts refuse.
//! This is artifact selection, not compiler or proof qualification. Run through
//! Cargo on a frozen source tree; do not concurrently rebuild the same target.

use std::path::{Path, PathBuf};

pub fn current_test_backend() -> PathBuf {
    let executable = std::env::current_exe().expect("running integration-test path");
    backend_for_test_executable(&executable).unwrap_or_else(|error| panic!("{error}"))
}

pub fn backend_for_test_executable(executable: &Path) -> Result<PathBuf, String> {
    if !executable.is_absolute() {
        return Err(format!("Cargo test path must be absolute: {executable:?}"));
    }
    let directory = executable.parent().ok_or("Cargo test has no directory")?;
    if directory.file_name().is_some_and(|name| name == "deps") {
        return regular_file(&directory.join(library_name()));
    }
    unit_backend(executable)
}

fn library_name() -> String {
    format!(
        "{}rustc_codegen_trust_cg{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    )
}

fn regular_file(path: &Path) -> Result<PathBuf, String> {
    let metadata = std::fs::symlink_metadata(path).map_err(|error| {
        format!("current Cargo test build has no artifact at {path:?}: {error}")
    })?;
    if !metadata.file_type().is_file() || metadata.len() == 0 {
        return Err(format!(
            "current Cargo artifact must be a nonempty regular file: {path:?}"
        ));
    }
    Ok(path.to_path_buf())
}

fn descriptor(path: &Path) -> Result<serde_json::Value, String> {
    regular_file(path)?;
    let bytes = std::fs::read(path).map_err(|error| format!("read {path:?}: {error}"))?;
    serde_json::from_slice(&bytes).map_err(|error| format!("Cargo descriptor {path:?}: {error}"))
}

fn unit_hash(text: &str) -> Option<u64> {
    (text.len() == 16
        && text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)))
    .then(|| u64::from_str_radix(text, 16).ok().map(u64::swap_bytes))
    .flatten()
}

fn unit_backend(executable: &Path) -> Result<PathBuf, String> {
    let invalid = || format!("unrecognized Cargo integration-test unit path: {executable:?}");
    let out = executable.parent().ok_or_else(invalid)?;
    let unit = out.parent().ok_or_else(invalid)?;
    let package = unit.parent().ok_or_else(invalid)?;
    let build = package.parent().ok_or_else(invalid)?;
    let hash = unit
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(invalid)?;
    let test = executable
        .file_name()
        .and_then(|name| name.to_str())
        .and_then(|name| name.strip_suffix(&format!("-{hash}")))
        .ok_or_else(invalid)?;
    if out.file_name().is_none_or(|name| name != "out")
        || build.file_name().is_none_or(|name| name != "build")
        || unit_hash(hash).is_none()
        || test.is_empty()
        || !test
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'-')
    {
        return Err(invalid());
    }
    let input = descriptor(
        &unit
            .join("fingerprint")
            .join(format!("test-integration-test-{test}.json")),
    )?;
    let dependencies = input["deps"]
        .as_array()
        .ok_or("Cargo test descriptor has no dependencies")?;
    let edges: Vec<_> = dependencies
        .iter()
        .filter(|edge| {
            edge.get(1).and_then(serde_json::Value::as_str) == Some("rustc_codegen_trust_cg")
        })
        .collect();
    let [edge] = edges.as_slice() else {
        return Err("Cargo test must name exactly one backend dependency".to_owned());
    };
    if edge.as_array().is_none_or(|values| values.len() != 4)
        || edge[0].as_u64().is_none()
        || edge[2].as_bool().is_none()
    {
        return Err("unrecognized Cargo backend dependency descriptor".to_owned());
    }
    let expected = edge[3]
        .as_u64()
        .ok_or("Cargo backend dependency has no fingerprint")?;
    let mut matches = Vec::new();
    for entry in std::fs::read_dir(package).map_err(|error| format!("read {package:?}: {error}"))? {
        let entry = entry.map_err(|error| error.to_string())?;
        if entry.file_name().to_str().and_then(unit_hash).is_none() {
            continue;
        }
        if !entry
            .file_type()
            .map_err(|error| error.to_string())?
            .is_dir()
        {
            return Err(format!(
                "Cargo unit directory is not a regular directory: {:?}",
                entry.path()
            ));
        }
        let fingerprint = entry.path().join("fingerprint/lib-rustc_codegen_trust_cg");
        if !fingerprint
            .try_exists()
            .map_err(|error| error.to_string())?
        {
            continue;
        }
        regular_file(&fingerprint)?;
        let value = std::fs::read_to_string(&fingerprint).map_err(|error| error.to_string())?;
        let actual = unit_hash(&value)
            .ok_or_else(|| format!("invalid Cargo library fingerprint: {fingerprint:?}"))?;
        if actual != expected {
            continue;
        }
        let library = descriptor(&fingerprint.with_extension("json"))?;
        for key in ["rustc", "config", "compile_kind"] {
            if input[key].as_u64().is_none() || input[key] != library[key] {
                return Err(format!("Cargo backend dependency differs in {key}"));
            }
        }
        matches.push(regular_file(
            &entry.path().join("out").join(library_name()),
        )?);
    }
    match matches.as_slice() {
        [library] => Ok(library.clone()),
        _ => Err(format!(
            "Cargo test dependency must identify one backend, found {}",
            matches.len()
        )),
    }
}
