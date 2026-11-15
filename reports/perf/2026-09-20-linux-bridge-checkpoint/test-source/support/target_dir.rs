use std::ffi::OsStr;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

/// Resolve Cargo's target root exactly once for the bridge integration tests.
/// Relative `CARGO_TARGET_DIR`/`CARGO_BUILD_TARGET_DIR` values are relative to
/// the invoking process's working directory (not to `CARGO_MANIFEST_DIR`).
#[allow(dead_code)]
pub fn cargo_target_dir(manifest_dir: &Path) -> PathBuf {
    let root = resolve_target_dir(
        manifest_dir,
        &std::env::current_dir().expect("integration-test current directory"),
        std::env::var_os("CARGO_TARGET_DIR")
            .or_else(|| std::env::var_os("CARGO_BUILD_TARGET_DIR"))
            .as_deref(),
    );
    match std::env::var("CARGO_BUILD_TARGET") {
        Ok(target) if !target.trim().is_empty() => {
            let host = (target.trim() == "host-tuple")
                .then(resolve_rustc_host_tuple)
                .flatten();
            let component = target_output_component(&target, host.as_deref()).unwrap_or_else(|| {
                panic!(
                    "CARGO_BUILD_TARGET={target:?} does not identify one Cargo artifact directory"
                )
            });
            root.join(component)
        }
        _ => root,
    }
}

/// Cargo names a custom JSON target's artifact directory after the file stem,
/// not after the path supplied to `--target`/`CARGO_BUILD_TARGET`. It also
/// substitutes the special `host-tuple` spelling before choosing the output
/// directory. Keeping this conversion separate makes both cases testable
/// without mutating process-global environment variables.
pub fn target_output_component(configured: &str, rustc_host: Option<&str>) -> Option<PathBuf> {
    let configured = configured.trim();
    if configured.is_empty() {
        return None;
    }
    if configured == "host-tuple" {
        return rustc_host
            .map(str::trim)
            .filter(|host| !host.is_empty())
            .map(PathBuf::from);
    }
    let path = Path::new(configured);
    let is_custom_spec_path = path.is_absolute()
        || path.components().count() > 1
        || path.extension() == Some(OsStr::new("json"));
    if is_custom_spec_path {
        path.file_stem().map(PathBuf::from)
    } else {
        Some(path.to_path_buf())
    }
}

fn resolve_rustc_host_tuple() -> Option<String> {
    let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let output = Command::new(rustc).arg("-vV").output().ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8(output.stdout)
        .ok()?
        .lines()
        .find_map(|line| line.strip_prefix("host: ").map(str::to_string))
}

pub fn resolve_target_dir(
    manifest_dir: &Path,
    current_dir: &Path,
    configured: Option<&OsStr>,
) -> PathBuf {
    let raw = configured
        .map(PathBuf::from)
        .unwrap_or_else(|| manifest_dir.join("target"));
    let absolute = if raw.is_absolute() {
        raw
    } else {
        current_dir.join(raw)
    };
    lexical_normalize(&absolute)
}

/// The directory in which Cargo places artifacts for an optional explicit
/// target triple and profile (including custom `--profile` names).
#[allow(dead_code)]
pub fn artifact_dir(target_root: &Path, target: Option<&str>, profile: &str) -> PathBuf {
    let mut out = target_root.to_path_buf();
    if let Some(target) = target.filter(|target| !target.is_empty()) {
        out.push(target);
    }
    out.push(profile);
    out
}

fn lexical_normalize(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                if out.file_name().is_some() {
                    out.pop();
                } else if !out.has_root() {
                    // Preserve a leading `..` only for genuinely relative
                    // paths. Absolute paths clamp at their filesystem root.
                    out.push(component.as_os_str());
                }
            }
            Component::Prefix(_) | Component::RootDir | Component::Normal(_) => {
                out.push(component.as_os_str());
            }
        }
    }
    out
}
