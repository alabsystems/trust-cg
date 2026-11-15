//! Pure Cargo target-directory resolution rules, exercised by
//! `tests/target_dir_resolution.rs`.
//!
//! No bridge test uses these to find a backend library: each loads the library
//! Cargo built for its own test build (`support/backend_artifact.rs`), and
//! `scripts/tests/test_bridge_backend_selection.py` refuses target-directory
//! probing. These functions read no environment.

use std::ffi::OsStr;
use std::path::{Component, Path, PathBuf};

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
