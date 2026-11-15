// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Resolve proof tools from aterm's self-contained package store.
//!
//! AY is deliberately NOT resolved here. The solver a verdict comes from is the
//! one shipped in the owning Trust toolchain's sysroot, admitted by build
//! identity (`crate::ay_identity`); a managed package that the environment
//! happens to expose is not that solver (measured 2026-09-17: the managed
//! `store/ay/8256` was ay 0.13.0 while the Trust 9178 sysroot ships ay 0.26.0).
//! The independent checker is the owning toolchain's `clean` too, for the same
//! reason (it must read that AY's proofs); this module's package is only its
//! fallback when that toolchain ships no capable checker
//! (`obligation_cert_store::default_clean_checker_candidates`).
//!
//! The `alab-*` launchers are scripts, not executable identities: hashing one
//! would bind a certificate to the launcher while missing changes to its tool.
//! Resolve `store/<program>/current/bin/<program>` to the versioned binary
//! before a caller probes, hashes, or executes it. Never parse or execute a
//! launcher to discover its target, and never look in sibling source checkouts.

use std::path::{Path, PathBuf};

#[derive(Clone, Copy)]
pub(crate) enum ProofTool {
    Clean,
}

impl ProofTool {
    fn name(self) -> &'static str {
        match self {
            Self::Clean => "clean",
        }
    }
}

pub(crate) fn packaged_tool_path(tool: ProofTool) -> Option<PathBuf> {
    let mut prefixes = Vec::new();
    // Custom aterm prefixes advertise their bin directory on PATH. Requiring
    // the store layout prevents a generic command named `clean` from winning.
    if let Some(path) = trust_cg_process_env::var_os("PATH") {
        for bin in std::env::split_paths(&path) {
            if bin.file_name().is_some_and(|name| name == "bin")
                && let Some(prefix) = bin.parent()
            {
                push_prefix(&mut prefixes, prefix.to_path_buf());
            }
        }
    }

    // Match atpkg's platform default even when a subprocess has a reduced PATH.
    #[cfg(target_os = "macos")]
    if let Some(home) = trust_cg_process_env::var_os("HOME") {
        push_prefix(
            &mut prefixes,
            PathBuf::from(home).join("Library/Application Support/aterm/pkg"),
        );
    }
    #[cfg(all(unix, not(target_os = "macos")))]
    if let Some(home) = trust_cg_process_env::var_os("HOME") {
        push_prefix(
            &mut prefixes,
            PathBuf::from(home).join(".local/share/aterm/pkg"),
        );
    }
    #[cfg(windows)]
    if let Some(local) = trust_cg_process_env::var_os("LOCALAPPDATA") {
        push_prefix(&mut prefixes, PathBuf::from(local).join("aterm/pkg"));
    } else if let Some(profile) = trust_cg_process_env::var_os("USERPROFILE") {
        push_prefix(
            &mut prefixes,
            PathBuf::from(profile).join("AppData/Local/aterm/pkg"),
        );
    }

    packaged_tool_path_in_prefixes(tool, &prefixes)
}

fn push_prefix(prefixes: &mut Vec<PathBuf>, prefix: PathBuf) {
    if !prefixes.contains(&prefix) {
        prefixes.push(prefix);
    }
}

fn tool_path(prefix: &Path, version: &str, tool: ProofTool) -> PathBuf {
    let name = tool.name();
    prefix
        .join("store")
        .join(name)
        .join(version)
        .join("bin")
        .join(format!("{name}{}", std::env::consts::EXE_SUFFIX))
}

fn packaged_tool_path_in_prefixes(tool: ProofTool, prefixes: &[PathBuf]) -> Option<PathBuf> {
    prefixes.iter().find_map(|prefix| {
        let path = tool_path(prefix, "current", tool).canonicalize().ok()?;
        path.is_file().then_some(path)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn put_tool(prefix: &Path, version: &str, tool: ProofTool, bytes: &[u8]) -> PathBuf {
        let path = tool_path(prefix, version, tool);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, bytes).unwrap();
        path.canonicalize().unwrap()
    }

    #[test]
    fn managed_tools_resolve_without_source_checkouts_or_launchers() {
        let prefix = tempfile::tempdir().unwrap();
        let tool = ProofTool::Clean;
        let expected = put_tool(prefix.path(), "current", tool, b"managed executable");
        assert_eq!(
            packaged_tool_path_in_prefixes(tool, &[prefix.path().to_path_buf()]),
            Some(expected),
        );
    }

    #[test]
    fn generic_commands_and_sibling_builds_are_not_managed_tools() {
        let prefix = tempfile::tempdir().unwrap();
        for directory in ["bin", "clean/target/release", "ay/target/release"] {
            let path = prefix.path().join(directory);
            std::fs::create_dir_all(&path).unwrap();
            for name in ["clean", "alab-clean", "ay", "alab-ay"] {
                std::fs::write(path.join(name), b"not a package").unwrap();
            }
        }
        assert!(
            packaged_tool_path_in_prefixes(ProofTool::Clean, &[prefix.path().to_path_buf()])
                .is_none()
        );
    }

    #[test]
    fn first_installed_prefix_wins_and_directories_are_not_executables() {
        let first = tempfile::tempdir().unwrap();
        let second = tempfile::tempdir().unwrap();
        let prefixes = [first.path().to_path_buf(), second.path().to_path_buf()];
        let fallback = put_tool(second.path(), "current", ProofTool::Clean, b"second");
        std::fs::create_dir_all(tool_path(first.path(), "current", ProofTool::Clean)).unwrap();
        assert_eq!(
            packaged_tool_path_in_prefixes(ProofTool::Clean, &prefixes),
            Some(fallback)
        );
        std::fs::remove_dir_all(tool_path(first.path(), "current", ProofTool::Clean)).unwrap();
        let preferred = put_tool(first.path(), "current", ProofTool::Clean, b"first");
        assert_eq!(
            packaged_tool_path_in_prefixes(ProofTool::Clean, &prefixes),
            Some(preferred)
        );
    }

    #[cfg(unix)]
    #[test]
    fn package_update_changes_binary_identity_without_hashing_the_shim() {
        let prefix = tempfile::tempdir().unwrap();
        let first = put_tool(prefix.path(), "1", ProofTool::Clean, b"checker version one");
        let second = put_tool(prefix.path(), "2", ProofTool::Clean, b"checker version two");
        let current = prefix.path().join("store/clean/current");
        std::os::unix::fs::symlink("1", &current).unwrap();
        let resolve = || {
            packaged_tool_path_in_prefixes(ProofTool::Clean, &[prefix.path().to_path_buf()])
                .unwrap()
        };
        let before = resolve();
        assert_eq!(before, first);
        let before_hash = crate::lrat_cert::checker_binary_sha256(&before).unwrap();
        std::fs::remove_file(&current).unwrap();
        std::os::unix::fs::symlink("2", &current).unwrap();
        let after = resolve();
        assert_eq!(after, second);
        assert_ne!(
            before_hash,
            crate::lrat_cert::checker_binary_sha256(&after).unwrap()
        );
        assert_eq!(std::fs::read(before).unwrap(), b"checker version one");
    }
}
