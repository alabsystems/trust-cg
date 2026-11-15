// trust-cg-codegen/tests/llvm_tool_discovery.rs - external LLVM tool lookup
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The search order of `common/llvm_tools.rs`, over fixture directory
//! layouts: the DWARF/CFI/section suites need `llvm-dwarfdump` and
//! `llvm-readelf`, and a host that has them only in a Trust compiler build or
//! behind `llvm-config` must still find them (TRUSTCG-24).

#[path = "common/llvm_tools.rs"]
mod llvm_tools;

use std::path::{Path, PathBuf};

use llvm_tools::ToolSearch;

const TOOL: &str = "llvm-dwarfdump";

struct Fixture {
    root: PathBuf,
}

impl Fixture {
    fn new(test: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "trust_cg_llvm_tool_discovery_{test}_{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&root).expect("fixture root");
        Self {
            root: root.canonicalize().expect("canonical fixture root"),
        }
    }

    fn dir(&self, relative: &str) -> PathBuf {
        let dir = self.root.join(relative);
        std::fs::create_dir_all(&dir).expect("fixture dir");
        dir
    }

    /// An executable file named `name` in `relative`, with `body` as its script.
    fn tool(&self, relative: &str, name: &str, body: &str) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let path = self.dir(relative).join(name);
        std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).expect("fixture tool");
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
            .expect("fixture tool mode");
        path
    }

    /// A search that sees only this fixture: no install directories, and
    /// `PATH` limited to `path`.
    fn search(&self, checkout: &str, path: &[&Path]) -> ToolSearch {
        ToolSearch {
            llvm_bin: None,
            install_dirs: Vec::new(),
            path: Some(std::env::join_paths(path).expect("fixture PATH")),
            llvm_config: None,
            checkout: self.dir(checkout),
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}

#[test]
fn a_sibling_trust_build_supplies_the_tools() {
    let fixture = Fixture::new("sibling");
    let host = format!("{}-fixture-host", std::env::consts::ARCH);
    let tool = fixture.tool(&format!("trust/build/{host}/llvm/bin"), TOOL, "exit 0");
    let search = fixture.search("trust-cg", &[]);
    assert_eq!(search.find(TOOL), Some(tool));
}

#[test]
fn the_superproject_build_supplies_a_first_party_submodule() {
    let fixture = Fixture::new("submodule");
    let tool = fixture.tool("trust/build/some-host/llvm/bin", TOOL, "exit 0");
    let search = fixture.search("trust/first-party/trust-cg", &[]);
    assert_eq!(search.find(TOOL), Some(tool));
}

#[test]
fn llvm_config_bindir_supplies_the_tools() {
    let fixture = Fixture::new("llvm_config");
    let bindir = fixture.dir("llvm/bin");
    let tool = fixture.tool("llvm/bin", TOOL, "exit 0");
    let config_dir = fixture.dir("config");
    fixture.tool(
        "config",
        "llvm-config",
        &format!(
            "[ \"$1\" = --bindir ] || exit 3\nprintf '%s\\n' '{}'",
            bindir.display()
        ),
    );
    let from_path = fixture.search("trust-cg", &[&config_dir]);
    assert_eq!(from_path.find(TOOL), Some(tool.clone()));

    let explicit = fixture.tool(
        "elsewhere",
        "my-llvm-config",
        &format!(
            "[ \"$1\" = --bindir ] || exit 3\nprintf '%s\\n' '{}'",
            bindir.display()
        ),
    );
    let mut search = fixture.search("trust-cg", &[]);
    search.llvm_config = Some(explicit.into_os_string());
    assert_eq!(search.find(TOOL), Some(tool));
}

#[test]
fn a_failing_llvm_config_is_not_a_directory() {
    let fixture = Fixture::new("llvm_config_fails");
    fixture.tool("llvm/bin", TOOL, "exit 0");
    let config_dir = fixture.dir("config");
    fixture.tool("config", "llvm-config", "echo /nowhere; exit 1");
    let search = fixture.search("trust-cg", &[&config_dir]);
    assert_eq!(search.find(TOOL), None);
}

#[test]
fn the_explicit_directory_and_path_win_over_derived_locations() {
    let fixture = Fixture::new("precedence");
    fixture.tool("trust/build/host/llvm/bin", TOOL, "exit 0");
    let on_path = fixture.tool("path", TOOL, "exit 0");
    let explicit = fixture.tool("explicit", TOOL, "exit 0");
    let path_dir = fixture.dir("path");

    let mut search = fixture.search("trust-cg", &[&path_dir]);
    assert_eq!(search.find(TOOL), Some(on_path));
    search.llvm_bin = Some(fixture.dir("explicit").into_os_string());
    assert_eq!(search.find(TOOL), Some(explicit));
}

#[test]
fn a_versioned_name_on_path_is_found() {
    let fixture = Fixture::new("versioned");
    let tool = fixture.tool("path", &format!("{TOOL}-18"), "exit 0");
    let search = fixture.search("trust-cg", &[&fixture.dir("path")]);
    assert_eq!(search.find(TOOL), Some(tool));
}

#[test]
fn nothing_found_is_none() {
    let fixture = Fixture::new("none");
    let search = fixture.search("trust-cg", &[&fixture.dir("empty")]);
    assert_eq!(search.find(TOOL), None);
}
