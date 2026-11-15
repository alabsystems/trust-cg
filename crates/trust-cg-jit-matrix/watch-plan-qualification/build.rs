// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Native content-observer fixture over an explicit original watch inventory.
//! The input is declarations only; no stored snapshot or receipt is consumed.

#[path = "../src/pipeline_watch_plan.rs"]
mod pipeline_watch_plan;

use std::fs;
use std::io::{self, Read as _};
use std::path::{Path, PathBuf};

fn main() -> io::Result<()> {
    println!("cargo:rerun-if-env-changed=CG_WATCH_PLAN_INPUT");
    println!("cargo:rerun-if-env-changed=CG_WATCH_PLAN_ROOT");
    let input = std::env::var_os("CG_WATCH_PLAN_INPUT");
    let root = std::env::var_os("CG_WATCH_PLAN_ROOT");
    let (input, root) = match (input, root) {
        (Some(input), Some(root)) => (input, root),
        // Source unit tests need no retained native world. The actual native
        // observation requires both explicit data inputs, never an implicit donor.
        (None, None) => return Ok(()),
        _ => return Err(io::Error::other("both watch inventory inputs are required")),
    };
    let input = PathBuf::from(input);
    let root = PathBuf::from(root);
    if !input.is_absolute() || !root.is_absolute() {
        return Err(io::Error::other("watch inventory inputs must be absolute"));
    }
    let mut text = String::new();
    fs::File::open(&input)?
        .take(16 * 1024 * 1024 + 1)
        .read_to_string(&mut text)?;
    if text.len() > 16 * 1024 * 1024 || !text.ends_with('\n') {
        return Err(io::Error::other(
            "watch inventory exceeds its bound or is incomplete",
        ));
    }
    let mut paths = Vec::new();
    for line in text.lines() {
        let path = line
            .strip_prefix("cargo:rerun-if-changed=")
            .ok_or_else(|| io::Error::other("unexpected original watch inventory line"))?;
        if path.is_empty() || path.len() > 32 * 1024 || paths.len() >= 16_384 {
            return Err(io::Error::other("watch inventory path bound"));
        }
        let path = Path::new(path);
        paths.push(if path.is_absolute() {
            path.to_owned()
        } else {
            root.join(path)
        });
    }
    if paths.is_empty() {
        return Err(io::Error::other("empty original watch inventory"));
    }
    let original = paths.len();
    pipeline_watch_plan::compact_recursive_watches(&mut paths);
    println!("cargo:rerun-if-changed={}", input.display());
    for path in &paths {
        println!("cargo:rerun-if-changed={}", path.display());
    }
    let output = PathBuf::from(
        std::env::var_os("OUT_DIR").ok_or_else(|| io::Error::other("Cargo OUT_DIR is missing"))?,
    );
    fs::write(
        output.join("watch-counts.txt"),
        format!("{original}\n{}\n", paths.len()),
    )
}
