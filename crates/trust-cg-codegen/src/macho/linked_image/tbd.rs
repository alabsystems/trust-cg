// trust-cg-codegen/macho/linked_image/tbd.rs - export lists from TAPI v4 text stubs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Reads the exported names of a TAPI text-based stub (`.tbd`, version 4
//! YAML), the form in which the macOS SDK ships libSystem: every document's
//! `install-name`, its `reexported-libraries`, and the `symbols`,
//! `weak-symbols`, `thread-local-symbols` and Objective-C class lists of the
//! `exports` and `reexports` groups whose targets include an arm64 macOS
//! slice. A library's export list is its own names plus those of every
//! library it re-exports within the same file. Other TAPI versions (v5 is
//! JSON) are refused by name.

use std::collections::{BTreeMap, BTreeSet};

/// One document's install name, re-exported libraries and exported names.
#[derive(Debug, Default)]
struct Document {
    install_name: String,
    reexported: Vec<String>,
    symbols: BTreeSet<String>,
    thread_locals: BTreeSet<String>,
}

/// Items of a `[ a, 'b', c ]` flow sequence.
fn flow_items(text: &str) -> Vec<String> {
    text.trim()
        .trim_start_matches('[')
        .trim_end_matches(']')
        .split(',')
        .map(|item| item.trim().trim_matches('\'').trim_matches('"').to_string())
        .filter(|item| !item.is_empty())
        .collect()
}

fn arm64_macos(targets: &[String]) -> bool {
    targets
        .iter()
        .any(|target| target.starts_with("arm64") && target.ends_with("-macos"))
}

/// Parse every document of a TAPI v4 `.tbd`.
fn documents(text: &str) -> Result<Vec<Document>, String> {
    let mut documents = Vec::new();
    let mut current: Option<Document> = None;
    let mut top_key = String::new();
    let mut group_targets_ok = false;
    let mut lines = text.lines().peekable();
    while let Some(line) = lines.next() {
        if line.starts_with("---") {
            if let Some(document) = current.take() {
                documents.push(document);
            }
            current = Some(Document::default());
            top_key.clear();
            continue;
        }
        if line.starts_with("...") {
            if let Some(document) = current.take() {
                documents.push(document);
            }
            continue;
        }
        let Some(document) = current.as_mut() else {
            continue;
        };
        let trimmed = line.trim_start();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let indented = line.len() != trimmed.len();
        let entry = trimmed.trim_start_matches("- ").trim_start();
        let Some((key, rest)) = entry.split_once(':') else {
            continue;
        };
        let key = key.trim();
        // A flow sequence may continue over several lines.
        let mut value = rest.trim().to_string();
        if value.starts_with('[') {
            while !value.contains(']') {
                let Some(next) = lines.next() else {
                    return Err(format!("unterminated list for `{key}`"));
                };
                value.push(' ');
                value.push_str(next.trim());
            }
        }
        if !indented {
            top_key = key.to_string();
            match key {
                "tbd-version" if value != "4" => {
                    return Err(format!(
                        "tbd-version {value} is not modeled (version 4 YAML only)"
                    ));
                }
                "install-name" => {
                    document.install_name = value.trim_matches('\'').trim_matches('"').to_string()
                }
                _ => {}
            }
            continue;
        }
        match (top_key.as_str(), key) {
            ("reexported-libraries", "libraries") => {
                document.reexported.extend(flow_items(&value));
            }
            ("exports" | "reexports", "targets") => {
                group_targets_ok = arm64_macos(&flow_items(&value));
            }
            ("exports" | "reexports", "symbols" | "weak-symbols") if group_targets_ok => {
                document.symbols.extend(flow_items(&value));
            }
            ("exports" | "reexports", "thread-local-symbols") if group_targets_ok => {
                let names = flow_items(&value);
                document.thread_locals.extend(names.iter().cloned());
                document.symbols.extend(names);
            }
            ("exports" | "reexports", "objc-classes") if group_targets_ok => {
                for class in flow_items(&value) {
                    document.symbols.insert(format!("_OBJC_CLASS_$_{class}"));
                    document
                        .symbols
                        .insert(format!("_OBJC_METACLASS_$_{class}"));
                }
            }
            _ => {}
        }
    }
    if let Some(document) = current.take() {
        documents.push(document);
    }
    if documents.is_empty() {
        return Err("no TAPI documents".into());
    }
    if let Some(document) = documents
        .iter()
        .find(|document| document.install_name.is_empty())
    {
        return Err(format!(
            "a TAPI document without an install-name ({} names)",
            document.symbols.len()
        ));
    }
    Ok(documents)
}

/// `(install name, names it exports, thread-local names)` of the first
/// document of `text`, including every library it re-exports from the same
/// file.
pub(super) fn tbd_exports(
    text: &str,
) -> Result<(String, BTreeSet<String>, BTreeSet<String>), String> {
    let documents = documents(text)?;
    let by_name: BTreeMap<&str, &Document> = documents
        .iter()
        .map(|document| (document.install_name.as_str(), document))
        .collect();
    let root = &documents[0];
    let mut names = BTreeSet::new();
    let mut thread_locals = BTreeSet::new();
    let mut pending = vec![root.install_name.as_str()];
    let mut seen = BTreeSet::new();
    while let Some(install_name) = pending.pop() {
        if !seen.insert(install_name) {
            continue;
        }
        let document = by_name.get(install_name).ok_or_else(|| {
            format!("re-exported library {install_name} has no document in the stub")
        })?;
        names.extend(document.symbols.iter().cloned());
        thread_locals.extend(document.thread_locals.iter().cloned());
        pending.extend(document.reexported.iter().map(String::as_str));
    }
    Ok((root.install_name.clone(), names, thread_locals))
}
