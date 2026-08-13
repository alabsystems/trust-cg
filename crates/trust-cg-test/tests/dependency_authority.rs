//! Regression checks for cross-repository dependency authority.
//!
//! Committed manifests and lockfiles must resolve independently of this
//! machine's sibling-checkout layout. Mutable path redirects are confined to a
//! gitignored, explicitly selected Cargo config.
//!
//! Revisions are DERIVED from the committed manifests and lockfiles, never
//! hardcoded here. Literals went stale on every dependency bump, which both
//! reddened this test and -- because transform T1 had to rewrite those literals
//! for the public export -- left the release gate unrunnable until somebody
//! noticed. trust-ir drifted `3fafb624 -> b3fcd5d6 -> e92e77a` that way.
//!
//! What this test owns is therefore internal consistency: exactly one revision
//! per upstream repo, agreed by every manifest and every lockfile, with no path
//! fallback anywhere. Deriving the expected value from one committed pin makes
//! that first read a tautology by construction; the content is in the agreement
//! across the other five-plus readers, which is precisely the drift that used to
//! ship (a `fuzz/` lockfile once floated to an older trust-ir on its own).
//!
//! Whether a revision is *audited* is deliberately not asserted here. That lives
//! where the attestation lives: `publish/transforms.sh` transform T1 fails closed
//! unless the resolved revision has a verified, tree-attested entry in the
//! release mapping ledger.

use std::fs;
use std::path::{Path, PathBuf};

const LOCKS: [&str; 3] = [
    "Cargo.lock",
    "crates/rustc-codegen-trust-cg/Cargo.lock",
    "fuzz/Cargo.lock",
];

/// A `git` + `rev` source identity read off committed dependency authority.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Pin {
    url: String,
    rev: String,
}

impl Pin {
    /// The `Cargo.lock` `source` spelling of this identity.
    fn lock_source(&self) -> String {
        format!("git+{}?rev={}#{}", self.url, self.rev, self.rev)
    }
}

fn assert_full_sha(rev: &str, context: &str) {
    assert_eq!(
        rev.len(),
        40,
        "{context}: rev must be a full 40-char sha: {rev}"
    );
    assert!(
        rev.chars().all(|character| character.is_ascii_hexdigit()),
        "{context}: rev must be hexadecimal: {rev}"
    );
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("canonicalize repository root")
}

fn read_toml(relative: &str) -> toml::Value {
    let path = repo_root().join(relative);
    let text = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    toml::from_str(&text).unwrap_or_else(|error| panic!("parse {}: {error}", path.display()))
}

fn dependency_table<'a>(
    manifest: &'a toml::Value,
    table_path: &[&str],
    name: &str,
    context: &str,
) -> &'a toml::Table {
    let mut node = manifest;
    for key in table_path {
        node = node
            .get(key)
            .unwrap_or_else(|| panic!("{context}: missing `{key}` table"));
    }
    node.get(name)
        .unwrap_or_else(|| panic!("{context}: missing `{name}` dependency"))
        .as_table()
        .unwrap_or_else(|| panic!("{context}: `{name}` must use table notation"))
}

/// Read an exact `git`/`rev` pin out of a committed manifest.
///
/// Rejects a `path` key outright: a path fallback would let this machine's
/// sibling checkout stand in for the committed authority.
fn manifest_pin(relative: &str, table_path: &[&str], name: &str) -> Pin {
    let context = format!("{relative} {name}");
    let manifest = read_toml(relative);
    let dep = dependency_table(&manifest, table_path, name, &context);
    assert!(
        dep.get("path").is_none(),
        "{context}: committed dependency authority must not contain a path fallback"
    );
    let url = dep
        .get("git")
        .and_then(toml::Value::as_str)
        .unwrap_or_else(|| panic!("{context}: must be an exact Git dependency"));
    let rev = dep
        .get("rev")
        .and_then(toml::Value::as_str)
        .unwrap_or_else(|| panic!("{context}: must pin an exact rev"));
    assert_full_sha(rev, &context);
    Pin {
        url: url.to_string(),
        rev: rev.to_string(),
    }
}

fn assert_manifest_pin(relative: &str, table_path: &[&str], name: &str, expected: &Pin) {
    assert_eq!(
        &manifest_pin(relative, table_path, name),
        expected,
        "{relative} `{name}` must bind the same source identity as the rest of the tree"
    );
}

fn lock_packages(lock_path: &str) -> Vec<toml::Value> {
    read_toml(lock_path)["package"]
        .as_array()
        .unwrap_or_else(|| panic!("{lock_path}: missing package array"))
        .clone()
}

/// Parse the single `git+<url>?rev=<rev>#<rev>` source for one locked package.
fn lock_pin(lock_path: &str, package_name: &str) -> Pin {
    let matching: Vec<_> = lock_packages(lock_path)
        .into_iter()
        .filter(|package| package["name"].as_str() == Some(package_name))
        .collect();
    assert_eq!(
        matching.len(),
        1,
        "{lock_path} must contain exactly one {package_name} package"
    );
    let context = format!("{lock_path} {package_name}");
    let source = matching[0]["source"]
        .as_str()
        .unwrap_or_else(|| panic!("{context}: locked package has no source"));
    parse_lock_source(source, &context)
}

fn parse_lock_source(source: &str, context: &str) -> Pin {
    let body = source
        .strip_prefix("git+")
        .unwrap_or_else(|| panic!("{context}: must resolve from an exact Git source: {source}"));
    let (url, tail) = body
        .split_once("?rev=")
        .unwrap_or_else(|| panic!("{context}: Git source carries no `?rev=`: {source}"));
    let (rev, fragment) = tail
        .split_once('#')
        .unwrap_or_else(|| panic!("{context}: Git source carries no `#<sha>`: {source}"));
    // Cargo writes the resolved commit twice; a mismatch means the pin was a
    // branch or tag that moved, not an immutable revision.
    assert_eq!(
        rev, fragment,
        "{context}: Git source rev and fragment disagree: {source}"
    );
    assert_full_sha(rev, context);
    Pin {
        url: url.to_string(),
        rev: rev.to_string(),
    }
}

fn assert_lock_pin(lock_path: &str, package_name: &str, expected: &Pin) {
    assert_eq!(
        lock_pin(lock_path, package_name).lock_source(),
        expected.lock_source(),
        "{lock_path} must bind {package_name} to the tree's source identity"
    );
}

/// Every `<prefix>*` package in the lock must share one source identity.
fn assert_lock_family(lock_path: &str, package_prefix: &str, expected: &Pin) {
    let packages: Vec<_> = lock_packages(lock_path)
        .into_iter()
        .filter(|package| {
            package["name"]
                .as_str()
                .is_some_and(|name| name.starts_with(package_prefix))
        })
        .collect();
    assert!(
        !packages.is_empty(),
        "{lock_path} must contain the {package_prefix} dependency family"
    );
    for package in packages {
        let name = package["name"].as_str().expect("package name");
        assert_eq!(
            package["source"].as_str(),
            Some(expected.lock_source().as_str()),
            "{lock_path} must bind {name} to the tree's source identity"
        );
    }
}

/// The workspace trust-ir pin is the tree's TrustIR authority.
fn trust_ir_authority() -> Pin {
    manifest_pin("Cargo.toml", &["workspace", "dependencies"], "trust-ir")
}

/// The regalloc ay-pb pin is the tree's AY authority.
fn ay_authority() -> Pin {
    manifest_pin(
        "crates/trust-cg-regalloc/Cargo.toml",
        &["dependencies"],
        "ay-pb",
    )
}

/// Clean has no manifest pin -- it reaches the graph transitively through
/// trust-ir -- so the root lockfile is the only place its identity is stated.
fn clean_authority() -> Pin {
    lock_pin("Cargo.lock", "clean-kernel")
}

#[test]
fn committed_manifests_bind_cross_repo_sources_exactly() {
    let trust_ir = trust_ir_authority();
    assert_manifest_pin(
        "Cargo.toml",
        &["workspace", "dependencies"],
        "trust-ir-build",
        &trust_ir,
    );
    assert_manifest_pin(
        "crates/rustc-codegen-trust-cg/Cargo.toml",
        &["dependencies"],
        "trust-ir",
        &trust_ir,
    );

    let ay = ay_authority();
    let regalloc = read_toml("crates/trust-cg-regalloc/Cargo.toml");
    let ay_pb = dependency_table(&regalloc, &["dependencies"], "ay-pb", "ay-pb");
    assert_eq!(
        ay_pb.get("optional").and_then(toml::Value::as_bool),
        Some(true),
        "AY allocator must remain opt-in"
    );
    assert_eq!(
        ay_pb.get("default-features").and_then(toml::Value::as_bool),
        Some(false),
        "AY default features must remain disabled"
    );
    let enables_cycle = ay_pb
        .get("features")
        .and_then(toml::Value::as_array)
        .into_iter()
        .flatten()
        .any(|feature| feature.as_str() == Some("trust-cg-backend"));
    assert!(
        !enables_cycle,
        "trust-cg must not enable AY's trust-cg-backend cycle edge"
    );

    // `ay-sat` exists in this manifest only to unify one feature into the SAT
    // core that `ay-pb` links.  It must stay on the same revision as `ay-pb`,
    // stay opt-in, and activate nothing beyond the reviewed raw-pointer BCP
    // traversal: `jit` would enable ay-sat's own retired JIT BCP path, and
    // `trust-cg-backend` would re-enter trust-cg and close a dependency cycle.
    assert_manifest_pin(
        "crates/trust-cg-regalloc/Cargo.toml",
        &["dependencies"],
        "ay-sat",
        &ay,
    );
    let ay_sat = dependency_table(&regalloc, &["dependencies"], "ay-sat", "ay-sat");
    assert_eq!(
        ay_sat.get("optional").and_then(toml::Value::as_bool),
        Some(true),
        "AY SAT feature-unification dependency must remain opt-in"
    );
    assert_eq!(
        ay_sat
            .get("default-features")
            .and_then(toml::Value::as_bool),
        Some(false),
        "AY SAT default features must remain disabled"
    );
    let sat_features: Vec<&str> = ay_sat
        .get("features")
        .and_then(toml::Value::as_array)
        .expect("ay-sat features")
        .iter()
        .filter_map(toml::Value::as_str)
        .collect();
    assert_eq!(
        sat_features,
        ["raw-pointer-bcp"],
        "only the reviewed raw-pointer BCP feature may be activated"
    );

    let ay_regalloc: Vec<&str> = regalloc["features"]["ay-regalloc"]
        .as_array()
        .expect("ay-regalloc feature list")
        .iter()
        .filter_map(toml::Value::as_str)
        .collect();
    assert_eq!(
        ay_regalloc,
        ["dep:ay-pb", "dep:ay-sat", "dep:trust-cg-process-env"],
        "ay-regalloc must activate the optimizer, the ay-sat feature-unification \
         pin, and the thread-local environment adapter"
    );
}

#[test]
fn committed_lockfiles_bind_cross_repo_sources_exactly() {
    let trust_ir = trust_ir_authority();
    let clean = clean_authority();

    // Every independently resolved Cargo root must consume the same TrustIR
    // authority.  In particular, `fuzz/` is deliberately outside the main
    // workspace and owns a lockfile of its own; omitting it here previously
    // allowed that compile-check lane to drift to an older TrustIR revision.
    for lock in LOCKS {
        assert_lock_pin(lock, "trust-ir", &trust_ir);
        assert_lock_pin(lock, "trust-ir-build", &trust_ir);
        assert_lock_pin(lock, "trust-ir-giveback", &trust_ir);
        assert_lock_pin(lock, "clean-kernel", &clean);
    }

    // The standalone fuzz graph does not enable the optional AY allocator.
    let ay = ay_authority();
    for lock in ["Cargo.lock", "crates/rustc-codegen-trust-cg/Cargo.lock"] {
        assert_lock_pin(lock, "ay-pb", &ay);
        assert_lock_pin(lock, "ay-sat", &ay);
        assert_lock_family(lock, "ay-", &ay);
    }
}

#[test]
fn public_dependency_authority_needs_no_local_redirect() {
    let config = read_toml(".cargo/config.toml");
    assert!(
        config.get("patch").is_none(),
        "public Cargo config must not redirect mapped dependencies to sibling paths"
    );
}
