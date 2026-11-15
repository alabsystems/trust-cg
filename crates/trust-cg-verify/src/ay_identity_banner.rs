// trust-cg-verify/ay_identity_banner.rs - parse the build identity AY stamps
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Shared VERBATIM by the library (`crate::ay_identity`) and by this crate's
// `build.rs` (through `#[path]`), so the identity the build RECORDS and the
// identity a running process COMPARES are read by one parser. Keep it free of
// crate dependencies for that reason.

/// The build identity an `ay` binary reports on `--version`.
///
/// AY's own build script stamps these lines from the source commit it was
/// built from (measured on the Trust 9178 bundle's `bin/ay`):
///
/// ```text
/// ay 0.26.0+build.9624.075a482aec84e441918d935743957876bd24afdb@2026-09-16T06:27:30Z
/// build.version=0.26.0
/// build.increment=9624
/// build.commit=075a482aec84e441918d935743957876bd24afdb
/// build.datetime_utc=2026-09-16T06:27:30Z
/// build.stamp=0.26.0+build.9624.075a482aec84e441918d935743957876bd24afdb@2026-09-16T06:27:30Z
/// ```
///
/// The COMMIT is the identity: two builds of one commit at different times
/// (a bundle and a stage2 sysroot) are the same solver source, while the
/// datetime is not part of it. A dirty build has no source identity at all and
/// is refused, never recorded.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AyBuildIdentity {
    commit: String,
    version: String,
    increment: String,
}

impl AyBuildIdentity {
    /// The 40-hex source commit the binary was built from.
    pub fn commit(&self) -> &str {
        &self.commit
    }

    /// The package version the binary reports.
    pub fn version(&self) -> &str {
        &self.version
    }

    /// The build increment the binary reports.
    pub fn increment(&self) -> &str {
        &self.increment
    }

    /// One-line human form used in diagnostics and recorded routes.
    pub fn describe(&self) -> String {
        format!(
            "ay {} build {} commit {}",
            self.version, self.increment, self.commit
        )
    }

    /// Rebuild an identity from recorded fields, applying the same validation
    /// as [`parse_ay_version_banner`].
    pub fn from_recorded_fields(
        commit: &str,
        version: &str,
        increment: &str,
    ) -> Result<Self, String> {
        validate_fields(commit, version, increment)?;
        Ok(Self {
            commit: commit.to_owned(),
            version: version.to_owned(),
            increment: increment.to_owned(),
        })
    }
}

fn is_commit(text: &str) -> bool {
    text.len() == 40
        && text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn is_plain_field(text: &str) -> bool {
    !text.is_empty()
        && text
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-' | b'_' | b'+'))
}

fn validate_fields(commit: &str, version: &str, increment: &str) -> Result<(), String> {
    if commit.contains("dirty") {
        return Err(format!(
            "build.commit={commit} is a DIRTY build, which has no source identity"
        ));
    }
    if !is_commit(commit) {
        return Err(format!(
            "build.commit={commit:?} is not a 40-character lowercase hex commit"
        ));
    }
    if !is_plain_field(version) {
        return Err(format!("build.version={version:?} is malformed"));
    }
    if increment.is_empty() || !increment.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!(
            "build.increment={increment:?} is not a decimal build number"
        ));
    }
    // AY numbers a build by `git rev-list --count HEAD`; a build without git
    // history (a `git archive` export) reports 0, whatever commit it was then
    // told it came from. Such a banner names no build.
    if increment.bytes().all(|byte| byte == b'0') {
        return Err(format!(
            "build.increment={increment} is an unnumbered build (built without git history, \
             e.g. from a source export), which has no build identity"
        ));
    }
    Ok(())
}

/// Parse `ay --version` output (stdout and stderr concatenated).
///
/// Fail closed: each of `build.version`, `build.increment`, `build.commit` and
/// `build.stamp` must occur EXACTLY once, the commit must be 40 lowercase hex
/// digits, and the stamp must spell the same version, increment and commit. A
/// banner that is missing a field, repeats one, disagrees with itself, or
/// marks the build dirty identifies no solver.
pub fn parse_ay_version_banner(output: &str) -> Result<AyBuildIdentity, String> {
    let mut version = None;
    let mut increment = None;
    let mut commit = None;
    let mut stamp = None;
    for line in output.lines().map(str::trim) {
        let slots = [
            ("build.version", &mut version),
            ("build.increment", &mut increment),
            ("build.commit", &mut commit),
            ("build.stamp", &mut stamp),
        ];
        for (name, slot) in slots {
            let Some(value) = line
                .strip_prefix(name)
                .and_then(|rest| rest.strip_prefix('='))
            else {
                continue;
            };
            if slot.is_some() {
                return Err(format!("`{name}=` occurs more than once"));
            }
            *slot = Some(value.to_owned());
        }
    }
    let field = |name: &str, value: Option<String>| {
        value.ok_or_else(|| format!("no `{name}=` line (not an AY build banner)"))
    };
    let version = field("build.version", version)?;
    let increment = field("build.increment", increment)?;
    let commit = field("build.commit", commit)?;
    let stamp = field("build.stamp", stamp)?;
    validate_fields(&commit, &version, &increment)?;
    let expected_prefix = format!("{version}+build.{increment}.{commit}@");
    if !stamp.starts_with(&expected_prefix) {
        return Err(format!(
            "build.stamp={stamp:?} disagrees with build.version/increment/commit \
             (expected it to start with {expected_prefix:?})"
        ));
    }
    Ok(AyBuildIdentity {
        commit,
        version,
        increment,
    })
}
