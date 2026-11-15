//! Validation of a local overlay toolchain's manifest (`<sysroot>/overlay.json`).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! `build.rs` includes this file (`#[path]`) to decide whether to record an
//! overlay; the library compiles it only for its unit tests, so the exact rule
//! `build.rs` applies is tested. It is pure: the caller reads the manifest and digests the files.
//! It must not name `crate::` paths, because `build.rs` is another crate root.
//!
//! The manifest schema is the one `scripts/assemble_trust_overlay.py` writes.
//! A manifest is accepted only when it names exactly the recorded `bin/ay`
//! (digest, commit and build number) and the current bytes of `bin/clean`;
//! any disagreement is a refusal, and `build.rs` then records nothing, so a
//! swapped `bin/ay` or `bin/clean` cannot run under the manifest's name.

/// Manifest schema `scripts/assemble_trust_overlay.py` writes.
pub(crate) const OVERLAY_SCHEMA: &str = "trust-cg.trust-overlay.v1";

/// The recorded AY a manifest must name.
pub(crate) struct RecordedAy<'a> {
    pub(crate) sha256: &'a str,
    pub(crate) commit: &'a str,
    pub(crate) increment: &'a str,
    /// Human-readable banner line, for the refusal text.
    pub(crate) describe: String,
}

/// An accepted overlay.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ValidatedOverlay {
    pub(crate) manifest_sha256: String,
    pub(crate) clean_sha256: String,
    pub(crate) clean_commit: String,
}

fn is_lower_hex(text: &str, len: usize) -> bool {
    text.len() == len
        && text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// Accept `manifest` (its raw bytes) for a sysroot whose `bin/ay` has the
/// recorded identity `ay` (`None`: none was recorded) and whose `bin/clean`
/// digested to `clean_found` (`Err`: it could not be digested). The error is
/// the refusal reason, without the manifest path.
pub(crate) fn validate_overlay_manifest(
    manifest: &[u8],
    ay: Option<&RecordedAy<'_>>,
    clean_found: Result<&str, &str>,
) -> Result<ValidatedOverlay, String> {
    let manifest_sha256 = {
        use sha2::{Digest, Sha256};
        format!("{:x}", Sha256::digest(manifest))
    };
    let value: serde_json::Value = serde_json::from_slice(manifest)
        .map_err(|error| format!("the manifest is not JSON: {error}"))?;
    let text = |pointer: &str| value.pointer(pointer).and_then(serde_json::Value::as_str);
    if text("/schema") != Some(OVERLAY_SCHEMA) {
        return Err(format!("the manifest schema is not {OVERLAY_SCHEMA}"));
    }
    let Some(ay) = ay else {
        return Err("its bin/ay has no recorded identity".into());
    };
    if text("/ay/sha256") != Some(ay.sha256)
        || text("/ay/commit") != Some(ay.commit)
        || text("/ay/increment") != Some(ay.increment)
    {
        return Err(format!(
            "the manifest's AY (sha256 {:?}, commit {:?}, build {:?}) is not bin/ay (sha256 {}, {})",
            text("/ay/sha256"),
            text("/ay/commit"),
            text("/ay/increment"),
            ay.sha256,
            ay.describe
        ));
    }
    let (Some(clean_sha256), Some(clean_commit)) =
        (text("/clean/sha256"), text("/clean/source/commit"))
    else {
        return Err("the manifest names no Clean sha256 and source commit".into());
    };
    if !is_lower_hex(clean_sha256, 64) || !is_lower_hex(clean_commit, 40) {
        return Err("the manifest's Clean sha256 or source commit is malformed".into());
    }
    let found = clean_found.map_err(|error| format!("cannot digest bin/clean: {error}"))?;
    if found != clean_sha256 {
        return Err(format!(
            "bin/clean has sha256 {found}, but the manifest names {clean_sha256}"
        ));
    }
    Ok(ValidatedOverlay {
        manifest_sha256,
        clean_sha256: clean_sha256.to_owned(),
        clean_commit: clean_commit.to_owned(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const AY_SHA: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const CLEAN_SHA: &str = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
    const CLEAN_COMMIT: &str = "5390f432b0000000000000000000000000000000";

    fn ay() -> RecordedAy<'static> {
        RecordedAy {
            sha256: AY_SHA,
            commit: "0b670d840",
            increment: "11378",
            describe: "ay 0.27.0 build 11378".into(),
        }
    }

    fn manifest(edit: impl FnOnce(&mut serde_json::Value)) -> Vec<u8> {
        let mut value = serde_json::json!({
            "schema": OVERLAY_SCHEMA,
            "ay": {"sha256": AY_SHA, "commit": "0b670d840", "increment": "11378"},
            "clean": {"sha256": CLEAN_SHA, "source": {"commit": CLEAN_COMMIT}},
        });
        edit(&mut value);
        serde_json::to_vec(&value).unwrap()
    }

    #[test]
    fn a_manifest_naming_both_files_is_accepted_and_digested() {
        let bytes = manifest(|_| {});
        let overlay = validate_overlay_manifest(&bytes, Some(&ay()), Ok(CLEAN_SHA)).unwrap();
        use sha2::{Digest, Sha256};
        assert_eq!(
            overlay.manifest_sha256,
            format!("{:x}", Sha256::digest(&bytes))
        );
        assert_eq!(overlay.clean_sha256, CLEAN_SHA);
        assert_eq!(overlay.clean_commit, CLEAN_COMMIT);
    }

    /// Every disagreement between the manifest and the files is a refusal
    /// (and `build.rs` then records no AY at all).
    #[test]
    fn a_manifest_that_does_not_name_the_files_is_refused() {
        let other = "d".repeat(64);
        let refusal = |bytes: Vec<u8>, ay: Option<&RecordedAy<'_>>, clean: Result<&str, &str>| {
            validate_overlay_manifest(&bytes, ay, clean).unwrap_err()
        };
        // bin/clean swapped after assembly.
        let reason = refusal(manifest(|_| {}), Some(&ay()), Ok(&other));
        assert!(reason.contains("bin/clean has sha256"), "{reason}");
        // bin/clean unreadable.
        let reason = refusal(manifest(|_| {}), Some(&ay()), Err("permission denied"));
        assert!(reason.contains("cannot digest bin/clean"), "{reason}");
        // bin/ay swapped (digest), or a banner the manifest does not name.
        for (pointer, value) in [
            ("/ay/sha256", other.as_str()),
            ("/ay/commit", "57a37e513"),
            ("/ay/increment", "11377"),
        ] {
            let bytes = manifest(|m| *m.pointer_mut(pointer).unwrap() = value.into());
            let reason = refusal(bytes, Some(&ay()), Ok(CLEAN_SHA));
            assert!(reason.contains("is not bin/ay"), "{pointer}: {reason}");
        }
        // No recorded AY identity.
        let reason = refusal(manifest(|_| {}), None, Ok(CLEAN_SHA));
        assert!(reason.contains("no recorded identity"), "{reason}");
        // Wrong schema, not JSON, malformed or missing Clean fields.
        let bytes = manifest(|m| m["schema"] = "trust-cg.trust-overlay.v0".into());
        assert!(refusal(bytes, Some(&ay()), Ok(CLEAN_SHA)).contains("schema"));
        assert!(refusal(b"{".to_vec(), Some(&ay()), Ok(CLEAN_SHA)).contains("not JSON"));
        let bytes = manifest(|m| m["clean"]["sha256"] = "CCCC".into());
        assert!(refusal(bytes, Some(&ay()), Ok("CCCC")).contains("malformed"));
        let bytes = manifest(|m| m["clean"]["source"] = serde_json::json!({}));
        assert!(refusal(bytes, Some(&ay()), Ok(CLEAN_SHA)).contains("no Clean sha256"));
    }
}
