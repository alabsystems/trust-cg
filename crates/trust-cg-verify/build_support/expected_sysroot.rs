// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Distinguish the selected metadata sysroot from an explicit hosting sysroot.
//! The host's AY identity is still recorded and checked independently.

use std::path::{Path, PathBuf};

fn same_directory(left: &Path, right: &Path) -> bool {
    match (left.canonicalize(), right.canonicalize()) {
        (Ok(left), Ok(right)) => left == right,
        _ => left == right,
    }
}

pub fn matches(
    expected: &Path,
    recorded: &Path,
    explicit_host: bool,
    compilation_sysroot: impl FnOnce() -> Result<PathBuf, String>,
) -> Result<bool, String> {
    if same_directory(expected, recorded) {
        return Ok(true);
    }
    if !explicit_host {
        return Ok(false);
    }
    // An explicit host already selects the recorded runtime and its AY. A
    // different expectation must authenticate the actual metadata compiler
    // context; the presence of a host alone never excuses a mismatch.
    Ok(same_directory(expected, &compilation_sysroot()?))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn direct_match_preserves_the_existing_path() {
        assert_eq!(
            matches(Path::new("/runtime"), Path::new("/runtime"), false, || {
                panic!("direct matches do not query a second context")
            }),
            Ok(true)
        );
    }

    #[test]
    fn mismatch_without_an_explicit_host_still_refuses() {
        assert_eq!(
            matches(Path::new("/metadata"), Path::new("/runtime"), false, || {
                panic!("no host grants no second-context authority")
            }),
            Ok(false)
        );
    }

    #[test]
    fn explicit_host_requires_the_actual_metadata_context() {
        assert_eq!(
            matches(Path::new("/metadata"), Path::new("/runtime"), true, || {
                Ok(PathBuf::from("/metadata"))
            }),
            Ok(true)
        );
    }

    #[test]
    fn host_presence_does_not_excuse_a_wrong_expectation() {
        assert_eq!(
            matches(Path::new("/wrong"), Path::new("/runtime"), true, || {
                Ok(PathBuf::from("/metadata"))
            }),
            Ok(false)
        );
    }

    #[test]
    fn failed_query_does_not_record_an_identity() {
        assert_eq!(
            matches(Path::new("/metadata"), Path::new("/runtime"), true, || {
                Err("compiler query failed".into())
            }),
            Err("compiler query failed".into())
        );
    }
}
