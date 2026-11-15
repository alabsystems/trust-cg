// trust-cg-codegen/link_driver/linked_image_evidence.rs - linked-image records for driver links
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The linked-image evidence record of an arm64 Darwin link the driver ran:
//! [`record_darwin_linked_image`] reads the linked output and every input
//! object, replays the objects' relocations against the image
//! ([`crate::macho::linked_image::record_linked_image`], atoms placed by the
//! image's own symbol table) with libSystem's export list from the SDK's
//! TAPI stub, and writes `<output>.linked-image.json`. When the replay
//! disagrees, or the record cannot be made, the output is removed: a caller
//! that asked for the evidence never keeps an image without it. A record an
//! earlier link left is removed first (and by every [`super::run_link`]), so
//! a record never sits next to an image it does not describe.

use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;

use super::{LinkOutputKind, LinkRequest};
use crate::macho::linked_image::{
    AtomPlacement, LinkedImageRefusal, LinkedImageRequest, LinkedObject, ProviderExports,
    linked_image_record_path, record_linked_image,
};
use crate::target::{Target, TargetOperatingSystem};

/// Why a link's linked-image record was not written. No record is left next
/// to the output, and the linked output was removed when `removed` is true.
#[derive(Debug)]
pub enum LinkedImageEvidenceError {
    /// The link is not one this record covers (named reason).
    Refused {
        /// Why.
        reason: String,
        /// Whether the linked output was removed.
        removed: bool,
    },
    /// An input, the output or libSystem's export list could not be read.
    Unreadable {
        /// What could not be read.
        what: String,
        /// Why.
        error: String,
        /// Whether the linked output was removed.
        removed: bool,
    },
    /// The replay disagreed with the image.
    Replay {
        /// Every finding.
        refusal: LinkedImageRefusal,
        /// Whether the linked output was removed.
        removed: bool,
    },
    /// The record could not be written next to the output, or a stale one
    /// there could not be removed.
    Write {
        /// The record path.
        path: PathBuf,
        /// Operating-system error.
        error: std::io::Error,
        /// Whether the linked output was removed.
        removed: bool,
    },
}

impl fmt::Display for LinkedImageEvidenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (text, removed) = match self {
            Self::Refused { reason, removed } => (
                format!("[TCG-LINK-IMAGE-EVIDENCE] no linked-image record: {reason}"),
                removed,
            ),
            Self::Unreadable {
                what,
                error,
                removed,
            } => (
                format!("[TCG-LINK-IMAGE-EVIDENCE] {what} could not be read: {error}"),
                removed,
            ),
            Self::Replay { refusal, removed } => (refusal.to_string(), removed),
            Self::Write {
                path,
                error,
                removed,
            } => (
                format!(
                    "[TCG-LINK-IMAGE-EVIDENCE] the record {} could not be written or replaced: {error}",
                    path.display()
                ),
                removed,
            ),
        };
        write!(
            f,
            "{text}\n  the linked output {}",
            if *removed {
                "was removed"
            } else {
                "could not be removed and must not be used"
            }
        )
    }
}

impl std::error::Error for LinkedImageEvidenceError {}

/// The first line `ld -v` prints for the linker `driver` runs, or why it is
/// unknown. Declared identity: the image's `LC_BUILD_VERSION` records the
/// linker version independently.
pub fn darwin_linker_identity(driver: &str) -> String {
    let linker = Command::new(driver)
        .arg("-print-prog-name=ld")
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string())
        .filter(|path| !path.is_empty())
        .unwrap_or_else(|| "ld".to_string());
    match Command::new(&linker).arg("-v").output() {
        Ok(output) => {
            let text = String::from_utf8_lossy(&output.stderr);
            let first = text.lines().next().unwrap_or("").trim();
            if first.is_empty() {
                format!("{linker} (no version printed)")
            } else {
                format!("{linker}: {first}")
            }
        }
        Err(error) => format!("{linker} (version unavailable: {error})"),
    }
}

/// libSystem's export list from the active SDK's `libSystem.B.tbd`
/// (`xcrun --show-sdk-path`, which honors `SDKROOT`).
pub fn sdk_libsystem_exports() -> Result<ProviderExports, String> {
    let output = Command::new("xcrun")
        .arg("--show-sdk-path")
        .output()
        .map_err(|error| format!("xcrun --show-sdk-path: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "xcrun --show-sdk-path failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let sdk = String::from_utf8_lossy(&output.stdout).trim().to_string();
    let path = Path::new(&sdk).join("usr/lib/libSystem.B.tbd");
    let text =
        std::fs::read_to_string(&path).map_err(|error| format!("{}: {error}", path.display()))?;
    ProviderExports::from_tbd(&text, path.display().to_string())
}

fn remove(output: &Path) -> bool {
    std::fs::remove_file(output).is_ok() || !output.exists()
}

/// Remove a `<output>.linked-image.json` an earlier link left: it describes
/// an image this link replaces. A record that cannot be removed is an error,
/// so no stale record ever sits next to a new or removed output.
pub fn remove_stale_linked_image_record(output: &Path) -> std::io::Result<()> {
    let record = linked_image_record_path(output);
    match std::fs::remove_file(&record) {
        Ok(()) => Ok(()),
        // Nothing is there, or the suffixed name is too long to name a file
        // (`ENAMETOOLONG`), so no record can be.
        Err(error)
            if matches!(
                error.kind(),
                std::io::ErrorKind::NotFound | std::io::ErrorKind::InvalidFilename
            ) =>
        {
            Ok(())
        }
        Err(error) => Err(error),
    }
}

/// Record the arm64 Darwin image `request` produced (see the module docs):
/// the record's path, or why there is none (the output then removed).
///
/// `providers` are the export lists of every dylib the image may bind to
/// besides libSystem, which is read from the SDK; a bind naming a dylib
/// without one (a `-l` library, for example) refuses the record.
pub fn record_darwin_linked_image(
    request: &LinkRequest,
    driver: &str,
    providers: &[ProviderExports],
) -> Result<PathBuf, LinkedImageEvidenceError> {
    let output = &request.output;
    if let Err(error) = remove_stale_linked_image_record(output) {
        return Err(LinkedImageEvidenceError::Write {
            path: linked_image_record_path(output),
            error,
            removed: remove(output),
        });
    }
    let target = request.target.with_default_os_abi();
    let refused = |reason: String| LinkedImageEvidenceError::Refused {
        reason,
        removed: remove(output),
    };
    if target.operating_system != TargetOperatingSystem::Darwin
        || target.architecture != Target::Aarch64
    {
        return Err(refused(format!(
            "{} images are not replayed (aarch64-apple-darwin only)",
            target.triple()
        )));
    }
    if !matches!(
        request.kind,
        LinkOutputKind::Executable | LinkOutputKind::SharedLibrary
    ) {
        return Err(refused("only executables and dylibs are replayed".into()));
    }
    if request.static_link {
        return Err(refused("a static link is not an arm64 Darwin image".into()));
    }
    let unreadable = |what: String, error: String| LinkedImageEvidenceError::Unreadable {
        what,
        error,
        removed: remove(output),
    };
    let mut all_providers = match sdk_libsystem_exports() {
        Ok(libsystem) => vec![libsystem],
        Err(error) => return Err(unreadable("libSystem's export list".into(), error)),
    };
    all_providers.extend(providers.iter().cloned());
    let mut objects = Vec::with_capacity(request.objects.len());
    for path in &request.objects {
        match std::fs::read(path) {
            // The file name keeps the record independent of the directory
            // the objects were written to (the CLI's is temporary).
            Ok(bytes) => objects.push((
                path.file_name().map_or_else(
                    || path.display().to_string(),
                    |name| name.to_string_lossy().into_owned(),
                ),
                bytes,
            )),
            Err(error) => {
                return Err(unreadable(
                    format!("input {}", path.display()),
                    error.to_string(),
                ));
            }
        }
    }
    let image = match std::fs::read(output) {
        Ok(bytes) => bytes,
        Err(error) => {
            return Err(unreadable(
                format!("output {}", output.display()),
                error.to_string(),
            ));
        }
    };
    let image_name = output.display().to_string();
    let replay = LinkedImageRequest {
        image_name: &image_name,
        image: &image,
        objects: objects
            .iter()
            .map(|(name, bytes)| LinkedObject { name, bytes })
            .collect(),
        placement: AtomPlacement::ImageSymbolTable,
        providers: all_providers,
        linker: format!("{driver} -> {}", darwin_linker_identity(driver)),
    };
    let record = match record_linked_image(&replay) {
        Ok(record) => record,
        Err(refusal) => {
            return Err(LinkedImageEvidenceError::Replay {
                refusal,
                removed: remove(output),
            });
        }
    };
    record
        .write_next_to(output)
        .map_err(|error| LinkedImageEvidenceError::Write {
            path: linked_image_record_path(output),
            error,
            removed: remove(output),
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::link_driver::{LinkError, run_link};
    use crate::target::TargetSpec;

    /// A stale record goes, a missing one or one whose suffixed name is too
    /// long to exist is no error, and a record that cannot be removed fails
    /// the link before the driver runs.
    #[test]
    fn run_link_removes_a_stale_record_before_the_driver_runs() {
        let directory = tempfile::tempdir().unwrap();
        let output = directory.path().join("prog");
        let record = linked_image_record_path(&output);
        remove_stale_linked_image_record(&output).expect("no record is no error");
        remove_stale_linked_image_record(&directory.path().join("n".repeat(255)))
            .expect("a name too long for the suffix holds no record");

        let request = LinkRequest::executable(
            TargetSpec::parse("aarch64-apple-darwin").unwrap(),
            vec![directory.path().join("a.o")],
            output.clone(),
        );
        std::fs::write(&record, "{}").unwrap();
        assert!(matches!(
            run_link(&request, "/nonexistent/trust-cg-no-such-driver"),
            Err(LinkError::Spawn { .. })
        ));
        assert!(!record.exists(), "removed before the driver was spawned");

        std::fs::create_dir(&record).unwrap();
        match run_link(&request, "/nonexistent/trust-cg-no-such-driver") {
            Err(LinkError::OutputStaging { action, .. }) => {
                assert!(action.contains("stale linked-image record"), "{action}");
            }
            other => panic!("expected the stale record to fail the link, got {other:?}"),
        }
        assert!(record.is_dir());
    }
}
