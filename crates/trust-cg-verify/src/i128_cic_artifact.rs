// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Explicit retention of opaque original-CIC evidence bytes, with no proof or
//! grade authority. Each file is published whole and without replacement.
//!
//! The caller supplies an already existing output directory. Unix operations
//! are anchored to that actual directory descriptor, so replacing its pathname
//! cannot redirect a write. An error may leave complete members of a partial
//! set; retry validates and reuses those members. This is not a three-file
//! transaction or a defense against an owner modifying artifacts after return.

use sha2::{Digest, Sha256};
use std::io;
use std::path::{Path, PathBuf};

const MAX_PACKET_BYTES: usize = 8 * 1024 * 1024;
const MAX_CONTEXT_BYTES: usize = 32 * 1024 * 1024;
const MAX_MANIFEST_BYTES: usize = 64 * 1024;

/// Paths to persisted bytes, never checked proof state. Payloads still require
/// independent original-input binding and fresh kernel replay when consumed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArtifactSet {
    packet: PathBuf,
    context_zstd: PathBuf,
    manifest: PathBuf,
}
impl ArtifactSet {
    pub fn packet(&self) -> &Path {
        &self.packet
    }
    pub fn context_zstd(&self) -> &Path {
        &self.context_zstd
    }
    pub fn manifest(&self) -> &Path {
        &self.manifest
    }
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

fn names(packet: &[u8], context: &[u8], manifest: &[u8]) -> [String; 3] {
    let sha = |bytes: &[u8]| format!("{:x}", Sha256::digest(bytes));
    [
        format!("original-i128-packet-{}.json", sha(packet)),
        format!("original-i128-context-{}.bincode.zst", sha(context)),
        format!("original-i128-manifest-{}.json", sha(manifest)),
    ]
}

/// Persist all three complete payloads under deterministic content-addressed
/// names inside `dir`. Payloads are opaque and supply no output path components.
/// Empty/oversized inputs, symlink roots/files and nonregular/mismatching
/// existing entries fail. Existing equal files are read and compared in full.
/// No existing artifact or unrelated peer entry is overwritten.
///
/// Atomic no-clobber publication is per file. If an I/O error interrupts a set,
/// complete published members remain for a validating retry. Non-Unix hosts
/// conservatively return Unsupported rather than using an unanchored fallback.
/// The explicit directory must already exist; parents are never created here.
/// This routine establishes byte retention only, never certificate validity.
pub fn persist_retained_artifacts(
    dir: &Path,
    packet: &[u8],
    context_zstd: &[u8],
    manifest: &[u8],
) -> io::Result<ArtifactSet> {
    for (bytes, limit) in [
        (packet, MAX_PACKET_BYTES),
        (context_zstd, MAX_CONTEXT_BYTES),
        (manifest, MAX_MANIFEST_BYTES),
    ] {
        if bytes.is_empty() || bytes.len() > limit {
            return Err(invalid("empty or oversized retained artifact"));
        }
    }
    // Remove trailing separators and `.` components before the no-follow
    // root open: `symlink/` must not evade the final-component link refusal.
    // Parent components are not evaluated lexically; the opened directory
    // object remains the authority for every subsequent relative operation.
    let dir: PathBuf = dir.components().collect();
    if dir.as_os_str().is_empty() {
        return Err(invalid("artifact root must be explicit and nonempty"));
    }
    let names = names(packet, context_zstd, manifest);
    let contents = [packet, context_zstd, manifest];
    platform::persist(&dir, &names, &contents)?;
    Ok(ArtifactSet {
        packet: dir.join(&names[0]),
        context_zstd: dir.join(&names[1]),
        manifest: dir.join(&names[2]),
    })
}

#[cfg(not(unix))]
mod platform {
    use super::*;
    pub(super) fn persist(_: &Path, _: &[String; 3], _: &[&[u8]; 3]) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "FD-anchored artifact publication is unavailable on this platform",
        ))
    }
}

#[cfg(unix)]
mod platform {
    use super::*;
    use std::ffi::CString;
    use std::fs::{File, Metadata, OpenOptions};
    use std::io::{Read, Write};
    use std::os::fd::{AsRawFd, FromRawFd};
    use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
    use std::sync::atomic::{AtomicU64, Ordering};

    struct Root {
        file: File,
    }

    fn same(a: &Metadata, b: &Metadata) -> bool {
        a.dev() == b.dev() && a.ino() == b.ino()
    }

    fn c_name(name: &str) -> io::Result<CString> {
        CString::new(name).map_err(|_| invalid("invalid internal artifact name"))
    }

    impl Root {
        fn open(dir: &Path) -> io::Result<Self> {
            let before = std::fs::symlink_metadata(dir)?;
            if !before.is_dir() || before.file_type().is_symlink() {
                return Err(invalid("artifact root must be a real directory"));
            }
            let file = OpenOptions::new()
                .read(true)
                .custom_flags(
                    libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
                )
                .open(dir)?;
            let opened = file.metadata()?;
            if !opened.is_dir() || !same(&before, &opened) {
                return Err(invalid("artifact root changed while opening"));
            }
            Ok(Self { file })
        }

        fn unchanged_path(&self, dir: &Path) -> io::Result<()> {
            let current = std::fs::symlink_metadata(dir)?;
            if current.is_dir()
                && !current.file_type().is_symlink()
                && same(&current, &self.file.metadata()?)
            {
                Ok(())
            } else {
                Err(invalid("artifact root pathname changed during publication"))
            }
        }

        fn open_regular(&self, name: &CString) -> io::Result<File> {
            // SAFETY: live directory FD and NUL-terminated single-component
            // internal name. No write/create flags; O_NOFOLLOW rejects links,
            // and O_NONBLOCK prevents a peer FIFO from blocking this check.
            let fd = unsafe {
                libc::openat(
                    self.file.as_raw_fd(),
                    name.as_ptr(),
                    libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
                )
            };
            if fd < 0 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: openat returned a fresh owned descriptor.
            let file = unsafe { File::from_raw_fd(fd) };
            if !file.metadata()?.is_file() {
                return Err(invalid("existing artifact is not a regular file"));
            }
            Ok(file)
        }

        fn equal_existing(&self, name: &CString, expected: &[u8]) -> io::Result<bool> {
            let mut file = match self.open_regular(name) {
                Ok(file) => file,
                Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(false),
                Err(error) => return Err(error),
            };
            let before = file.metadata()?;
            if before.len() != expected.len() as u64 {
                return Err(io::Error::new(
                    io::ErrorKind::AlreadyExists,
                    "existing artifact length differs from actual payload",
                ));
            }
            let mut offset = 0;
            let mut chunk = [0u8; 8192];
            while offset < expected.len() {
                let amount = chunk.len().min(expected.len() - offset);
                file.read_exact(&mut chunk[..amount])?;
                if chunk[..amount] != expected[offset..offset + amount] {
                    return Err(io::Error::new(
                        io::ErrorKind::AlreadyExists,
                        "existing artifact bytes differ from actual payload",
                    ));
                }
                offset += amount;
            }
            if file.read(&mut chunk[..1])? != 0 {
                return Err(invalid("artifact grew during bounded comparison"));
            }
            // Bind the verified open file to the current directory entry too.
            let current = self.open_regular(name)?;
            if !same(&before, &file.metadata()?) || !same(&before, &current.metadata()?) {
                return Err(invalid("artifact entry changed during comparison"));
            }
            Ok(true)
        }

        fn stage(&self) -> io::Result<Staged<'_>> {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            for _ in 0..256 {
                let name = c_name(&format!(
                    ".original-i128-staging-{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ))?;
                // SAFETY: root is live, name is an internal single component,
                // and O_EXCL creates a fresh file without replacing an entry.
                let fd = unsafe {
                    libc::openat(
                        self.file.as_raw_fd(),
                        name.as_ptr(),
                        libc::O_WRONLY
                            | libc::O_CREAT
                            | libc::O_EXCL
                            | libc::O_NOFOLLOW
                            | libc::O_NONBLOCK
                            | libc::O_CLOEXEC,
                        0o600 as libc::c_uint,
                    )
                };
                if fd >= 0 {
                    // SAFETY: openat returned this fresh owned descriptor.
                    let file = unsafe { File::from_raw_fd(fd) };
                    return Ok(Staged {
                        root: self,
                        name,
                        file,
                    });
                }
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::AlreadyExists {
                    return Err(error);
                }
            }
            Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "artifact staging namespace exhausted",
            ))
        }

        fn publish(&self, name: &CString, bytes: &[u8]) -> io::Result<()> {
            if self.equal_existing(name, bytes)? {
                return Ok(());
            }
            let mut staged = self.stage()?;
            staged.file.write_all(bytes)?;
            staged.file.sync_all()?;
            // SAFETY: both paths are internal components beneath the same
            // held directory. linkat publishes a complete file atomically and
            // refuses every existing destination, including a symlink.
            let linked = unsafe {
                libc::linkat(
                    self.file.as_raw_fd(),
                    staged.name.as_ptr(),
                    self.file.as_raw_fd(),
                    name.as_ptr(),
                    0,
                )
            };
            if linked != 0 {
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::AlreadyExists {
                    return Err(error);
                }
            }
            // A concurrent equal publisher is okay; never accept name/size or
            // successful link alone instead of comparing the complete bytes.
            if !self.equal_existing(name, bytes)? {
                return Err(invalid("published artifact disappeared"));
            }
            Ok(())
        }
    }

    struct Staged<'a> {
        root: &'a Root,
        name: CString,
        file: File,
    }
    impl Drop for Staged<'_> {
        fn drop(&mut self) {
            // Never clean a different entry if a peer replaced our staging
            // name. Cleanup failure leaves a non-authoritative temporary file.
            if let (Ok(opened), Ok(named)) =
                (self.file.metadata(), self.root.open_regular(&self.name))
                && named.metadata().is_ok_and(|m| same(&opened, &m))
            {
                // SAFETY: anchored internal name currently identifies our
                // staging inode. This never names a final/peer artifact.
                unsafe { libc::unlinkat(self.root.file.as_raw_fd(), self.name.as_ptr(), 0) };
            }
        }
    }

    pub(super) fn persist(
        dir: &Path,
        names: &[String; 3],
        contents: &[&[u8]; 3],
    ) -> io::Result<()> {
        let root = Root::open(dir)?;
        let names = [c_name(&names[0])?, c_name(&names[1])?, c_name(&names[2])?];
        // Reject known conflicts before adding any new member of this set.
        for (name, bytes) in names.iter().zip(contents) {
            root.equal_existing(name, bytes)?;
        }
        for (name, bytes) in names.iter().zip(contents) {
            root.publish(name, bytes)?;
        }
        root.file.sync_all()?;
        root.unchanged_path(dir)
    }

    #[cfg(test)]
    pub(super) fn replaced_root_control(dir: &Path, moved: &Path, other: &Path) -> io::Result<()> {
        let root = Root::open(dir)?;
        std::fs::rename(dir, moved)?;
        std::os::unix::fs::symlink(other, dir)?;
        root.publish(&c_name("anchored-control")?, b"actual original directory")?;
        root.unchanged_path(dir)
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::symlink;

    const PACKET: &[u8] = b"{\"original\": [4, 64], \"proof\": \"retained\"}";
    const CONTEXT: &[u8] = b"complete compressed retained context including proof bodies";
    const MANIFEST: &[u8] = b"{\"schema\": 1, \"context\": \"actual complete bytes\"}";

    #[test]
    fn retains_all_payload_bytes_with_content_addressed_paths() {
        let dir = tempfile::tempdir().unwrap();
        let out = persist_retained_artifacts(dir.path(), PACKET, CONTEXT, MANIFEST).unwrap();
        assert_eq!(std::fs::read(out.packet()).unwrap(), PACKET);
        assert_eq!(std::fs::read(out.context_zstd()).unwrap(), CONTEXT);
        assert_eq!(std::fs::read(out.manifest()).unwrap(), MANIFEST);
        for (path, name) in [out.packet(), out.context_zstd(), out.manifest()]
            .into_iter()
            .zip(names(PACKET, CONTEXT, MANIFEST))
        {
            assert_eq!(path.file_name().unwrap(), name.as_str());
            assert_eq!(path.parent().unwrap(), dir.path());
        }
        assert_eq!(std::fs::read_dir(dir.path()).unwrap().count(), 3);
    }

    #[test]
    fn equal_existing_files_are_checked_and_reused_without_touching_peer_files() {
        let dir = tempfile::tempdir().unwrap();
        let peer = dir.path().join("peer.txt");
        std::fs::write(&peer, b"keep peer bytes").unwrap();
        let first = persist_retained_artifacts(dir.path(), PACKET, CONTEXT, MANIFEST).unwrap();
        let second = persist_retained_artifacts(dir.path(), PACKET, CONTEXT, MANIFEST).unwrap();
        assert_eq!(first, second);
        assert_eq!(std::fs::read(peer).unwrap(), b"keep peer bytes");
        assert_eq!(std::fs::read_dir(dir.path()).unwrap().count(), 4);
    }

    #[test]
    fn wrong_existing_bytes_and_lengths_are_refused_without_overwrite_or_partial_addition() {
        for bytes in [&b"x"[..], &vec![b'x'; CONTEXT.len()][..]] {
            let dir = tempfile::tempdir().unwrap();
            let paths = names(PACKET, CONTEXT, MANIFEST);
            let wrong = dir.path().join(&paths[1]);
            std::fs::write(&wrong, bytes).unwrap();
            assert!(persist_retained_artifacts(dir.path(), PACKET, CONTEXT, MANIFEST).is_err());
            assert_eq!(std::fs::read(&wrong).unwrap(), bytes);
            assert!(!dir.path().join(&paths[0]).exists());
            assert!(!dir.path().join(&paths[2]).exists());
        }
    }

    #[test]
    fn complete_partial_set_is_validated_and_completed_but_truncated_member_refuses() {
        let dir = tempfile::tempdir().unwrap();
        let paths = names(PACKET, CONTEXT, MANIFEST);
        std::fs::write(dir.path().join(&paths[0]), PACKET).unwrap();
        let out = persist_retained_artifacts(dir.path(), PACKET, CONTEXT, MANIFEST).unwrap();
        assert_eq!(std::fs::read(out.context_zstd()).unwrap(), CONTEXT);
        std::fs::write(out.manifest(), &MANIFEST[..MANIFEST.len() - 1]).unwrap();
        assert!(persist_retained_artifacts(dir.path(), PACKET, CONTEXT, MANIFEST).is_err());
        assert_eq!(std::fs::read(out.packet()).unwrap(), PACKET);
        assert_eq!(
            std::fs::read(out.manifest()).unwrap(),
            &MANIFEST[..MANIFEST.len() - 1]
        );
    }

    #[test]
    fn root_and_existing_file_symlinks_are_refused_including_equal_targets() {
        let parent = tempfile::tempdir().unwrap();
        let real = parent.path().join("real");
        std::fs::create_dir(&real).unwrap();
        let alias = parent.path().join("alias");
        symlink(&real, &alias).unwrap();
        assert!(persist_retained_artifacts(&alias, PACKET, CONTEXT, MANIFEST).is_err());
        let trailing = PathBuf::from(format!("{}/", alias.display()));
        assert!(persist_retained_artifacts(&trailing, PACKET, CONTEXT, MANIFEST).is_err());
        assert!(persist_retained_artifacts(&alias.join("."), PACKET, CONTEXT, MANIFEST).is_err());
        assert_eq!(std::fs::read_dir(&real).unwrap().count(), 0);
        let paths = names(PACKET, CONTEXT, MANIFEST);
        let target = parent.path().join("peer-target");
        std::fs::write(&target, PACKET).unwrap();
        symlink(&target, real.join(&paths[0])).unwrap();
        assert!(persist_retained_artifacts(&real, PACKET, CONTEXT, MANIFEST).is_err());
        assert_eq!(std::fs::read(target).unwrap(), PACKET);
        assert!(
            std::fs::symlink_metadata(real.join(&paths[0]))
                .unwrap()
                .file_type()
                .is_symlink()
        );
    }

    #[test]
    fn nonregular_and_missing_roots_or_artifacts_are_refused() {
        let dir = tempfile::tempdir().unwrap();
        let missing = dir.path().join("missing");
        assert!(persist_retained_artifacts(&missing, PACKET, CONTEXT, MANIFEST).is_err());
        assert!(!missing.exists());
        let paths = names(PACKET, CONTEXT, MANIFEST);
        std::fs::create_dir(dir.path().join(&paths[2])).unwrap();
        assert!(persist_retained_artifacts(dir.path(), PACKET, CONTEXT, MANIFEST).is_err());
        assert!(!dir.path().join(&paths[0]).exists());
    }

    #[test]
    fn existing_fifo_refuses_without_blocking_or_writing_it() {
        use std::ffi::CString;
        use std::os::unix::ffi::OsStrExt;
        let dir = tempfile::tempdir().unwrap();
        let paths = names(PACKET, CONTEXT, MANIFEST);
        let fifo = dir.path().join(&paths[1]);
        let name = CString::new(fifo.as_os_str().as_bytes()).unwrap();
        // SAFETY: a NUL-terminated path in this test's owned directory.
        assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
        assert!(persist_retained_artifacts(dir.path(), PACKET, CONTEXT, MANIFEST).is_err());
        assert!(!dir.path().join(&paths[0]).exists());
        assert!(!std::fs::symlink_metadata(fifo).unwrap().is_file());
    }

    #[test]
    fn empty_and_oversized_inputs_refuse_before_any_files_are_created() {
        let dir = tempfile::tempdir().unwrap();
        assert!(persist_retained_artifacts(dir.path(), b"", CONTEXT, MANIFEST).is_err());
        assert!(persist_retained_artifacts(dir.path(), PACKET, b"", MANIFEST).is_err());
        assert!(persist_retained_artifacts(dir.path(), PACKET, CONTEXT, b"").is_err());
        assert!(
            persist_retained_artifacts(
                dir.path(),
                PACKET,
                CONTEXT,
                &vec![0; MAX_MANIFEST_BYTES + 1]
            )
            .is_err()
        );
        assert_eq!(std::fs::read_dir(dir.path()).unwrap().count(), 0);
    }

    #[test]
    fn changed_payloads_have_distinct_names_and_never_replace_old_sets() {
        let dir = tempfile::tempdir().unwrap();
        let first = persist_retained_artifacts(dir.path(), PACKET, CONTEXT, MANIFEST).unwrap();
        let second =
            persist_retained_artifacts(dir.path(), b"different packet", CONTEXT, MANIFEST).unwrap();
        assert_ne!(first.packet(), second.packet());
        assert_eq!(first.context_zstd(), second.context_zstd());
        assert_eq!(first.manifest(), second.manifest());
        assert_eq!(std::fs::read(first.packet()).unwrap(), PACKET);
        assert_eq!(std::fs::read(second.packet()).unwrap(), b"different packet");
    }

    #[test]
    fn replacing_root_path_cannot_redirect_writes_to_the_symlink_target() {
        let parent = tempfile::tempdir().unwrap();
        let dir = parent.path().join("root");
        let moved = parent.path().join("moved-original");
        let other = parent.path().join("outside");
        std::fs::create_dir(&dir).unwrap();
        std::fs::create_dir(&other).unwrap();
        assert!(platform::replaced_root_control(&dir, &moved, &other).is_err());
        assert_eq!(std::fs::read_dir(&other).unwrap().count(), 0);
        assert_eq!(
            std::fs::read(moved.join("anchored-control")).unwrap(),
            b"actual original directory"
        );
    }
}
