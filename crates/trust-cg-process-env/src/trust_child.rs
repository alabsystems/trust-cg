// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Descriptor handoff to an exact Trust toolchain child.

use std::process::Command;

#[cfg(unix)]
use std::{os::fd::RawFd, os::unix::process::CommandExt};

/// Advertise the scheduler and admission descriptors explicitly to Trust std.
/// The parent admission owns the descriptors and the child authenticates the
/// original environment and handles.
#[cfg(unix)]
pub fn inherit_resources(command: &mut Command) {
    for key in [
        "ATERM_SDK_LEASE_V3",
        "ATERM_WORKLOAD_HOST_STORE_FD_V1",
        "TRUST_CPU_IMPLICIT_FD",
        "TRUST_FIXED_ADMISSION_FD_V1",
    ] {
        if let Ok(value) = std::env::var(key)
            && let Some(fd) = descriptor(&value).filter(|&fd| live(fd))
        {
            command.inherit_fd(fd);
        }
    }
    for key in ["ATERM_WORKLOAD_CPU_FDS_V1", "BUILD_SLOT_FENCE_FDS"] {
        if let Ok(value) = std::env::var(key) {
            for fd in value
                .split(',')
                .filter_map(descriptor)
                .filter(|&fd| live(fd))
            {
                command.inherit_fd(fd);
            }
        }
    }
    for key in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"] {
        if let Ok(flags) = std::env::var(key)
            && let Some([read, write]) = gnu_pipe_descriptors(&flags)
            && live(read)
            && live(write)
        {
            command.inherit_fd(read).inherit_fd(write);
        }
    }
}

#[cfg(not(unix))]
pub fn inherit_resources(_: &mut Command) {}

#[cfg(unix)]
fn live(fd: RawFd) -> bool {
    // SAFETY: F_GETFD only inspects this descriptor and takes no variadic argument.
    // A closed locator stays in the environment for the Trust importer to judge.
    unsafe { libc::fcntl(fd, libc::F_GETFD) >= 0 }
}

#[cfg(unix)]
fn descriptor(word: &str) -> Option<RawFd> {
    if !word.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let fd = word.parse().ok()?;
    (fd >= 3).then_some(fd)
}

#[cfg(unix)]
fn gnu_pipe_descriptors(flags: &str) -> Option<[RawFd; 2]> {
    // The current spelling takes precedence over the legacy spelling. A
    // later FIFO advertisement or a disabled jobserver supersedes a pipe.
    let value = ["--jobserver-auth=", "--jobserver-fds="]
        .into_iter()
        .find_map(|prefix| {
            flags
                .split_ascii_whitespace()
                .filter_map(|word| word.strip_prefix(prefix))
                .last()
        })?;
    let (read, write) = value.split_once(',')?;
    Some([descriptor(read)?, descriptor(write)?])
}

#[cfg(all(test, unix))]
mod tests {
    use super::gnu_pipe_descriptors;

    #[test]
    fn selects_the_last_current_gnu_pipe() {
        assert_eq!(gnu_pipe_descriptors("-j --jobserver-fds=3,4"), Some([3, 4]));
        assert_eq!(
            gnu_pipe_descriptors("--jobserver-auth=5,6 --jobserver-fds=3,4 --jobserver-auth=7,8"),
            Some([7, 8])
        );
    }

    #[test]
    fn a_fifo_or_invalid_descriptor_does_not_select_a_pipe() {
        assert_eq!(
            gnu_pipe_descriptors("--jobserver-fds=3,4 --jobserver-auth=fifo:/tmp/job"),
            None
        );
        assert_eq!(gnu_pipe_descriptors("--jobserver-auth=1,4"), None);
        assert_eq!(gnu_pipe_descriptors("--jobserver-auth=3,4,5"), None);
    }
}
