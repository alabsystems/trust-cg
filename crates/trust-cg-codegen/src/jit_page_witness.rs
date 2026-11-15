// trust-cg-codegen - Kernel page-protection witness for published JIT memory
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: Linux proc(5), /proc/pid/maps (address range, perms, offset,
//            dev, inode, pathname; perms are r/w/x then p=private or s=shared)

//! Kernel page-protection witness for published JIT allocations.
//!
//! On Linux the kernel reports its own view of every mapping through
//! `/proc/self/maps`. The JIT observes the whole published allocation right
//! after the read-execute seal, and the compile service observes it again on
//! the three checked installed routes (`get_contract_symbol_bound`,
//! `native_install_gate_packet(_for_surface)` and `into_installed_artifact`),
//! so a protection changed outside the publisher (for example an `mprotect`
//! back to writable) is refused by name there. Other hosts have no such file;
//! they publish with a recorded-only witness.
//!
//! Two readers exist, and neither observes the whole process at one instant:
//!
//! * The `PROCMAP_QUERY` ioctl on an open `/proc/self/maps` (Linux 6.11 and
//!   later) answers one VMA per call, and the kernel documents each answer as
//!   self-consistent. When one VMA covers the whole allocation (the published
//!   case: one anonymous mapping sealed read-execute by one `mprotect`), the
//!   observation is that single answer. When several VMAs are needed they are
//!   successive calls, with no consistency guarantee between them.
//! * The text of `/proc/self/maps` (the fallback when the ioctl is absent) is
//!   assembled by the kernel chunk by chunk, with the mm lock dropped between
//!   chunks. While other threads map, unmap or change protections, one read
//!   can report a VMA twice, rows out of order, or a combination of states
//!   that never existed at any single instant. The reader retries the whole
//!   file, a bounded number of times, when rows around the range overlap or
//!   go backwards or the range is not covered, and refuses by name after the
//!   last attempt. An accepted text read guarantees only that its rows are
//!   ordered and cover the range and that each row was true at some moment
//!   during the read, not that all rows held together.
//!
//! Either way an observation is execution evidence of the kernel's state
//! during the read. It is not proof that the protection held between two
//! reads, and it binds no thread or execution-lease context.

use thiserror::Error;

use crate::jit_contract::{
    PageProtectionWitnessRefusal, PageProtectionWitnessSource,
    page_permissions_writable_and_executable,
};

/// Path of the kernel's mapping table for the current process.
pub const PROC_SELF_MAPS: &str = "/proc/self/maps";

/// Witness source of this host's in-process JIT.
pub const fn host_page_protection_witness_source() -> PageProtectionWitnessSource {
    if cfg!(target_os = "linux") {
        PageProtectionWitnessSource::KernelProcSelfMaps
    } else {
        PageProtectionWitnessSource::RecordedOnly
    }
}

/// One address-ordered run of equal kernel permissions inside an observed
/// range, clipped to that range.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelPageRun {
    /// First byte of the run.
    pub start: u64,
    /// One past the last byte of the run.
    pub end: u64,
    /// Permission string reported by the kernel (`r-xp`, `rw-p`, ...).
    pub permissions: String,
}

/// Which kernel interface answered an observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KernelMapsReader {
    /// The `PROCMAP_QUERY` ioctl on `/proc/self/maps`: one self-consistent
    /// kernel answer per VMA.
    ProcmapQuery,
    /// The text of `/proc/self/maps`, accepted only once it was ordered and
    /// covered the range.
    MapsText,
    /// Test-injected maps text (library unit tests only).
    Injected,
}

/// The kernel's view of every byte of `[start, end)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelPageProtectionObservation {
    /// First observed byte.
    pub start: u64,
    /// One past the last observed byte.
    pub end: u64,
    /// Covering runs in address order; adjacent rows with equal permissions
    /// are merged, so a uniformly protected range has exactly one run.
    pub runs: Vec<KernelPageRun>,
    /// Kernel interface that produced the accepted answer.
    pub reader: KernelMapsReader,
    /// Whole-observation attempts made, including the accepted one (1 when
    /// the first read was consistent and covered the range).
    pub attempts: u32,
}

impl KernelPageProtectionObservation {
    /// Permission string of the whole range: the single run's permissions,
    /// or every run's permissions in address order separated by `|`.
    pub fn permissions(&self) -> String {
        self.runs
            .iter()
            .map(|run| run.permissions.as_str())
            .collect::<Vec<_>>()
            .join("|")
    }

    /// Whether any run is both writable and executable.
    pub fn writable_and_executable(&self) -> bool {
        page_permissions_writable_and_executable(&self.permissions())
    }
}

/// Why the kernel could not witness a range.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum KernelPageProtectionError {
    /// The host has no `/proc/self/maps`.
    #[error(
        "[TCG-JIT-PAGE-WITNESS-UNREADABLE] no kernel page-protection witness on {os}: /proc/self/maps is read only on Linux"
    )]
    Unsupported {
        /// Host operating system.
        os: &'static str,
    },
    /// `/proc/self/maps` could not be read or queried.
    #[error("[TCG-JIT-PAGE-WITNESS-UNREADABLE] cannot read /proc/self/maps: {detail}")]
    Unreadable {
        /// I/O error text.
        detail: String,
    },
    /// A `/proc/self/maps` row did not parse. Never retried.
    #[error("[TCG-JIT-PAGE-WITNESS-UNREADABLE] malformed /proc/self/maps row `{row}`: {detail}")]
    Malformed {
        /// The offending row.
        row: String,
        /// What was wrong with it.
        detail: String,
    },
    /// Rows that bear on the observed range overlap or go backwards: the
    /// text was assembled across a concurrent mapping change. Retried; after
    /// the last attempt it is the named refusal.
    #[error(
        "[TCG-JIT-PAGE-WITNESS-UNREADABLE] no consistent /proc/self/maps snapshot of the observed range after {attempts} read(s): row `{row}` {detail}"
    )]
    Inconsistent {
        /// The first row out of order in the last read.
        row: String,
        /// What was inconsistent about it.
        detail: String,
        /// Whole-file reads made.
        attempts: u32,
    },
    /// The rows leave part of the observed range unmapped.
    #[error(
        "[TCG-JIT-PAGE-WITNESS-UNCOVERED] /proc/self/maps does not cover [{gap_start:#x}, {gap_end:#x}) of the observed range [{start:#x}, {end:#x})"
    )]
    RangeNotCovered {
        /// First observed byte.
        start: u64,
        /// One past the last observed byte.
        end: u64,
        /// First uncovered byte.
        gap_start: u64,
        /// One past the last byte of the first uncovered gap.
        gap_end: u64,
    },
    /// The requested range is empty or wraps the address space.
    #[error(
        "[TCG-JIT-PAGE-WITNESS-UNCOVERED] the observed range at {start:#x} of {len} bytes is empty or wraps the address space"
    )]
    InvalidRange {
        /// First requested byte.
        start: u64,
        /// Requested length.
        len: u64,
    },
}

impl KernelPageProtectionError {
    /// The named witness refusal this error maps to.
    pub const fn refusal(&self) -> PageProtectionWitnessRefusal {
        match self {
            Self::RangeNotCovered { .. } | Self::InvalidRange { .. } => {
                PageProtectionWitnessRefusal::RangeNotCovered
            }
            Self::Unsupported { .. }
            | Self::Unreadable { .. }
            | Self::Malformed { .. }
            | Self::Inconsistent { .. } => PageProtectionWitnessRefusal::Unobservable,
        }
    }

    /// Whether a fresh whole observation may give a different answer: the
    /// text was inconsistent, or the range was not covered (a concurrent
    /// change of the observed mapping itself). Malformed rows, I/O errors
    /// and invalid ranges are refused at once.
    pub const fn is_retryable(&self) -> bool {
        matches!(
            self,
            Self::Inconsistent { .. } | Self::RangeNotCovered { .. }
        )
    }
}

/// Whole-observation attempts made before a structural inconsistency or an
/// uncovered range is refused by name.
pub const KERNEL_WITNESS_READ_ATTEMPTS: u32 = 16;

fn parse_maps_row(row: &str) -> Result<(u64, u64, &str), KernelPageProtectionError> {
    let malformed = |detail: &str| KernelPageProtectionError::Malformed {
        row: row.to_owned(),
        detail: detail.to_owned(),
    };
    let mut fields = row.split_ascii_whitespace();
    let range = fields
        .next()
        .ok_or_else(|| malformed("missing address range"))?;
    let permissions = fields
        .next()
        .ok_or_else(|| malformed("missing permissions"))?;
    let (start, end) = range
        .split_once('-')
        .ok_or_else(|| malformed("address range has no `-`"))?;
    let start =
        u64::from_str_radix(start, 16).map_err(|_| malformed("start address is not hex"))?;
    let end = u64::from_str_radix(end, 16).map_err(|_| malformed("end address is not hex"))?;
    if end <= start {
        return Err(malformed("end address does not follow start address"));
    }
    let bytes = permissions.as_bytes();
    let well_formed = bytes.len() == 4
        && matches!(bytes[0], b'r' | b'-')
        && matches!(bytes[1], b'w' | b'-')
        && matches!(bytes[2], b'x' | b'-')
        && matches!(bytes[3], b'p' | b's');
    if !well_formed {
        return Err(malformed("permissions are not `[r-][w-][x-][ps]`"));
    }
    Ok((start, end, permissions))
}

fn observed_end(start: u64, len: u64) -> Result<u64, KernelPageProtectionError> {
    start
        .checked_add(len)
        .filter(|_| len > 0)
        .ok_or(KernelPageProtectionError::InvalidRange { start, len })
}

/// Append `[run_start, run_end)` with `permissions`, merging it into the last
/// run when the permissions are equal.
fn push_run(runs: &mut Vec<KernelPageRun>, run_start: u64, run_end: u64, permissions: &str) {
    match runs.last_mut() {
        Some(last) if last.permissions == permissions && last.end == run_start => {
            last.end = run_end;
        }
        _ => runs.push(KernelPageRun {
            start: run_start,
            end: run_end,
            permissions: permissions.to_owned(),
        }),
    }
}

/// Observe `[start, start + len)` in one `/proc/self/maps` text.
///
/// Every byte must be covered by address-ordered rows; the first gap is
/// reported as [`KernelPageProtectionError::RangeNotCovered`]. A malformed
/// row anywhere is refused as [`KernelPageProtectionError::Malformed`]. A row
/// that overlaps or goes back behind its predecessor is
/// [`KernelPageProtectionError::Inconsistent`] (retryable) unless it lies
/// wholly below the range before any of the range was covered, where it
/// cannot affect coverage: the kernel restarted a chunk after a concurrent
/// change below the range. Nothing is skipped silently. This function reads
/// one text; [`observe_kernel_page_protection`] retries whole reads.
pub fn observe_page_protection_in_maps(
    maps: &str,
    start: u64,
    len: u64,
) -> Result<KernelPageProtectionObservation, KernelPageProtectionError> {
    let end = observed_end(start, len)?;
    let mut cursor = start;
    let mut previous_end = 0u64;
    let mut runs: Vec<KernelPageRun> = Vec::new();
    for row in maps.lines().filter(|row| !row.trim().is_empty()) {
        let (row_start, row_end, permissions) = parse_maps_row(row)?;
        if row_start < previous_end {
            let wholly_below_uncovered_range = cursor == start && row_end <= start;
            if !wholly_below_uncovered_range {
                return Err(KernelPageProtectionError::Inconsistent {
                    row: row.to_owned(),
                    detail: format!(
                        "starts at {row_start:#x}, before the previous row's end {previous_end:#x}"
                    ),
                    attempts: 1,
                });
            }
        }
        // The running maximum: a tolerated backwards row must not lower the
        // bound a later row is checked against.
        previous_end = previous_end.max(row_end);
        if row_end <= cursor {
            continue;
        }
        if row_start >= end {
            break;
        }
        if row_start > cursor {
            return Err(KernelPageProtectionError::RangeNotCovered {
                start,
                end,
                gap_start: cursor,
                gap_end: row_start,
            });
        }
        let run_end = row_end.min(end);
        push_run(&mut runs, cursor, run_end, permissions);
        cursor = run_end;
        if cursor >= end {
            break;
        }
    }
    if cursor < end {
        return Err(KernelPageProtectionError::RangeNotCovered {
            start,
            end,
            gap_start: cursor,
            gap_end: end,
        });
    }
    Ok(KernelPageProtectionObservation {
        start,
        end,
        runs,
        reader: KernelMapsReader::MapsText,
        attempts: 1,
    })
}

/// Observe `[start, start + len)` from successive whole `/proc/self/maps`
/// texts returned by `read`, retrying a retryable answer up to
/// [`KERNEL_WITNESS_READ_ATTEMPTS`] times.
///
/// The first consistent, covering text is accepted. A read error, a
/// malformed row or an invalid range is refused at once; an inconsistent or
/// uncovered answer is refused by name only after the last attempt, with the
/// attempt count.
pub fn observe_page_protection_in_maps_reads(
    mut read: impl FnMut() -> Result<String, KernelPageProtectionError>,
    start: u64,
    len: u64,
) -> Result<KernelPageProtectionObservation, KernelPageProtectionError> {
    retry_observation(|| observe_page_protection_in_maps(&read()?, start, len))
}

fn retry_observation(
    mut observe_once: impl FnMut() -> Result<KernelPageProtectionObservation, KernelPageProtectionError>,
) -> Result<KernelPageProtectionObservation, KernelPageProtectionError> {
    let mut attempt = 0u32;
    loop {
        attempt += 1;
        match observe_once() {
            Ok(mut observation) => {
                observation.attempts = attempt;
                return Ok(observation);
            }
            Err(error) if error.is_retryable() && attempt < KERNEL_WITNESS_READ_ATTEMPTS => {
                std::thread::yield_now();
            }
            Err(KernelPageProtectionError::Inconsistent { row, detail, .. }) => {
                return Err(KernelPageProtectionError::Inconsistent {
                    row,
                    detail,
                    attempts: attempt,
                });
            }
            Err(error) => return Err(error),
        }
    }
}

fn read_proc_self_maps() -> Result<String, KernelPageProtectionError> {
    std::fs::read_to_string(PROC_SELF_MAPS).map_err(|error| KernelPageProtectionError::Unreadable {
        detail: error.to_string(),
    })
}

/// Read the kernel's current view of `[start, start + len)`.
///
/// On Linux this asks `PROCMAP_QUERY` first and falls back to the retrying
/// text reader ([`observe_kernel_page_protection_from_maps_text`]) when the
/// kernel lacks the ioctl. Returns [`KernelPageProtectionError::Unsupported`]
/// on hosts without `/proc/self/maps`. The answer describes the kernel's
/// state during the read (see the module documentation for what each reader
/// guarantees); another thread may change the mapping immediately afterwards.
pub fn observe_kernel_page_protection(
    start: u64,
    len: u64,
) -> Result<KernelPageProtectionObservation, KernelPageProtectionError> {
    #[cfg(test)]
    if let Some(observation) = test_hooks::observe_injected(start, len) {
        return observation;
    }
    if host_page_protection_witness_source() != PageProtectionWitnessSource::KernelProcSelfMaps {
        return Err(KernelPageProtectionError::Unsupported {
            os: std::env::consts::OS,
        });
    }
    let end = observed_end(start, len)?;
    match procmap_query::observe(start, end) {
        Some(answer) => answer,
        None => observe_kernel_page_protection_from_maps_text(start, len),
    }
}

/// Read `[start, start + len)` from the text of `/proc/self/maps` only,
/// retrying whole reads as [`observe_page_protection_in_maps_reads`] does.
/// [`observe_kernel_page_protection`] uses this when `PROCMAP_QUERY` is
/// unavailable; it is public so the fallback can be exercised on a kernel
/// that has the ioctl.
pub fn observe_kernel_page_protection_from_maps_text(
    start: u64,
    len: u64,
) -> Result<KernelPageProtectionObservation, KernelPageProtectionError> {
    if host_page_protection_witness_source() != PageProtectionWitnessSource::KernelProcSelfMaps {
        return Err(KernelPageProtectionError::Unsupported {
            os: std::env::consts::OS,
        });
    }
    observe_page_protection_in_maps_reads(read_proc_self_maps, start, len)
}

/// Whether this process's kernel answers `PROCMAP_QUERY`. `false` on
/// non-Linux hosts, on architectures whose ioctl encoding this module does
/// not carry, and on kernels older than 6.11.
pub fn kernel_supports_procmap_query() -> bool {
    procmap_query::supported()
}

/// `PROCMAP_QUERY` (Linux 6.11+, `include/uapi/linux/fs.h`): ask the kernel
/// for the VMA covering an address through an open `/proc/self/maps`.
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "riscv64"
    )
))]
mod procmap_query {
    use std::fs::File;
    use std::os::fd::AsRawFd;
    use std::sync::atomic::{AtomicU8, Ordering};

    use super::{
        KernelMapsReader, KernelPageProtectionError, KernelPageProtectionObservation,
        KernelPageRun, PROC_SELF_MAPS, push_run, retry_observation,
    };

    /// `struct procmap_query` of the Linux UAPI.
    #[repr(C)]
    #[derive(Debug, Default)]
    struct ProcmapQuery {
        size: u64,
        query_flags: u64,
        query_addr: u64,
        vma_start: u64,
        vma_end: u64,
        vma_flags: u64,
        vma_page_size: u64,
        vma_offset: u64,
        inode: u64,
        dev_major: u32,
        dev_minor: u32,
        vma_name_size: u32,
        build_id_size: u32,
        vma_name_addr: u64,
        build_id_addr: u64,
    }

    const _: () = assert!(std::mem::size_of::<ProcmapQuery>() == 104);

    /// `_IOWR('f', 17, struct procmap_query)` in the generic ioctl encoding
    /// used by x86-64, AArch64 and RISC-V.
    const PROCMAP_QUERY: std::ffi::c_ulong = (3 << 30)
        | ((std::mem::size_of::<ProcmapQuery>() as std::ffi::c_ulong) << 16)
        | ((b'f' as std::ffi::c_ulong) << 8)
        | 17;
    const VMA_READABLE: u64 = 0x01;
    const VMA_WRITABLE: u64 = 0x02;
    const VMA_EXECUTABLE: u64 = 0x04;
    const VMA_SHARED: u64 = 0x08;
    const COVERING_OR_NEXT_VMA: u64 = 0x10;

    const ENOENT: i32 = 2;
    const EINVAL: i32 = 22;
    const ENOTTY: i32 = 25;
    const ENOSYS: i32 = 38;
    const EOPNOTSUPP: i32 = 95;

    const UNKNOWN: u8 = 0;
    const SUPPORTED: u8 = 1;
    const UNSUPPORTED: u8 = 2;
    static SUPPORT: AtomicU8 = AtomicU8::new(UNKNOWN);

    unsafe extern "C" {
        fn ioctl(fd: std::ffi::c_int, request: std::ffi::c_ulong, ...) -> std::ffi::c_int;
    }

    enum Answer {
        Vma {
            start: u64,
            end: u64,
            flags: u64,
        },
        /// `ENOENT`: no VMA matches the query.
        NoVma,
        /// `ENOTTY`: this kernel has no `PROCMAP_QUERY`; remembered.
        NotSupported,
        /// `EINVAL`, `ENOSYS` or `EOPNOTSUPP`: this query was declined; the
        /// text reader answers this observation, and the ioctl is tried again
        /// next time.
        Declined,
    }

    fn query(maps: &File, addr: u64, flags: u64) -> Result<Answer, KernelPageProtectionError> {
        let mut request = ProcmapQuery {
            size: std::mem::size_of::<ProcmapQuery>() as u64,
            query_flags: flags,
            query_addr: addr,
            ..ProcmapQuery::default()
        };
        // SAFETY: `maps` is an open `/proc/self/maps`; `request` is a live,
        // correctly sized `struct procmap_query` whose name and build-id
        // buffers are absent (sizes and addresses zero), so the kernel
        // writes only into `request`.
        let status = unsafe {
            ioctl(
                maps.as_raw_fd(),
                PROCMAP_QUERY,
                &mut request as *mut ProcmapQuery,
            )
        };
        if status == 0 {
            return Ok(Answer::Vma {
                start: request.vma_start,
                end: request.vma_end,
                flags: request.vma_flags,
            });
        }
        let error = std::io::Error::last_os_error();
        match error.raw_os_error() {
            Some(ENOENT) => Ok(Answer::NoVma),
            Some(ENOTTY) => Ok(Answer::NotSupported),
            Some(EINVAL | ENOSYS | EOPNOTSUPP) => Ok(Answer::Declined),
            _ => Err(KernelPageProtectionError::Unreadable {
                detail: format!("PROCMAP_QUERY at {addr:#x}: {error}"),
            }),
        }
    }

    /// `/proc/pid/maps` permission notation of a VMA's query flags.
    fn permissions(flags: u64) -> String {
        [
            if flags & VMA_READABLE != 0 { 'r' } else { '-' },
            if flags & VMA_WRITABLE != 0 { 'w' } else { '-' },
            if flags & VMA_EXECUTABLE != 0 {
                'x'
            } else {
                '-'
            },
            if flags & VMA_SHARED != 0 { 's' } else { 'p' },
        ]
        .into_iter()
        .collect()
    }

    /// One pass over `[start, end)`; `Err(fallback)` when the ioctl did not
    /// answer, with `fallback.remember` set when the kernel lacks it.
    fn observe_once(
        maps: &File,
        start: u64,
        end: u64,
    ) -> Result<Result<KernelPageProtectionObservation, KernelPageProtectionError>, Fallback> {
        let mut cursor = start;
        let mut runs: Vec<KernelPageRun> = Vec::new();
        while cursor < end {
            match query(maps, cursor, 0) {
                Err(error) => return Ok(Err(error)),
                Ok(Answer::NotSupported) => return Err(Fallback { remember: true }),
                Ok(Answer::Declined) => return Err(Fallback { remember: false }),
                Ok(Answer::Vma {
                    start: vma_start,
                    end: vma_end,
                    flags,
                }) => {
                    if !(vma_start <= cursor && cursor < vma_end) {
                        return Ok(Err(KernelPageProtectionError::Unreadable {
                            detail: format!(
                                "PROCMAP_QUERY at {cursor:#x} answered [{vma_start:#x}, {vma_end:#x}), which does not cover it"
                            ),
                        }));
                    }
                    let run_end = vma_end.min(end);
                    push_run(&mut runs, cursor, run_end, &permissions(flags));
                    cursor = run_end;
                }
                Ok(Answer::NoVma) => {
                    let gap_end = match query(maps, cursor, COVERING_OR_NEXT_VMA) {
                        Err(error) => return Ok(Err(error)),
                        Ok(Answer::NotSupported) => return Err(Fallback { remember: true }),
                        Ok(Answer::Declined) => return Err(Fallback { remember: false }),
                        Ok(Answer::Vma { start: next, .. }) if next > cursor => next.min(end),
                        Ok(Answer::Vma { .. } | Answer::NoVma) => end,
                    };
                    return Ok(Err(KernelPageProtectionError::RangeNotCovered {
                        start,
                        end,
                        gap_start: cursor,
                        gap_end,
                    }));
                }
            }
        }
        Ok(Ok(KernelPageProtectionObservation {
            start,
            end,
            runs,
            reader: KernelMapsReader::ProcmapQuery,
            attempts: 1,
        }))
    }

    struct Fallback {
        remember: bool,
    }

    /// Observe `[start, end)` with `PROCMAP_QUERY`, re-querying the whole
    /// range when it is not covered, up to the shared attempt bound. `None`
    /// when the ioctl did not answer, so the text reader must.
    pub(super) fn observe(
        start: u64,
        end: u64,
    ) -> Option<Result<KernelPageProtectionObservation, KernelPageProtectionError>> {
        if SUPPORT.load(Ordering::Relaxed) == UNSUPPORTED {
            return None;
        }
        let maps = match File::open(PROC_SELF_MAPS) {
            Ok(maps) => maps,
            Err(error) => {
                return Some(Err(KernelPageProtectionError::Unreadable {
                    detail: error.to_string(),
                }));
            }
        };
        let mut fallback = None;
        let answer = retry_observation(|| match observe_once(&maps, start, end) {
            Ok(answer) => answer,
            Err(reason) => {
                fallback = Some(reason);
                // Not retryable: ends the loop at once.
                Err(KernelPageProtectionError::Unsupported { os: "linux" })
            }
        });
        match fallback {
            Some(Fallback { remember }) => {
                if remember {
                    SUPPORT.store(UNSUPPORTED, Ordering::Relaxed);
                }
                None
            }
            None => {
                SUPPORT.store(SUPPORTED, Ordering::Relaxed);
                Some(answer)
            }
        }
    }

    pub(super) fn supported() -> bool {
        match SUPPORT.load(Ordering::Relaxed) {
            SUPPORTED => true,
            UNSUPPORTED => false,
            _ => {
                let Ok(maps) = File::open(PROC_SELF_MAPS) else {
                    return false;
                };
                // Any address: an answer or ENOENT both mean the ioctl exists.
                match query(&maps, 0, COVERING_OR_NEXT_VMA) {
                    Ok(Answer::Vma { .. } | Answer::NoVma) => {
                        SUPPORT.store(SUPPORTED, Ordering::Relaxed);
                        true
                    }
                    Ok(Answer::NotSupported) => {
                        SUPPORT.store(UNSUPPORTED, Ordering::Relaxed);
                        false
                    }
                    Ok(Answer::Declined) | Err(_) => false,
                }
            }
        }
    }
}

#[cfg(not(all(
    target_os = "linux",
    any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "riscv64"
    )
)))]
mod procmap_query {
    use super::{KernelPageProtectionError, KernelPageProtectionObservation};

    pub(super) fn observe(
        _start: u64,
        _end: u64,
    ) -> Option<Result<KernelPageProtectionObservation, KernelPageProtectionError>> {
        None
    }

    pub(super) fn supported() -> bool {
        false
    }
}

/// Page-protection witness an executable buffer took when it was published.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PublicationPageWitness {
    /// The host has no kernel re-read; only the recorded protection exists.
    RecordedOnly,
    /// The kernel's view of the whole allocation right after the seal.
    Observed(KernelPageProtectionObservation),
    /// The kernel could not witness the allocation right after the seal.
    Failed(KernelPageProtectionError),
    /// A test-fabricated buffer that never went through a publish sequence.
    NotPublished,
}

impl PublicationPageWitness {
    /// Witness a freshly sealed allocation with this host's source.
    pub fn capture(start: u64, len: u64) -> Self {
        match host_page_protection_witness_source() {
            PageProtectionWitnessSource::RecordedOnly => Self::RecordedOnly,
            PageProtectionWitnessSource::KernelProcSelfMaps => {
                match observe_kernel_page_protection(start, len) {
                    Ok(observation) => Self::Observed(observation),
                    Err(error) => Self::Failed(error),
                }
            }
        }
    }

    /// Source this witness was taken with.
    pub fn source(&self) -> PageProtectionWitnessSource {
        match self {
            Self::RecordedOnly => PageProtectionWitnessSource::RecordedOnly,
            Self::Observed(_) | Self::Failed(_) => PageProtectionWitnessSource::KernelProcSelfMaps,
            Self::NotPublished => host_page_protection_witness_source(),
        }
    }

    /// Observed permission string, when the kernel witnessed the allocation.
    pub fn observed_permissions(&self) -> Option<String> {
        match self {
            Self::Observed(observation) => Some(observation.permissions()),
            Self::RecordedOnly | Self::Failed(_) | Self::NotPublished => None,
        }
    }
}

/// Test-only substitution of the `/proc/self/maps` texts read on the current
/// thread, so library tests can drive the lookup path through kernel answers
/// a live process cannot safely produce (an uncovered range, a mixed range,
/// a torn read). Injected texts go through the same retrying text reader.
#[cfg(test)]
pub(crate) mod test_hooks {
    use std::cell::RefCell;
    use std::collections::VecDeque;

    use super::{
        KernelMapsReader, KernelPageProtectionError, KernelPageProtectionObservation,
        observe_page_protection_in_maps_reads,
    };

    /// Queued texts; the last one answers every further read.
    struct Injected {
        reads: VecDeque<String>,
        served: u32,
    }

    thread_local! {
        static MAPS_OVERRIDE: RefCell<Option<Injected>> = const { RefCell::new(None) };
    }

    fn next_read() -> Result<String, KernelPageProtectionError> {
        MAPS_OVERRIDE.with(|slot| {
            let mut slot = slot.borrow_mut();
            let injected = slot
                .as_mut()
                .expect("an injected maps override is installed");
            injected.served += 1;
            let text = if injected.reads.len() > 1 {
                injected.reads.pop_front()
            } else {
                injected.reads.front().cloned()
            };
            Ok(text.expect("an injected maps override holds at least one text"))
        })
    }

    /// The injected answer for `[start, start + len)`, or `None` when no
    /// override is installed on this thread.
    pub(crate) fn observe_injected(
        start: u64,
        len: u64,
    ) -> Option<Result<KernelPageProtectionObservation, KernelPageProtectionError>> {
        let installed = MAPS_OVERRIDE.with(|slot| slot.borrow().is_some());
        installed.then(|| {
            observe_page_protection_in_maps_reads(next_read, start, len).map(|mut observation| {
                observation.reader = KernelMapsReader::Injected;
                observation
            })
        })
    }

    // The installers below serve only the Linux kernel-reader tests in
    // `compile_service` (the one host whose witness reads `/proc/self/maps`),
    // so they are compiled where those tests are; elsewhere they would be
    // dead code under the workspace's deny(warnings).
    /// Restores the real kernel reader when dropped.
    #[cfg(all(
        target_os = "linux",
        any(target_arch = "aarch64", target_arch = "x86_64")
    ))]
    pub(crate) struct MapsOverrideGuard(());

    #[cfg(all(
        target_os = "linux",
        any(target_arch = "aarch64", target_arch = "x86_64")
    ))]
    impl MapsOverrideGuard {
        /// Whole-file reads served so far.
        pub(crate) fn reads_served(&self) -> u32 {
            MAPS_OVERRIDE.with(|slot| slot.borrow().as_ref().map_or(0, |i| i.served))
        }
    }

    #[cfg(all(
        target_os = "linux",
        any(target_arch = "aarch64", target_arch = "x86_64")
    ))]
    impl Drop for MapsOverrideGuard {
        fn drop(&mut self) {
            MAPS_OVERRIDE.with(|slot| slot.borrow_mut().take());
        }
    }

    /// Answer every kernel observation on this thread from `maps`.
    #[cfg(all(
        target_os = "linux",
        any(target_arch = "aarch64", target_arch = "x86_64")
    ))]
    pub(crate) fn override_maps(maps: impl Into<String>) -> MapsOverrideGuard {
        override_maps_reads([maps.into()])
    }

    /// Answer successive whole-file reads on this thread from `reads` in
    /// order; the last text answers every read after it.
    #[cfg(all(
        target_os = "linux",
        any(target_arch = "aarch64", target_arch = "x86_64")
    ))]
    pub(crate) fn override_maps_reads(
        reads: impl IntoIterator<Item = String>,
    ) -> MapsOverrideGuard {
        let reads: VecDeque<String> = reads.into_iter().collect();
        assert!(!reads.is_empty(), "inject at least one maps text");
        MAPS_OVERRIDE.with(|slot| *slot.borrow_mut() = Some(Injected { reads, served: 0 }));
        MapsOverrideGuard(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAPS: &str = "\
00400000-00452000 r-xp 00000000 08:02 173521      /usr/bin/dbus-daemon
7f0000000000-7f0000002000 r-xp 00000000 00:00 0
7f0000002000-7f0000003000 r-xp 00000000 00:00 0
7f0000003000-7f0000004000 rw-p 00000000 00:00 0
7f0000004000-7f0000005000 rwxp 00000000 00:00 0
7f0000008000-7f0000009000 r-xp 00000000 00:00 0
ffffc0000000-ffffc0021000 rw-p 00000000 00:00 0                          [stack]
";

    #[test]
    fn a_uniform_range_across_adjacent_rows_is_one_run() {
        let observation =
            observe_page_protection_in_maps(MAPS, 0x7f00_0000_1000, 0x2000).expect("covered");
        assert_eq!(observation.permissions(), "r-xp");
        assert_eq!(
            observation.runs,
            vec![KernelPageRun {
                start: 0x7f00_0000_1000,
                end: 0x7f00_0000_3000,
                permissions: "r-xp".to_owned(),
            }]
        );
        assert!(!observation.writable_and_executable());
    }

    #[test]
    fn a_mixed_range_lists_each_run_and_flags_write_execute() {
        let observation =
            observe_page_protection_in_maps(MAPS, 0x7f00_0000_2000, 0x3000).expect("covered");
        assert_eq!(observation.permissions(), "r-xp|rw-p|rwxp");
        assert!(observation.writable_and_executable());
        let writable =
            observe_page_protection_in_maps(MAPS, 0x7f00_0000_3000, 0x1000).expect("covered");
        assert_eq!(writable.permissions(), "rw-p");
        assert!(!writable.writable_and_executable());
    }

    #[test]
    fn an_uncovered_range_is_refused_with_its_first_gap() {
        for (start, len, gap) in [
            // Straddles the hole after the rwxp row.
            (
                0x7f00_0000_4000,
                0x5000,
                (0x7f00_0000_5000, 0x7f00_0000_8000),
            ),
            // Wholly inside the hole.
            (
                0x7f00_0000_6000,
                0x1000,
                (0x7f00_0000_6000, 0x7f00_0000_7000),
            ),
            // Page zero: below every row.
            (0x1000, 0x1000, (0x1000, 0x2000)),
            // Beyond every row.
            (
                0xffff_ffff_0000,
                0x1000,
                (0xffff_ffff_0000, 0xffff_ffff_1000),
            ),
        ] {
            let error = observe_page_protection_in_maps(MAPS, start, len)
                .expect_err("uncovered range must be refused");
            assert_eq!(
                error,
                KernelPageProtectionError::RangeNotCovered {
                    start,
                    end: start + len,
                    gap_start: gap.0,
                    gap_end: gap.1,
                }
            );
            assert_eq!(
                error.refusal(),
                PageProtectionWitnessRefusal::RangeNotCovered
            );
            assert!(
                error
                    .to_string()
                    .starts_with("[TCG-JIT-PAGE-WITNESS-UNCOVERED]")
            );
        }
        for len in [0, u64::MAX] {
            assert_eq!(
                observe_page_protection_in_maps(MAPS, 0x7f00_0000_0000, len)
                    .expect_err("empty or wrapping range")
                    .refusal(),
                PageProtectionWitnessRefusal::RangeNotCovered
            );
        }
    }

    #[test]
    fn malformed_or_unordered_rows_are_refused_not_skipped() {
        for (maps, start, retryable) in [
            (
                "7f0000000000 r-xp 00000000 00:00 0\n",
                0x7f00_0000_0000,
                false,
            ),
            (
                "7f0000000000-7f0000001000 rwx 00000000 00:00 0\n",
                0x7f00_0000_0000,
                false,
            ),
            (
                "7f0000000000-7f0000001000 r-xq 00000000 00:00 0\n",
                0x7f00_0000_0000,
                false,
            ),
            (
                "7f0000001000-7f0000000000 r-xp 00000000 00:00 0\n",
                0x7f00_0000_0000,
                false,
            ),
            (
                "zz-7f0000001000 r-xp 00000000 00:00 0\n",
                0x7f00_0000_0000,
                false,
            ),
            // A row that goes back in address order after a covering row:
            // a torn read, refused for this text and retried by the reader.
            (
                "7f0000002000-7f0000003000 r-xp 00000000 00:00 0\n\
                 7f0000000000-7f0000001000 r-xp 00000000 00:00 0\n",
                0x7f00_0000_2800,
                true,
            ),
        ] {
            let error = observe_page_protection_in_maps(maps, start, 0x1000)
                .expect_err("malformed maps must be refused");
            assert_eq!(
                error.refusal(),
                PageProtectionWitnessRefusal::Unobservable,
                "{maps}"
            );
            assert!(
                error
                    .to_string()
                    .starts_with("[TCG-JIT-PAGE-WITNESS-UNREADABLE]")
            );
            assert_eq!(error.is_retryable(), retryable, "{maps}");
        }
    }

    fn reads_of(
        texts: Vec<&'static str>,
    ) -> (
        impl FnMut() -> Result<String, KernelPageProtectionError>,
        std::rc::Rc<std::cell::Cell<u32>>,
    ) {
        let served = std::rc::Rc::new(std::cell::Cell::new(0u32));
        let counter = served.clone();
        let read = move || {
            let index = counter.get() as usize;
            counter.set(counter.get() + 1);
            Ok(texts[index.min(texts.len() - 1)].to_owned())
        };
        (read, served)
    }

    /// A torn read in which the kernel re-emitted the observed VMA after it
    /// changed (`r-xp` then, from a later chunk, `rw-p` over the same start).
    const TORN_OVER_RANGE: &str = "\
7f0000000000-7f0000002000 r-xp 00000000 00:00 0
7f0000000000-7f0000004000 rw-p 00000000 00:00 0
";
    const CONSISTENT_RANGE: &str = "\
7f0000000000-7f0000004000 r-xp 00000000 00:00 0
";

    #[test]
    fn an_overlapping_snapshot_is_retried_not_accepted() {
        // The torn text alone is refused, never read as a mixed range.
        let torn = observe_page_protection_in_maps(TORN_OVER_RANGE, 0x7f00_0000_0000, 0x4000)
            .expect_err("an overlapping snapshot is not an observation");
        assert!(
            matches!(torn, KernelPageProtectionError::Inconsistent { .. }),
            "{torn:?}"
        );
        assert!(torn.is_retryable());

        // Torn, then consistent: the second whole read is accepted.
        let (read, served) = reads_of(vec![TORN_OVER_RANGE, CONSISTENT_RANGE]);
        let observation =
            observe_page_protection_in_maps_reads(read, 0x7f00_0000_0000, 0x4000).expect("retried");
        assert_eq!(served.get(), 2);
        assert_eq!(observation.attempts, 2);
        assert_eq!(observation.permissions(), "r-xp");
        assert_eq!(observation.reader, KernelMapsReader::MapsText);

        // Torn on every read: refused by name after the last attempt.
        let (read, served) = reads_of(vec![TORN_OVER_RANGE]);
        let error = observe_page_protection_in_maps_reads(read, 0x7f00_0000_0000, 0x4000)
            .expect_err("no consistent read");
        assert_eq!(served.get(), KERNEL_WITNESS_READ_ATTEMPTS);
        assert!(
            matches!(
                error,
                KernelPageProtectionError::Inconsistent { attempts, .. }
                    if attempts == KERNEL_WITNESS_READ_ATTEMPTS
            ),
            "{error:?}"
        );
        assert_eq!(error.refusal(), PageProtectionWitnessRefusal::Unobservable);
        let text = error.to_string();
        assert!(
            text.starts_with(
                "[TCG-JIT-PAGE-WITNESS-UNREADABLE] no consistent /proc/self/maps snapshot"
            ),
            "{text}"
        );
        assert!(text.contains(&format!("after {KERNEL_WITNESS_READ_ATTEMPTS} read(s)")));
    }

    #[test]
    fn a_torn_row_wholly_below_the_range_does_not_affect_coverage() {
        // The shape seen on the Linux host while glibc grew a malloc arena:
        // the arena row is listed again, grown, from a later chunk.
        let maps = "\
fc5109574000-fc5109578000 rw-p 00000000 00:00 0
fc5109574000-fc5109580000 rw-p 00000000 00:00 0
fd0000000000-fd0000004000 r-xp 00000000 00:00 0
";
        let observation =
            observe_page_protection_in_maps(maps, 0xfd00_0000_0000, 0x4000).expect("covered");
        assert_eq!(observation.permissions(), "r-xp");
        assert_eq!(observation.attempts, 1);
        // The same disorder once the range has begun is not tolerated.
        let within = "\
fd0000000000-fd0000002000 r-xp 00000000 00:00 0
fc5109574000-fc5109580000 rw-p 00000000 00:00 0
fd0000002000-fd0000004000 r-xp 00000000 00:00 0
";
        assert!(matches!(
            observe_page_protection_in_maps(within, 0xfd00_0000_0000, 0x4000),
            Err(KernelPageProtectionError::Inconsistent { .. })
        ));
        // A backwards row that reaches into the range is not tolerated.
        let reaching = "\
fc0000000000-fcff00002000 rw-p 00000000 00:00 0
fcff00000000-fd0000004000 r-xp 00000000 00:00 0
";
        assert!(matches!(
            observe_page_protection_in_maps(reaching, 0xfd00_0000_0000, 0x4000),
            Err(KernelPageProtectionError::Inconsistent { .. })
        ));
        // A tolerated backwards row does not lower the ordering bound: the
        // next row still overlaps the first one and reaches into the range.
        let after_tolerated = "\
100000-200000 rw-p 00000000 00:00 0
150000-180000 rw-p 00000000 00:00 0
190000-300000 r-xp 00000000 00:00 0
";
        assert!(matches!(
            observe_page_protection_in_maps(after_tolerated, 0x25_0000, 0x1000),
            Err(KernelPageProtectionError::Inconsistent { .. })
        ));
    }

    #[test]
    fn uncovered_reads_are_retried_and_malformed_reads_are_not() {
        let uncovered = "7f0000000000-7f0000001000 r-xp 00000000 00:00 0\n";
        let (read, served) = reads_of(vec![uncovered, CONSISTENT_RANGE]);
        let observation =
            observe_page_protection_in_maps_reads(read, 0x7f00_0000_0000, 0x4000).expect("retried");
        assert_eq!((served.get(), observation.attempts), (2, 2));

        let (read, served) = reads_of(vec![uncovered]);
        let error = observe_page_protection_in_maps_reads(read, 0x7f00_0000_0000, 0x4000)
            .expect_err("never covered");
        assert_eq!(served.get(), KERNEL_WITNESS_READ_ATTEMPTS);
        assert_eq!(
            error,
            KernelPageProtectionError::RangeNotCovered {
                start: 0x7f00_0000_0000,
                end: 0x7f00_0000_4000,
                gap_start: 0x7f00_0000_1000,
                gap_end: 0x7f00_0000_4000,
            }
        );

        let (read, served) = reads_of(vec!["not a maps row\n", CONSISTENT_RANGE]);
        let error = observe_page_protection_in_maps_reads(read, 0x7f00_0000_0000, 0x4000)
            .expect_err("a malformed row is refused at once");
        assert_eq!(served.get(), 1);
        assert!(matches!(error, KernelPageProtectionError::Malformed { .. }));

        let mut failures = 0u32;
        let error = observe_page_protection_in_maps_reads(
            || {
                failures += 1;
                Err(KernelPageProtectionError::Unreadable {
                    detail: "injected".to_owned(),
                })
            },
            0x7f00_0000_0000,
            0x4000,
        )
        .expect_err("an I/O error is refused at once");
        assert_eq!(failures, 1);
        assert_eq!(error.refusal(), PageProtectionWitnessRefusal::Unobservable);
    }

    #[test]
    fn the_host_source_is_the_kernel_only_on_linux() {
        assert_eq!(
            host_page_protection_witness_source(),
            if cfg!(target_os = "linux") {
                PageProtectionWitnessSource::KernelProcSelfMaps
            } else {
                PageProtectionWitnessSource::RecordedOnly
            }
        );
    }

    /// The live kernel file really is read on Linux: a range in page zero
    /// (below `vm.mmap_min_addr`, so never mapped) is uncovered.
    #[cfg(target_os = "linux")]
    #[test]
    fn the_live_kernel_does_not_cover_page_zero() {
        let error =
            observe_kernel_page_protection(0x1000, 0x1000).expect_err("page zero is never mapped");
        assert_eq!(
            error.refusal(),
            PageProtectionWitnessRefusal::RangeNotCovered
        );
    }

    /// Both live readers see a heap allocation as private read-write, and
    /// the default reader is `PROCMAP_QUERY` exactly when the kernel has it.
    #[cfg(target_os = "linux")]
    #[test]
    fn the_live_readers_agree_on_a_heap_allocation() {
        let block = vec![0u8; 1 << 20];
        let start = block.as_ptr() as u64;
        let len = block.len() as u64;
        let default = observe_kernel_page_protection(start, len).expect("heap is mapped");
        let text = observe_kernel_page_protection_from_maps_text(start, len).expect("heap");
        assert_eq!(default.permissions(), "rw-p");
        assert_eq!(text.permissions(), "rw-p");
        assert_eq!(default.runs, text.runs);
        assert_eq!(text.reader, KernelMapsReader::MapsText);
        assert_eq!(
            default.reader,
            if kernel_supports_procmap_query() {
                KernelMapsReader::ProcmapQuery
            } else {
                KernelMapsReader::MapsText
            }
        );
        let error = observe_kernel_page_protection_from_maps_text(0x1000, 0x1000)
            .expect_err("page zero is never mapped");
        assert_eq!(
            error.refusal(),
            PageProtectionWitnessRefusal::RangeNotCovered
        );
        drop(block);
    }
}
