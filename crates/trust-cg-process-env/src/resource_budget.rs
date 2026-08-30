// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed compiler resource and search-policy contracts.
//!
//! [`ArtifactNeutralExecutorBudget`] is an immutable snapshot of resources
//! that may change *how* order-stable, work-complete compilation runs without
//! changing its result. It is suitable for bounded worker pools, but it is not
//! a process-wide permit broker: independently created pools can still exceed
//! the snapshot in aggregate until they share an executor.
//!
//! [`IdentityBoundSearchPolicy`] is deliberately a different type. Candidate
//! fuel, iteration limits, solver fuel, and schedule revisions can change the
//! selected result and therefore belong in artifact/evidence identity. A wall
//! clock watchdog is intentionally absent from both types: it may cancel or
//! fail a compilation, but a timed-out or partial search must never publish an
//! artifact as though the timeout were an artifact-neutral resource knob.
//!
//! The contract lives in the dependency-light process-environment leaf so all
//! Trust Codegen frontends can share it. TY benefits from the same bounded
//! execution as Rust, direct TrustIR, JIT, and future source-language
//! frontends; none of the policy is TLA+-specific.

use std::env::VarError;
use std::fmt;
use std::num::{NonZeroU32, NonZeroU64, NonZeroUsize};

/// Operator control for Trust Codegen-owned CPU fanout.
pub const TRUST_CG_MAX_PARALLELISM_ENV: &str = "TRUST_CG_MAX_PARALLELISM";

/// Rust frontend control for its default proof-walk large-stack width.
pub const TCG_PROOF_WALK_WORKERS_ENV: &str = "TCG_PROOF_WALK_WORKERS";

/// Established stack reservation for recursive proof evaluation.
///
/// This is a resource reservation, not a semantic compiler input. Keeping the
/// value in the shared leaf prevents frontends from silently choosing
/// different large-stack sizes for the same proof engine.
pub const PROOF_VERIFIER_STACK_BYTES: usize = 32 * 1024 * 1024;

/// Immutable view of the host resources used to resolve one executor budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HostResourceSnapshot {
    available_parallelism: NonZeroUsize,
    available_memory_bytes: Option<NonZeroU64>,
}

impl HostResourceSnapshot {
    /// Capture the host resources visible to the current process.
    #[must_use]
    pub fn capture() -> Self {
        Self {
            available_parallelism: capture_available_parallelism(),
            available_memory_bytes: host_available_memory_bytes(),
        }
    }

    /// Capture CPU availability without probing host memory.
    ///
    /// Pools with a fixed memory policy should use this cheaper snapshot. It
    /// avoids reading `/proc/meminfo` on Linux merely to resolve a CPU cap.
    /// A consumer that allocates [`ArtifactNeutralExecutorBudget::large_stack_slots`]
    /// must use [`Self::capture`] instead so the aggregate reservation is
    /// memory-bounded.
    #[must_use]
    pub fn capture_cpu_only() -> Self {
        Self {
            available_parallelism: capture_available_parallelism(),
            available_memory_bytes: None,
        }
    }

    /// Construct a deterministic host snapshot, primarily for embeddings and
    /// policy tests.
    #[must_use]
    pub const fn new(
        available_parallelism: NonZeroUsize,
        available_memory_bytes: Option<NonZeroU64>,
    ) -> Self {
        Self {
            available_parallelism,
            available_memory_bytes,
        }
    }

    /// Number of logical workers the host reports as available.
    #[must_use]
    pub const fn available_parallelism(self) -> NonZeroUsize {
        self.available_parallelism
    }

    /// Instantaneous host-available-memory heuristic, when supported.
    ///
    /// This observation cannot reserve memory. Other threads or processes can
    /// invalidate it immediately after capture, so allocation must still fail
    /// closed.
    #[must_use]
    pub const fn available_memory_bytes(self) -> Option<NonZeroU64> {
        self.available_memory_bytes
    }
}

/// Defaults supplied by one compiler embedding before operator overrides.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArtifactNeutralExecutorDefaults {
    cpu_slots: NonZeroUsize,
    large_stack_slots: NonZeroUsize,
    large_stack_bytes_per_slot: NonZeroUsize,
}

impl ArtifactNeutralExecutorDefaults {
    /// Create typed non-zero executor defaults.
    #[must_use]
    pub const fn new(
        cpu_slots: NonZeroUsize,
        large_stack_slots: NonZeroUsize,
        large_stack_bytes_per_slot: NonZeroUsize,
    ) -> Self {
        Self {
            cpu_slots,
            large_stack_slots,
            large_stack_bytes_per_slot,
        }
    }
}

/// Immutable artifact-neutral execution-resource snapshot.
///
/// The snapshot may only govern lanes whose output is independent of task
/// interleaving and worker count. Search code must use
/// [`IdentityBoundSearchPolicy`] and bind it into artifact/evidence identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArtifactNeutralExecutorBudget {
    cpu_slots: NonZeroUsize,
    large_stack_slots: NonZeroUsize,
    large_stack_bytes_per_slot: NonZeroUsize,
    host: HostResourceSnapshot,
}

impl ArtifactNeutralExecutorBudget {
    /// Capture and resolve a budget for the current host.
    ///
    /// A present `TRUST_CG_MAX_PARALLELISM` must be a positive base-10
    /// integer. Invalid, zero, non-Unicode, and out-of-range values are rejected
    /// instead of silently widening to a default.
    pub fn capture(defaults: ArtifactNeutralExecutorDefaults) -> Result<Self, ResourceBudgetError> {
        Self::capture_for_host(defaults, HostResourceSnapshot::capture())
    }

    /// Capture and resolve a budget against an explicit host snapshot.
    ///
    /// This uses [`crate::var`], so thread-local test and embedding overrides
    /// remain isolated and no process-environment mutation is required. When
    /// the host snapshot carries available memory, large-stack slots are capped
    /// so their aggregate reservation cannot exceed that observation. This is
    /// a bound, not an OS reservation; pool construction must still handle a
    /// later allocation failure.
    pub fn capture_for_host(
        defaults: ArtifactNeutralExecutorDefaults,
        host: HostResourceSnapshot,
    ) -> Result<Self, ResourceBudgetError> {
        let configured = capture_positive_usize_control(TRUST_CG_MAX_PARALLELISM_ENV)?;
        Self::resolve(defaults, host, configured)
    }

    /// Resolve already-parsed inputs without consulting ambient state.
    ///
    /// Known memory below one large-stack slot is rejected. `None` preserves
    /// the conservative platform fallback for hosts without a memory probe;
    /// actual pool/thread construction must still fail closed on allocation.
    pub fn resolve(
        defaults: ArtifactNeutralExecutorDefaults,
        host: HostResourceSnapshot,
        configured_max_parallelism: Option<NonZeroUsize>,
    ) -> Result<Self, ResourceBudgetError> {
        let host_slots = host.available_parallelism;
        let cpu_slots = min_nonzero(
            configured_max_parallelism.unwrap_or(defaults.cpu_slots),
            host_slots,
        );
        // Preserve the established operator contract: an explicit global
        // parallelism value also selects the verifier-pool width. Without an
        // override, an embedding may choose a smaller large-stack default.
        let requested_large_stack_slots =
            configured_max_parallelism.unwrap_or(defaults.large_stack_slots);
        let mut large_stack_slots = min_nonzero(requested_large_stack_slots, cpu_slots);

        // Keep the aggregate stack reservation representable even on a narrow
        // host, then apply the captured memory ceiling when one is available.
        let representable_slots =
            NonZeroUsize::new(usize::MAX / defaults.large_stack_bytes_per_slot.get())
                .unwrap_or(NonZeroUsize::MIN);
        large_stack_slots = min_nonzero(large_stack_slots, representable_slots);

        if let Some(available_memory_bytes) = host.available_memory_bytes {
            let bytes_per_slot =
                u64::try_from(defaults.large_stack_bytes_per_slot.get()).unwrap_or(u64::MAX);
            let memory_slots = available_memory_bytes.get() / bytes_per_slot;
            let memory_slots = usize::try_from(memory_slots).unwrap_or(usize::MAX);
            let Some(memory_slots) = NonZeroUsize::new(memory_slots) else {
                return Err(ResourceBudgetError::InsufficientLargeStackMemory {
                    available_bytes: available_memory_bytes.get(),
                    bytes_per_slot: defaults.large_stack_bytes_per_slot.get(),
                });
            };
            large_stack_slots = min_nonzero(large_stack_slots, memory_slots);
        }

        Ok(Self {
            cpu_slots,
            large_stack_slots,
            large_stack_bytes_per_slot: defaults.large_stack_bytes_per_slot,
            host,
        })
    }

    /// Maximum CPU slots available to one compatible executor.
    #[must_use]
    pub const fn cpu_slots(self) -> NonZeroUsize {
        self.cpu_slots
    }

    /// Maximum concurrently reserved large stacks for one compatible executor.
    #[must_use]
    pub const fn large_stack_slots(self) -> NonZeroUsize {
        self.large_stack_slots
    }

    /// Bytes reserved for each large-stack slot.
    #[must_use]
    pub const fn large_stack_bytes_per_slot(self) -> NonZeroUsize {
        self.large_stack_bytes_per_slot
    }

    /// Total large-stack reservation represented by this snapshot.
    ///
    /// `None` means the product does not fit in `usize`; consumers must reject
    /// that configuration rather than wrap it.
    #[must_use]
    pub fn max_large_stack_reservation_bytes(self) -> Option<NonZeroUsize> {
        self.large_stack_slots
            .get()
            .checked_mul(self.large_stack_bytes_per_slot.get())
            .and_then(NonZeroUsize::new)
    }

    /// Host facts against which this immutable budget was resolved.
    #[must_use]
    pub const fn host(self) -> HostResourceSnapshot {
        self.host
    }
}

/// Deterministic search inputs that must travel with artifact identity.
///
/// These values are intentionally not read from ambient environment here. A
/// search owner must parse them at its policy boundary, construct this value,
/// and hash/serialize every field into cache and evidence identity before any
/// result can be reused or published.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IdentityBoundSearchPolicy {
    deterministic_candidate_fuel: NonZeroU64,
    max_iterations: NonZeroU64,
    solver_fuel: NonZeroU64,
    schedule_version: NonZeroU32,
}

impl IdentityBoundSearchPolicy {
    /// Construct an explicit identity-bound search policy.
    #[must_use]
    pub const fn new(
        deterministic_candidate_fuel: NonZeroU64,
        max_iterations: NonZeroU64,
        solver_fuel: NonZeroU64,
        schedule_version: NonZeroU32,
    ) -> Self {
        Self {
            deterministic_candidate_fuel,
            max_iterations,
            solver_fuel,
            schedule_version,
        }
    }

    /// Deterministic candidate work admitted by the search.
    #[must_use]
    pub const fn deterministic_candidate_fuel(self) -> NonZeroU64 {
        self.deterministic_candidate_fuel
    }

    /// Maximum deterministic search iterations.
    #[must_use]
    pub const fn max_iterations(self) -> NonZeroU64 {
        self.max_iterations
    }

    /// Deterministic solver-work allowance.
    #[must_use]
    pub const fn solver_fuel(self) -> NonZeroU64 {
        self.solver_fuel
    }

    /// Revision of the deterministic search schedule.
    #[must_use]
    pub const fn schedule_version(self) -> NonZeroU32 {
        self.schedule_version
    }

    /// Stable, endian-independent identity material for cache/evidence keys.
    ///
    /// The four fields are encoded in declaration order using big-endian
    /// integers. A caller should domain-separate this byte sequence with its
    /// algorithm and artifact-format revision.
    #[must_use]
    pub fn canonical_identity_bytes(self) -> [u8; 28] {
        let mut identity = [0_u8; 28];
        identity[0..8].copy_from_slice(&self.deterministic_candidate_fuel.get().to_be_bytes());
        identity[8..16].copy_from_slice(&self.max_iterations.get().to_be_bytes());
        identity[16..24].copy_from_slice(&self.solver_fuel.get().to_be_bytes());
        identity[24..28].copy_from_slice(&self.schedule_version.get().to_be_bytes());
        identity
    }
}

/// Invalid artifact-neutral executor configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceBudgetError {
    /// The control exists but is not valid Unicode.
    NonUnicode { key: &'static str },
    /// The control is not a positive base-10 integer representable as `usize`.
    InvalidPositiveInteger { key: &'static str },
    /// Available host memory cannot back even one requested large stack.
    InsufficientLargeStackMemory {
        available_bytes: u64,
        bytes_per_slot: usize,
    },
}

impl fmt::Display for ResourceBudgetError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonUnicode { key } => write!(
                formatter,
                "{key} must be Unicode containing a positive base-10 integer"
            ),
            Self::InvalidPositiveInteger { key } => {
                write!(formatter, "{key} must be a positive base-10 integer")
            }
            Self::InsufficientLargeStackMemory {
                available_bytes,
                bytes_per_slot,
            } => write!(
                formatter,
                "host reports {available_bytes} available bytes, less than one {bytes_per_slot}-byte large-stack slot"
            ),
        }
    }
}

impl std::error::Error for ResourceBudgetError {}

/// Capture one optional positive-integer resource control.
///
/// Parsing is centralized here, but parsing does not classify a control as
/// artifact-neutral. The caller must use the result only in an order-stable,
/// work-complete execution lane or bind it into semantic policy identity.
pub fn capture_positive_usize_control(
    key: &'static str,
) -> Result<Option<NonZeroUsize>, ResourceBudgetError> {
    match crate::var(key) {
        Ok(value) => parse_positive_usize(key, &value).map(Some),
        Err(VarError::NotPresent) => Ok(None),
        Err(VarError::NotUnicode(_)) => Err(ResourceBudgetError::NonUnicode { key }),
    }
}

fn parse_positive_usize(
    key: &'static str,
    value: &str,
) -> Result<NonZeroUsize, ResourceBudgetError> {
    value
        .trim()
        .parse::<usize>()
        .ok()
        .and_then(NonZeroUsize::new)
        .ok_or(ResourceBudgetError::InvalidPositiveInteger { key })
}

const fn min_nonzero(left: NonZeroUsize, right: NonZeroUsize) -> NonZeroUsize {
    if left.get() <= right.get() {
        left
    } else {
        right
    }
}

fn capture_available_parallelism() -> NonZeroUsize {
    std::thread::available_parallelism().unwrap_or(NonZeroUsize::MIN)
}

/// Host-available memory in bytes, or `None` when it cannot be determined.
///
/// Linux `MemAvailable` is the kernel's estimate of memory obtainable without
/// swapping. On macOS, the estimate is the checked sum of free pages (which
/// already includes speculative pages) and explicitly purgeable pages. Active,
/// inactive, wired, and compressed pages are intentionally excluded: reclaiming
/// an inactive page can require paging or can reactivate it, while the other
/// classes are not disposable physical pages.
///
/// Every platform result is an instantaneous heuristic, not a reservation.
/// Concurrent allocation can invalidate it immediately. Probe failure, a zero
/// result, or unrepresentable arithmetic preserves the conservative `None`
/// contract instead of publishing a fabricated memory quantity.
fn host_available_memory_bytes() -> Option<NonZeroU64> {
    #[cfg(target_os = "linux")]
    {
        let meminfo = std::fs::read_to_string("/proc/meminfo").ok()?;
        for line in meminfo.lines() {
            if let Some(rest) = line.strip_prefix("MemAvailable:") {
                let kib: u64 = rest.split_whitespace().next()?.parse().ok()?;
                return NonZeroU64::new(kib.saturating_mul(1024));
            }
        }
        None
    }
    #[cfg(target_os = "macos")]
    {
        macos_memory::available_memory_bytes()
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        None
    }
}

/// Convert the macOS page classes that are explicitly free or purgeable.
///
/// `free_pages` already contains speculative pages in the public Mach
/// contract, so there is deliberately no separate speculative-page operand.
/// Checked arithmetic makes a stale or future wider counter fail as unknown
/// instead of wrapping or saturating to an invented budget.
#[cfg(any(target_os = "macos", test))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MacosReclaimablePageProbe {
    free_pages: u64,
    purgeable_pages: u64,
    page_size_bytes: u64,
}

#[cfg(any(target_os = "macos", test))]
fn macos_reclaimable_memory_bytes(probe: Option<MacosReclaimablePageProbe>) -> Option<NonZeroU64> {
    let probe = probe?;
    probe
        .free_pages
        .checked_add(probe.purgeable_pages)?
        .checked_mul(probe.page_size_bytes)
        .and_then(NonZeroU64::new)
}

#[cfg(target_os = "macos")]
mod macos_memory {
    use super::{MacosReclaimablePageProbe, NonZeroU64, macos_reclaimable_memory_bytes};

    // `libc` exposes the other public Mach declarations used below but not
    // this send-right release routine. The SDK declares both arguments as
    // Mach port names (`ipc_space_t` is an alias for `mach_port_t`).
    unsafe extern "C" {
        fn mach_port_deallocate(
            task: libc::mach_port_t,
            name: libc::mach_port_t,
        ) -> libc::kern_return_t;
    }

    /// Query public Mach VM statistics without spawning `vm_stat` or `sysctl`.
    ///
    /// `os_proc_available_memory` cannot be used here: the Apple SDK marks it
    /// unavailable on macOS. `host_statistics64` is the stable macOS interface
    /// for the page classes used by the conservative estimate.
    #[allow(
        deprecated,
        reason = "libc deprecates only its binding; mach_host_self is a public macOS SDK API"
    )]
    pub(super) fn available_memory_bytes() -> Option<NonZeroU64> {
        // SAFETY: `_SC_PAGESIZE` takes no pointer and has no caller-side
        // invariants. A negative or zero result is rejected below.
        let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        let page_size = u64::try_from(page_size).ok().filter(|size| *size != 0)?;

        // SAFETY: every field in the libc ABI structure is an integer, for
        // which an all-zero bit pattern is valid. Pre-initializing the whole
        // structure also makes partial older-kernel replies safe to inspect
        // after their returned field count is checked.
        let mut statistics = unsafe { std::mem::zeroed::<libc::vm_statistics64>() };
        let mut count = libc::HOST_VM_INFO64_COUNT;

        // SAFETY: this no-argument public Mach routine returns a send right to
        // the host port. The right is released below on every non-null path.
        let host = unsafe { libc::mach_host_self() };
        if host == libc::MACH_PORT_NULL.cast_unsigned() {
            return None;
        }

        // SAFETY: `statistics` is a live, correctly aligned ABI structure;
        // `count` advertises its full integer-sized capacity and both pointers
        // remain valid for the duration of this synchronous call.
        let status = unsafe {
            libc::host_statistics64(
                host,
                libc::HOST_VM_INFO64,
                std::ptr::addr_of_mut!(statistics).cast::<libc::integer_t>(),
                std::ptr::addr_of_mut!(count),
            )
        };

        // SAFETY: `host` is the send right returned by `mach_host_self`, and
        // `mach_task_self()` names the calling task's IPC space. Cleanup does
        // not affect the already copied statistics.
        let _release_status = unsafe { mach_port_deallocate(libc::mach_task_self(), host) };

        // A newer client can run on an older kernel that returns only an older
        // structure revision. Require the reply to cover `purgeable_count`,
        // but do not require unrelated fields appended after it.
        let purgeable_end = std::mem::offset_of!(libc::vm_statistics64, purgeable_count)
            .checked_add(std::mem::size_of::<libc::natural_t>())?;
        let integer_size = std::mem::size_of::<libc::integer_t>();
        let required_count =
            purgeable_end.checked_add(integer_size.checked_sub(1)?)? / integer_size;
        let required_count = libc::mach_msg_type_number_t::try_from(required_count).ok()?;

        let probe = (status == libc::KERN_SUCCESS && count >= required_count).then_some(
            MacosReclaimablePageProbe {
                free_pages: u64::from(statistics.free_count),
                purgeable_pages: u64::from(statistics.purgeable_count),
                page_size_bytes: page_size,
            },
        );
        macos_reclaimable_memory_bytes(probe)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::with_env_overrides;

    fn nonzero(value: usize) -> NonZeroUsize {
        NonZeroUsize::new(value).expect("test value is non-zero")
    }

    fn defaults() -> ArtifactNeutralExecutorDefaults {
        ArtifactNeutralExecutorDefaults::new(
            nonzero(8),
            nonzero(2),
            nonzero(PROOF_VERIFIER_STACK_BYTES),
        )
    }

    fn host(cpu_slots: usize) -> HostResourceSnapshot {
        HostResourceSnapshot::new(nonzero(cpu_slots), NonZeroU64::new(16 * 1024 * 1024 * 1024))
    }

    #[test]
    fn absent_override_uses_embedding_defaults_and_host_cap() {
        crate::with_env_overrides_removed(&[TRUST_CG_MAX_PARALLELISM_ENV], || {
            let budget = ArtifactNeutralExecutorBudget::capture_for_host(defaults(), host(4))
                .expect("absent override is valid");
            assert_eq!(budget.cpu_slots().get(), 4);
            assert_eq!(budget.large_stack_slots().get(), 2);
            assert_eq!(budget.large_stack_bytes_per_slot().get(), 32 * 1024 * 1024);
            assert_eq!(
                budget
                    .max_large_stack_reservation_bytes()
                    .map(NonZeroUsize::get),
                Some(64 * 1024 * 1024)
            );
        });
    }

    #[test]
    fn explicit_override_is_host_bounded_and_controls_large_stack_slots() {
        with_env_overrides(&[(TRUST_CG_MAX_PARALLELISM_ENV, "99")], || {
            let budget = ArtifactNeutralExecutorBudget::capture_for_host(defaults(), host(6))
                .expect("positive override is valid");
            assert_eq!(budget.cpu_slots().get(), 6);
            assert_eq!(budget.large_stack_slots().get(), 6);
        });
    }

    #[test]
    fn explicit_high_parallelism_cannot_overreserve_known_large_stack_memory() {
        let low_memory_host =
            HostResourceSnapshot::new(nonzero(64), NonZeroU64::new(64 * 1024 * 1024));
        with_env_overrides(&[(TRUST_CG_MAX_PARALLELISM_ENV, "64")], || {
            let budget =
                ArtifactNeutralExecutorBudget::capture_for_host(defaults(), low_memory_host)
                    .expect("two proof stacks fit in the captured memory");
            assert_eq!(budget.cpu_slots().get(), 64);
            assert_eq!(budget.large_stack_slots().get(), 2);
            assert_eq!(
                budget
                    .max_large_stack_reservation_bytes()
                    .map(NonZeroUsize::get),
                Some(64 * 1024 * 1024)
            );
        });
    }

    #[test]
    fn known_memory_below_one_large_stack_fails_closed() {
        let insufficient_host =
            HostResourceSnapshot::new(nonzero(64), NonZeroU64::new(16 * 1024 * 1024));
        assert_eq!(
            ArtifactNeutralExecutorBudget::capture_for_host(defaults(), insufficient_host),
            Err(ResourceBudgetError::InsufficientLargeStackMemory {
                available_bytes: 16 * 1024 * 1024,
                bytes_per_slot: PROOF_VERIFIER_STACK_BYTES,
            })
        );
    }

    #[test]
    fn zero_invalid_and_overflowing_controls_are_rejected() {
        for value in ["0", "", "invalid", "184467440737095516160"] {
            with_env_overrides(&[(TRUST_CG_MAX_PARALLELISM_ENV, value)], || {
                assert_eq!(
                    ArtifactNeutralExecutorBudget::capture_for_host(defaults(), host(64)),
                    Err(ResourceBudgetError::InvalidPositiveInteger {
                        key: TRUST_CG_MAX_PARALLELISM_ENV
                    })
                );
            });
        }
    }

    #[test]
    fn bridge_large_stack_default_uses_the_same_strict_parser() {
        with_env_overrides(&[(TCG_PROOF_WALK_WORKERS_ENV, " 4 ")], || {
            assert_eq!(
                capture_positive_usize_control(TCG_PROOF_WALK_WORKERS_ENV)
                    .expect("positive override is valid")
                    .map(NonZeroUsize::get),
                Some(4)
            );
        });
        with_env_overrides(&[(TCG_PROOF_WALK_WORKERS_ENV, "0")], || {
            assert_eq!(
                capture_positive_usize_control(TCG_PROOF_WALK_WORKERS_ENV),
                Err(ResourceBudgetError::InvalidPositiveInteger {
                    key: TCG_PROOF_WALK_WORKERS_ENV
                })
            );
        });
    }

    #[cfg(unix)]
    #[test]
    fn non_unicode_resource_value_is_rejected() {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt;

        let scope = crate::override_scope();
        let value = OsString::from_vec(vec![b'2', 0x80]);
        let _guard = crate::ScopedEnvVar::set(&scope, TRUST_CG_MAX_PARALLELISM_ENV, value);
        assert_eq!(
            ArtifactNeutralExecutorBudget::capture_for_host(defaults(), host(64)),
            Err(ResourceBudgetError::NonUnicode {
                key: TRUST_CG_MAX_PARALLELISM_ENV
            })
        );
    }

    #[test]
    fn capture_is_thread_local_and_immutable() {
        let barrier = std::sync::Barrier::new(2);
        std::thread::scope(|threads| {
            threads.spawn(|| {
                with_env_overrides(&[(TRUST_CG_MAX_PARALLELISM_ENV, "3")], || {
                    let captured =
                        ArtifactNeutralExecutorBudget::capture_for_host(defaults(), host(64))
                            .expect("left override is valid");
                    barrier.wait();
                    barrier.wait();
                    assert_eq!(captured.cpu_slots().get(), 3);
                });
            });
            threads.spawn(|| {
                with_env_overrides(&[(TRUST_CG_MAX_PARALLELISM_ENV, "invalid")], || {
                    barrier.wait();
                    assert!(
                        ArtifactNeutralExecutorBudget::capture_for_host(defaults(), host(64))
                            .is_err()
                    );
                    barrier.wait();
                });
            });
        });
    }

    #[test]
    fn macos_reclaimable_page_math_is_exact() {
        assert_eq!(
            macos_reclaimable_memory_bytes(Some(MacosReclaimablePageProbe {
                free_pages: 10,
                purgeable_pages: 3,
                page_size_bytes: 16 * 1024,
            }))
            .map(NonZeroU64::get),
            Some(13 * 16 * 1024)
        );
    }

    #[test]
    fn macos_reclaimable_page_math_rejects_failed_and_zero_probes() {
        assert_eq!(macos_reclaimable_memory_bytes(None), None);
        assert_eq!(
            macos_reclaimable_memory_bytes(Some(MacosReclaimablePageProbe {
                free_pages: 0,
                purgeable_pages: 0,
                page_size_bytes: 16 * 1024,
            })),
            None
        );
        assert_eq!(
            macos_reclaimable_memory_bytes(Some(MacosReclaimablePageProbe {
                free_pages: 1,
                purgeable_pages: 0,
                page_size_bytes: 0,
            })),
            None
        );
    }

    #[test]
    fn macos_reclaimable_page_math_rejects_overflow() {
        assert_eq!(
            macos_reclaimable_memory_bytes(Some(MacosReclaimablePageProbe {
                free_pages: u64::MAX,
                purgeable_pages: 1,
                page_size_bytes: 1,
            })),
            None
        );
        assert_eq!(
            macos_reclaimable_memory_bytes(Some(MacosReclaimablePageProbe {
                free_pages: u64::MAX,
                purgeable_pages: 0,
                page_size_bytes: 2,
            })),
            None
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn live_macos_capture_can_back_an_established_proof_stack() {
        crate::with_env_overrides_removed(&[TRUST_CG_MAX_PARALLELISM_ENV], || {
            let snapshot = HostResourceSnapshot::capture();
            let memory = snapshot
                .available_memory_bytes()
                .expect("public Mach VM statistics should be available on macOS");
            assert!(memory.get() >= PROOF_VERIFIER_STACK_BYTES as u64);
            ArtifactNeutralExecutorBudget::capture_for_host(defaults(), snapshot)
                .expect("an ordinary macOS host should support one established proof stack");
        });
    }

    #[test]
    fn search_policy_identity_changes_with_every_semantic_field() {
        let base = IdentityBoundSearchPolicy::new(
            NonZeroU64::new(10).unwrap(),
            NonZeroU64::new(20).unwrap(),
            NonZeroU64::new(30).unwrap(),
            NonZeroU32::new(1).unwrap(),
        );
        assert_ne!(
            base,
            IdentityBoundSearchPolicy::new(
                NonZeroU64::new(11).unwrap(),
                base.max_iterations(),
                base.solver_fuel(),
                base.schedule_version(),
            )
        );
        assert_ne!(
            base,
            IdentityBoundSearchPolicy::new(
                base.deterministic_candidate_fuel(),
                NonZeroU64::new(21).unwrap(),
                base.solver_fuel(),
                base.schedule_version(),
            )
        );
        assert_ne!(
            base,
            IdentityBoundSearchPolicy::new(
                base.deterministic_candidate_fuel(),
                base.max_iterations(),
                NonZeroU64::new(31).unwrap(),
                base.schedule_version(),
            )
        );
        assert_ne!(
            base,
            IdentityBoundSearchPolicy::new(
                base.deterministic_candidate_fuel(),
                base.max_iterations(),
                base.solver_fuel(),
                NonZeroU32::new(2).unwrap(),
            )
        );
        assert_eq!(
            base.canonical_identity_bytes(),
            [
                0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0,
                1,
            ]
        );
    }
}
