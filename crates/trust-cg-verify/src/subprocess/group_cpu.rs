//! CPU time consumed by a supervised child's process group.
//!
//! A deadline is wall-clock time. Whether a child spent that time computing or
//! waiting for a processor on a loaded host is not visible on the wall clock;
//! its CPU time is. The supervisor starts every child in a process group of its
//! own ([`super::configure_process_group`]: the group id is the child's pid),
//! and AY solves in a worker process it forks into that group while the direct
//! child only supervises it (measured 2026-10-01 on the toolchain AY 0.26.0
//! build 9624, one-shot and `--incremental` alike: after 3 s of solving the
//! worker had 2.94 s of CPU and the direct child 0.01 s), so the measurement
//! covers the whole group: every member's own user and system time plus the
//! time of its children it has already reaped.
//!
//! The measurement never exceeds what the group consumed: a process that left
//! the group is not counted. On macOS a member that cannot be read makes the
//! whole measurement `None` (every listed member must be read, so a window's
//! start and end are taken over the same kind of total); on Linux a process
//! that exits between the listing of `/proc` and the read of its record cannot
//! be attributed and is skipped. Other platforms report `None`: no
//! measurement, never a guess.

use std::time::Duration;

/// CPU time (user + system) the members of process group `group` have
/// consumed so far, including their reaped children's. `None` when it cannot
/// be measured here (an unsupported platform, a group that is not live, a
/// member that cannot be read, or more members than one listing holds).
pub(crate) fn process_group_cpu(group: u32) -> Option<Duration> {
    platform::process_group_cpu(group)
}

/// Members one measurement lists at most; a fuller group is not measured.
#[cfg(target_os = "macos")]
const MAX_MEMBERS: usize = 256;

#[cfg(target_os = "macos")]
mod platform {
    use std::ffi::c_int;
    use std::sync::OnceLock;
    use std::time::Duration;

    pub(super) fn process_group_cpu(group: u32) -> Option<Duration> {
        let group = libc::pid_t::try_from(group)
            .ok()
            .filter(|group| *group > 1)?;
        let mut members: [libc::pid_t; super::MAX_MEMBERS] = [0; super::MAX_MEMBERS];
        let capacity = c_int::try_from(std::mem::size_of_val(&members)).ok()?;
        // SAFETY: `members` is writable storage of exactly `capacity` bytes for
        // the duration of the call; the kernel writes at most that many.
        let listed =
            unsafe { libc::proc_listpgrppids(group, members.as_mut_ptr().cast(), capacity) };
        // `proc_listpgrppids` returns the number of pids written. A full buffer
        // may have been cut short: not measured.
        let listed = usize::try_from(listed).ok()?;
        if listed == 0 || listed >= super::MAX_MEMBERS {
            return None;
        }
        let members = &members[..listed];
        if !members.contains(&group) {
            return None;
        }
        let mut ticks: u128 = 0;
        for &member in members {
            // SAFETY: an all-zero `rusage_info_v2` is a valid value of this
            // plain integer record.
            let mut usage: libc::rusage_info_v2 = unsafe { std::mem::zeroed() };
            // SAFETY: `usage` is a writable `rusage_info_v2`, the record the
            // `RUSAGE_INFO_V2` flavor fills; the kernel writes no more.
            let read = unsafe {
                libc::proc_pid_rusage(
                    member,
                    libc::RUSAGE_INFO_V2,
                    (&raw mut usage).cast::<libc::rusage_info_t>(),
                )
            };
            if read != 0 {
                return None;
            }
            ticks += u128::from(usage.ri_user_time)
                + u128::from(usage.ri_system_time)
                + u128::from(usage.ri_child_user_time)
                + u128::from(usage.ri_child_system_time);
        }
        // `rusage_info` times are Mach absolute-time units, not nanoseconds,
        // on Apple silicon (125/3 ns per unit there, 1/1 on Intel).
        let (numer, denom) = timebase()?;
        let nanos = ticks.checked_mul(u128::from(numer))? / u128::from(denom);
        Some(Duration::from_nanos(u64::try_from(nanos).ok()?))
    }

    /// The Mach timebase (`numer / denom` nanoseconds per unit), read once.
    fn timebase() -> Option<(u32, u32)> {
        static TIMEBASE: OnceLock<Option<(u32, u32)>> = OnceLock::new();
        *TIMEBASE.get_or_init(read_timebase)
    }

    // libc marks its Mach bindings deprecated in favour of the `mach2` crate;
    // the call and record are the same.
    #[allow(deprecated)]
    fn read_timebase() -> Option<(u32, u32)> {
        let mut info = libc::mach_timebase_info { numer: 0, denom: 0 };
        // SAFETY: `info` is a writable `mach_timebase_info` for the call.
        let status = unsafe { libc::mach_timebase_info(&raw mut info) };
        (status == 0 && info.numer != 0 && info.denom != 0).then_some((info.numer, info.denom))
    }
}

#[cfg(any(target_os = "linux", target_os = "android"))]
mod platform {
    use std::time::Duration;

    pub(super) fn process_group_cpu(group: u32) -> Option<Duration> {
        if group <= 1 {
            return None;
        }
        // SAFETY: `sysconf` reads a configuration value; no memory is passed.
        let hertz = u64::try_from(unsafe { libc::sysconf(libc::_SC_CLK_TCK) })
            .ok()
            .filter(|hertz| *hertz > 0)?;
        let mut ticks: u64 = 0;
        let mut found_leader = false;
        for entry in std::fs::read_dir("/proc").ok()? {
            let entry = entry.ok()?;
            let name = entry.file_name();
            let Some(pid) = name.to_str().and_then(|name| name.parse::<u32>().ok()) else {
                continue;
            };
            // A process that exited after the listing cannot be attributed.
            let Ok(record) = std::fs::read_to_string(format!("/proc/{pid}/stat")) else {
                continue;
            };
            let (member_group, member_ticks) = super::parse_proc_stat(&record)?;
            if member_group == group {
                found_leader |= pid == group;
                ticks = ticks.checked_add(member_ticks)?;
            }
        }
        if !found_leader {
            return None;
        }
        let nanos = u128::from(ticks) * 1_000_000_000 / u128::from(hertz);
        Some(Duration::from_nanos(u64::try_from(nanos).ok()?))
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux", target_os = "android")))]
mod platform {
    use std::time::Duration;

    pub(super) fn process_group_cpu(_group: u32) -> Option<Duration> {
        None
    }
}

/// `(process group, utime + stime + cutime + cstime in clock ticks)` from the
/// text of `/proc/<pid>/stat`. The command name (field 2) is parenthesised and
/// may itself contain spaces and parentheses, so the fields are counted from
/// after its LAST `)`: there the state is field 3 and the group field 5, and
/// the four times are fields 14 to 17.
#[cfg(any(target_os = "linux", target_os = "android", test))]
fn parse_proc_stat(record: &str) -> Option<(u32, u64)> {
    let after_name = record.get(record.rfind(')')? + 1..)?;
    let fields: Vec<&str> = after_name.split_ascii_whitespace().collect();
    let group = fields.get(2)?.parse().ok()?;
    let mut ticks: u64 = 0;
    for field in fields.get(11..15)? {
        // `cutime`/`cstime` are printed as signed; a negative value is not a
        // time this measurement can use.
        ticks = ticks.checked_add(u64::try_from(field.parse::<i64>().ok()?).ok()?)?;
    }
    Some((group, ticks))
}

#[cfg(test)]
#[path = "group_cpu_tests.rs"]
mod tests;
