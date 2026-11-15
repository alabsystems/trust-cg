// trust-cg-codegen/tests/jit_icache_coherence.rs - native I/D-cache coherence controls
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Republication rows (both hosts). They publish a straight-line AArch64
// image that spans several pages (three 16 KiB pages, i.e. twelve 4 KiB
// pages, plus a tail that ends mid-line) and execute every instruction of
// it. Then they patch the image and republish it into a fresh mapping. The
// kernel normally places that mapping at the virtual address the previous
// image just vacated, where a stale instruction-cache line would execute the
// OLD code. Every instruction is an `ADD X0, X0, #imm12`, so the returned
// value is the exact sum of the immediates the core actually fetched: a
// single stale or unmaintained line anywhere in the image changes the
// result. These rows are positive end-to-end controls, not discriminating
// ones. A republished image lands on fresh physical pages, which the kernel
// maintains itself when it first maps them executable. With the `ic ivau`
// walk removed these rows still passed on Apple M4 and on the Linux AArch64
// host.
//
// In-place rows (Linux only). They discriminate. Each rewrites code on the
// SAME physical page it just executed, through an RX -> RW -> RX cycle on
// memory the test owns (published buffers never take that cycle). Linux
// skips its own maintenance for a page it has already made coherent, so the
// only thing between the rewrite and the next fetch is the production walk:
// `trust_cg_codegen::jit::flush_instruction_cache` calls `sys::flush_icache`,
// the same function the publisher calls. These rows pin what that walk does,
// not that publication calls it. Unmaintained witness rounds alternate with the
// production rounds on the same page. When CTR_EL0.DIC is 0 the witness
// rounds must execute stale code, which shows the hazard is live on the
// host. Every production round must execute the new code, on the writing
// core and on a second core, with a placement for each core type in the
// affinity mask (the Linux AArch64 host has Cortex-X925 and Cortex-A725
// cores). Removing the `ic ivau` walk, or doubling its
// stride past CTR_EL0's minimum line, fails both rows on the Linux AArch64
// host. The mutation evidence is recorded in
// reports/perf/2026-09-23-linux-icache-in-place-control/README.md.
//
// Structural rows (both hosts). Removing the publisher's call to the walk
// (in `MappedRegion::seal_rx_and_verify`) is not detected by any execution
// row on Linux: the republication rows land on fresh pages, which the kernel
// maintains, and the in-place rows call the walk directly. The publisher row
// therefore reads the per-thread walk record
// (`jit::instruction_cache_walks_on_current_thread`) around each
// publication. It requires at least one completed walk, the last of which
// starts at the mapping's first byte and covers the whole image (one call
// site, `MappedRegion::seal_rx_and_verify`, serves both publication paths;
// the row drives the serialized-buffer path). This detects a removed call and a
// shortened range; it is a record of the call, not of its cache effect or of
// its order relative to the read-execute seal. The empty-range row requires
// `flush_instruction_cache(start, 0)` to visit no line even at a dangling
// address. Evidence record:
// reports/perf/2026-09-23-linux-icache-publisher-walk-control/README.md.
//
// The encodings are checked by an independent field decoder before
// publication. Required-floor target: registered in
// scripts/check_linux_aarch64.py.
//
// Evidence boundary: this is execution evidence from the hosts that ran it,
// not a proof. When CTR_EL0.DIC is 1 the hardware keeps instruction fetch
// coherent and the in-place rows are positive-only. A kernel that reports
// DIC as 0 on coherent hardware, or that maintains a page on every change to
// execute permission, hides the hazard: the in-place rows then fail their
// non-vacuity check instead of passing. When CTR_EL0.IDC is 1,
// as on the Linux AArch64 host, instruction fetch already sees the data
// cache, so no row detects a missing `dc cvau` walk. Darwin has no in-place
// row here; there the discriminating control is the same-page library test
// `jit::tests::in_place_rewrite_is_coherent_only_through_the_maintenance_walk`.

#![cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]

use std::collections::HashMap;

use trust_cg_codegen::jit::{
    AARCH64_MAX_CACHE_LINE_BYTES, AARCH64_MIN_CACHE_LINE_BYTES, ExecutableBuffer,
    JitCacheLineSource, flush_instruction_cache, instruction_cache_walks_on_current_thread,
    jit_cache_line_geometry, publish_serialized_buffer_for_target,
};
use trust_cg_codegen::jit_contract::TargetDescriptor;

/// Three 16 KiB pages (twelve 4 KiB pages) plus a 148-byte tail.
const IMAGE_BYTES: usize = 3 * 16 * 1024 + 148;
const INSTRUCTIONS: usize = IMAGE_BYTES / 4;
const ADDS: usize = INSTRUCTIONS - 1;
const ENTRY_STRIDE: usize = 4096;
const RET: u32 = 0xd65f_03c0;

/// `ADD X0, X0, #imm12` (A64 ADD immediate, sf=1, op=0, S=0, sh=0).
fn encode_add_x0(imm: u32) -> u32 {
    assert!(imm < 4096, "imm12 out of range: {imm}");
    0x9100_0000 | (imm << 10)
}

/// Independent field decode of an ADD (immediate) word: returns imm12 only
/// for exactly `ADD X0, X0, #imm12` with no shift.
fn decode_add_x0(word: u32) -> Option<u32> {
    let sf_op_s = word >> 29; // sf=1, op=0, S=0
    let class = (word >> 23) & 0x3f; // 0b100010 add/sub immediate
    let sh = (word >> 22) & 1;
    let rn = (word >> 5) & 0x1f;
    let rd = word & 0x1f;
    (sf_op_s == 0b100 && class == 0b10_0010 && sh == 0 && rn == 0 && rd == 0)
        .then_some((word >> 10) & 0xfff)
}

/// Round-dependent immediates: strictly increasing in `round` for every
/// index, so a line fetched from any earlier round lowers the sum.
fn round_immediates(round: u32) -> Vec<u32> {
    assert!(round < 15);
    (0..ADDS as u32)
        .map(|i| (i * 7 + round * 13) % 251 + round * 256)
        .collect()
}

fn image_for(immediates: &[u32]) -> Vec<u8> {
    assert_eq!(immediates.len(), ADDS);
    let mut words: Vec<u32> = immediates.iter().copied().map(encode_add_x0).collect();
    words.push(RET);
    for (index, (&word, &imm)) in words.iter().zip(immediates).enumerate() {
        assert_eq!(
            decode_add_x0(word),
            Some(imm),
            "encoding {index} does not decode"
        );
    }
    assert_eq!(decode_add_x0(RET), None);
    let image: Vec<u8> = words.iter().flat_map(|word| word.to_le_bytes()).collect();
    assert_eq!(image.len(), IMAGE_BYTES);
    image
}

fn entry_offsets() -> Vec<usize> {
    (0..IMAGE_BYTES - 4).step_by(ENTRY_STRIDE).collect()
}

fn publish(image: &[u8]) -> ExecutableBuffer {
    let offsets = entry_offsets();
    let names: Vec<String> = offsets
        .iter()
        .map(|offset| format!("entry_{offset:05x}"))
        .collect();
    let symbol_offsets: HashMap<String, u64> = names
        .iter()
        .zip(&offsets)
        .map(|(name, &offset)| (name.clone(), offset as u64))
        .collect();
    let ranges = names
        .iter()
        .zip(&offsets)
        .map(|(name, &offset)| (name.clone(), offset as u64..image.len() as u64))
        .collect();
    // SAFETY: the image is the reviewed straight-line ADD/RET sequence built
    // above; every word was independently decoded, every symbol offset is an
    // instruction boundary inside the image, and the target contract is the
    // live host contract.
    let buffer = unsafe {
        publish_serialized_buffer_for_target(
            image,
            names,
            symbol_offsets,
            ranges,
            &TargetDescriptor::for_trust_cg_host_jit(),
        )
    }
    .expect("publish multi-page image");
    assert_eq!(
        buffer.code_slice(),
        image,
        "mapping must hold the exact image"
    );
    buffer
        .verify_published_code_integrity()
        .expect("published image hash");
    buffer
}

/// Execute every entry and require the exact fetched-immediate sums.
fn assert_executes(buffer: &ExecutableBuffer, immediates: &[u32], context: &str) {
    for offset in entry_offsets() {
        let name = format!("entry_{offset:05x}");
        let f = unsafe {
            buffer
                .get_fn_bound::<extern "C" fn(u64) -> u64>(&name)
                .expect("entry resolves")
        };
        let first = offset / 4;
        let expected: u64 = immediates[first..].iter().map(|&imm| u64::from(imm)).sum();
        let seed = 0x5eed_0000_0000u64 + offset as u64;
        assert_eq!(
            (*f.as_ref())(seed),
            seed + expected,
            "{context}: entry at byte {offset:#x} executed stale or unmaintained code"
        );
    }
}

#[test]
fn cache_line_geometry_is_architectural_and_its_source_is_recorded() {
    let geometry = jit_cache_line_geometry();
    for line in [
        geometry.dcache_min_line_bytes,
        geometry.icache_min_line_bytes,
    ] {
        assert!(line.is_power_of_two(), "{geometry:?}");
        assert!(
            (AARCH64_MIN_CACHE_LINE_BYTES..=AARCH64_MAX_CACHE_LINE_BYTES).contains(&line),
            "{geometry:?}"
        );
    }
    #[cfg(target_os = "linux")]
    {
        assert_eq!(geometry.source, JitCacheLineSource::CtrEl0, "{geometry:?}");
        let raw = geometry.ctr_el0.expect("Linux reads CTR_EL0");
        assert_eq!(geometry.dcache_min_line_bytes, 4 << ((raw >> 16) & 0xf));
        assert_eq!(geometry.icache_min_line_bytes, 4 << (raw & 0xf));
    }
    #[cfg(target_os = "macos")]
    {
        assert!(
            matches!(
                geometry.source,
                JitCacheLineSource::ArchitecturalMinimumFallback(_)
            ),
            "{geometry:?}"
        );
        assert!(geometry.is_fallback(), "{geometry:?}");
        assert_eq!(geometry.ctr_el0, None);
        assert_eq!(geometry.dcache_min_line_bytes, AARCH64_MIN_CACHE_LINE_BYTES);
        assert_eq!(geometry.icache_min_line_bytes, AARCH64_MIN_CACHE_LINE_BYTES);
        assert_eq!(
            geometry.source.as_str(),
            "architectural_minimum_fallback:ctr_el0_unreadable"
        );
    }
}

#[test]
fn multi_page_image_republished_after_patching_executes_every_line() {
    let mut previous_base = None;
    let mut reused_bases = 0usize;
    for round in 0..12 {
        let immediates = round_immediates(round);
        let buffer = publish(&image_for(&immediates));
        assert!(
            buffer.allocated_size() >= IMAGE_BYTES,
            "image must span its whole allocation"
        );
        let base = buffer.code_slice().as_ptr() as usize;
        if previous_base == Some(base) {
            reused_bases += 1;
        }
        previous_base = Some(base);
        assert_executes(&buffer, &immediates, &format!("round {round}"));
        // Dropping unmaps the image before the next round publishes, so the
        // next mapping can reuse this virtual range.
    }
    println!("icache-coherence: {reused_bases}/11 republished rounds reused the previous base");
    // Non-vacuity: at least one patched image must have been fetched from
    // the exact virtual range its predecessor occupied.
    assert!(
        reused_bases > 0,
        "no republished round reused the vacated virtual range; the stale-line hazard was not exercised"
    );
}

#[test]
fn single_line_patches_are_visible_after_republication() {
    let mut immediates = round_immediates(0);
    let mut buffer = publish(&image_for(&immediates));
    assert_executes(&buffer, &immediates, "baseline");

    // One instruction per patch: the first and last word of every 4 KiB
    // page, the word straddling each 16 KiB boundary, the middle of a line,
    // and the final ADD before RET.
    let mut patch_indices = Vec::new();
    for page in 0..IMAGE_BYTES.div_ceil(ENTRY_STRIDE) {
        let first = page * ENTRY_STRIDE / 4;
        patch_indices.push(first);
        patch_indices.push(first + ENTRY_STRIDE / 4 - 1);
    }
    patch_indices.extend([4096 * 4 / 4 - 1, 16384 / 4, 16384 * 2 / 4 + 5, 37, ADDS - 1]);
    patch_indices.retain(|&index| index < ADDS);
    patch_indices.sort_unstable();
    patch_indices.dedup();

    for (step, index) in patch_indices.into_iter().enumerate() {
        immediates[index] = (immediates[index] + 1 + step as u32) % 4096;
        // Release the old mapping first so the patched image lands where the
        // unpatched one was fetched from.
        drop(buffer);
        buffer = publish(&image_for(&immediates));
        assert_executes(&buffer, &immediates, &format!("patch at word {index}"));
    }
}

/// Structural publisher row (both hosts; see the file header). Every
/// publication must complete a maintenance walk on the publishing thread
/// whose range starts at the mapping's first byte and covers the whole image.
/// The republication rows cannot see a publisher that skips its walk, because
/// the kernel maintains the fresh pages they land on.
#[test]
fn every_publication_walks_its_published_image() {
    for round in 0..4 {
        let immediates = round_immediates(round);
        let image = image_for(&immediates);
        let before = instruction_cache_walks_on_current_thread();
        let buffer = publish(&image);
        let after = instruction_cache_walks_on_current_thread();
        let base = buffer.code_slice().as_ptr() as usize;
        assert!(
            after.count > before.count,
            "round {round}: publication at {base:#x} completed no instruction-cache maintenance \
             walk on the publishing thread (walks before {before:?}, after {after:?})"
        );
        let walk = after.last.expect("a completed walk is recorded");
        assert_eq!(
            walk.start, base,
            "round {round}: the last maintenance walk {walk:?} does not start at the published \
             image's first byte {base:#x}"
        );
        assert!(
            walk.len >= image.len() && walk.len <= buffer.allocated_size(),
            "round {round}: the last maintenance walk {walk:?} does not cover the {}-byte image \
             inside its {}-byte mapping at {base:#x}",
            image.len(),
            buffer.allocated_size()
        );
        assert_executes(
            &buffer,
            &immediates,
            &format!("publisher walk round {round}"),
        );
    }
}

/// `flush_instruction_cache` of an empty range visits no line and records no
/// walk, even at a dangling or unmapped address. The walk starts at the line
/// containing `start`, so without the empty-range check the first call below
/// maintains the line at address 0 and the process faults.
#[test]
fn an_empty_range_is_not_walked_even_at_a_dangling_address() {
    let before = instruction_cache_walks_on_current_thread();
    for start in [
        std::ptr::NonNull::<u8>::dangling().as_ptr().cast_const(),
        Vec::<u8>::new().as_ptr(),
        usize::MAX as *const u8,
    ] {
        // SAFETY: the range is empty, which the function's contract permits
        // at any address.
        unsafe { flush_instruction_cache(start, 0) };
    }
    assert_eq!(
        instruction_cache_walks_on_current_thread(),
        before,
        "an empty range must not run or record a maintenance walk"
    );
}

/// Discriminating same-physical-page rows (Linux only; see the file header).
#[cfg(target_os = "linux")]
mod in_place {
    use std::ffi::c_void;
    use std::io;
    use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};
    use std::time::{Duration, Instant};

    use trust_cg_codegen::jit::{
        JitCacheLineSource, flush_instruction_cache, jit_cache_line_geometry,
    };

    use super::RET;

    const PROT_READ: i32 = 1;
    const PROT_WRITE: i32 = 2;
    const PROT_EXEC: i32 = 4;
    const MAP_PRIVATE: i32 = 0x02;
    const MAP_ANONYMOUS: i32 = 0x20;
    const SC_PAGESIZE: i32 = 30;
    /// glibc's `cpu_set_t` is 1024 bits.
    const CPU_SET_WORDS: usize = 16;

    unsafe extern "C" {
        fn mmap(
            addr: *mut c_void,
            len: usize,
            prot: i32,
            flags: i32,
            fd: i32,
            offset: i64,
        ) -> *mut c_void;
        fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
        fn munmap(addr: *mut c_void, len: usize) -> i32;
        fn sysconf(name: i32) -> i64;
        fn sched_getaffinity(pid: i32, cpusetsize: usize, mask: *mut u64) -> i32;
        fn sched_setaffinity(pid: i32, cpusetsize: usize, mask: *const u64) -> i32;
        fn sched_getcpu() -> i32;
    }

    /// Two 16 KiB pages plus 37 words: `WORDS - 1` ADDs and a final RET.
    const WORDS: usize = 2 * 16 * 1024 / 4 + 37;
    const IMAGE_LEN: usize = WORDS * 4;
    /// The image starts 12 bytes into a cache line, so the walk must reach a
    /// partial first line as well as a partial last one.
    const START_OFFSET: usize = 12;
    /// Round 0 installs the first image; rounds 1.. alternate an unmaintained
    /// witness round (odd) with a production-walk round (even).
    const ROUNDS: u32 = 1025;
    /// Each ADD adds `tag * TAG_UNIT` (its immediate is shifted left by 12).
    const TAG_UNIT: u64 = 1 << 12;
    const SPIN_DEADLINE: Duration = Duration::from_secs(60);
    const STOP: u64 = u64::MAX;

    /// `ADD X0, X0, #imm12, LSL #12` (A64 ADD immediate, sf=1, op=0, S=0,
    /// sh=1).
    fn encode_add_x0_lsl12(imm: u32) -> u32 {
        assert!(imm < 4096, "imm12 out of range: {imm}");
        0x9140_0000 | (imm << 10)
    }

    /// Independent field decode: imm12 only for exactly
    /// `ADD X0, X0, #imm12, LSL #12`.
    fn decode_add_x0_lsl12(word: u32) -> Option<u32> {
        let sf_op_s = word >> 29; // sf=1, op=0, S=0
        let class = (word >> 23) & 0x3f; // 0b100010 add/sub immediate
        let sh = (word >> 22) & 1;
        let rn = (word >> 5) & 0x1f;
        let rd = word & 0x1f;
        (sf_op_s == 0b100 && class == 0b10_0010 && sh == 1 && rn == 0 && rd == 0)
            .then_some((word >> 10) & 0xfff)
    }

    /// Generation tag of `round`: strictly increasing, so every word fetched
    /// from an earlier round lowers the sum by a whole number of
    /// `TAG_UNIT`s. Every round has the same shape (ADDs, then RET at the
    /// same word), so any mixture of generations a core fetches is still a
    /// straight-line ADD sequence ending in RET.
    fn tag(round: u32) -> u32 {
        round + 1
    }

    fn image(round: u32) -> Vec<u8> {
        let word = encode_add_x0_lsl12(tag(round));
        assert_eq!(decode_add_x0_lsl12(word), Some(tag(round)));
        assert_eq!(decode_add_x0_lsl12(RET), None);
        let mut words = vec![word; WORDS - 1];
        words.push(RET);
        let image: Vec<u8> = words.iter().flat_map(|word| word.to_le_bytes()).collect();
        assert_eq!(image.len(), IMAGE_LEN);
        image
    }

    fn expected_sum(round: u32) -> u64 {
        (WORDS as u64 - 1) * u64::from(tag(round)) * TAG_UNIT
    }

    fn seed(round: u32) -> u64 {
        0x5eed_0000_0000 + u64::from(round)
    }

    fn maintained(round: u32) -> bool {
        round.is_multiple_of(2)
    }

    /// Outcomes of one kind of round.
    #[derive(Debug, Default)]
    struct Tally {
        rounds: u32,
        stale_rounds: u32,
        /// Sum over executed words of the generation gap to the current
        /// round; equals the stale word count when every stale word is one
        /// round old.
        stale_generations: u64,
        max_stale_generations: u64,
        first_stale_round: Option<u32>,
        /// Results that are not the expected sum lowered by whole
        /// generations (never expected).
        other_mismatches: u32,
    }

    impl Tally {
        fn record(&mut self, round: u32, result: u64) {
            self.rounds += 1;
            let expected = seed(round) + expected_sum(round);
            if result == expected {
                return;
            }
            let deficit = expected.wrapping_sub(result);
            if result < expected && result >= seed(round) && deficit.is_multiple_of(TAG_UNIT) {
                let generations = deficit / TAG_UNIT;
                self.stale_rounds += 1;
                self.stale_generations += generations;
                self.max_stale_generations = self.max_stale_generations.max(generations);
                self.first_stale_round.get_or_insert(round);
            } else {
                self.other_mismatches += 1;
            }
        }

        fn summary(&self) -> String {
            format!(
                "{}/{} rounds stale ({} stale generations, at most {} in a round, first at round {:?})",
                self.stale_rounds,
                self.rounds,
                self.stale_generations,
                self.max_stale_generations,
                self.first_stale_round
            )
        }
    }

    /// The host's cache type, read here independently of the library.
    #[derive(Debug)]
    struct CacheType {
        raw: u64,
        idc: bool,
        dic: bool,
        imin_line: usize,
        dmin_line: usize,
    }

    fn host_cache_type() -> CacheType {
        let raw: u64;
        // SAFETY: reads the cache-type identification register (Linux lets
        // EL0 read it directly or emulates the read); no memory is touched.
        unsafe {
            core::arch::asm!(
                "mrs {raw}, ctr_el0",
                raw = out(reg) raw,
                options(nomem, nostack, preserves_flags),
            );
        }
        let cache = CacheType {
            raw,
            idc: (raw >> 28) & 1 == 1,
            dic: (raw >> 29) & 1 == 1,
            imin_line: 4 << (raw & 0xf),
            dmin_line: 4 << ((raw >> 16) & 0xf),
        };
        let geometry = jit_cache_line_geometry();
        assert_eq!(geometry.source, JitCacheLineSource::CtrEl0, "{geometry:?}");
        assert_eq!(
            geometry.ctr_el0,
            Some(raw),
            "the production walk must use the CTR_EL0 value this row reads: {cache:?}"
        );
        assert_eq!(geometry.icache_min_line_bytes, cache.imin_line, "{cache:?}");
        assert_eq!(geometry.dcache_min_line_bytes, cache.dmin_line, "{cache:?}");
        cache
    }

    fn allowed_cpus() -> Vec<usize> {
        let mut mask = [0u64; CPU_SET_WORDS];
        // SAFETY: `mask` is a writable cpu_set_t-sized buffer.
        let rc = unsafe { sched_getaffinity(0, size_of_val(&mask), mask.as_mut_ptr()) };
        assert_eq!(rc, 0, "sched_getaffinity: {}", io::Error::last_os_error());
        (0..CPU_SET_WORDS * 64)
            .filter(|&cpu| (mask[cpu / 64] >> (cpu % 64)) & 1 == 1)
            .collect()
    }

    fn pin_current_thread(cpu: usize) {
        let mut mask = [0u64; CPU_SET_WORDS];
        mask[cpu / 64] |= 1 << (cpu % 64);
        // SAFETY: `mask` is a readable cpu_set_t-sized buffer; pid 0 is the
        // calling thread (a thread this test spawned).
        let rc = unsafe { sched_setaffinity(0, size_of_val(&mask), mask.as_ptr()) };
        assert_eq!(
            rc,
            0,
            "sched_setaffinity({cpu}): {}",
            io::Error::last_os_error()
        );
        assert_eq!(current_cpu(), cpu, "thread did not move to CPU {cpu}");
    }

    fn current_cpu() -> usize {
        // SAFETY: plain query of the calling thread's CPU.
        let cpu = unsafe { sched_getcpu() };
        assert!(cpu >= 0, "sched_getcpu: {}", io::Error::last_os_error());
        cpu as usize
    }

    fn isb() {
        // SAFETY: a context-synchronisation barrier; no memory or register
        // state changes.
        unsafe { core::arch::asm!("isb", options(nostack, preserves_flags)) };
    }

    /// Test-owned anonymous mapping, rewritten in place. It is never an
    /// `ExecutableBuffer`, so the published-buffer W^X guarantee is not in
    /// play; each protection it is given is still either RW or RX.
    struct Page {
        base: *mut u8,
        size: usize,
    }

    impl Page {
        fn new() -> Self {
            // SAFETY: sysconf has no preconditions.
            let page = unsafe { sysconf(SC_PAGESIZE) };
            assert!(page > 0, "sysconf(_SC_PAGESIZE): {page}");
            let size = (START_OFFSET + IMAGE_LEN).next_multiple_of(page as usize);
            // SAFETY: a fresh private anonymous RW mapping; no existing
            // memory is replaced.
            let base = unsafe {
                mmap(
                    std::ptr::null_mut(),
                    size,
                    PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS,
                    -1,
                    0,
                )
            };
            assert!(
                base as usize != usize::MAX && !base.is_null(),
                "mmap: {}",
                io::Error::last_os_error()
            );
            Self {
                base: base.cast(),
                size,
            }
        }

        fn entry(&self) -> *mut u8 {
            // SAFETY: START_OFFSET + IMAGE_LEN <= size.
            unsafe { self.base.add(START_OFFSET) }
        }

        fn protect(&self, prot: i32) {
            // SAFETY: the whole extent this value mapped.
            let rc = unsafe { mprotect(self.base.cast(), self.size, prot) };
            assert_eq!(rc, 0, "mprotect({prot:#x}): {}", io::Error::last_os_error());
        }

        /// Write `round`'s image over the previous one on the same physical
        /// page and make it executable again. A maintained round runs the
        /// production walk while the page is still writable, the publisher's
        /// order; a witness round issues the same barriers with no cache
        /// maintenance at all.
        fn rewrite(&self, round: u32) {
            if round > 0 {
                self.protect(PROT_READ | PROT_WRITE);
            }
            let bytes = image(round);
            // SAFETY: the page is RW and the image fits after START_OFFSET;
            // no thread executes it until the RX flip below.
            unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), self.entry(), IMAGE_LEN) };
            if maintained(round) {
                // SAFETY: the range is mapped and readable.
                unsafe { flush_instruction_cache(self.entry(), IMAGE_LEN) };
            } else {
                // SAFETY: barriers only.
                unsafe { core::arch::asm!("dsb ish", "isb", options(nostack, preserves_flags)) };
            }
            self.protect(PROT_READ | PROT_EXEC);
        }
    }

    impl Drop for Page {
        fn drop(&mut self) {
            // SAFETY: the exact extent `new` mapped; nothing executes it now.
            unsafe { munmap(self.base.cast(), self.size) };
        }
    }

    /// Call the image at `entry`. Callers issue `isb` first.
    fn execute(entry: usize, round: u32) -> u64 {
        // SAFETY: `entry` is the first word of an RX image whose words, in
        // every generation, are ADD X0, X0, #tag, LSL #12 followed by RET.
        let f: extern "C" fn(u64) -> u64 = unsafe { std::mem::transmute(entry) };
        f(seed(round))
    }

    /// Spin until `cell` holds something other than `seen`.
    fn wait_for_change(cell: &AtomicU64, seen: u64, what: &str) -> u64 {
        let start = Instant::now();
        loop {
            for _ in 0..4096 {
                let value = cell.load(Ordering::Acquire);
                if value != seen {
                    return value;
                }
                std::hint::spin_loop();
            }
            assert!(
                start.elapsed() < SPIN_DEADLINE,
                "timed out waiting for {what}"
            );
        }
    }

    /// Posts STOP when the writer leaves, including by panic, so the
    /// executor never waits for a round that will not come.
    struct StopOnDrop<'a>(&'a AtomicU64);

    impl Drop for StopOnDrop<'_> {
        fn drop(&mut self) {
            self.0.store(STOP, Ordering::Release);
        }
    }

    /// Allowed CPUs grouped by core type (MIDR_EL1 as sysfs exposes it), in
    /// CPU order. A CPU whose MIDR_EL1 is not exposed joins the `None` group.
    fn core_types(cpus: &[usize]) -> Vec<(Option<u64>, Vec<usize>)> {
        let mut groups: Vec<(Option<u64>, Vec<usize>)> = Vec::new();
        for &cpu in cpus {
            let midr = std::fs::read_to_string(format!(
                "/sys/devices/system/cpu/cpu{cpu}/regs/identification/midr_el1"
            ))
            .ok()
            .and_then(|text| u64::from_str_radix(text.trim().trim_start_matches("0x"), 16).ok());
            match groups.iter_mut().find(|(key, _)| *key == midr) {
                Some((_, members)) => members.push(cpu),
                None => groups.push((midr, vec![cpu])),
            }
        }
        groups
    }

    fn midr_of(groups: &[(Option<u64>, Vec<usize>)], cpu: usize) -> String {
        groups
            .iter()
            .find(|(_, members)| members.contains(&cpu))
            .and_then(|(midr, _)| *midr)
            .map_or_else(|| "unknown".to_owned(), |midr| format!("{midr:#x}"))
    }

    /// One row's outcome at one CPU placement.
    struct Placement {
        label: String,
        witness: Tally,
        production: Tally,
    }

    /// Print every placement first, then require, for each, that the
    /// production walk never left stale code and, when CTR_EL0.DIC is 0,
    /// that its witness rounds observed the hazard.
    fn report_and_require(row: &str, cache: &CacheType, placements: &[Placement]) {
        for placement in placements {
            println!(
                "icache-coherence in-place ({row}) [{}]: ctr_el0={:#x} IminLine={} DminLine={} \
                 IDC={} DIC={}; unmaintained witness {}; production walk {}; other mismatches \
                 witness {} production {}",
                placement.label,
                cache.raw,
                cache.imin_line,
                cache.dmin_line,
                u8::from(cache.idc),
                u8::from(cache.dic),
                placement.witness.summary(),
                placement.production.summary(),
                placement.witness.other_mismatches,
                placement.production.other_mismatches,
            );
        }
        if cache.dic {
            println!(
                "icache-coherence in-place ({row}): CTR_EL0.DIC=1, instruction fetch is coherent \
                 in hardware; this row is positive-only on this host"
            );
        }
        assert!(!placements.is_empty(), "{row}: no CPU placement ran");
        for Placement {
            label,
            witness,
            production,
        } in placements
        {
            assert_eq!(
                witness.other_mismatches + production.other_mismatches,
                0,
                "{row} [{label}]: a result was not an expected sum lowered by whole generations \
                 (witness {witness:?}, production {production:?})"
            );
            assert_eq!(
                production.stale_rounds,
                0,
                "{row} [{label}]: the production maintenance walk left stale instructions: {}",
                production.summary()
            );
            if !cache.dic {
                assert!(
                    witness.stale_rounds > 0,
                    "{row} [{label}]: CTR_EL0.DIC=0 but no unmaintained in-place rewrite executed \
                     stale code in {} rounds, so this row cannot detect a missing or over-wide \
                     walk here",
                    witness.rounds
                );
            }
        }
    }

    fn record(round: u32, result: u64, witness: &mut Tally, production: &mut Tally) {
        if round == 0 {
            assert_eq!(
                result,
                seed(0) + expected_sum(0),
                "first image on a fresh page"
            );
        } else if maintained(round) {
            production.record(round, result);
        } else {
            witness.record(round, result);
        }
    }

    /// Write, maintain and execute every round on `cpu`.
    fn run_on_one_core(cpu: usize) -> (Tally, Tally) {
        std::thread::scope(|scope| {
            scope
                .spawn(|| {
                    pin_current_thread(cpu);
                    let page = Page::new();
                    let entry = page.entry() as usize;
                    let (mut witness, mut production) = (Tally::default(), Tally::default());
                    let mut off_cpu = 0u32;
                    for round in 0..ROUNDS {
                        page.rewrite(round);
                        isb();
                        let result = execute(entry, round);
                        off_cpu += u32::from(current_cpu() != cpu);
                        record(round, result, &mut witness, &mut production);
                    }
                    assert_eq!(off_cpu, 0, "the row left CPU {cpu}");
                    (witness, production)
                })
                .join()
                .expect("single-core writer/executor thread")
        })
    }

    /// Write and maintain every round on `writer_cpu`; execute it on
    /// `executor_cpu` after an `isb`.
    fn run_across_cores(writer_cpu: usize, executor_cpu: usize) -> (Tally, Tally) {
        assert_ne!(writer_cpu, executor_cpu);
        let posted = AtomicU64::new(0);
        let finished = AtomicU64::new(0);
        let result = AtomicU64::new(0);
        let entry_address = AtomicUsize::new(0);
        let executor_off_cpu = AtomicU32::new(0);
        let (witness, production, writer_off_cpu) = std::thread::scope(|scope| {
            let executor = scope.spawn(|| {
                pin_current_thread(executor_cpu);
                let mut seen = 0;
                loop {
                    let round_plus_one = wait_for_change(&posted, seen, "the next rewrite");
                    if round_plus_one == STOP {
                        break;
                    }
                    seen = round_plus_one;
                    // The rewrite and the walk ran on the writer's core; this
                    // core synchronises its context before fetching.
                    isb();
                    let entry = entry_address.load(Ordering::Relaxed);
                    let value = execute(entry, (round_plus_one - 1) as u32);
                    if current_cpu() != executor_cpu {
                        executor_off_cpu.fetch_add(1, Ordering::Relaxed);
                    }
                    result.store(value, Ordering::Relaxed);
                    finished.store(round_plus_one, Ordering::Release);
                }
            });
            let writer = scope.spawn(|| {
                let _stop = StopOnDrop(&posted);
                pin_current_thread(writer_cpu);
                let page = Page::new();
                entry_address.store(page.entry() as usize, Ordering::Relaxed);
                let (mut witness, mut production) = (Tally::default(), Tally::default());
                let mut off_cpu = 0u32;
                for round in 0..ROUNDS {
                    page.rewrite(round);
                    off_cpu += u32::from(current_cpu() != writer_cpu);
                    let round_plus_one = u64::from(round) + 1;
                    posted.store(round_plus_one, Ordering::Release);
                    let done = wait_for_change(&finished, round_plus_one - 1, "the executor");
                    assert_eq!(done, round_plus_one, "executor answered out of order");
                    let value = result.load(Ordering::Relaxed);
                    record(round, value, &mut witness, &mut production);
                }
                (witness, production, off_cpu)
            });
            let tallies = writer.join().expect("writer thread");
            executor.join().expect("executor thread");
            tallies
        });
        assert_eq!(writer_off_cpu, 0, "the writer left CPU {writer_cpu}");
        assert_eq!(
            executor_off_cpu.load(Ordering::Relaxed),
            0,
            "the executor left CPU {executor_cpu}"
        );
        (witness, production)
    }

    /// One core writes, runs the production walk and executes, round after
    /// round, on the same physical page. It runs once on a CPU of every core
    /// type in the affinity mask.
    #[test]
    fn in_place_rewrite_executes_new_code_only_through_the_production_walk_on_one_core() {
        let cache = host_cache_type();
        let groups = core_types(&allowed_cpus());
        let placements: Vec<Placement> = groups
            .iter()
            .map(|(_, members)| {
                // The middle CPU of the type, away from the cross-core row's
                // writer when the rows run in parallel.
                let cpu = members[members.len() / 2];
                let (witness, production) = run_on_one_core(cpu);
                Placement {
                    label: format!("cpu={cpu} midr={}", midr_of(&groups, cpu)),
                    witness,
                    production,
                }
            })
            .collect();
        report_and_require("one core", &cache, &placements);
    }

    /// One core rewrites and runs the production walk; a thread pinned to
    /// another core executes each round after an `isb`. The walk's `ic ivau`
    /// must reach the executing core's instruction cache. There is an
    /// executor of every core type in the affinity mask; the writer is the
    /// first allowed CPU that is not the executor.
    #[test]
    fn in_place_rewrite_executes_new_code_only_through_the_production_walk_on_another_core() {
        let cache = host_cache_type();
        let cpus = allowed_cpus();
        assert!(
            cpus.len() >= 2,
            "the cross-core row needs two CPUs in the affinity mask, found {cpus:?}"
        );
        let groups = core_types(&cpus);
        let placements: Vec<Placement> = groups
            .iter()
            .map(|(_, members)| {
                let executor_cpu = *members.last().expect("a core type has a CPU");
                let writer_cpu = *cpus
                    .iter()
                    .find(|&&cpu| cpu != executor_cpu)
                    .expect("two allowed CPUs");
                let (witness, production) = run_across_cores(writer_cpu, executor_cpu);
                Placement {
                    label: format!(
                        "writer_cpu={writer_cpu} midr={} executor_cpu={executor_cpu} midr={}",
                        midr_of(&groups, writer_cpu),
                        midr_of(&groups, executor_cpu)
                    ),
                    witness,
                    production,
                }
            })
            .collect();
        report_and_require("another core", &cache, &placements);
    }
}
