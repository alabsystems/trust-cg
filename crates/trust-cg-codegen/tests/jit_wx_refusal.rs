// trust-cg-codegen/tests/jit_wx_refusal.rs - public-API W^X refusal controls
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// A caller asking a published JIT buffer for writable+executable (or merely
// writable) pages must receive a typed `JitError`, never a panic, and the
// refusal must leave the mapping read-execute: still callable, still not
// writable. The not-writable half runs in a child process because the
// expected outcome is a fatal memory-protection signal; a paired child that
// only reads the page proves the child harness itself reports success. On
// Apple Silicon the writing child first enters MAP_JIT write mode, and a third
// child proves that mode admits writes to a genuinely RWX MAP_JIT page, so the
// fault discriminates an RWX grant there too (execute mode alone would fault
// on any MAP_JIT write).
//
// The installed-binding rows exercise the page-protection witness (binding
// v6, manifest v3). On Linux the JIT observes the whole allocation through
// /proc/self/maps (PROCMAP_QUERY, or the retrying text reader) right after the
// read-execute seal, and the checked installed routes (contract lookup here,
// and into_installed_artifact) observe it again: a page this test mprotects
// writable, writable and executable, or inaccessible after publication is
// refused by name before any byte is read, and a range the maps do not cover
// is refused by name. A churn row requires zero spurious refusals while other
// threads change mappings, after showing the churn tears raw text reads. On macOS the
// binding records a recorded-only source. Forging the sealed witness is
// refused by the binding's private seal here; the named refusals of resealed
// forgeries are library unit tests, because only a cfg(test) hook can reseal.
//
// Required-floor target: registered in scripts/check_linux_aarch64.py.

#![cfg(all(
    unix,
    any(target_arch = "x86_64", target_arch = "aarch64"),
    any(target_os = "macos", target_os = "linux")
))]

use std::collections::HashMap;
use std::os::unix::process::ExitStatusExt;

use trust_cg_codegen::Compiler;
use trust_cg_codegen::compiler::CompilerConfig;
use trust_cg_codegen::jit::{ExecutableBuffer, JitError, JitPageProtection};
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

const ANSWER: &str = "answer";
const CHILD_ENV: &str = "TRUST_CG_JIT_WX_REFUSAL_CHILD";

fn publish_answer(module_name: &str) -> ExecutableBuffer {
    let mut mb = ModuleBuilder::new(module_name);
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function(ANSWER, ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let answer = fb.iconst(Ty::I64, 42);
    fb.ret(vec![answer]);
    fb.build();
    Compiler::new(CompilerConfig::for_host_jit())
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(
            &mb.build().expect("ModuleBuilder::build: test fixture"),
            &HashMap::new(),
        )
        .expect("host JIT compile must succeed")
        .buffer
}

fn call_answer(buffer: &ExecutableBuffer) -> i64 {
    let f = unsafe {
        buffer
            .get_fn_bound::<extern "C" fn() -> i64>(ANSWER)
            .expect("published symbol must resolve")
    };
    (*f.as_ref())()
}

#[test]
fn rwx_request_is_a_typed_refusal_and_the_buffer_stays_executable() {
    let buffer = publish_answer("wx_refusal_rwx");
    assert_eq!(call_answer(&buffer), 42);
    let base = buffer.code_slice().as_ptr() as u64;

    let error = buffer
        .request_page_protection(JitPageProtection::ReadWriteExecute)
        .expect_err("writable+executable must be refused");
    match &error {
        JitError::WritableExecutableProtectionRefused {
            requested,
            buffer_base,
            allocation_len,
        } => {
            assert_eq!(*requested, JitPageProtection::ReadWriteExecute);
            assert_eq!(*buffer_base, base);
            assert_eq!(*allocation_len, buffer.allocated_size());
        }
        other => panic!("expected a W^X refusal, got {other:?}"),
    }
    assert!(error.to_string().contains("W^X refusal"), "{error}");
    assert!(!JitPageProtection::ReadWriteExecute.is_w_xor_x());

    // The refusal changed nothing: the code still runs and still hashes to
    // its publication digest.
    assert_eq!(call_answer(&buffer), 42);
    buffer
        .verify_published_code_integrity()
        .expect("refused request must not disturb the published image");
}

#[test]
fn published_buffer_refuses_to_become_writable_again() {
    let buffer = publish_answer("wx_refusal_rw");
    let error = buffer
        .request_page_protection(JitPageProtection::ReadWrite)
        .expect_err("a published buffer must not return to RW");
    assert!(
        matches!(
            error,
            JitError::PublishedProtectionDowngradeRefused {
                requested: JitPageProtection::ReadWrite,
                ..
            }
        ),
        "{error:?}"
    );
    assert!(error.to_string().contains("republished"), "{error}");
    assert_eq!(call_answer(&buffer), 42);
}

#[test]
fn read_execute_request_is_granted_and_reasserts_publication() {
    let buffer = publish_answer("wx_refusal_rx");
    for _ in 0..3 {
        buffer
            .request_page_protection(JitPageProtection::ReadExecute)
            .expect("read+execute is the published state and must be granted");
        assert_eq!(call_answer(&buffer), 42);
    }
    assert!(JitPageProtection::ReadExecute.is_w_xor_x());
    assert!(JitPageProtection::ReadWrite.is_w_xor_x());
}

/// Child body: publish, have every writable request refused, then either
/// read (must exit cleanly) or write (must die by SIGSEGV/SIGBUS) the first
/// code byte.
fn run_child(mode: &str) {
    let buffer = publish_answer("wx_refusal_child");
    for requested in [
        JitPageProtection::ReadWriteExecute,
        JitPageProtection::ReadWrite,
    ] {
        buffer
            .request_page_protection(requested)
            .expect_err("writable request must be refused");
    }
    assert_eq!(call_answer(&buffer), 42);
    let code = buffer.code_slice().as_ptr() as *mut u8;
    match mode {
        "read" => {
            let byte = unsafe { std::ptr::read_volatile(code) };
            println!("wx-refusal child read {byte:#04x}");
        }
        "write" => {
            // Apple Silicon: a MAP_JIT page's effective permission also
            // depends on the per-thread write-protect toggle, and a thread in
            // execute mode faults on ANY MAP_JIT write, even to an RWX page.
            // Enter write mode first so the fault below proves the page
            // protection itself is read-execute: had a refused request
            // actually granted RWX, this write would succeed.
            #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
            unsafe {
                apple_jit::pthread_jit_write_protect_np(0)
            };
            // Must fault: the refused requests left the page read-execute.
            unsafe { std::ptr::write_volatile(code, 0) };
            println!("wx-refusal child WROTE a published code page");
        }
        other => panic!("unknown child mode {other}"),
    }
}

/// Apple Silicon controls for the per-thread MAP_JIT write toggle.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod apple_jit {
    use std::ffi::c_void;

    pub const PROT_RWX: i32 = 0x1 | 0x2 | 0x4;
    pub const MAP_PRIVATE_ANON_JIT: i32 = 0x0002 | 0x1000 | 0x0800;
    pub const PAGE: usize = 16 * 1024;

    unsafe extern "C" {
        pub fn pthread_jit_write_protect_np(enabled: i32);
        pub fn mmap(
            addr: *mut c_void,
            len: usize,
            prot: i32,
            flags: i32,
            fd: i32,
            offset: i64,
        ) -> *mut c_void;
        pub fn munmap(addr: *mut c_void, len: usize) -> i32;
    }

    /// Child body for the write-toggle positive control: a MAP_JIT page that
    /// really is RWX accepts a write once the thread enters write mode, so a
    /// fault on the published page is caused by its protection, not by the
    /// toggle failing to take effect.
    pub fn write_rwx_control() {
        // SAFETY: fresh private anonymous mapping owned by this child; the
        // write stays inside it and the mapping is released before exit.
        unsafe {
            let page = mmap(
                std::ptr::null_mut(),
                PAGE,
                PROT_RWX,
                MAP_PRIVATE_ANON_JIT,
                -1,
                0,
            );
            assert!(
                !page.is_null() && page as isize != -1,
                "MAP_JIT RWX control mapping failed"
            );
            pthread_jit_write_protect_np(0);
            std::ptr::write_volatile(page.cast::<u8>(), 0xd6);
            pthread_jit_write_protect_np(1);
            println!("wx-refusal child wrote the RWX MAP_JIT control page");
            munmap(page, PAGE);
        }
    }
}

fn spawn_child(test_name: &str, mode: &str) -> std::process::Output {
    std::process::Command::new(std::env::current_exe().expect("current test binary"))
        .arg(test_name)
        .arg("--exact")
        .arg("--nocapture")
        .arg("--test-threads=1")
        .env(CHILD_ENV, mode)
        .output()
        .expect("spawn W^X child")
}

#[test]
fn refused_requests_leave_published_code_unwritable() {
    if let Some(mode) = std::env::var_os(CHILD_ENV) {
        match mode.to_str().expect("utf-8 child mode") {
            #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
            "write-rwx-control" => apple_jit::write_rwx_control(),
            mode => run_child(mode),
        }
        return;
    }
    let name = "refused_requests_leave_published_code_unwritable";

    // Positive control: the same child harness exits cleanly when it only
    // reads the page, so a failing write child is not a broken harness.
    let read = spawn_child(name, "read");
    assert!(
        read.status.success(),
        "read child must succeed; status={:?}\nstdout:\n{}\nstderr:\n{}",
        read.status,
        String::from_utf8_lossy(&read.stdout),
        String::from_utf8_lossy(&read.stderr),
    );
    assert!(String::from_utf8_lossy(&read.stdout).contains("wx-refusal child read"));

    // Apple Silicon: the write child enters MAP_JIT write mode before it
    // writes. This control proves write mode really does admit writes to an
    // RWX MAP_JIT page, so the write child's fault is evidence that the
    // published page is not RWX.
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    {
        let control = spawn_child(name, "write-rwx-control");
        assert!(
            control.status.success()
                && String::from_utf8_lossy(&control.stdout)
                    .contains("wrote the RWX MAP_JIT control page"),
            "RWX MAP_JIT write-mode control must succeed; status={:?}\nstdout:\n{}\nstderr:\n{}",
            control.status,
            String::from_utf8_lossy(&control.stdout),
            String::from_utf8_lossy(&control.stderr),
        );
    }

    let write = spawn_child(name, "write");
    let signal = write.status.signal();
    assert!(
        matches!(signal, Some(libc_signal) if libc_signal == SIGSEGV || libc_signal == SIGBUS),
        "writing published code after refused requests must fault; status={:?}\nstdout:\n{}\nstderr:\n{}",
        write.status,
        String::from_utf8_lossy(&write.stdout),
        String::from_utf8_lossy(&write.stderr),
    );
    assert!(!String::from_utf8_lossy(&write.stdout).contains("WROTE"));
}

const SIGSEGV: i32 = 11;
#[cfg(target_os = "macos")]
const SIGBUS: i32 = 10;
#[cfg(target_os = "linux")]
const SIGBUS: i32 = 7;

/// Installed-binding page-protection witness rows (binding v6, manifest v3).
mod installed_witness {
    use std::sync::Arc;

    use trust_cg_codegen::jit_contract::{
        AbiDescriptor, AbiValue, AbiValueKind, ArtifactContractError, ArtifactManifestV1,
        ArtifactSymbol, Endianness, ExecutableMemoryProtection, InvalidationKey, JitArtifactKind,
        LayoutManifest, PageProtectionWitnessRefusal, PageProtectionWitnessSource,
        PageProtectionWitnessStage, ProofPolicy, SymbolLookupContract, SymbolSignature,
        SymbolVisibility, TargetDescriptor,
    };
    use trust_cg_codegen::jit_page_witness::PublicationPageWitness;
    use trust_cg_codegen::{
        ArtifactKind, ArtifactPayload, CompileGeneration, CompileRequest, CompileResponse,
        CompileStatus, InstalledArtifact, SourceKind, Target,
    };
    use trust_ir::Ty;
    use trust_ir_build::ModuleBuilder;

    use super::ANSWER;

    fn answer_signature() -> SymbolSignature {
        SymbolSignature::extern_c(vec![], vec![AbiValue::new(AbiValueKind::I64)])
    }

    /// Host-JIT executable manifest declaring the exported `answer` symbol.
    fn answer_manifest(artifact_id: &str, generation: u64) -> ArtifactManifestV1 {
        let target = TargetDescriptor::for_trust_cg_host_jit();
        let abi =
            AbiDescriptor::for_trust_cg_target_os(Target::host(), target.operating_system.clone());
        let layout =
            LayoutManifest::lp64(Endianness::Little, Target::host().stack_alignment() as u16);
        let proof_policy = ProofPolicy::disabled();
        let invalidation = InvalidationKey::new(
            "sha256:jit-wx-refusal-witness-source",
            "trust-cg-codegen:HostJitFast",
            target.checksum(),
            abi.checksum(),
            layout.checksum(),
            proof_policy.checksum(),
            generation,
        );
        let mut manifest = ArtifactManifestV1::new(
            artifact_id,
            JitArtifactKind::ExecutableMemory,
            target,
            abi,
            layout,
            invalidation,
            proof_policy,
        );
        manifest.symbols.push(ArtifactSymbol {
            name: ANSWER.to_owned(),
            visibility: SymbolVisibility::Exported,
            signature: answer_signature(),
            offset_bytes: Some(0),
            checksum: None,
        });
        manifest
    }

    fn answer_contract(manifest: &ArtifactManifestV1) -> SymbolLookupContract {
        SymbolLookupContract::new(
            ANSWER,
            answer_signature(),
            manifest.target.checksum(),
            manifest.abi.checksum(),
            manifest.layout.checksum(),
        )
        .with_invalidation_checksum(manifest.invalidation.checksum())
        .with_manifest_checksum(manifest.checksum())
    }

    fn compile_answer(request_id: &str, manifest: &ArtifactManifestV1) -> CompileResponse {
        let mut mb = ModuleBuilder::new(request_id);
        let ty = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function(ANSWER, ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let answer = fb.iconst(Ty::I64, 42);
        fb.ret(vec![answer]);
        fb.build();
        let mut request = CompileRequest::new(
            request_id,
            CompileGeneration::new(manifest.invalidation.generation),
        )
        .with_artifact_manifest(manifest.clone());
        request.artifact_kind = ArtifactKind::ExecutableMemory;
        request.provenance.source_kind = SourceKind::TrustIrModule;
        request.provenance.source_fingerprint = Some(format!("sha256:{request_id}-source"));
        let response = super::permit_compile_service().compile(
            request,
            &mb.build().expect("ModuleBuilder::build: test fixture"),
        );
        assert_eq!(
            response.status,
            CompileStatus::Compiled,
            "{:?}",
            response.diagnostics
        );
        response
    }

    #[allow(clippy::result_large_err)] // Test helper returns the compiler's own error type unchanged.
    fn call(
        installed: &InstalledArtifact,
        manifest: &ArtifactManifestV1,
    ) -> Result<i64, ArtifactContractError> {
        let typed = installed.get_contract_symbol_bound::<extern "C" fn() -> i64>(
            manifest,
            &answer_contract(manifest),
        )?;
        // SAFETY: `answer` takes no arguments and returns an i64, exactly the
        // manifest-bound contract checked by the lookup above.
        let answer = unsafe { typed.into_fn() };
        Ok(answer())
    }

    /// Positive row on every host: the installed binding carries this host's
    /// witness, equal to the target contract and the manifest; lookup by
    /// name succeeds and runs the code.
    #[test]
    fn installed_binding_records_this_hosts_page_protection_witness() {
        let manifest = answer_manifest("jit-wx-witness-positive", 931);
        assert_eq!(manifest.schema, "trust-cg.artifact/v3");
        let response = compile_answer("jit_wx_witness_positive", &manifest);
        let binding = response
            .artifact
            .as_ref()
            .and_then(|artifact| artifact.install.installed_payload_binding.as_ref())
            .expect("installed payload binding")
            .clone();
        assert_eq!(
            binding.schema,
            "trust-cg.compile_service.installed_payload_binding.v6"
        );
        let witness = &binding.executable_memory.page_protection_witness;
        assert_eq!(
            Some(&binding.executable_memory),
            ExecutableMemoryProtection::for_trust_cg_target(&binding.authoritative_target).as_ref()
        );
        assert_eq!(
            manifest.executable_memory.as_ref(),
            Some(&binding.executable_memory)
        );
        assert_eq!(witness.recorded_permissions, "r-xp");
        let buffer = match response.payload.as_ref().expect("payload") {
            ArtifactPayload::Executable(payload) => Arc::clone(&payload.buffer),
            ArtifactPayload::Object(_) => panic!("expected executable payload"),
        };
        if cfg!(target_os = "linux") {
            assert_eq!(
                witness.source,
                PageProtectionWitnessSource::KernelProcSelfMaps
            );
            assert_eq!(witness.observed_permissions.as_deref(), Some("r-xp"));
            assert!(matches!(
                buffer.publication_page_witness(),
                PublicationPageWitness::Observed(observation)
                    if observation.permissions() == "r-xp"
            ));
        } else {
            assert_eq!(witness.source, PageProtectionWitnessSource::RecordedOnly);
            assert_eq!(witness.observed_permissions, None);
            assert_eq!(
                buffer.publication_page_witness(),
                &PublicationPageWitness::RecordedOnly
            );
        }
        let installed = response
            .into_installed_artifact()
            .expect("installed artifact");
        for _ in 0..3 {
            assert_eq!(call(&installed, &manifest).expect("lookup by name"), 42);
        }
    }

    /// A forged sealed witness cannot be resealed through the public API: the
    /// binding's private seal refuses it, whether the forgery is on the
    /// recorded or the observed half.
    #[test]
    fn a_forged_sealed_witness_is_refused_by_the_binding_seal() {
        let manifest = answer_manifest("jit-wx-witness-forged", 932);
        let installed = compile_answer("jit_wx_witness_forged", &manifest)
            .into_installed_artifact()
            .expect("installed artifact");
        assert_eq!(call(&installed, &manifest).expect("untampered lookup"), 42);
        type Forgery = fn(&mut ExecutableMemoryProtection);
        let forgeries: [(&str, Forgery); 3] = [
            ("recorded rwxp", |protection| {
                protection.page_protection_witness.recorded_permissions = "rwxp".to_owned();
            }),
            ("recorded rwxp with matching raw protection", |protection| {
                protection.published_protection |= 0x2;
                protection.page_protection_witness.recorded_permissions = "rwxp".to_owned();
            }),
            ("observed rw-p", |protection| {
                protection.page_protection_witness.observed_permissions = Some("rw-p".to_owned());
            }),
        ];
        for (name, forge) in forgeries {
            let mut metadata = installed.metadata.clone();
            forge(
                &mut metadata
                    .installed_payload_binding
                    .as_mut()
                    .expect("installed payload binding")
                    .executable_memory,
            );
            let forged = InstalledArtifact::new(Arc::clone(&installed.buffer), metadata);
            let error = call(&forged, &manifest).expect_err(name);
            assert!(
                error.to_string().contains("private canonical seal"),
                "{name}: {error}"
            );
        }
        assert_eq!(
            call(&installed, &manifest).expect("original still valid"),
            42
        );
    }

    #[cfg_attr(not(target_os = "linux"), allow(dead_code))]
    fn assert_named_lookup_refusal(
        error: &ArtifactContractError,
        expected: PageProtectionWitnessRefusal,
        fragment: &str,
    ) {
        match error {
            ArtifactContractError::PageProtectionWitnessRefused {
                refusal,
                stage,
                detail,
            } => {
                assert_eq!(*refusal, expected, "{error}");
                assert_eq!(*stage, PageProtectionWitnessStage::Lookup, "{error}");
                assert!(detail.contains(fragment), "{error}");
            }
            other => panic!("expected {} refusal, got {other}", expected.code()),
        }
        assert!(error.to_string().starts_with(expected.code()), "{error}");
    }

    #[cfg(target_os = "linux")]
    mod linux {
        use std::ffi::c_void;

        use std::sync::Arc;
        use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

        use trust_cg_codegen::jit_contract::PageProtectionWitnessRefusal;
        use trust_cg_codegen::jit_page_witness::{
            KERNEL_WITNESS_READ_ATTEMPTS, KernelMapsReader, KernelPageProtectionError,
            PublicationPageWitness, kernel_supports_procmap_query, observe_kernel_page_protection,
            observe_kernel_page_protection_from_maps_text,
        };

        use super::{answer_manifest, assert_named_lookup_refusal, call, compile_answer};

        unsafe extern "C" {
            fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
            fn mmap(
                addr: *mut c_void,
                len: usize,
                prot: i32,
                flags: i32,
                fd: i32,
                offset: i64,
            ) -> *mut c_void;
            fn munmap(addr: *mut c_void, len: usize) -> i32;
            fn sysconf(name: i32) -> i64;
        }
        const MAP_PRIVATE: i32 = 0x02;
        const MAP_ANONYMOUS: i32 = 0x20;
        const SC_PAGESIZE: i32 = 30;
        const PROT_NONE: i32 = 0;
        const PROT_READ: i32 = 1;
        const PROT_WRITE: i32 = 2;
        const PROT_EXEC: i32 = 4;

        /// Positive row: a raw published buffer's publication witness and a
        /// fresh kernel read both report `r-xp` for the whole allocation.
        #[test]
        fn kernel_witness_reads_r_xp_for_a_published_buffer() {
            let buffer = super::super::publish_answer("wx_witness_raw");
            let base = buffer.code_slice().as_ptr() as u64;
            let end = base + buffer.allocated_size() as u64;
            let PublicationPageWitness::Observed(published) = buffer.publication_page_witness()
            else {
                panic!("{:?}", buffer.publication_page_witness());
            };
            let live = buffer
                .observe_kernel_page_protection()
                .expect("live kernel witness");
            for observation in [published, &live] {
                assert_eq!((observation.start, observation.end), (base, end));
                assert_eq!(observation.permissions(), "r-xp");
                assert!(!observation.writable_and_executable());
            }
            assert_eq!(super::super::call_answer(&buffer), 42);
        }

        /// Negative rows: after publication this test mprotects the installed
        /// allocation writable, writable and executable, inaccessible, and
        /// read-only. Each lookup by name is refused with the named witness
        /// refusal before any byte is read; read-execute again restores it.
        #[test]
        fn installed_lookup_refuses_a_page_mprotected_after_publication() {
            let manifest = answer_manifest("jit-wx-witness-mprotect", 933);
            let installed = compile_answer("jit_wx_witness_mprotect", &manifest)
                .into_installed_artifact()
                .expect("installed artifact");
            assert_eq!(call(&installed, &manifest).expect("positive row"), 42);
            let base = installed.buffer.code_slice().as_ptr() as *mut c_void;
            let len = installed.buffer.allocated_size();
            let protect = |prot: i32| {
                // SAFETY: `base`/`len` are this test's own live executable
                // allocation, and nothing else runs from it meanwhile.
                let status = unsafe { mprotect(base, len, prot) };
                assert_eq!(status, 0, "mprotect({prot:#x})");
            };
            for (prot, refusal, observed) in [
                (
                    PROT_READ | PROT_WRITE,
                    PageProtectionWitnessRefusal::ObservedRecordedMismatch,
                    "reports `rw-p`, but the recorded protection is `r-xp`",
                ),
                (
                    PROT_READ | PROT_WRITE | PROT_EXEC,
                    PageProtectionWitnessRefusal::WritableExecutable,
                    "writable and executable permissions `rwxp` (recorded `r-xp`)",
                ),
                (
                    PROT_NONE,
                    PageProtectionWitnessRefusal::ObservedRecordedMismatch,
                    "reports `---p`, but the recorded protection is `r-xp`",
                ),
                (
                    PROT_READ,
                    PageProtectionWitnessRefusal::ObservedRecordedMismatch,
                    "reports `r--p`, but the recorded protection is `r-xp`",
                ),
            ] {
                protect(prot);
                let result = call(&installed, &manifest);
                protect(PROT_READ | PROT_EXEC);
                let error = result.expect_err("a changed protection must be refused");
                assert_named_lookup_refusal(&error, refusal, observed);
                assert_eq!(call(&installed, &manifest).expect("read-execute again"), 42);
            }
        }

        /// Churn one thread's mappings until `stop`: anonymous mappings of
        /// 1 to 8 pages made, partly protected read-only (splitting the VMA),
        /// restored and unmapped, interleaved with malloc/free of 8 KiB to
        /// 512 KiB blocks, which grows and trims this thread's glibc arena.
        fn churn(stop: &AtomicBool, operations: &AtomicU64, seed: u64) {
            // SAFETY: `sysconf(_SC_PAGESIZE)` has no preconditions.
            let page = unsafe { sysconf(SC_PAGESIZE) } as usize;
            let mut state = seed | 1;
            let mut held: Vec<Vec<u8>> = Vec::new();
            while !stop.load(Ordering::Relaxed) {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                let pages = 1 + (state % 8) as usize;
                let len = pages * page;
                // SAFETY: a fresh private anonymous mapping owned by this
                // loop; nothing else refers to it.
                let region = unsafe {
                    mmap(
                        std::ptr::null_mut(),
                        len,
                        PROT_READ | PROT_WRITE,
                        MAP_PRIVATE | MAP_ANONYMOUS,
                        -1,
                        0,
                    )
                };
                assert_ne!(region as isize, -1, "churn mmap");
                // SAFETY: `region`/`len` are the mapping made above; the
                // first page is protected and restored, then all unmapped.
                unsafe {
                    region.cast::<u8>().write_volatile(1);
                    assert_eq!(mprotect(region, page, PROT_READ), 0);
                    assert_eq!(mprotect(region, page, PROT_READ | PROT_WRITE), 0);
                    assert_eq!(munmap(region, len), 0);
                }
                let block = 8 * 1024 + (state as usize % (504 * 1024));
                held.push(vec![state as u8; block]);
                if held.len() > 16 {
                    held.drain(..8);
                }
                operations.fetch_add(1, Ordering::Relaxed);
            }
        }

        /// Whether one whole `/proc/self/maps` read lists a row that starts
        /// before its predecessor ends: the torn read the witness retries.
        fn one_read_is_torn() -> bool {
            let maps = std::fs::read_to_string("/proc/self/maps").expect("read maps");
            let mut previous_end = 0u64;
            for row in maps.lines() {
                let range = row.split_ascii_whitespace().next().expect("range");
                let (start, end) = range.split_once('-').expect("range has -");
                let start = u64::from_str_radix(start, 16).expect("hex start");
                let end = u64::from_str_radix(end, 16).expect("hex end");
                if start < previous_end {
                    return true;
                }
                previous_end = end;
            }
            false
        }

        /// Concurrency control: while churn threads map, protect, unmap and
        /// malloc, this thread repeatedly compiles, installs (a checked
        /// route) and looks up by contract (a checked route) through the
        /// compile service, and reads the published allocation with the
        /// retrying text reader directly. It first shows the churn really
        /// tears raw `/proc/self/maps` reads on this kernel, then requires
        /// zero witness refusals.
        #[test]
        fn witness_survives_concurrent_mapping_churn() {
            const CHURN_THREADS: u64 = 8;
            const COMPILE_ITERATIONS: u64 = 64;
            const LOOKUPS_PER_INSTALL: u64 = 8;
            const TEXT_READS: u64 = 4_000;
            const RAW_READS: u64 = 2_000;
            const RAW_READ_CAP: u64 = 200_000;

            let stop = Arc::new(AtomicBool::new(false));
            let operations = Arc::new(AtomicU64::new(0));
            let churners: Vec<_> = (0..CHURN_THREADS)
                .map(|index| {
                    let stop = Arc::clone(&stop);
                    let operations = Arc::clone(&operations);
                    std::thread::spawn(move || {
                        churn(&stop, &operations, 0x9e37_79b9_7f4a_7c15 ^ (index << 32))
                    })
                })
                .collect();
            while operations.load(Ordering::Relaxed) < 1_000 {
                std::thread::yield_now();
            }

            // Stressor control: the churn tears raw reads. At least
            // RAW_READS reads, continuing until one is torn (bounded).
            let mut raw_reads = 0u64;
            let mut torn = 0u64;
            while raw_reads < RAW_READS || (torn == 0 && raw_reads < RAW_READ_CAP) {
                raw_reads += 1;
                torn += u64::from(one_read_is_torn());
            }

            let mut installs = 0u64;
            let mut lookups = 0u64;
            let mut refusals: Vec<String> = Vec::new();
            for iteration in 0..COMPILE_ITERATIONS {
                let manifest = answer_manifest(
                    &format!("jit-wx-witness-churn-{iteration}"),
                    940 + iteration,
                );
                // Publication witness: `compile_answer` requires Compiled.
                let response =
                    compile_answer(&format!("jit_wx_witness_churn_{iteration}"), &manifest);
                let Some(installed) = response.into_installed_artifact() else {
                    refusals.push(format!("iteration {iteration}: install refused"));
                    continue;
                };
                installs += 1;
                for _ in 0..LOOKUPS_PER_INSTALL {
                    lookups += 1;
                    match call(&installed, &manifest) {
                        Ok(42) => {}
                        Ok(other) => panic!("answer returned {other}"),
                        Err(error) => refusals.push(format!("iteration {iteration}: {error}")),
                    }
                }
            }

            let buffer = super::super::publish_answer("wx_witness_churn_text");
            let base = buffer.code_slice().as_ptr() as u64;
            let len = buffer.allocated_size() as u64;
            let mut retried_text_reads = 0u64;
            let mut max_attempts = 0u32;
            for _ in 0..TEXT_READS {
                match observe_kernel_page_protection_from_maps_text(base, len) {
                    Ok(observation) => {
                        assert_eq!(observation.reader, KernelMapsReader::MapsText);
                        assert_eq!(observation.permissions(), "r-xp");
                        assert!(observation.attempts <= KERNEL_WITNESS_READ_ATTEMPTS);
                        retried_text_reads += u64::from(observation.attempts > 1);
                        max_attempts = max_attempts.max(observation.attempts);
                    }
                    Err(error) => refusals.push(format!("text reader: {error}")),
                }
            }
            let default_reader = observe_kernel_page_protection(base, len)
                .expect("default reader under churn")
                .reader;

            stop.store(true, Ordering::Relaxed);
            for churner in churners {
                churner.join().expect("churn thread");
            }
            eprintln!(
                "witness churn: churn_threads={CHURN_THREADS} churn_operations={} \
                 raw_reads={raw_reads} raw_reads_torn={torn} installs={installs} \
                 contract_lookups={lookups} text_reads={TEXT_READS} \
                 text_reads_retried={retried_text_reads} max_text_attempts={max_attempts} \
                 default_reader={default_reader:?} procmap_query={} refusals={}",
                operations.load(Ordering::Relaxed),
                kernel_supports_procmap_query(),
                refusals.len()
            );
            assert!(
                torn > 0,
                "{raw_reads} raw /proc/self/maps reads under churn were never torn: \
                 the stressor did not exercise the retry on this kernel"
            );
            assert!(
                refusals.is_empty(),
                "spurious witness refusals under churn: {refusals:#?}"
            );
            assert_eq!(installs, COMPILE_ITERATIONS);
            assert_eq!(lookups, COMPILE_ITERATIONS * LOOKUPS_PER_INSTALL);
            assert_eq!(
                default_reader,
                if kernel_supports_procmap_query() {
                    KernelMapsReader::ProcmapQuery
                } else {
                    KernelMapsReader::MapsText
                }
            );
        }

        /// Negative row: a range `/proc/self/maps` does not cover is refused
        /// by name. Page zero lies below `vm.mmap_min_addr` and the upper
        /// half of the address space belongs to the kernel, so neither is
        /// ever a user mapping.
        #[test]
        fn kernel_witness_refuses_a_range_the_maps_do_not_cover() {
            for ((start, len), observe) in [(0x1000, 0x1000), (0xffff_0000_0000_0000, 0x1000)]
                .into_iter()
                .flat_map(|range| {
                    [
                        (range, observe_kernel_page_protection as fn(u64, u64) -> _),
                        (range, observe_kernel_page_protection_from_maps_text),
                    ]
                })
            {
                let error = observe(start, len).expect_err("an unmapped range is not covered");
                assert!(
                    matches!(
                        error,
                        KernelPageProtectionError::RangeNotCovered { gap_start, .. }
                            if gap_start == start
                    ),
                    "{error:?}"
                );
                assert_eq!(
                    error.refusal(),
                    PageProtectionWitnessRefusal::RangeNotCovered
                );
                assert!(
                    error
                        .to_string()
                        .starts_with("[TCG-JIT-PAGE-WITNESS-UNCOVERED]"),
                    "{error}"
                );
            }
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// This file's fixtures carry no codegen license (`body_gate: None`), which
/// the compile service REFUSES by default (roadmap WS7.5, decision gate
/// DG-73). Its services state `Permit` explicitly, so no request passes
/// because it was silently refused.
fn permit_compile_service() -> trust_cg_codegen::CompileService {
    trust_cg_codegen::CompileService::new(trust_cg_codegen::CompileServiceConfig {
        codegen_license: trust_cg_codegen::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit),
        ..trust_cg_codegen::CompileServiceConfig::default()
    })
}
