// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Operational resource/adapter controls. Private fixture requirements below
//! grant no source proof or public invocation authority.

use super::*;

fn requirement(bytes: usize) -> SourceEntryStackRequirement {
    SourceEntryStackRequirement {
        private_bytes: bytes,
        module_digest: trust_ir::proof::ProofDigest::sha256([1; 32]),
        code_digest: trust_ir::proof::ProofDigest::sha256([2; 32]),
        function: 0,
        image_digest: None,
        image_len: 0,
        entry_offset: 0,
        argument_count: 0,
    }
}

std::arch::global_asm!(
    ".text",
    ".p2align 2",
    ".globl _trust_cg_owned_stack_sp_probe",
    ".private_extern _trust_cg_owned_stack_sp_probe",
    "_trust_cg_owned_stack_sp_probe:",
    "mov x0, sp",
    "ret",
    ".p2align 2",
    ".globl _trust_cg_owned_stack_frame_probe",
    ".private_extern _trust_cg_owned_stack_frame_probe",
    "_trust_cg_owned_stack_frame_probe:",
    "stp x29, x30, [sp, #-16]!",
    "mov x29, sp",
    "mov x0, sp",
    "ldp x29, x30, [sp], #16",
    "ret",
);
unsafe extern "C" {
    fn trust_cg_owned_stack_sp_probe() -> u64;
    fn trust_cg_owned_stack_frame_probe() -> u64;
}

fn probe() -> *const u8 {
    trust_cg_owned_stack_sp_probe as *const () as *const u8
}

#[test]
fn owned_rw_mapping_records_real_extent_and_no_kernel_observation() {
    let owner = OwnedEntryStack::allocate(65_537).unwrap();
    let record = owner.allocation();
    assert_ne!(record.identity, 0);
    assert_eq!(record.usable_bytes, 65_536);
    assert!(record.mapped_bytes >= record.usable_bytes + HEADER_BYTES);
    assert_eq!(
        record.protection_source,
        PageProtectionWitnessSource::RecordedOnly
    );
    let (_, sp, _) = owner.extent().unwrap();
    assert_eq!(sp % ALIGNMENT, 0);
}

#[test]
fn real_adapter_establishes_the_exact_owned_sp_and_reuses_no_nonce() {
    let mut owner = OwnedEntryStack::allocate(65_536).unwrap();
    let required = requirement(16);
    let expected_sp = owner.extent().unwrap().1;
    for nonce in 1..=3 {
        let call = owner.borrow_invocation(&required).unwrap();
        assert_eq!(call.nonce, nonce);
        // SAFETY: the test-only probe performs no access and returns via LR.
        // This exercises runtime mechanics, not a source/proof receipt.
        let actual_sp = unsafe { call.invoke0_u64(probe()) }.unwrap();
        assert_eq!(actual_sp as usize, expected_sp);
    }
    println!("OWNED_ENTRY_STACK_CPU_SP_MATCH=1");
}

#[test]
fn a_real_standard_frame_uses_only_the_owned_private_window() {
    let required = requirement(16);
    let mut owner = OwnedEntryStack::allocate(16).unwrap();
    let expected_frame_sp = owner.extent().unwrap().1 - 16;
    let call = owner.borrow_invocation(&required).unwrap();
    // SAFETY: this test-only probe has the exact standard FP/LR save/restore
    // envelope, touches sixteen private bytes, and returns its actual frame SP.
    // It is an operational control, not source or machine proof authority.
    let actual =
        unsafe { call.invoke0_u64(trust_cg_owned_stack_frame_probe as *const () as *const u8) }
            .unwrap();
    assert_eq!(actual as usize, expected_frame_sp);
    let mut absent = OwnedEntryStack::allocate(0).unwrap();
    assert!(matches!(
        absent.borrow_invocation(&required),
        Err(EntryStackError::Insufficient {
            required: 16,
            available: 0
        })
    ));
    println!("OWNED_ENTRY_STACK_CPU_STANDARD_FRAME_MATCH=1");
}

#[test]
fn insufficient_zero_and_overflowing_resources_refuse_before_execution() {
    let mut owner = OwnedEntryStack::allocate(15).unwrap();
    assert_eq!(owner.allocation().usable_bytes, 0);
    assert!(matches!(
        owner.borrow_invocation(&requirement(16)),
        Err(EntryStackError::Insufficient { .. })
    ));
    assert!(matches!(
        OwnedEntryStack::allocate(usize::MAX),
        Err(EntryStackError::Extent)
    ));
    owner.next_invocation = u64::MAX;
    assert!(matches!(
        owner.borrow_invocation(&requirement(0)),
        Err(EntryStackError::IdentityExhausted)
    ));
    assert_eq!(owner.next_invocation, u64::MAX);
}

#[test]
fn foreign_identity_thread_and_storage_alias_refuse_without_a_call() {
    let mut owner = OwnedEntryStack::allocate(32).unwrap();
    let required = requirement(16);
    {
        let mut call = owner.borrow_invocation(&required).unwrap();
        call.allocation += 1;
        // SAFETY: failure occurs before the valid test probe is invoked.
        assert!(matches!(
            unsafe { call.invoke0_u64(probe()) },
            Err(EntryStackError::StaleInvocation)
        ));
    }
    {
        let mut call = owner.borrow_invocation(&required).unwrap();
        call.thread = std::thread::spawn(|| std::thread::current().id())
            .join()
            .unwrap();
        // SAFETY: failure occurs before the valid test probe is invoked.
        assert!(matches!(
            unsafe { call.invoke0_u64(probe()) },
            Err(EntryStackError::StaleInvocation)
        ));
    }
    {
        let call = owner.borrow_invocation(&required).unwrap();
        let target = call.stack.base.as_ptr();
        // SAFETY: the owner must reject this aliased non-executable target
        // before any instruction fetch; a regression would be a hard failure.
        assert!(matches!(
            unsafe { call.invoke0_u64(target) },
            Err(EntryStackError::AliasedStorage)
        ));
    }
}

#[test]
fn altered_adapter_words_and_missing_source_identity_refuse() {
    adapter::check_actual_adapter().unwrap();
    let words = [
        0x9100_03e9u32,
        0xf900_0029,
        0xaa00_03f0,
        0x9100_005f,
        0xa900_7bfd,
        0xf900_0be1,
        0x9100_03fd,
        0xd63f_0200,
        0xf940_0be9,
        0xf940_012a,
        0xa940_7bfd,
        0x9100_015f,
        0xd65f_03c0,
    ];
    let bytes: Vec<_> = words.into_iter().flat_map(u32::to_le_bytes).collect();
    for offset in 0..bytes.len() {
        let mut changed = bytes.clone();
        changed[offset] ^= 1;
        assert!(adapter::check_words(&changed).is_err());
    }
    assert!(adapter::check_words(&bytes[..bytes.len() - 4]).is_err());
    let mut absent = requirement(0);
    absent.module_digest = trust_ir::proof::ProofDigest::sha256([0; 32]);
    let mut owner = OwnedEntryStack::allocate(32).unwrap();
    assert!(matches!(
        owner.borrow_invocation(&absent),
        Err(EntryStackError::Source(_))
    ));
}

static SIGNAL_HANDLER_ADDRESS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

extern "C" fn record_signal_stack(_: libc::c_int) {
    let local = 0u8;
    // Lock-free native atomic store only; no allocation, locks or Rust callback
    // into the source. The address observes the handler's actual stack region.
    SIGNAL_HANDLER_ADDRESS.store(std::ptr::addr_of!(local) as usize, Ordering::SeqCst);
}

#[test]
fn pending_signal_runs_on_the_host_stack_after_the_owned_sp_interval() {
    struct RestoreHost {
        mask: libc::sigset_t,
        action: libc::sigaction,
    }
    impl Drop for RestoreHost {
        fn drop(&mut self) {
            // SAFETY: the test restores its originating thread's captured mask
            // and actual old process action, on the host stack after invocation.
            unsafe {
                libc::pthread_sigmask(libc::SIG_SETMASK, &self.mask, std::ptr::null_mut());
                libc::sigaction(libc::SIGUSR1, &self.action, std::ptr::null_mut());
            }
        }
    }
    let mut before = 0;
    // SAFETY: null input requests this thread's mask into a live native object.
    assert_eq!(
        unsafe { libc::pthread_sigmask(libc::SIG_SETMASK, std::ptr::null(), &mut before) },
        0
    );
    // SAFETY: all-zero signal actions are valid initial native storage; the
    // action is filled below before use, and the old action is written by OS.
    let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
    let mut old_action: libc::sigaction = unsafe { std::mem::zeroed() };
    action.sa_sigaction = record_signal_stack as *const () as usize;
    // SAFETY: these live target-selected objects and signal are valid; this
    // single-threaded test installs only a no-allocation atomic-store handler.
    assert_eq!(unsafe { libc::sigemptyset(&mut action.sa_mask) }, 0);
    assert_eq!(
        unsafe { libc::sigaction(libc::SIGUSR1, &action, &mut old_action) },
        0
    );
    let _restore = RestoreHost {
        mask: before,
        action: old_action,
    };
    let mut active = before;
    // SAFETY: select a normally unblocked test signal, then restore the actual
    // original mask through the scoped cleanup above even on a test failure.
    assert_eq!(unsafe { libc::sigdelset(&mut active, libc::SIGUSR1) }, 0);
    assert_eq!(
        unsafe { libc::pthread_sigmask(libc::SIG_SETMASK, &active, std::ptr::null_mut()) },
        0
    );
    SIGNAL_HANDLER_ADDRESS.store(0, Ordering::SeqCst);
    let signals = signal_mask::BlockedSignals::enter().unwrap();
    // SAFETY: queue only this test thread's supported signal while it is
    // actually blocked. No handler may execute during the alternate-SP interval.
    assert_eq!(
        unsafe { libc::pthread_kill(libc::pthread_self(), libc::SIGUSR1) },
        0
    );
    assert_eq!(SIGNAL_HANDLER_ADDRESS.load(Ordering::SeqCst), 0);
    let required = requirement(0);
    let mut owner = OwnedEntryStack::allocate(0).unwrap();
    let (base, sp, end) = owner.extent().unwrap();
    let call = owner.borrow_invocation(&required).unwrap();
    // SAFETY: same inert SP probe as the operational positive above. Internal
    // invocation guard retains the outer blocked mask until host SP returns.
    assert_eq!(unsafe { call.invoke0_u64(probe()) }.unwrap() as usize, sp);
    assert_eq!(SIGNAL_HANDLER_ADDRESS.load(Ordering::SeqCst), 0);
    signals.restore().unwrap();
    let handler_address = SIGNAL_HANDLER_ADDRESS.load(Ordering::SeqCst);
    assert_ne!(handler_address, 0);
    assert!(!(base..end).contains(&handler_address));
    println!("OWNED_ENTRY_STACK_PENDING_SIGNAL_DELIVERED_ON_HOST_STACK=1");
}

#[test]
fn aggregate_invocation_binds_full_image_digest_extent_and_selected_offset() {
    let image: Vec<u8> = [0xd65f03c0u32, 0xd503201f]
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect();
    let mut requirement = requirement(16);
    requirement.image_digest = Some(trust_ir::proof::ProofDigest::sha256(
        crate::jit_cert::sha256_digest(&image),
    ));
    requirement.image_len = image.len();
    requirement.entry_offset = 0;
    let mut stack = OwnedEntryStack::allocate(64).unwrap();
    let mut invocation = stack.borrow_invocation(&requirement).unwrap();
    invocation.bind_image(&image).unwrap();
    let mut changed = image.clone();
    changed[0] ^= 1;
    assert!(invocation.bind_image(&changed).is_err());
    assert!(invocation.bind_image(&image[..4]).is_err());
    invocation.bind_image(&image).unwrap();
    // No native call is attempted: a wrong entry is rejected before adapter.
    assert!(unsafe { invocation.invoke0_u64(image.as_ptr().add(4)) }.is_err());
}

#[test]
fn aggregate_invocation_without_whole_image_binding_refuses_before_adapter() {
    let image = 0xd65f03c0u32.to_le_bytes();
    let mut requirement = requirement(16);
    requirement.image_digest = Some(trust_ir::proof::ProofDigest::sha256(
        crate::jit_cert::sha256_digest(&image),
    ));
    requirement.image_len = 4;
    let mut stack = OwnedEntryStack::allocate(64).unwrap();
    let invocation = stack.borrow_invocation(&requirement).unwrap();
    assert!(unsafe { invocation.invoke0_u64(image.as_ptr()) }.is_err());
}

#[test]
fn whole_image_overlap_refuses_even_when_entry_precedes_the_stack() {
    assert!(matches!(
        disjoint_image_extent(80, 32, 100, 200),
        Err(EntryStackError::AliasedStorage)
    ));
    assert!(matches!(
        disjoint_image_extent(180, 32, 100, 200),
        Err(EntryStackError::AliasedStorage)
    ));
    assert_eq!(
        disjoint_image_extent(200, 32, 100, 200).unwrap(),
        (200, 232)
    );
    assert!(matches!(
        disjoint_image_extent(usize::MAX - 3, 8, 100, 200),
        Err(EntryStackError::Extent)
    ));
}

extern "C" fn argument_probe(value: u64) -> u64 {
    value
}

#[test]
fn one_word_adapter_preserves_full_word_and_refuses_wrong_arity() {
    // Operational ABI probe only. The separate source-peer consumer must
    // establish source/LIR/final-word and real owned-storage authority.
    adapter::check_actual_adapter1().unwrap();
    let target = argument_probe as *const () as *const u8;
    let mut stack = OwnedEntryStack::allocate(65_536).unwrap();
    let mut required = requirement(1024);
    required.argument_count = 1;
    assert!(matches!(
        unsafe {
            stack
                .borrow_invocation(&required)
                .unwrap()
                .invoke0_u64(target)
        },
        Err(EntryStackError::ArgumentCount {
            expected: 1,
            actual: 0
        })
    ));
    for value in [0, 1, 42, 1u64 << 63, u64::MAX] {
        let invocation = stack.borrow_invocation(&required).unwrap();
        assert_eq!(
            unsafe { invocation.invoke1_u64(target, value) }.unwrap(),
            value
        );
    }
    let no_arguments = requirement(16);
    assert!(matches!(
        unsafe {
            stack
                .borrow_invocation(&no_arguments)
                .unwrap()
                .invoke1_u64(target, 42)
        },
        Err(EntryStackError::ArgumentCount {
            expected: 0,
            actual: 1
        })
    ));
}

#[test]
fn one_word_adapter_rejects_wrong_argument_register_and_extent() {
    let words = [
        0x9100_03e9u32,
        0xf900_0029,
        0xaa00_03f0,
        0x9100_005f,
        0xa900_7bfd,
        0xf900_0be1,
        0x9100_03fd,
        0xaa03_03e0,
        0xd63f_0200,
        0xf940_0be9,
        0xf940_012a,
        0xa940_7bfd,
        0x9100_015f,
        0xd65f_03c0,
    ];
    let good: Vec<_> = words.into_iter().flat_map(u32::to_le_bytes).collect();
    adapter::check_words1(&good).unwrap();
    let mut changed = good.clone();
    changed[7 * 4..8 * 4].copy_from_slice(&0xaa02_03e0u32.to_le_bytes());
    assert!(adapter::check_words1(&changed).is_err());
    assert!(adapter::check_words1(&good[..good.len() - 4]).is_err());
    let mut extra = good;
    extra.extend_from_slice(&0xd503_201fu32.to_le_bytes());
    assert!(adapter::check_words1(&extra).is_err());
}
