// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Invocation-owned, non-executable stack storage for checked native entries.
//!
//! A capacity is an allocation request, never a permission witness. The
//! private allocation owner is created only after the existing anonymous RW
//! mapper succeeds. A borrowed invocation joins that owner to an exact sealed
//! source/byte requirement; it cannot be cloned, serialized or sent to another
//! thread. The fixed ARM64 adapter establishes that invocation's SP itself.
//! This runtime ownership/binding does not mint a function proof, caller BL
//! credit, SourceBoundReplay, relocation transport or an installation license.

use std::marker::PhantomData;
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::jit_contract::PageProtectionWitnessSource;

const ALIGNMENT: usize = 16;
const HEADER_BYTES: usize = 32;
const MAX_STACK_BYTES: usize = 64 * 1024 * 1024;
static NEXT_ALLOCATION: AtomicU64 = AtomicU64::new(1);

/// A named failure never produces an invocation token or callable pointer.
#[derive(Debug, thiserror::Error)]
pub enum EntryStackError {
    #[error("owned native entry stacks require ARM64/macOS")]
    UnsupportedHost,
    #[error("entry-stack capacity or address arithmetic is invalid")]
    Extent,
    #[error("could not allocate private read-write entry storage: {0}")]
    Allocate(#[source] std::io::Error),
    #[error("entry-stack allocation or invocation identity exhausted")]
    IdentityExhausted,
    #[error("entry needs {required} private bytes; this owner grants {available}")]
    Insufficient { required: usize, available: usize },
    #[error("entry-stack invocation belongs to another owner, generation or thread")]
    StaleInvocation,
    #[error("entry stack overlaps another live entry resource")]
    AliasedStorage,
    #[error("fixed native entry adapter does not match its checked instruction contract")]
    Adapter,
    #[error("entry expects {expected} scalar arguments, but invocation supplied {actual}")]
    ArgumentCount { expected: usize, actual: usize },
    #[error("owned entry requires a checked thread signal-mask contract: {0}")]
    SignalContract(String),
    #[error("source-bound entry contract refused: {0}")]
    Source(String),
    #[error("native entry publication refused: {0}")]
    Publication(String),
}

/// Allocation facts from the actual owner. macOS attribution stays recorded-only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EntryStackAllocation {
    /// Non-reused allocation identity, not an address or proof receipt.
    pub identity: u64,
    /// The privately owned usable extent below entry SP, excluding the adapter header.
    pub usable_bytes: usize,
    /// Entire actual RW mapping, including the header and page rounding.
    pub mapped_bytes: usize,
    /// How the RW/private allocation permissions are attributed.
    pub protection_source: PageProtectionWitnessSource,
}

/// Exclusively owned anonymous RW storage. It is never executable or `MAP_JIT`.
///
/// The owner exposes no raw pointer and has no Clone/serialization constructor.
/// Moving it transfers ownership; each invocation borrows it exclusively.
pub struct OwnedEntryStack {
    base: NonNull<u8>,
    mapped_bytes: usize,
    usable_bytes: usize,
    identity: u64,
    next_invocation: u64,
}

// SAFETY: moving this non-Clone value transfers exclusive ownership of one
// anonymous RW mapping. An invocation borrows it exclusively and is !Send.
unsafe impl Send for OwnedEntryStack {}

impl std::fmt::Debug for OwnedEntryStack {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OwnedEntryStack")
            .field("allocation", &self.allocation())
            .finish_non_exhaustive()
    }
}

impl OwnedEntryStack {
    /// Allocate real private RW backing. Page-rounding surplus is not granted
    /// as usable stack; the requested usable extent rounds down to SP alignment.
    pub fn allocate(usable_bytes: usize) -> Result<Self, EntryStackError> {
        if !cfg!(all(target_arch = "aarch64", target_os = "macos")) {
            return Err(EntryStackError::UnsupportedHost);
        }
        if usable_bytes > MAX_STACK_BYTES {
            return Err(EntryStackError::Extent);
        }
        let usable_bytes = usable_bytes & !(ALIGNMENT - 1);
        let requested = usable_bytes
            .checked_add(HEADER_BYTES)
            .and_then(|n| n.checked_add(super::sys::PAGE_SIZE - 1))
            .ok_or(EntryStackError::Extent)?;
        let mapped_bytes = requested & !(super::sys::PAGE_SIZE - 1);
        let identity = NEXT_ALLOCATION
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
            .map_err(|_| EntryStackError::IdentityExhausted)?;
        // SAFETY: the existing mapper requests a fresh private anonymous RW
        // region, never executable/MAP_JIT. This value alone owns the returned
        // exact extent until Drop. No address is supplied by a caller.
        let pointer = unsafe { super::sys::mmap_data_rw(0, mapped_bytes) }
            .map_err(EntryStackError::Allocate)?;
        let Some(base) = NonNull::new(pointer) else {
            // SAFETY: this is the exact successful mapping extent, even for a
            // null-address result; null cannot enter our private owner.
            unsafe { super::sys::munmap(pointer, mapped_bytes) };
            return Err(EntryStackError::Extent);
        };
        let owner = Self {
            base,
            mapped_bytes,
            usable_bytes,
            identity,
            next_invocation: 1,
        };
        owner.extent()?;
        Ok(owner)
    }

    /// Actual immutable allocation metadata, without a callable/storage capability.
    pub fn allocation(&self) -> EntryStackAllocation {
        EntryStackAllocation {
            identity: self.identity,
            usable_bytes: self.usable_bytes,
            mapped_bytes: self.mapped_bytes,
            protection_source: PageProtectionWitnessSource::RecordedOnly,
        }
    }

    pub(super) fn check_readonly_eight(
        &self,
        row: &super::readonly_data::ReadonlyEightBorrow<'_>,
    ) -> Result<(), EntryStackError> {
        let (base, _, end) = self.extent()?;
        let row_extent = row
            .extent()
            .map_err(|error| EntryStackError::Source(error.to_string()))?;
        super::readonly_data::check_disjoint(row_extent, (base, end))
            .map_err(|error| EntryStackError::Source(error.to_string()))
    }

    fn extent(&self) -> Result<(usize, usize, usize), EntryStackError> {
        let base = self.base.as_ptr() as usize;
        let end = base
            .checked_add(self.mapped_bytes)
            .ok_or(EntryStackError::Extent)?;
        let sp = base
            .checked_add(self.usable_bytes)
            .ok_or(EntryStackError::Extent)?;
        if !base.is_multiple_of(ALIGNMENT)
            || sp % ALIGNMENT != 0
            || self.usable_bytes > MAX_STACK_BYTES
            || sp
                .checked_add(HEADER_BYTES)
                .is_none_or(|header| header > end)
            || self.identity == 0
        {
            return Err(EntryStackError::Extent);
        }
        Ok((base, sp, end))
    }

    pub(crate) fn borrow_invocation<'a>(
        &'a mut self,
        requirement: &'a SourceEntryStackRequirement,
    ) -> Result<EntryStackInvocation<'a>, EntryStackError> {
        let (base, sp, _) = self.extent()?;
        requirement.check()?;
        if requirement.private_bytes > self.usable_bytes {
            return Err(EntryStackError::Insufficient {
                required: requirement.private_bytes,
                available: self.usable_bytes,
            });
        }
        if sp
            .checked_sub(requirement.private_bytes)
            .is_none_or(|low| low < base)
        {
            return Err(EntryStackError::Extent);
        }
        let nonce = self.next_invocation;
        self.next_invocation = nonce
            .checked_add(1)
            .ok_or(EntryStackError::IdentityExhausted)?;
        Ok(EntryStackInvocation {
            allocation: self.identity,
            nonce,
            sp,
            thread: std::thread::current().id(),
            checked_image: None,
            stack: self,
            requirement,
            not_send: PhantomData,
        })
    }
}

impl Drop for OwnedEntryStack {
    fn drop(&mut self) {
        // SAFETY: this exact mapping was allocated by this non-Clone owner.
        // Exclusive invocation borrows prevent it from being dropped in-flight.
        unsafe { super::sys::munmap(self.base.as_ptr(), self.mapped_bytes) };
    }
}

/// Private requirement paired only by the consuming source/byte owner. These
/// are conditional ABI requirements, never a storage allocation or proof grade.
pub(crate) struct SourceEntryStackRequirement {
    private_bytes: usize,
    pub(crate) module_digest: trust_ir::proof::ProofDigest,
    pub(crate) code_digest: trust_ir::proof::ProofDigest,
    pub(crate) function: u32,
    image_digest: Option<trust_ir::proof::ProofDigest>,
    image_len: usize,
    entry_offset: usize,
    pub(crate) argument_count: usize,
}

impl SourceEntryStackRequirement {
    pub(crate) fn private_bytes(&self) -> usize {
        self.private_bytes
    }

    pub(crate) fn from_checked_affine_entry(
        bytes: &trust_cg_verify::aarch64_affine_lowering::CheckedAarch64TrustIrAffineBytes<'_>,
        module_digest: trust_ir::proof::ProofDigest,
        code_digest: trust_ir::proof::ProofDigest,
    ) -> Result<Self, EntryStackError> {
        if bytes.statistics().parameter_count != 0 {
            return Err(EntryStackError::Source(
                "entry adapter requires no source arguments".into(),
            ));
        }
        let source = bytes.source();
        let signature = bytes
            .module()
            .func_type(source.ty)
            .ok_or_else(|| EntryStackError::Source("entry function signature is missing".into()))?;
        if !signature.params.is_empty()
            || !matches!(
                signature.returns.as_slice(),
                [trust_ir::Ty::I64 | trust_ir::Ty::U64]
            )
        {
            return Err(EntryStackError::Source(
                "entry adapter requires an exact 64-bit scalar return".into(),
            ));
        }
        let value = Self {
            private_bytes: bytes.statistics().private_stack_bytes,
            module_digest,
            code_digest,
            function: source.id.index(),
            image_digest: None,
            image_len: 0,
            entry_offset: 0,
            argument_count: 0,
        };
        value.check()?;
        Ok(value)
    }

    #[cfg(feature = "source-defined-call")]
    pub(crate) fn from_checked_defined_call_entry(
        owner: &crate::compiler::CoreCheckedDefinedCallImage,
    ) -> Result<Self, EntryStackError> {
        let endpoints = owner
            .linked()
            .verification_endpoints()
            .map_err(EntryStackError::Source)?;
        let caller = owner
            .linked()
            .functions()
            .iter()
            .find(|f| f.function() == owner.caller())
            .ok_or_else(|| {
                EntryStackError::Source("selected aggregate entry range is missing".into())
            })?;
        let value = Self {
            private_bytes: owner.required_private_stack_bytes(),
            module_digest: endpoints.module().stable_digest(),
            code_digest: caller.linked_digest(),
            function: owner.caller().index(),
            argument_count: 0,
            image_digest: Some(owner.linked().image_digest()),
            image_len: owner.linked().image().len(),
            entry_offset: caller.range().start,
        };
        value.check()?;
        Ok(value)
    }

    pub(crate) fn requires_whole_image(&self) -> bool {
        self.image_digest.is_some()
    }

    pub(crate) fn from_conditional_peer(
        peer: &trust_cg_verify::aarch64_affine_lowering::ConditionalPeerEntryRequirement,
    ) -> Result<Self, EntryStackError> {
        let requirement = Self {
            private_bytes: peer.required_private_stack_bytes(),
            module_digest: peer.module_digest(),
            code_digest: peer.final_code_digest(),
            function: peer.function().index(),
            argument_count: peer.argument_count(),
            image_digest: None,
            image_len: 0,
            entry_offset: 0,
        };
        requirement.check()?;
        Ok(requirement)
    }

    fn check(&self) -> Result<(), EntryStackError> {
        if self.argument_count > 1
            || self.private_bytes > MAX_STACK_BYTES
            || self.module_digest.is_zero()
            || self.code_digest.is_zero()
            || match self.image_digest {
                Some(digest) => {
                    digest.is_zero()
                        || self.image_len == 0
                        || !self.image_len.is_multiple_of(4)
                        || !self.entry_offset.is_multiple_of(4)
                        || self.entry_offset >= self.image_len
                }
                None => self.image_len != 0 || self.entry_offset != 0,
            }
        {
            return Err(EntryStackError::Source(
                "missing exact source/code requirement identity".into(),
            ));
        }
        Ok(())
    }
}

pub(crate) struct EntryStackInvocation<'a> {
    stack: &'a mut OwnedEntryStack,
    requirement: &'a SourceEntryStackRequirement,
    allocation: u64,
    nonce: u64,
    sp: usize,
    thread: std::thread::ThreadId,
    checked_image: Option<(usize, usize)>,
    not_send: PhantomData<Rc<()>>,
}

#[repr(C)]
struct HostContext {
    saved_sp: usize,
}

fn disjoint_image_extent(
    image_base: usize,
    image_len: usize,
    stack_base: usize,
    stack_end: usize,
) -> Result<(usize, usize), EntryStackError> {
    let image_end = image_base
        .checked_add(image_len)
        .ok_or(EntryStackError::Extent)?;
    if image_base < stack_end && stack_base < image_end {
        return Err(EntryStackError::AliasedStorage);
    }
    Ok((image_base, image_end))
}

impl EntryStackInvocation<'_> {
    /// Bind the actual complete installed image to this invocation. The image
    /// must remain immutable/alive under the consumer's execution lease through
    /// invoke. Check the entire extent, not just whether entry lies in stack.
    pub(crate) fn bind_image(&mut self, image: &[u8]) -> Result<(), EntryStackError> {
        self.checked_image = None;
        let expected = self.requirement.image_digest.ok_or_else(|| {
            EntryStackError::Source("entry does not have an aggregate image requirement".into())
        })?;
        let base = image.as_ptr() as usize;
        let end = base
            .checked_add(image.len())
            .ok_or(EntryStackError::Extent)?;
        let (stack_base, _, stack_end) = self.stack.extent()?;
        if image.len() != self.requirement.image_len
            || base % 4 != 0
            || trust_ir::proof::ProofDigest::sha256(crate::jit_cert::sha256_digest(image))
                != expected
        {
            return Err(EntryStackError::Source(
                "installed whole image differs from checked aggregate".into(),
            ));
        }
        self.checked_image = Some(disjoint_image_extent(
            base,
            end - base,
            stack_base,
            stack_end,
        )?);
        Ok(())
    }
}

/// Borrowed actual mapping facts for one sealed peer requirement. No public
/// pointer/numeric constructor, clone or serialization can create this loan.
pub(crate) struct PeerEntryStorageBinding<'loan, 'owner> {
    invocation: &'loan EntryStackInvocation<'owner>,
}
impl PeerEntryStorageBinding<'_, '_> {
    pub(crate) fn entry_sp(&self) -> usize {
        self.invocation.sp
    }
    pub(crate) fn allocation_identity(&self) -> u64 {
        self.invocation.allocation
    }
}

impl<'owner> EntryStackInvocation<'owner> {
    pub(crate) fn bind_peer_requirement<'loan>(
        &'loan self,
        peer: &trust_cg_verify::aarch64_affine_lowering::ConditionalPeerEntryRequirement,
    ) -> Result<PeerEntryStorageBinding<'loan, 'owner>, EntryStackError> {
        if self.stack.identity != self.allocation
            || self.stack.next_invocation
                != self
                    .nonce
                    .checked_add(1)
                    .ok_or(EntryStackError::StaleInvocation)?
            || self.thread != std::thread::current().id()
            || self.stack.extent()?.1 != self.sp
            || self.requirement.module_digest != peer.module_digest()
            || self.requirement.function != peer.function().index()
            || self.requirement.code_digest != peer.final_code_digest()
            || self.requirement.private_bytes != peer.required_private_stack_bytes()
            || self.requirement.argument_count != peer.argument_count()
        {
            return Err(EntryStackError::StaleInvocation);
        }
        self.requirement.check()?;
        if self.requirement.private_bytes > self.stack.usable_bytes {
            return Err(EntryStackError::Insufficient {
                required: self.requirement.private_bytes,
                available: self.stack.usable_bytes,
            });
        }
        Ok(PeerEntryStorageBinding { invocation: self })
    }

    /// Invoked only by the exact source-bound installed-entry consumer below
    /// the existing manifest, code-readback and execution-lease gates.
    pub(crate) unsafe fn invoke0_u64(self, target: *const u8) -> Result<u64, EntryStackError> {
        // SAFETY: forwarded unchanged to the common validated invocation.
        unsafe { self.invoke_u64(target, None) }
    }

    pub(crate) unsafe fn invoke1_u64(
        self,
        target: *const u8,
        argument: u64,
    ) -> Result<u64, EntryStackError> {
        // SAFETY: the sealed one-word source owner supplies the argument ABI.
        unsafe { self.invoke_u64(target, Some(argument)) }
    }

    unsafe fn invoke_u64(
        self,
        target: *const u8,
        argument: Option<u64>,
    ) -> Result<u64, EntryStackError> {
        let actual = usize::from(argument.is_some());
        if self.requirement.argument_count != actual {
            return Err(EntryStackError::ArgumentCount {
                expected: self.requirement.argument_count,
                actual,
            });
        }
        if self.stack.identity != self.allocation
            || self.stack.next_invocation
                != self
                    .nonce
                    .checked_add(1)
                    .ok_or(EntryStackError::StaleInvocation)?
            || self.thread != std::thread::current().id()
            || self.stack.extent()?.1 != self.sp
        {
            return Err(EntryStackError::StaleInvocation);
        }
        self.requirement.check()?;
        if target.is_null() || target as usize % 4 != 0 {
            return Err(EntryStackError::Source(
                "invalid exact entry pointer".into(),
            ));
        }
        if self.requirement.requires_whole_image() {
            let (image_base, image_end) = self.checked_image.ok_or_else(|| {
                EntryStackError::Source(
                    "aggregate invocation has no checked whole-image binding".into(),
                )
            })?;
            if image_base.checked_add(self.requirement.entry_offset) != Some(target as usize)
                || target as usize >= image_end
            {
                return Err(EntryStackError::Source(
                    "aggregate invocation selects another image entry".into(),
                ));
            }
        }
        let (base, _, end) = self.stack.extent()?;
        let mut context = HostContext { saved_sp: 0 };
        let address = std::ptr::addr_of_mut!(context) as usize;
        let context_end = address
            .checked_add(std::mem::size_of::<HostContext>())
            .ok_or(EntryStackError::Extent)?;
        if address < end && base < context_end || (base..end).contains(&(target as usize)) {
            return Err(EntryStackError::AliasedStorage);
        }
        #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
        {
            match argument {
                None => adapter::check_actual_adapter()?,
                Some(_) => adapter::check_actual_adapter1()?,
            }
            // SAFETY: the sealed consumer supplies the exact published scalar->64
            // entry and its source-bound normal-return/private-footprint claim.
            // This exclusive lease owns every byte below SP required by that
            // claim and the separate 32-byte adapter header. Context is a live,
            // disjoint borrowed Rust object. The checked fixed adapter saves
            // the actual host SP, establishes this SP, preserves its header
            // across the admitted callee and restores host SP/FP/LR on return.
            // Ordinary unmasked handlers can use arbitrary bytes below SP.
            // Do not infer their footprint from source/private-frame geometry.
            // Block and read back every maskable handler while SP is elsewhere;
            // restore the caller's exact mask only after host SP is restored.
            let signals = signal_mask::BlockedSignals::enter()?;
            let value = unsafe {
                match argument {
                    None => adapter::invoke(target, &mut context, self.sp),
                    Some(value) => adapter::invoke1(target, &mut context, self.sp, value),
                }
            };
            signals.restore()?;
            if context.saved_sp == 0 || !context.saved_sp.is_multiple_of(ALIGNMENT) {
                return Err(EntryStackError::Adapter);
            }
            Ok(value)
        }
        #[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
        Err(EntryStackError::UnsupportedHost)
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[path = "entry_stack/signal_mask.rs"]
mod signal_mask;

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod adapter {
    use super::{EntryStackError, HostContext};

    // Runtime ABI adapter only; it is not an alternative code generator. Each
    // word is independently checked below before the routine can be called.
    std::arch::global_asm!(
        ".text",
        ".p2align 2",
        ".globl _trust_cg_owned_stack_entry0_u64",
        ".private_extern _trust_cg_owned_stack_entry0_u64",
        "_trust_cg_owned_stack_entry0_u64:",
        "mov x9, sp",
        "str x9, [x1]",
        "mov x16, x0",
        "mov sp, x2",
        "stp x29, x30, [sp]",
        "str x1, [sp, #16]",
        "mov x29, sp",
        "blr x16",
        "ldr x9, [sp, #16]",
        "ldr x10, [x9]",
        "ldp x29, x30, [sp]",
        "mov sp, x10",
        "ret",
        ".globl _trust_cg_owned_stack_entry0_u64_end",
        ".private_extern _trust_cg_owned_stack_entry0_u64_end",
        "_trust_cg_owned_stack_entry0_u64_end:",
    );

    std::arch::global_asm!(
        ".text",
        ".p2align 2",
        ".globl _trust_cg_owned_stack_entry1_u64",
        ".private_extern _trust_cg_owned_stack_entry1_u64",
        "_trust_cg_owned_stack_entry1_u64:",
        "mov x9, sp",
        "str x9, [x1]",
        "mov x16, x0",
        "mov sp, x2",
        "stp x29, x30, [sp]",
        "str x1, [sp, #16]",
        "mov x29, sp",
        "mov x0, x3",
        "blr x16",
        "ldr x9, [sp, #16]",
        "ldr x10, [x9]",
        "ldp x29, x30, [sp]",
        "mov sp, x10",
        "ret",
        ".globl _trust_cg_owned_stack_entry1_u64_end",
        ".private_extern _trust_cg_owned_stack_entry1_u64_end",
        "_trust_cg_owned_stack_entry1_u64_end:",
    );

    unsafe extern "C" {
        fn trust_cg_owned_stack_entry0_u64(
            target: *const u8,
            context: *mut HostContext,
            sp: usize,
        ) -> u64;
        fn trust_cg_owned_stack_entry0_u64_end();
        fn trust_cg_owned_stack_entry1_u64(
            target: *const u8,
            context: *mut HostContext,
            sp: usize,
            argument: u64,
        ) -> u64;
        fn trust_cg_owned_stack_entry1_u64_end();
    }

    pub(super) fn check_actual_adapter() -> Result<(), EntryStackError> {
        let start = trust_cg_owned_stack_entry0_u64 as *const () as usize;
        let end = trust_cg_owned_stack_entry0_u64_end as *const () as usize;
        let size = end.checked_sub(start).ok_or(EntryStackError::Adapter)?;
        if size != 13 * 4 || start % 4 != 0 {
            return Err(EntryStackError::Adapter);
        }
        // SAFETY: the two private symbols delimit this immutable 52-byte
        // assembly routine in the running image; the checked exact extent
        // excludes a reversed/truncated/cross-function read.
        let code = unsafe { std::slice::from_raw_parts(start as *const u8, size) };
        check_words(code)
    }

    pub(super) fn check_words(code: &[u8]) -> Result<(), EntryStackError> {
        // Arm A64 encodings, decoded independently from the assembler text:
        // ADD X9,SP,#0; STR X9,[X1]; ORR X16,XZR,X0; ADD SP,X2,#0;
        // STP X29,X30,[SP]; STR X1,[SP,#16]; ADD X29,SP,#0; BLR X16;
        // LDR X9,[SP,#16]; LDR X10,[X9]; LDP X29,X30,[SP]; ADD SP,X10,#0;
        // RET X30. No literal, relocation, branch alternative or extra word.
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
        if code.len() != words.len() * 4
            || code
                .as_chunks::<4>()
                .0
                .iter()
                .zip(words)
                .any(|(actual, expected)| *actual != expected.to_le_bytes())
        {
            return Err(EntryStackError::Adapter);
        }
        Ok(())
    }

    pub(super) fn check_actual_adapter1() -> Result<(), EntryStackError> {
        let start = trust_cg_owned_stack_entry1_u64 as *const () as usize;
        let end = trust_cg_owned_stack_entry1_u64_end as *const () as usize;
        let size = end.checked_sub(start).ok_or(EntryStackError::Adapter)?;
        if size != 14 * 4 || start % 4 != 0 {
            return Err(EntryStackError::Adapter);
        }
        // SAFETY: these private symbols bound this immutable 56-byte adapter.
        let code = unsafe { std::slice::from_raw_parts(start as *const u8, size) };
        check_words1(code)
    }

    pub(super) fn check_words1(code: &[u8]) -> Result<(), EntryStackError> {
        // Same checked stack/context preservation as entry0, with one ORR
        // copying the genuine fourth native argument X3 into source ABI X0.
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
        if code.len() != words.len() * 4
            || code
                .as_chunks::<4>()
                .0
                .iter()
                .zip(words)
                .any(|(actual, expected)| *actual != expected.to_le_bytes())
        {
            return Err(EntryStackError::Adapter);
        }
        Ok(())
    }

    pub(super) unsafe fn invoke1(
        target: *const u8,
        context: &mut HostContext,
        sp: usize,
        argument: u64,
    ) -> u64 {
        // SAFETY: forwarded from the same source/manifest/lease owner; the
        // additional scalar argument is copied by the checked adapter words.
        unsafe { trust_cg_owned_stack_entry1_u64(target, context, sp, argument) }
    }

    pub(super) unsafe fn invoke(target: *const u8, context: &mut HostContext, sp: usize) -> u64 {
        // SAFETY: forwarded from the invocation owner; all three pointer/SP
        // premises and the exact checked adapter bytes were established there.
        unsafe { trust_cg_owned_stack_entry0_u64(target, context, sp) }
    }
}

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
mod tests;
