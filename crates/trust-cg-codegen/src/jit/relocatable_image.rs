//! Relocatable JIT images: the raw AArch64 link split in two.
//!
//! [`super::JitCompiler::compile_raw`] encodes every function, resolves and
//! patches every image-relative fixup (internal `BL`, local `ADRP`/`ADD`),
//! appends one veneer per external callee and only THEN writes the
//! process-local absolute addresses (the veneer literals) into a heap copy
//! that it maps, replays and seals. Everything before that last step is a pure
//! function of the compile inputs; only the literal values belong to a
//! process.
//!
//! [`RelocatableImage`] is that pre-literal image plus the exact relocation
//! inventory the linker used:
//!
//! * the veneer literal slots, each named by its external symbol;
//! * the local `ADRP`/`ADD` rows (pre-patch word, site, target), so the
//!   independent decoder in `local_address_replay` can re-check them at the
//!   NEW mapped base;
//! * the function ranges and canonical symbols;
//! * the digest of the external-symbol NAME set the compile resolved against
//!   (whether a named call is internal or external depends on that set), and
//!   the resolution policy;
//! * the SHA-256 of the image bytes.
//!
//! [`RelocatableImage::relink`] re-runs the same literal patch, the same
//! replay check and the same RW-to-RX bytes-hash seal, and yields an
//! [`ExecutableBuffer`] whose published bytes equal a cold compile's in the
//! same process byte for byte (the tests pin that).
//!
//! # What is refused, by name
//!
//! Only images whose ONLY process-local content is a veneer literal are
//! relocatable. [`RelocatableImageRefusal`] names each exclusion: profile
//! counters and timing cells (raw heap pointers), unwind tables (registered
//! with this process's unwinder), data images and GOT slots (not yet carried),
//! verified compiles (their certificates are not persisted) and named calls
//! that resolved internally only through the `_name` alias fallback (a
//! resolution that depends on the process symbol table).
//!
//! # Trust
//!
//! A relocatable image read back from storage is attacker-controllable bytes
//! that are about to become executable. [`RelocatableImage::from_bytes`]
//! checks structure and integrity (every invariant the linker established that
//! can be re-checked from the bytes), but integrity is not provenance:
//! [`RelocatableImage::relink`] is `unsafe`, and its caller must authenticate
//! the bytes (the `TCJ2` envelope in `trust-cg-jit-matrix` does so with a
//! keyed seal) before calling it.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use sha2::{Digest, Sha256};
use thiserror::Error;

use super::local_address_replay::{ExportedAddressRow, LocalAddressReplay};
use super::{
    ExecutableBuffer, ExecutionGate, JitError, JitExternalSymbolResolutionPolicy,
    JitPublicationContract, MappedRegion, TargetFeatureSet, WindowsJitUnwindRegistration,
    corrupt_published_byte_if_requested, executable_buffer_allocation_cookie,
    resolve_external_symbol, sys, write_u64_literal_in_image,
};

/// Leading magic of a serialized [`RelocatableImage`].
pub const RELOCATABLE_IMAGE_MAGIC: &[u8; 8] = b"TCGRIM01";

/// Serialized layout version of a [`RelocatableImage`]. Bump on any change.
pub const RELOCATABLE_IMAGE_FORMAT_VERSION: u32 = 1;

/// Bytes of one AArch64 veneer stub: `LDR X16, [PC, #8]`, `BR X16`, `.quad`.
const AARCH64_VENEER_LEN: usize = 16;
/// The two instruction words of an AArch64 veneer stub, literal zeroed.
const AARCH64_VENEER_WORDS: [u32; 2] = [0x5800_0050, 0xD61F_0200];
/// Offset of the absolute-address literal inside an AArch64 veneer stub.
const AARCH64_VENEER_LITERAL_OFFSET: usize = 8;

/// Why a compile produced no [`RelocatableImage`]. Each is a property of the
/// artifact, not a failure: the executable buffer is still returned.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RelocatableImageRefusal {
    /// The host is not AArch64: the raw lane and its veneer encoding are
    /// AArch64-only.
    UnsupportedTarget,
    /// Profile counters or timing cells: their raw heap pointers are baked
    /// into trampolines.
    ProfileHooks,
    /// In-memory unwind tables are registered with this process's unwinder.
    UnwindTables,
    /// A module data image: its bases are not carried by this format.
    DataImage,
    /// GOT slots: not carried by this format.
    GotSlots,
    /// A verifying compile attached certificates that are not persisted.
    Verified,
    /// The caller required relocation replay evidence for a proof request.
    RelocationReplayRequired,
    /// A named call resolved to a local function only through the `_name`
    /// alias fallback, after the process symbol table had no such symbol.
    /// Another process could resolve it differently.
    AliasResolvedInternalTarget,
    /// A function states target features beyond the JIT profile (L03-P9).
    /// The image format does not record them, so a relinking process could
    /// not check that its CPU implements them.
    FunctionTargetFeatures,
}

impl RelocatableImageRefusal {
    /// Stable name for counters and diagnostics.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UnsupportedTarget => "unsupported_target",
            Self::ProfileHooks => "profile_hooks",
            Self::UnwindTables => "unwind_tables",
            Self::DataImage => "data_image",
            Self::GotSlots => "got_slots",
            Self::Verified => "verified",
            Self::RelocationReplayRequired => "relocation_replay_required",
            Self::AliasResolvedInternalTarget => "alias_resolved_internal_target",
            Self::FunctionTargetFeatures => "function_target_features",
        }
    }
}

impl std::fmt::Display for RelocatableImageRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Failure to decode or relink a [`RelocatableImage`]. A caller treats every
/// one as a cache miss.
#[derive(Debug, Error)]
pub enum RelinkError {
    /// The image, or the relink request, failed a structural or identity
    /// check before any memory was mapped.
    #[error("relocatable image rejected: {0}")]
    Rejected(String),
    /// The shared link/publication machinery refused (unresolved symbol,
    /// replay mismatch, mapping or seal failure).
    #[error(transparent)]
    Jit(#[from] JitError),
}

fn rejected(detail: impl Into<String>) -> RelinkError {
    RelinkError::Rejected(detail.into())
}

/// One veneer literal slot: the external callee and its veneer's offset.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ExternLiteral {
    symbol: String,
    veneer_offset: u64,
}

/// The pre-literal image of one raw AArch64 JIT link plus the relocation
/// inventory needed to publish it in another process. See the module docs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelocatableImage {
    code: Vec<u8>,
    function_image_len: usize,
    extern_literals: Vec<ExternLiteral>,
    local_rows: Vec<ExportedAddressRow>,
    function_ranges: Vec<(String, Range<u64>)>,
    canonical_symbols: Vec<String>,
    policy: JitExternalSymbolResolutionPolicy,
    extern_name_set_sha256: [u8; 32],
    image_sha256: [u8; 32],
}

/// Digest of the external-symbol NAME set a raw link resolves against, with
/// the resolution policy. Addresses are deliberately absent (they are what
/// differs between processes); null entries are distinct from absent ones,
/// because a null explicit binding blocks the process-symbol fallback.
pub fn extern_name_set_sha256(
    extern_symbols: &HashMap<String, *const u8>,
    policy: JitExternalSymbolResolutionPolicy,
) -> [u8; 32] {
    let mut names: Vec<(&str, bool)> = extern_symbols
        .iter()
        .map(|(name, pointer)| (name.as_str(), pointer.is_null()))
        .collect();
    names.sort_unstable();
    let mut hasher = Sha256::new();
    hasher.update(b"trust-cg.relocatable-image.extern-name-set.v1\0");
    hasher.update(policy.canonical_name().as_bytes());
    hasher.update([0]);
    hasher.update((names.len() as u64).to_le_bytes());
    for (name, null) in names {
        hasher.update((name.len() as u64).to_le_bytes());
        hasher.update(name.as_bytes());
        hasher.update([u8::from(null)]);
    }
    hasher.finalize().into()
}

/// Inputs of [`RelocatableImage::capture`], taken from `compile_raw_inner`
/// after every image-relative patch and before any process-local write.
pub(super) struct CaptureInputs<'a> {
    pub(super) code: &'a [u8],
    pub(super) function_image_len: usize,
    pub(super) veneers: &'a HashMap<String, u64>,
    pub(super) local_address_replay: Option<&'a LocalAddressReplay>,
    pub(super) function_ranges: &'a [(String, Range<u64>)],
    pub(super) canonical_symbols: &'a [String],
    pub(super) extern_symbols: &'a HashMap<String, *const u8>,
    pub(super) policy: JitExternalSymbolResolutionPolicy,
}

impl RelocatableImage {
    pub(super) fn capture(inputs: CaptureInputs<'_>) -> Self {
        let mut extern_literals: Vec<ExternLiteral> = inputs
            .veneers
            .iter()
            .map(|(symbol, &veneer_offset)| ExternLiteral {
                symbol: symbol.clone(),
                veneer_offset,
            })
            .collect();
        extern_literals.sort_by_key(|literal| literal.veneer_offset);
        let local_rows = inputs
            .local_address_replay
            .map(LocalAddressReplay::export_rows)
            .unwrap_or_default();
        debug_assert!(
            inputs
                .local_address_replay
                .is_none_or(|replay| replay.function_image_len() == inputs.function_image_len)
        );
        Self {
            code: inputs.code.to_vec(),
            function_image_len: inputs.function_image_len,
            extern_literals,
            local_rows,
            function_ranges: inputs.function_ranges.to_vec(),
            canonical_symbols: inputs.canonical_symbols.to_vec(),
            policy: inputs.policy,
            extern_name_set_sha256: extern_name_set_sha256(inputs.extern_symbols, inputs.policy),
            image_sha256: Sha256::digest(inputs.code).into(),
        }
    }

    /// SHA-256 of the pre-literal image bytes.
    pub fn image_sha256(&self) -> [u8; 32] {
        self.image_sha256
    }

    /// Length of the image (functions plus veneers).
    pub fn code_len(&self) -> usize {
        self.code.len()
    }

    /// Length of the function part of the image (before the veneers).
    pub fn function_image_len(&self) -> usize {
        self.function_image_len
    }

    /// The external callees, in veneer order.
    pub fn extern_symbol_names(&self) -> impl Iterator<Item = &str> {
        self.extern_literals
            .iter()
            .map(|literal| literal.symbol.as_str())
    }

    /// Canonical function symbols, in image order.
    pub fn canonical_symbols(&self) -> &[String] {
        &self.canonical_symbols
    }

    /// Function byte ranges, in image order.
    pub fn function_ranges(&self) -> &[(String, Range<u64>)] {
        &self.function_ranges
    }

    /// Number of local `ADRP`/`ADD` relocation rows carried.
    pub fn local_address_row_count(&self) -> usize {
        self.local_rows.len()
    }

    /// External-symbol resolution policy the compile used.
    pub fn external_symbol_resolution(&self) -> JitExternalSymbolResolutionPolicy {
        self.policy
    }

    /// Digest of the external-symbol name set the compile resolved against
    /// (see [`extern_name_set_sha256`]).
    pub fn extern_name_set_digest(&self) -> [u8; 32] {
        self.extern_name_set_sha256
    }

    /// Serialize deterministically, with a trailing SHA-256 over every
    /// preceding byte. All integers are little-endian.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.code.len() + 256);
        out.extend_from_slice(RELOCATABLE_IMAGE_MAGIC);
        put_u32(&mut out, RELOCATABLE_IMAGE_FORMAT_VERSION);
        out.push(policy_byte(self.policy));
        put_u64(&mut out, self.function_image_len as u64);
        put_u64(&mut out, self.code.len() as u64);
        out.extend_from_slice(&self.code);
        put_u64(&mut out, self.extern_literals.len() as u64);
        for literal in &self.extern_literals {
            put_str(&mut out, &literal.symbol);
            put_u64(&mut out, literal.veneer_offset);
        }
        put_u64(&mut out, self.local_rows.len() as u64);
        for row in &self.local_rows {
            put_u32(&mut out, row.offset);
            put_u32(&mut out, row.original_word);
            put_u64(&mut out, row.target);
            out.push(u8::from(row.page));
        }
        put_u64(&mut out, self.function_ranges.len() as u64);
        for (name, range) in &self.function_ranges {
            put_str(&mut out, name);
            put_u64(&mut out, range.start);
            put_u64(&mut out, range.end);
        }
        put_u64(&mut out, self.canonical_symbols.len() as u64);
        for name in &self.canonical_symbols {
            put_str(&mut out, name);
        }
        out.extend_from_slice(&self.extern_name_set_sha256);
        out.extend_from_slice(&self.image_sha256);
        let trailer: [u8; 32] = Sha256::digest(&out).into();
        out.extend_from_slice(&trailer);
        out
    }

    /// Decode and structurally validate a serialized image. Integrity only:
    /// see the module docs on provenance.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, RelinkError> {
        if bytes.len() < RELOCATABLE_IMAGE_MAGIC.len() + 4 + 32 {
            return Err(rejected("serialized image is too short"));
        }
        let (body, trailer) = bytes.split_at(bytes.len() - 32);
        let digest: [u8; 32] = Sha256::digest(body).into();
        if digest.as_slice() != trailer {
            return Err(rejected("serialized image trailer SHA-256 mismatch"));
        }
        let mut cur = Cursor { rest: body };
        if cur.take(RELOCATABLE_IMAGE_MAGIC.len())? != RELOCATABLE_IMAGE_MAGIC {
            return Err(rejected("bad relocatable image magic"));
        }
        let version = cur.u32()?;
        if version != RELOCATABLE_IMAGE_FORMAT_VERSION {
            return Err(rejected(format!(
                "unsupported relocatable image version {version}"
            )));
        }
        let policy = policy_from_byte(cur.u8()?)?;
        let function_image_len = cur.usize()?;
        let code_len = cur.usize()?;
        let code = cur.take(code_len)?.to_vec();
        let literal_count = cur.count(8 + 8)?;
        let mut extern_literals = Vec::with_capacity(literal_count);
        for _ in 0..literal_count {
            let symbol = cur.string()?;
            let veneer_offset = cur.u64()?;
            extern_literals.push(ExternLiteral {
                symbol,
                veneer_offset,
            });
        }
        let row_count = cur.count(4 + 4 + 8 + 1)?;
        let mut local_rows = Vec::with_capacity(row_count);
        for _ in 0..row_count {
            let offset = cur.u32()?;
            let original_word = cur.u32()?;
            let target = cur.u64()?;
            let page = match cur.u8()? {
                0 => false,
                1 => true,
                other => return Err(rejected(format!("bad relocation row part byte {other}"))),
            };
            local_rows.push(ExportedAddressRow {
                offset,
                original_word,
                target,
                page,
            });
        }
        let range_count = cur.count(8 + 8 + 8)?;
        let mut function_ranges = Vec::with_capacity(range_count);
        for _ in 0..range_count {
            let name = cur.string()?;
            let start = cur.u64()?;
            let end = cur.u64()?;
            function_ranges.push((name, start..end));
        }
        let canonical_count = cur.count(8)?;
        let mut canonical_symbols = Vec::with_capacity(canonical_count);
        for _ in 0..canonical_count {
            canonical_symbols.push(cur.string()?);
        }
        let extern_name_set_sha256 = cur.array32()?;
        let image_sha256 = cur.array32()?;
        if !cur.rest.is_empty() {
            return Err(rejected("trailing bytes after the relocatable image"));
        }
        let image = Self {
            code,
            function_image_len,
            extern_literals,
            local_rows,
            function_ranges,
            canonical_symbols,
            policy,
            extern_name_set_sha256,
            image_sha256,
        };
        image.validate_structure()?;
        Ok(image)
    }

    /// Re-check every invariant the linker established that the bytes alone
    /// can witness, and rebuild the local-address replay inventory. Returns
    /// the alias-aware symbol table the published buffer carries.
    fn validate_structure(
        &self,
    ) -> Result<(Option<LocalAddressReplay>, HashMap<String, u64>), RelinkError> {
        let digest: [u8; 32] = Sha256::digest(&self.code).into();
        if digest != self.image_sha256 {
            return Err(rejected(
                "image bytes do not match the recorded image SHA-256",
            ));
        }
        if self.code.is_empty() || self.function_ranges.is_empty() {
            return Err(rejected("an empty image is not an executable artifact"));
        }
        if self.function_image_len > self.code.len() {
            return Err(rejected("function image is longer than the image"));
        }
        // Function ranges: contiguous from 0, exactly covering the function
        // image, one per canonical symbol in the same order, and the
        // alias-aware table compile_raw builds (name and `_name`) with no
        // collision.
        if self.canonical_symbols.len() != self.function_ranges.len() {
            return Err(rejected(
                "canonical symbols do not pair with function ranges",
            ));
        }
        let mut previous_end = 0u64;
        let mut symbol_offsets = HashMap::with_capacity(self.function_ranges.len() * 2);
        let mut entries = HashSet::with_capacity(self.function_ranges.len());
        for ((name, range), canonical) in self.function_ranges.iter().zip(&self.canonical_symbols) {
            if name != canonical {
                return Err(rejected(format!(
                    "function range `{name}` does not match canonical symbol `{canonical}`"
                )));
            }
            if range.start != previous_end || range.end < range.start {
                return Err(rejected(format!(
                    "function range `{name}` is not contiguous with its predecessor"
                )));
            }
            previous_end = range.end;
            entries.insert(range.start);
            if symbol_offsets.insert(name.clone(), range.start).is_some()
                || symbol_offsets
                    .insert(format!("_{name}"), range.start)
                    .is_some()
            {
                return Err(rejected(format!("duplicate symbol `{name}`")));
            }
        }
        if previous_end != self.function_image_len as u64 {
            return Err(rejected("function ranges do not cover the function image"));
        }
        // Appended region: exactly one canonical veneer stub per external
        // callee, contiguous, in offset order, literal zeroed, names unique.
        let appended = self.code.len() - self.function_image_len;
        if appended != self.extern_literals.len() * AARCH64_VENEER_LEN {
            return Err(rejected(
                "the appended region is not exactly one veneer per external callee",
            ));
        }
        let mut names = HashSet::with_capacity(self.extern_literals.len());
        for (index, literal) in self.extern_literals.iter().enumerate() {
            let expected = (self.function_image_len + index * AARCH64_VENEER_LEN) as u64;
            if literal.veneer_offset != expected {
                return Err(rejected(format!(
                    "veneer for `{}` is not at its slot",
                    literal.symbol
                )));
            }
            if !names.insert(literal.symbol.as_str()) {
                return Err(rejected(format!(
                    "duplicate veneer for `{}`",
                    literal.symbol
                )));
            }
            let start = expected as usize;
            let stub = &self.code[start..start + AARCH64_VENEER_LEN];
            let words_ok = AARCH64_VENEER_WORDS
                .iter()
                .enumerate()
                .all(|(word, value)| stub[word * 4..word * 4 + 4] == value.to_le_bytes());
            if !words_ok || stub[AARCH64_VENEER_LITERAL_OFFSET..] != [0u8; 8] {
                return Err(rejected(format!(
                    "veneer for `{}` is not a canonical unpatched stub",
                    literal.symbol
                )));
            }
        }
        // Local address rows: re-validated, and every target an exact entry.
        let replay = if self.local_rows.is_empty() {
            None
        } else {
            for row in &self.local_rows {
                if !entries.contains(&row.target) {
                    return Err(rejected(format!(
                        "local address row at {:#x} does not target a function entry",
                        row.offset
                    )));
                }
            }
            Some(LocalAddressReplay::from_exported_rows(
                self.function_image_len,
                &self.local_rows,
            )?)
        };
        Ok((replay, symbol_offsets))
    }

    /// Publish this image in the current process: resolve every veneer
    /// literal by name against `extern_symbols` (with the recorded policy),
    /// re-run the local-address replay at the actual mapped base, and seal the
    /// mapping RW-to-RX under the same bytes-hash check a cold compile uses.
    ///
    /// Refused before anything is mapped when the external-symbol name set
    /// differs from the compile's (a name that was internal could now resolve
    /// externally, or the reverse), or when any structural check fails.
    ///
    /// # Safety
    ///
    /// The image bytes become executable. The caller must have authenticated
    /// them as Trust Codegen output for the live compiler build, target and
    /// feature profile (for example a keyed seal over a content-addressed
    /// envelope), and every `extern_symbols` address must be a live function
    /// with the ABI the compiled call sites expect, for as long as the
    /// returned buffer can execute.
    pub unsafe fn relink(
        &self,
        extern_symbols: &HashMap<String, *const u8>,
    ) -> Result<ExecutableBuffer, RelinkError> {
        if !cfg!(target_arch = "aarch64") {
            return Err(rejected("relocatable images are AArch64-only"));
        }
        if !sys::host_supported() {
            return Err(RelinkError::Jit(JitError::UnsupportedHost {
                arch: std::env::consts::ARCH,
                os: std::env::consts::OS,
            }));
        }
        let (replay, symbol_offsets) = self.validate_structure()?;
        if extern_name_set_sha256(extern_symbols, self.policy) != self.extern_name_set_sha256 {
            return Err(rejected(
                "the external-symbol name set differs from the one the image was linked against",
            ));
        }

        let image_len = self.code.len();
        let mut published = self.code.clone();
        for literal in &self.extern_literals {
            let address = resolve_external_symbol(&literal.symbol, extern_symbols, self.policy)
                .ok_or_else(|| JitError::UnresolvedSymbol(literal.symbol.clone()))?;
            let literal_offset = literal.veneer_offset as usize + AARCH64_VENEER_LITERAL_OFFSET;
            if let Some(replay) = &replay {
                replay.check_appended_literal(literal_offset, image_len)?;
            }
            write_u64_literal_in_image(&mut published, image_len, literal_offset, address as u64)?;
        }

        publish_image(
            published,
            self.function_ranges.clone(),
            symbol_offsets,
            self.canonical_symbols.clone(),
            HashMap::new(),
            None,
            TargetFeatureSet::EMPTY,
            Vec::new(),
            replay.as_ref(),
            None,
        )
        .map_err(RelinkError::Jit)
    }
}

// Private evidence variant constructed only from the actual checked owner.
// It authenticates whole-image/range readback without pretending that a caller
// per-function JitCertificate exists. It grants no public executable conversion.
struct AggregateImageEvidence<'a> {
    image: &'a [u8],
    ranges: Vec<(String, Range<u64>, String)>,
}
#[cfg(feature = "source-defined-call")]
impl<'a> AggregateImageEvidence<'a> {
    fn from_checked(owner: &'a crate::compiler::CoreCheckedDefinedCallImage) -> Self {
        Self {
            image: owner.linked().image(),
            ranges: owner
                .linked()
                .functions()
                .iter()
                .map(|f| {
                    (
                        f.name().to_owned(),
                        f.range().start as u64..f.range().end as u64,
                        crate::jit_cert::digest_hex(&f.linked_digest().bytes),
                    )
                })
                .collect(),
        }
    }
}

// One publication owner for the legacy authenticated relinker and the sealed
// Core continuation. It preserves the existing mapping/seal/cache-walk/readback
// mechanics; the Core entry additionally carries its existing certificates.
#[allow(clippy::too_many_arguments)]
fn publish_image(
    published: Vec<u8>,
    function_ranges: Vec<(String, Range<u64>)>,
    symbol_offsets: HashMap<String, u64>,
    canonical_symbols: Vec<String>,
    certificates: HashMap<String, crate::jit_cert::JitCertificate>,
    inventory: Option<super::installed_replay::InstalledReplayInventory>,
    function_target_features: TargetFeatureSet<crate::target::AArch64IsaFeature>,
    proof_optimization_certificates: Vec<crate::pipeline::ProofOptimizationCertificateCitation>,
    replay: Option<&LocalAddressReplay>,
    aggregate: Option<&AggregateImageEvidence<'_>>,
) -> Result<ExecutableBuffer, JitError> {
    if let Some(owner) = aggregate
        && (published != owner.image
            || function_ranges.len() != owner.ranges.len()
            || function_ranges.iter().zip(&owner.ranges).any(
                |((name, range), (expected_name, expected_range, _))| {
                    name != expected_name || range != expected_range
                },
            ))
    {
        return Err(JitError::InstalledArtifactReplayRejected {
            function: "<aggregate>".into(),
            offset: 0,
            detail: "aggregate image/ranges differ from the checked immutable owner".into(),
        });
    }
    let image_len = published.len();
    let alloc_size = sys::page_align(image_len);
    let mut region = MappedRegion::allocate_rw(alloc_size)?;
    if aggregate.is_some()
        && ((region.as_mut_ptr() as usize) % 4 != 0
            || (region.as_mut_ptr() as usize)
                .checked_add(image_len)
                .is_none())
    {
        return Err(JitError::InstalledArtifactReplayRejected {
            function: "<aggregate>".into(),
            offset: 0,
            detail: "mapped aggregate placement violates checked alignment/extent".into(),
        });
    }

    if let Some(replay) = &replay {
        replay.replay(&published, region.as_mut_ptr() as u64)?;
    }
    let expected_sha256 = crate::jit_diagnostics::sha256_hex(&published);
    let jit_write_guard = sys::JitWriteGuard::enter();
    // SAFETY: `region` owns a writable allocation of `alloc_size >=
    // image_len` bytes; `published` is heap memory distinct from it.
    unsafe {
        std::ptr::copy_nonoverlapping(published.as_ptr(), region.as_mut_ptr(), image_len);
    }
    corrupt_published_byte_if_requested(region.as_mut_ptr(), image_len);
    region.seal_rx_and_verify(image_len, &expected_sha256)?;
    drop(jit_write_guard);
    let installed_replay = if let Some(inventory) = &inventory {
        let mut digests = Vec::with_capacity(function_ranges.len());
        for (name, range) in &function_ranges {
            let digest = if let Some(owner) = aggregate {
                // This is a linked-image proof range, not a manufactured
                // per-function JitCertificate or normalized pre-link digest.
                let expected = owner
                    .ranges
                    .iter()
                    .find(|(expected, _, _)| expected == name)
                    .ok_or_else(|| JitError::InstalledArtifactReplayRejected {
                        function: name.clone(),
                        offset: range.start,
                        detail: "missing checked aggregate range".into(),
                    })?;
                expected.2.clone()
            } else {
                certificates
                    .get(name)
                    .ok_or_else(|| JitError::InstalledArtifactReplayRejected {
                        function: name.clone(),
                        offset: range.start,
                        detail: "missing Core publication certificate".into(),
                    })?
                    .normalized_machine_code_sha256()
                    .to_owned()
            };
            digests.push(digest);
        }
        let ranges: Vec<_> = function_ranges
            .iter()
            .zip(&digests)
            .map(
                |((name, range), digest)| super::installed_replay::CertifiedRange {
                    name,
                    range: range.clone(),
                    certified_sha256: digest,
                },
            )
            .collect();
        // SAFETY: this is the same sealed readable mapping owned above.
        let installed =
            unsafe { std::slice::from_raw_parts(region.as_mut_ptr().cast_const(), image_len) };
        Some(inventory.replay(&published, installed, region.as_mut_ptr() as u64, &ranges)?)
    } else {
        None
    };
    let page_witness = region.publication_page_witness();
    let allocation = region.allocation_record();
    let (memory, alloc_size) = region.into_published_parts();
    let allocation_cookie =
        executable_buffer_allocation_cookie(memory, alloc_size, image_len, image_len);
    let buffer = ExecutableBuffer {
        memory,
        data_region: None,
        len: alloc_size,
        len_shadow: alloc_size,
        allocation_cookie,
        code_len: image_len,
        published_len: image_len,
        published_image_sha256: expected_sha256,
        host_jit_selected_codegen_profile: None,
        publication: JitPublicationContract::published_rx(),
        allocation,
        page_witness,
        teardown_policy: crate::jit_contract::TeardownPolicy::RefCounted,
        execution_gate: ExecutionGate::new_shared(),
        windows_unwind: WindowsJitUnwindRegistration::default(),
        eh_frame_unwind: crate::jit_unwind::EhFrameJitUnwindRegistration::default(),
        unwind_manifest: None,
        function_ranges,
        symbol_offsets,
        data_symbols: HashMap::new(),
        data_image: None,
        canonical_symbols,
        counters: HashMap::new(),
        timing_cells: HashMap::new(),
        timing_state: None,
        certificates,
        installed_replay,
        proof_optimization_certificates,
        function_target_features,
    };
    debug_assert_eq!(buffer.allocation_len_opaque(), alloc_size);
    Ok(buffer)
}

#[cfg(feature = "verify")]
pub(crate) fn publish_core_artifact(
    input: &crate::compiler::CoreInstallationArtifact,
) -> Result<ExecutableBuffer, JitError> {
    publish_core_input(CorePublicationInput::Ordinary(input))
}

#[cfg(feature = "verify")]
pub(crate) fn publish_physically_bound_core_peer(
    input: &crate::compiler::CoreInstallationArtifact,
    storage: &std::sync::Arc<crate::compiler::core_peer_entry::CoreBoundPeerProof>,
) -> Result<ExecutableBuffer, JitError> {
    input
        .validate_physically_bound_peer(storage)
        .map_err(|detail| JitError::InstalledArtifactReplayRejected {
            function: "<physically-bound-peer>".into(),
            offset: 0,
            detail,
        })?;
    publish_core_input(CorePublicationInput::PhysicallyBound(input, storage))
}

#[cfg(feature = "verify")]
enum CorePublicationInput<'a> {
    Ordinary(&'a crate::compiler::CoreInstallationArtifact),
    PhysicallyBound(
        &'a crate::compiler::CoreInstallationArtifact,
        &'a std::sync::Arc<crate::compiler::core_peer_entry::CoreBoundPeerProof>,
    ),
}
#[cfg(feature = "verify")]
impl CorePublicationInput<'_> {
    fn artifact(&self) -> &crate::compiler::CoreInstallationArtifact {
        match self {
            Self::Ordinary(input) | Self::PhysicallyBound(input, _) => input,
        }
    }
    fn complete_peer_function(&self, name: &str, bytes: &[u8]) -> Result<bool, String> {
        match self {
            Self::Ordinary(_) => Ok(false),
            Self::PhysicallyBound(input, storage) => {
                input.physically_bound_peer_function(storage, name, bytes)
            }
        }
    }
    fn peer_branch(&self, image: &[u8]) -> Result<Option<(&str, u32, u64)>, String> {
        match self {
            Self::Ordinary(_) => Ok(None),
            Self::PhysicallyBound(_, storage) => {
                storage.check_image(image)?;
                let (name, site, target) = storage.branch();
                Ok(Some((
                    name,
                    u32::try_from(site).map_err(|_| "peer site overflow")?,
                    u64::try_from(target).map_err(|_| "peer target overflow")?,
                )))
            }
        }
    }
}
#[cfg(feature = "verify")]
fn publish_core_input(owner: CorePublicationInput<'_>) -> Result<ExecutableBuffer, JitError> {
    let input = owner.artifact();
    if !cfg!(all(target_arch = "aarch64", target_os = "macos")) || !sys::host_supported() {
        return Err(JitError::UnsupportedHost {
            arch: std::env::consts::ARCH,
            os: std::env::consts::OS,
        });
    }
    super::ensure_aarch64_function_features_supported(
        "<sealed-core-image>",
        input.publication_features(),
        crate::aarch64_dispatch::aarch64_host_features(),
    )?;
    let mut code = Vec::new();
    let mut ranges = Vec::new();
    let mut symbols = HashMap::new();
    let mut canonical = Vec::new();
    let mut certificates = HashMap::new();
    for (name, bytes, certificate, alignment) in input.publication_rows() {
        // The initial typed owner accepts ordinary alignment through one page.
        // Larger source alignment is preserved as an explicit refusal.
        if alignment > 12 || bytes.is_empty() || bytes.len() % 4 != 0 {
            return Err(JitError::InstalledArtifactReplayRejected {
                function: name.into(),
                offset: 0,
                detail: "unsupported Core text alignment/extent".into(),
            });
        }
        let checked_peer = owner
            .complete_peer_function(name, bytes)
            .map_err(|detail| JitError::InstalledArtifactReplayRejected {
                function: name.into(),
                offset: 0,
                detail,
            })?;
        if !checked_peer {
            crate::aarch64::layout_crosscheck::check_rebased_function_placement(bytes).map_err(
                |error| JitError::InstalledArtifactReplayRejected {
                    function: name.into(),
                    offset: 0,
                    detail: error.to_string(),
                },
            )?;
        }
        let align = 1usize << alignment.max(2);
        let padding = (align - code.len() % align) % align;
        code.try_reserve(padding.checked_add(bytes.len()).ok_or_else(|| {
            JitError::InstalledArtifactReplayRejected {
                function: name.into(),
                offset: 0,
                detail: "Core image extent overflow".into(),
            }
        })?)
        .map_err(|error| JitError::InstalledArtifactReplayRejected {
            function: name.into(),
            offset: 0,
            detail: error.to_string(),
        })?;
        for _ in 0..padding / 4 {
            code.extend_from_slice(&0xd503201fu32.to_le_bytes());
        }
        let start = code.len() as u64;
        let alias = format!("_{name}");
        if symbols.contains_key(name) || symbols.contains_key(&alias) {
            return Err(JitError::DuplicateSymbol(name.into()));
        }
        symbols.insert(name.into(), start);
        symbols.insert(alias, start);
        canonical.push(name.into());
        code.extend_from_slice(bytes);
        let range = start..code.len() as u64;
        ranges.push((name.into(), range.clone()));
        certificates.insert(name.into(), certificate.rebound_for_publication(range));
    }
    if canonical.is_empty() {
        return Err(JitError::InstalledArtifactReplayRejected {
            function: "<module>".into(),
            offset: 0,
            detail: "empty Core publication".into(),
        });
    }
    let mut replay = super::installed_replay::InstalledReplayInventory::default();
    if let Some((name, site, target)) =
        owner
            .peer_branch(&code)
            .map_err(|detail| JitError::InstalledArtifactReplayRejected {
                function: "<physically-bound-peer-image>".into(),
                offset: 0,
                detail,
            })?
    {
        replay.branch(
            site,
            super::installed_replay::BranchTarget::Function {
                name: name.into(),
                entry: target,
            },
        );
    }
    publish_image(
        code,
        ranges,
        symbols,
        canonical,
        certificates,
        Some(replay),
        input.publication_features(),
        input.publication_citations(),
        None,
        None,
    )
}

fn policy_byte(policy: JitExternalSymbolResolutionPolicy) -> u8 {
    match policy {
        JitExternalSymbolResolutionPolicy::ExplicitThenProcess => 1,
        JitExternalSymbolResolutionPolicy::ExplicitOnly => 2,
    }
}

fn policy_from_byte(byte: u8) -> Result<JitExternalSymbolResolutionPolicy, RelinkError> {
    match byte {
        1 => Ok(JitExternalSymbolResolutionPolicy::ExplicitThenProcess),
        2 => Ok(JitExternalSymbolResolutionPolicy::ExplicitOnly),
        other => Err(rejected(format!("bad resolution policy byte {other}"))),
    }
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_str(out: &mut Vec<u8>, value: &str) {
    put_u64(out, value.len() as u64);
    out.extend_from_slice(value.as_bytes());
}

struct Cursor<'a> {
    rest: &'a [u8],
}

impl<'a> Cursor<'a> {
    fn take(&mut self, len: usize) -> Result<&'a [u8], RelinkError> {
        if self.rest.len() < len {
            return Err(rejected("serialized image is truncated"));
        }
        let (head, tail) = self.rest.split_at(len);
        self.rest = tail;
        Ok(head)
    }

    fn u8(&mut self) -> Result<u8, RelinkError> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> Result<u32, RelinkError> {
        Ok(u32::from_le_bytes(self.array()?))
    }

    fn u64(&mut self) -> Result<u64, RelinkError> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    /// `N` bytes as an array. `take` returns exactly `N` bytes, so the
    /// conversion cannot fail; it is still an error, never a panic.
    fn array<const N: usize>(&mut self) -> Result<[u8; N], RelinkError> {
        self.take(N)?
            .try_into()
            .map_err(|_| rejected("serialized image is truncated"))
    }

    fn usize(&mut self) -> Result<usize, RelinkError> {
        usize::try_from(self.u64()?).map_err(|_| rejected("length exceeds the address space"))
    }

    /// A record count, bounded by the bytes that remain so a forged count
    /// cannot drive a huge allocation.
    fn count(&mut self, min_record_len: usize) -> Result<usize, RelinkError> {
        let count = self.usize()?;
        if count.saturating_mul(min_record_len) > self.rest.len() {
            return Err(rejected("record count exceeds the remaining bytes"));
        }
        Ok(count)
    }

    fn string(&mut self) -> Result<String, RelinkError> {
        let len = self.usize()?;
        let bytes = self.take(len)?;
        String::from_utf8(bytes.to_vec()).map_err(|_| rejected("symbol name is not UTF-8"))
    }

    fn array32(&mut self) -> Result<[u8; 32], RelinkError> {
        self.array()
    }
}

#[cfg(all(test, target_arch = "aarch64"))]
#[allow(deprecated)]
mod tests {
    use super::*;
    use crate::jit::{JitCompiler, JitConfig};
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::operand::MachOperand::Special;
    use trust_cg_ir::regs::{FP, LR, SpecialReg, X0};

    const HOST_SYMBOL: &str = "_trust_cg_relocatable_image_test_host";

    extern "C" fn host_add_ten(x: i64) -> i64 {
        x + 10
    }

    extern "C" fn host_add_twenty(x: i64) -> i64 {
        x + 20
    }

    fn push(func: &mut MachFunction, inst: MachInst) {
        let id = func.push_inst(inst);
        func.append_inst(func.entry, id);
    }

    /// `call_extern(a) = callee(a)` through a veneer.
    fn extern_caller(callee: &str) -> MachFunction {
        let mut func = MachFunction::new(
            "call_extern".into(),
            Signature::new(vec![Type::I64], vec![Type::I64]),
        );
        push(
            &mut func,
            MachInst::new(
                AArch64Opcode::StpPreIndex,
                vec![
                    MachOperand::PReg(FP),
                    MachOperand::PReg(LR),
                    Special(SpecialReg::SP),
                    MachOperand::Imm(-16),
                ],
            ),
        );
        push(
            &mut func,
            MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Symbol(callee.into())]),
        );
        push(
            &mut func,
            MachInst::new(
                AArch64Opcode::LdpPostIndex,
                vec![
                    MachOperand::PReg(FP),
                    MachOperand::PReg(LR),
                    Special(SpecialReg::SP),
                    MachOperand::Imm(16),
                ],
            ),
        );
        push(
            &mut func,
            MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]),
        );
        func
    }

    /// `address() = &target` through a local ADRP/ADD pair.
    fn local_address(target: &str) -> MachFunction {
        let mut func = MachFunction::new("address".into(), Signature::new(vec![], vec![Type::I64]));
        push(
            &mut func,
            MachInst::new(
                AArch64Opcode::Adrp,
                vec![MachOperand::PReg(X0), MachOperand::Symbol(target.into())],
            ),
        );
        push(
            &mut func,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X0),
                    MachOperand::Symbol(target.into()),
                ],
            ),
        );
        push(
            &mut func,
            MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]),
        );
        func
    }

    fn return_const(name: &str, value: i64) -> MachFunction {
        let mut func = MachFunction::new(name.into(), Signature::new(vec![], vec![Type::I64]));
        push(
            &mut func,
            MachInst::new(
                AArch64Opcode::Movz,
                vec![MachOperand::PReg(X0), MachOperand::Imm(value)],
            ),
        );
        push(
            &mut func,
            MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]),
        );
        func
    }

    fn functions() -> Vec<MachFunction> {
        vec![
            extern_caller(HOST_SYMBOL),
            local_address("target"),
            return_const("target", 42),
        ]
    }

    fn externs(host: extern "C" fn(i64) -> i64) -> HashMap<String, *const u8> {
        HashMap::from([(HOST_SYMBOL.to_string(), host as *const u8)])
    }

    fn compile(
        ext: &HashMap<String, *const u8>,
    ) -> (
        ExecutableBuffer,
        Result<RelocatableImage, RelocatableImageRefusal>,
    ) {
        JitCompiler::new(JitConfig::default())
            .compile_raw_relocatable(&functions(), ext)
            .expect("raw link")
    }

    fn call(buffer: &ExecutableBuffer, x: i64) -> i64 {
        let f: extern "C" fn(i64) -> i64 = unsafe { buffer.get_fn("call_extern").unwrap() };
        f(x)
    }

    fn address(buffer: &ExecutableBuffer) -> u64 {
        let f: extern "C" fn() -> u64 = unsafe { buffer.get_fn("address").unwrap() };
        f()
    }

    /// Re-seal a serialized image after an edit: recompute the image SHA-256
    /// when `code` changed, then the trailer. What a forger without any key
    /// can do; `from_bytes` must still refuse every structural lie.
    fn reseal(bytes: &mut Vec<u8>) {
        bytes.truncate(bytes.len() - 32);
        let trailer: [u8; 32] = Sha256::digest(&bytes).into();
        bytes.extend_from_slice(&trailer);
    }

    #[test]
    fn capture_changes_nothing_the_linker_publishes() {
        let ext = externs(host_add_ten);
        let plain = JitCompiler::new(JitConfig::default())
            .compile_raw(&functions(), &ext)
            .unwrap();
        let (buffer, image) = compile(&ext);
        let image = image.expect("veneer-only image is relocatable");
        assert_eq!(plain.code_slice(), buffer.code_slice());
        assert_eq!(plain.symbol_offsets(), buffer.symbol_offsets());
        assert_eq!(plain.function_ranges(), buffer.function_ranges());
        assert_eq!(
            image.extern_symbol_names().collect::<Vec<_>>(),
            [HOST_SYMBOL]
        );
        assert_eq!(image.local_address_row_count(), 2);
        assert_eq!(
            image.code_len(),
            image.function_image_len() + AARCH64_VENEER_LEN
        );
    }

    #[test]
    fn relink_in_the_same_process_publishes_the_cold_bytes_exactly() {
        let ext = externs(host_add_ten);
        let (cold, image) = compile(&ext);
        let image = image.unwrap();
        let warm = unsafe { image.relink(&ext) }.expect("relink");
        assert_eq!(cold.code_slice(), warm.code_slice());
        assert_eq!(cold.published_image_sha256(), warm.published_image_sha256());
        assert_eq!(cold.symbol_offsets(), warm.symbol_offsets());
        assert_eq!(cold.canonical_symbols(), warm.canonical_symbols());
        assert_eq!(cold.function_ranges(), warm.function_ranges());
        warm.verify_published_code_integrity().unwrap();
        assert_eq!(call(&warm, 32), 42);
        // The local ADRP/ADD pair resolves in the NEW mapping.
        assert_eq!(address(&warm), warm.get_fn_ptr("target").unwrap() as u64);
        assert_ne!(address(&warm), address(&cold));
        let target: extern "C" fn() -> i64 = unsafe { warm.get_fn("target").unwrap() };
        assert_eq!(target(), 42);
    }

    #[test]
    fn relink_rebinds_every_external_literal_by_name() {
        let (cold, image) = compile(&externs(host_add_ten));
        let image = image.unwrap();
        // Same NAME set, another address: exactly what another process sees.
        let warm = unsafe { image.relink(&externs(host_add_twenty)) }.unwrap();
        assert_eq!(call(&cold, 1), 11);
        assert_eq!(call(&warm, 1), 21, "the veneer literal was re-resolved");
        let differing: Vec<usize> = cold
            .code_slice()
            .iter()
            .zip(warm.code_slice())
            .enumerate()
            .filter(|(_, (a, b))| a != b)
            .map(|(index, _)| index)
            .collect();
        let literal = image.function_image_len() + AARCH64_VENEER_LITERAL_OFFSET;
        assert!(
            differing
                .iter()
                .all(|&index| (literal..literal + 8).contains(&index)),
            "only the veneer literal may differ: {differing:?}"
        );
    }

    #[test]
    fn relink_refuses_a_different_extern_name_set() {
        let (_, image) = compile(&externs(host_add_ten));
        let image = image.unwrap();
        let mut extra = externs(host_add_ten);
        extra.insert("_an_unrelated_helper".into(), host_add_twenty as *const u8);
        assert!(matches!(
            unsafe { image.relink(&extra) },
            Err(RelinkError::Rejected(_))
        ));
        let mut nulled = externs(host_add_ten);
        nulled.insert("_an_unrelated_helper".into(), std::ptr::null());
        assert!(matches!(
            unsafe { image.relink(&nulled) },
            Err(RelinkError::Rejected(_))
        ));
        assert!(matches!(
            unsafe { image.relink(&HashMap::new()) },
            Err(RelinkError::Rejected(_))
        ));
    }

    #[test]
    fn serialized_image_round_trips_and_relinks() {
        let ext = externs(host_add_ten);
        let (cold, image) = compile(&ext);
        let image = image.unwrap();
        let bytes = image.to_bytes();
        assert_eq!(bytes, image.to_bytes(), "serialization is deterministic");
        let decoded = RelocatableImage::from_bytes(&bytes).expect("decode");
        assert_eq!(decoded, image);
        let warm = unsafe { decoded.relink(&ext) }.unwrap();
        assert_eq!(warm.code_slice(), cold.code_slice());
        assert_eq!(call(&warm, 5), 15);
    }

    #[test]
    fn every_single_byte_flip_of_a_serialized_image_is_refused() {
        let (_, image) = compile(&externs(host_add_ten));
        let bytes = image.unwrap().to_bytes();
        for index in 0..bytes.len() {
            let mut flipped = bytes.clone();
            flipped[index] ^= 0x40;
            assert!(
                RelocatableImage::from_bytes(&flipped).is_err(),
                "flip at {index} decoded"
            );
        }
        assert!(RelocatableImage::from_bytes(&bytes[..bytes.len() - 1]).is_err());
        assert!(RelocatableImage::from_bytes(&[]).is_err());
    }

    /// A resealed image cut short anywhere inside its body is refused by
    /// name: every fixed-width field read (`u32`, `u64`, the 32-byte digests)
    /// checks the remaining length itself, so a short read is a
    /// `RelinkError`, never a panic.
    #[test]
    fn a_resealed_truncated_image_is_refused_at_every_length() {
        let (_, image) = compile(&externs(host_add_ten));
        let bytes = image.unwrap().to_bytes();
        let body = &bytes[..bytes.len() - 32];
        for cut in RELOCATABLE_IMAGE_MAGIC.len() + 4..body.len() {
            let mut truncated = body[..cut].to_vec();
            let trailer: [u8; 32] = Sha256::digest(&truncated).into();
            truncated.extend_from_slice(&trailer);
            assert!(
                RelocatableImage::from_bytes(&truncated).is_err(),
                "a body cut at {cut} of {} decoded",
                body.len()
            );
        }
    }

    #[test]
    fn a_resealed_structural_forgery_is_refused() {
        let (_, image) = compile(&externs(host_add_ten));
        let image = image.unwrap();
        let veneer = image.function_image_len();
        // Each forgery edits the decoded image, then re-derives every digest a
        // keyless forger can compute.
        let forge = |edit: &dyn Fn(&mut RelocatableImage)| {
            let mut forged = image.clone();
            edit(&mut forged);
            forged.image_sha256 = Sha256::digest(&forged.code).into();
            let mut bytes = forged.to_bytes();
            reseal(&mut bytes);
            RelocatableImage::from_bytes(&bytes)
        };
        // A pre-written veneer literal (an address smuggled into the image).
        assert!(forge(&|f| f.code[veneer + 8] = 0x41).is_err());
        // A veneer stub that is not LDR/BR.
        assert!(forge(&|f| f.code[veneer] ^= 1).is_err());
        // A literal slot pointing into function code.
        assert!(forge(&|f| f.extern_literals[0].veneer_offset = 0).is_err());
        // A second slot for the same name, or a missing one.
        assert!(
            forge(&|f| {
                let dup = f.extern_literals[0].clone();
                f.extern_literals.push(ExternLiteral {
                    veneer_offset: dup.veneer_offset + AARCH64_VENEER_LEN as u64,
                    ..dup
                });
                f.code
                    .extend_from_within(veneer..veneer + AARCH64_VENEER_LEN);
            })
            .is_err()
        );
        assert!(forge(&|f| f.extern_literals.clear()).is_err());
        // A local row that no longer targets a function entry, or whose
        // pre-patch word is not ADRP/ADD.
        assert!(forge(&|f| f.local_rows[0].target += 4).is_err());
        assert!(forge(&|f| f.local_rows[0].original_word = 0xd503_201f).is_err());
        // Ranges that leave a gap, or a renamed canonical symbol.
        assert!(forge(&|f| f.function_ranges[1].1.start += 4).is_err());
        assert!(forge(&|f| f.canonical_symbols[0] = "other".into()).is_err());
        // A digest that does not name the bytes.
        let mut stale = image.clone();
        stale.code[0] ^= 1;
        let mut bytes = stale.to_bytes();
        reseal(&mut bytes);
        assert!(RelocatableImage::from_bytes(&bytes).is_err());
        // The untouched image still decodes (the controls are not vacuous).
        assert!(forge(&|_| {}).is_ok());
    }

    #[test]
    fn process_local_artifacts_are_named_refusals() {
        let ext = externs(host_add_ten);
        let counted = JitCompiler::new(JitConfig {
            emit_entry_counters: true,
            ..JitConfig::default()
        })
        .compile_raw_relocatable(&functions(), &ext)
        .unwrap();
        assert_eq!(
            counted.1.unwrap_err(),
            RelocatableImageRefusal::ProfileHooks
        );

        // A call bound to a local function only through its `_name` alias.
        let alias_only = vec![
            extern_caller("_trust_cg_relocatable_alias_only_target"),
            return_const("trust_cg_relocatable_alias_only_target", 7),
        ];
        let (buffer, image) = JitCompiler::new(JitConfig::default())
            .compile_raw_relocatable(&alias_only, &HashMap::new())
            .unwrap();
        assert_eq!(call(&buffer, 0), 7);
        assert_eq!(
            image.unwrap_err(),
            RelocatableImageRefusal::AliasResolvedInternalTarget
        );

        // A function stating its own target feature beyond the JIT profile
        // (L03-P9): the image format does not record it, so no image. The
        // buffer itself records the feature for a serialized contract.
        let crc = TargetFeatureSet::from_aarch64_features([crate::target::AArch64IsaFeature::Crc]);
        if crate::aarch64_dispatch::aarch64_host_features().implements_all(crc) {
            let mut stating = return_const("stating_crc", 5);
            stating.function_target_features = crc;
            let (buffer, image) = JitCompiler::new(JitConfig::default())
                .compile_raw_relocatable(&[stating], &HashMap::new())
                .unwrap();
            let stating: extern "C" fn() -> i64 = unsafe { buffer.get_fn("stating_crc").unwrap() };
            assert_eq!(stating(), 5);
            assert_eq!(buffer.aarch64_function_target_features(), crc);
            assert_eq!(
                image.unwrap_err(),
                RelocatableImageRefusal::FunctionTargetFeatures
            );
        }
    }

    #[test]
    fn a_module_without_externs_or_local_addresses_relinks() {
        let (cold, image) = JitCompiler::new(JitConfig::default())
            .compile_raw_relocatable(&[return_const("only", 9)], &HashMap::new())
            .unwrap();
        let image = image.unwrap();
        assert_eq!(image.code_len(), image.function_image_len());
        let warm = unsafe { image.relink(&HashMap::new()) }.unwrap();
        assert_eq!(warm.code_slice(), cold.code_slice());
        let f: extern "C" fn() -> i64 = unsafe { warm.get_fn("only").unwrap() };
        assert_eq!(f(), 9);
    }
}

#[cfg(all(test, feature = "source-defined-call"))]
mod aggregate_readback_tests {
    #[test]
    fn aggregate_readback_refuses_callee_result_frame_and_actual_bl_target_changes() {
        use super::super::installed_replay::{
            BranchTarget, CertifiedRange, InstalledReplayInventory,
        };
        let image: Vec<u8> = [
            0xd2800540u32,
            0xd65f03c0,
            0xa9bf7bfd,
            0x910003fd,
            0x97fffffc,
            0xa8c17bfd,
            0xd65f03c0,
        ]
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect();
        let leaf = crate::jit_diagnostics::sha256_hex(&image[..8]);
        let caller = crate::jit_diagnostics::sha256_hex(&image[8..]);
        let ranges = [
            CertifiedRange {
                name: "leaf",
                range: 0..8,
                certified_sha256: &leaf,
            },
            CertifiedRange {
                name: "entry",
                range: 8..28,
                certified_sha256: &caller,
            },
        ];
        let mut inventory = InstalledReplayInventory::default();
        inventory.branch(
            16,
            BranchTarget::Function {
                name: "leaf".into(),
                entry: 0,
            },
        );
        inventory.replay(&image, &image, 0x10000, &ranges).unwrap();
        for (offset, word) in [
            (0, 0xd2800560u32),
            (8, 0xa9bf7bfc),
            (16, 0x97fffffd),
            (20, 0xa8c27bfd),
        ] {
            let mut installed = image.clone();
            installed[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
            assert!(
                inventory
                    .replay(&image, &installed, 0x10000, &ranges)
                    .is_err()
            );
        }
        let mut wrong_target = InstalledReplayInventory::default();
        wrong_target.branch(
            16,
            BranchTarget::Function {
                name: "foreign".into(),
                entry: 4,
            },
        );
        assert!(
            wrong_target
                .replay(&image, &image, 0x10000, &ranges)
                .is_err()
        );
    }
}

/// Publish one already checked complete linked image without relayout or
/// repatching. The original rejected caller has no fabricated certificate;
/// installed readback derives its digest range from the real aggregate owner.
#[cfg(feature = "source-defined-call")]
pub(crate) fn publish_checked_defined_call(
    owner: &crate::compiler::CoreCheckedDefinedCallImage,
) -> Result<ExecutableBuffer, JitError> {
    if !cfg!(all(target_arch = "aarch64", target_os = "macos")) || !sys::host_supported() {
        return Err(JitError::UnsupportedHost {
            arch: std::env::consts::ARCH,
            os: std::env::consts::OS,
        });
    }
    let rejected = owner
        .linked()
        .predecessor()
        .machine_rejection()
        .ok_or_else(|| JitError::InstalledArtifactReplayRejected {
            function: "<aggregate>".into(),
            offset: 0,
            detail: "checked owner lost original rejection".into(),
        })?;
    let features = owner.publication_features();
    super::ensure_aarch64_function_features_supported(
        "<checked-defined-call>",
        features,
        crate::aarch64_dispatch::aarch64_host_features(),
    )?;
    let mut ranges = Vec::new();
    let mut symbols = HashMap::new();
    let mut canonical = Vec::new();
    let mut certificates = HashMap::new();
    for function in owner.linked().functions() {
        let range = function.range();
        let start = range.start as u64;
        for name in [function.name().to_owned(), format!("_{}", function.name())] {
            if symbols.insert(name.clone(), start).is_some() {
                return Err(JitError::DuplicateSymbol(name));
            }
        }
        ranges.push((function.name().to_owned(), start..range.end as u64));
        canonical.push(function.name().to_owned());
        for (id, name, _, certificate) in rejected.prior_replayed_functions() {
            if id == function.function() && name == function.name() {
                certificates.insert(
                    name.to_owned(),
                    certificate.rebound_for_publication(start..range.end as u64),
                );
            }
        }
    }
    let callee = owner
        .linked()
        .functions()
        .iter()
        .find(|f| f.function() == owner.callee())
        .ok_or_else(|| JitError::InstalledArtifactReplayRejected {
            function: "<aggregate>".into(),
            offset: 0,
            detail: "checked callee range is missing".into(),
        })?;
    let mut inventory = super::installed_replay::InstalledReplayInventory::default();
    inventory.branch(
        owner.linked().branch_offset(),
        super::installed_replay::BranchTarget::Function {
            name: callee.name().to_owned(),
            entry: callee.range().start as u64,
        },
    );
    let evidence = AggregateImageEvidence::from_checked(owner);
    publish_image(
        owner.linked().image().to_vec(),
        ranges,
        symbols,
        canonical,
        certificates,
        Some(inventory),
        features,
        Vec::new(),
        None,
        Some(&evidence),
    )
}
