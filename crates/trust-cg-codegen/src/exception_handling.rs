// trust-cg-codegen - Exception handling LSDA table generation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: Itanium C++ ABI Exception Handling
//            (https://itanium-cxx-abi.github.io/cxx-abi/abi-eh.html)
// Reference: ~/llvm-project-ref/llvm/lib/CodeGen/AsmPrinter/EHStreamer.cpp
//            (LSDA emission)
// Reference: DWARF 4 spec, Section 7.3 (DWARF Expression encoding)

//! Language-Specific Data Area (LSDA) table generation for C++ exception
//! handling on AArch64 macOS.
//!
//! The LSDA is emitted in the `__TEXT,__gcc_except_tab` section of a Mach-O
//! object file. Compact-unwind entries can reference it directly; DWARF
//! fallback entries reference it from FDE augmentation data. The personality
//! routine (`__gxx_personality_v0` for C++, `rust_eh_personality` for Rust)
//! uses it to dispatch exceptions to the correct landing pad.
//!
//! # LSDA layout (Itanium ABI)
//!
//! ```text
//! +-----------------------+
//! | Header                |
//! |  - LPStart encoding   |  u8: DW_EH_PE_omit => use function start
//! |  - TType encoding     |  u8: DW_EH_PE_omit if no type table
//! |  - TType base offset  |  ULEB128 (only if TType encoding != omit)
//! |  - Call site encoding  |  u8: DW_EH_PE_udata4 for AArch64
//! |  - Call site length    |  ULEB128
//! +-----------------------+
//! | Call Site Table        |
//! |  For each call site:   |
//! |  - region start        |  encoded (offset from function start)
//! |  - region length       |  encoded
//! |  - landing pad offset  |  encoded (0 = no landing pad)
//! |  - action index        |  ULEB128 (0 = cleanup only)
//! +-----------------------+
//! | Action Table           |
//! |  For each action:      |
//! |  - type filter index   |  SLEB128 (>0 catch, 0 cleanup, <0 filter)
//! |  - next action offset  |  SLEB128 (0 = end of chain)
//! +-----------------------+
//! | Type Table             |
//! |  (grows backward from  |
//! |   TType base offset)   |
//! |  - type info pointers  |  4 bytes each (udata4 encoding)
//! +-----------------------+
//! ```
//!
//! # Personality routines
//!
//! Compact-mode EH entries reference the personality routine through compact
//! unwind fields. DWARF-fallback EH entries reference it through CIE
//! augmentation data in `__eh_frame`. Common personality routines:
//! - `__gxx_personality_v0` — C++ (libcxxabi / libstdc++)
//! - `rust_eh_personality` — Rust panic unwinding
//! - `__gcc_personality_v0` — C cleanup-only

/// Canonical linker-level Rust personality name before object-format mangling.
/// Mach-O adds its one platform underscore at emission; ELF uses this spelling
/// directly. Historical `_rust_eh_personality` / `__rust_eh_personality`
/// spellings are object-level/internal aliases, not portable linker names.
pub const RUST_EH_PERSONALITY_SYMBOL: &str = "rust_eh_personality";

/// Why an EH personality symbol cannot be represented safely in an object.
///
/// Object symbol tables are NUL-terminated at serialization time. Accepting an
/// empty name or an embedded NUL would therefore either create an anonymous
/// undefined symbol or silently truncate the requested personality name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum PersonalitySymbolError {
    /// Structural exception-handling metadata omitted its personality.
    #[error("structural exception-handling metadata requires an explicit personality symbol")]
    Missing,
    /// An empty symbol cannot name a personality routine.
    #[error("exception-handling personality symbol must not be empty")]
    Empty,
    /// A NUL would truncate the symbol in the object string table.
    #[error("exception-handling personality symbol must not contain NUL bytes")]
    EmbeddedNul,
}

/// Why high-level landing-pad metadata cannot be serialized as a valid LSDA.
///
/// The Itanium call-site and action tables use byte offsets, not vector
/// indices. Rejecting malformed ranges and references here keeps every target
/// backend from independently guessing or silently emitting a different EH
/// program than the metadata describes.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum ExceptionTableBuildError {
    /// The personality name is missing or not representable in an object.
    #[error("invalid exception-handling personality: {0}")]
    InvalidPersonality(#[from] PersonalitySymbolError),
    /// Landing-pad offset zero is the Itanium no-handler sentinel.
    #[error("landing pad {index} uses offset 0, reserved by the LSDA as no-handler")]
    ZeroLandingPadOffset { index: usize },
    /// Two descriptors at the same byte offset would have ambiguous actions.
    #[error("duplicate landing-pad descriptor at byte offset {offset}")]
    DuplicateLandingPadOffset { offset: u32 },
    /// A pad that neither catches nor cleans up has no executable EH meaning.
    #[error("landing pad at byte offset {offset} has neither catches nor cleanup semantics")]
    EmptyLandingPad { offset: u32 },
    /// Repeating a filter in one chain is semantically redundant and obscures
    /// the intended handler order.
    #[error("landing pad at byte offset {offset} repeats catch type index {type_index}")]
    DuplicateCatchType { offset: u32, type_index: u32 },
    /// Positive typed catches need typeinfo symbol relocations, not numeric IDs.
    #[error(
        "landing pad at byte offset {offset} uses typed catch index {type_index}, but the LSDA byte-only path has no typeinfo-symbol relocation authority; only catch-all index 0 and cleanup are currently wired"
    )]
    TypedCatchRelocationUnsupported { offset: u32, type_index: u32 },
    /// The serialized action table uses 1-based `u32` byte offsets.
    #[error("serialized LSDA action table exceeds its u32 byte-offset domain")]
    ActionTableTooLarge,
    /// Positive type filters are signed 32-bit indices in an action record.
    #[error("LSDA type table has too many entries for an i32 action filter")]
    TypeTableTooLarge,
    /// A zero-sized region can never match an instruction pointer.
    #[error("call-site range {index} at byte offset {start} has zero length")]
    EmptyCallSite { index: usize, start: u32 },
    /// A range endpoint overflowed the LSDA's `u32` offset domain.
    #[error("call-site range {index} [{start}, {start} + {length}) overflows u32")]
    CallSiteRangeOverflow {
        index: usize,
        start: u32,
        length: u32,
    },
    /// The Itanium personality requires monotonically ordered, disjoint ranges.
    #[error(
        "call-site range {index} starts at {start}, before the preceding range ends at {previous_end}"
    )]
    OverlappingOrUnsortedCallSites {
        index: usize,
        start: u32,
        previous_end: u32,
    },
    /// A nonzero landing-pad offset must name exactly one descriptor.
    #[error("call-site range {index} references unknown landing-pad offset {offset}")]
    UnknownLandingPadOffset { index: usize, offset: u32 },
    /// Every semantic landing pad must be reachable from a protected range.
    #[error("landing-pad descriptor at byte offset {offset} has no call-site reference")]
    OrphanLandingPadOffset { offset: u32 },
}

/// Normalize the one known legacy personality alias at every codegen bridge.
/// Preserve Itanium/C++ spellings such as `__gxx_personality_v0`: their leading
/// underscores are part of the actual C ABI name (and Mach-O adds one more).
pub fn canonical_personality_symbol(name: &str) -> &str {
    match name {
        "_rust_eh_personality" | "__rust_eh_personality" => RUST_EH_PERSONALITY_SYMBOL,
        other => other,
    }
}

/// Validate and canonicalize a personality required by structural EH data.
///
/// The known historical Rust aliases are normalized to the portable linker
/// spelling. Every other valid name is preserved byte-for-byte; in particular,
/// C++ ABI names legitimately begin with underscores.
pub fn required_personality_symbol(name: Option<&str>) -> Result<&str, PersonalitySymbolError> {
    let name = name.ok_or(PersonalitySymbolError::Missing)?;
    if name.is_empty() {
        return Err(PersonalitySymbolError::Empty);
    }
    if name.as_bytes().contains(&0) {
        return Err(PersonalitySymbolError::EmbeddedNul);
    }
    Ok(canonical_personality_symbol(name))
}

// ---------------------------------------------------------------------------
// DWARF pointer encoding constants (DW_EH_PE_*)
// ---------------------------------------------------------------------------

/// DWARF Exception Handling Pointer Encoding format.
///
/// Defines how pointers in the LSDA (and eh_frame) are encoded.
/// The encoding byte has two parts:
/// - Low 4 bits: value format (absptr, udata2, udata4, etc.)
/// - High 4 bits: application (absptr, pcrel, datarel, etc.)
///
/// Reference: DWARF 4 spec, Table 7.9 (Pointer encoding)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum DwEhPe {
    /// DW_EH_PE_absptr: absolute pointer (native size).
    AbsPtr = 0x00,
    /// DW_EH_PE_uleb128: unsigned LEB128 (variable length).
    Uleb128 = 0x01,
    /// DW_EH_PE_udata2: unsigned 2-byte value.
    UData2 = 0x02,
    /// DW_EH_PE_udata4: unsigned 4-byte value.
    UData4 = 0x03,
    /// DW_EH_PE_udata8: unsigned 8-byte value.
    UData8 = 0x04,
    /// DW_EH_PE_sdata4: signed 4-byte value.
    SData4 = 0x0B,
    /// DW_EH_PE_omit: value is omitted (not present).
    Omit = 0xFF,
}

impl DwEhPe {
    /// Size in bytes of a value encoded with this format.
    ///
    /// Returns `None` for `Omit` (no value present) and `AbsPtr` (size
    /// depends on the target's pointer width).
    pub fn encoded_size(&self) -> Option<u32> {
        match self {
            DwEhPe::UData2 => Some(2),
            DwEhPe::UData4 | DwEhPe::SData4 => Some(4),
            DwEhPe::UData8 => Some(8),
            DwEhPe::AbsPtr => None,  // depends on target pointer size
            DwEhPe::Uleb128 => None, // variable length
            DwEhPe::Omit => None,
        }
    }
}

// ---------------------------------------------------------------------------
// LSDA data types
// ---------------------------------------------------------------------------

/// A single call site entry in the LSDA call site table.
///
/// Each entry describes a contiguous region of instructions that may throw
/// (or invoke cleanup code). The unwinder scans this table to find the
/// landing pad for a given instruction pointer.
///
/// All offsets are relative to the function start (LPStart).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallSiteEntry {
    /// Start of the call site region, as a byte offset from function start.
    pub region_start: u32,
    /// Length of the call site region in bytes.
    pub region_length: u32,
    /// Offset of the landing pad from function start.
    /// 0 means no landing pad (exception propagates to caller).
    pub landing_pad: u32,
    /// 1-based byte offset into the serialized action table.
    /// 0 means no action (cleanup-only or no handling).
    pub action_idx: u32,
}

impl CallSiteEntry {
    /// Create a call site with a landing pad and action.
    pub fn new(region_start: u32, region_length: u32, landing_pad: u32, action_idx: u32) -> Self {
        Self {
            region_start,
            region_length,
            landing_pad,
            action_idx,
        }
    }

    /// Create a call site with no landing pad (exception propagates).
    pub fn no_landing_pad(region_start: u32, region_length: u32) -> Self {
        Self {
            region_start,
            region_length,
            landing_pad: 0,
            action_idx: 0,
        }
    }

    /// Create a cleanup-only call site (landing pad but action_idx = 0).
    pub fn cleanup(region_start: u32, region_length: u32, landing_pad: u32) -> Self {
        Self {
            region_start,
            region_length,
            landing_pad,
            action_idx: 0,
        }
    }
}

/// A single action entry in the LSDA action table.
///
/// Actions form a linked list (via `next_action_offset`). Each action
/// specifies a type filter that the personality routine checks against
/// the thrown exception type.
///
/// The type filter values have special meaning:
/// - Positive: index into the type table (catch clause)
/// - Zero: cleanup action (always matches, like a destructor call)
/// - Negative: index into the filter table (exception spec)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActionEntry {
    /// Type filter index.
    /// Positive = catch (index into type table).
    /// Zero = cleanup.
    /// Negative = exception specification filter.
    pub type_filter: i32,
    /// Byte offset to the next action in the chain.
    ///
    /// Per the Itanium personality traversal, this displacement is relative to
    /// the address of the encoded displacement field (immediately after the
    /// `type_filter` SLEB128), not to the start of the action record.
    /// 0 = end of chain (no more actions for this call site).
    pub next_action_offset: i32,
}

impl ActionEntry {
    /// Create a catch action for a specific type.
    ///
    /// `type_index` is a 1-based index into the type table.
    pub fn catch(type_index: u32) -> Self {
        Self {
            type_filter: type_index as i32,
            next_action_offset: 0,
        }
    }

    /// Create a cleanup action (runs destructors, then re-throws).
    pub fn cleanup() -> Self {
        Self {
            type_filter: 0,
            next_action_offset: 0,
        }
    }

    /// Create a catch-all action that points at a NULL type-table slot.
    ///
    /// In the Itanium ABI a `catch(...)` is encoded as a **positive** action
    /// type-filter that indexes a type-table entry whose typeinfo pointer is
    /// NULL (the personality treats NULL as "match any type"). Type-filter 0
    /// means *cleanup*, which never stops the unwind — encoding a catch-all as
    /// 0 makes the personality report "no handler" and the program terminates.
    ///
    /// `type_index` is the 1-based index of the NULL type-table slot.
    pub fn catch_all(type_index: u32) -> Self {
        Self {
            type_filter: type_index as i32,
            next_action_offset: 0,
        }
    }
}

/// A type info entry in the LSDA type table.
///
/// Each entry holds a reference to a type info object (e.g.,
/// `std::type_info` for C++). The index is used by action entries
/// to identify which exception types to catch.
///
/// Index 0 is reserved for "cleanup" (no specific type match).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeInfo {
    /// Type info index. For now this is an opaque index that will be
    /// resolved to a symbol reference or relocation during object emission.
    /// 0 = catch-all / cleanup (matches any type).
    pub type_info_index: u32,
}

impl TypeInfo {
    /// Create a type info entry.
    pub fn new(index: u32) -> Self {
        Self {
            type_info_index: index,
        }
    }

    /// Create a catch-all type info entry (index 0).
    pub fn catch_all() -> Self {
        Self { type_info_index: 0 }
    }
}

// ---------------------------------------------------------------------------
// ExceptionTable — complete LSDA data for one function
// ---------------------------------------------------------------------------

/// Complete exception handling table for a single function.
///
/// Contains all the data needed to generate an LSDA: call site entries,
/// action entries, and type info entries. The `generate_lsda()` function
/// serializes this to the binary format expected by the personality routine.
#[derive(Debug, Clone)]
pub struct ExceptionTable {
    /// Call site entries (instruction regions that may throw).
    pub call_sites: Vec<CallSiteEntry>,
    /// Action entries (type filter chains for landing pads).
    pub actions: Vec<ActionEntry>,
    /// Type info entries (exception type references).
    pub type_infos: Vec<TypeInfo>,
    /// Personality routine symbol name (e.g., "__gxx_personality_v0").
    pub personality: Option<String>,
}

impl ExceptionTable {
    /// Create a new empty exception table.
    pub fn new() -> Self {
        Self {
            call_sites: Vec::new(),
            actions: Vec::new(),
            type_infos: Vec::new(),
            personality: None,
        }
    }

    /// Create an exception table with a C++ personality routine.
    pub fn with_cxx_personality() -> Self {
        Self {
            call_sites: Vec::new(),
            actions: Vec::new(),
            type_infos: Vec::new(),
            personality: Some("__gxx_personality_v0".to_string()),
        }
    }

    /// Create an exception table with a Rust personality routine.
    pub fn with_rust_personality() -> Self {
        Self {
            call_sites: Vec::new(),
            actions: Vec::new(),
            type_infos: Vec::new(),
            personality: Some(RUST_EH_PERSONALITY_SYMBOL.to_string()),
        }
    }

    /// Add a call site entry.
    pub fn add_call_site(&mut self, entry: CallSiteEntry) {
        self.call_sites.push(entry);
    }

    /// Add an action entry. Returns its 1-based vector position.
    ///
    /// This is not generally the serialized byte offset required by
    /// [`CallSiteEntry::action_idx`], because SLEB128 records are variable
    /// width. Production code uses the checked landing-pad builder instead.
    pub fn add_action(&mut self, entry: ActionEntry) -> u32 {
        self.actions.push(entry);
        self.actions.len() as u32
    }

    /// Add a type info entry. Returns the 1-based type index.
    pub fn add_type_info(&mut self, entry: TypeInfo) -> u32 {
        self.type_infos.push(entry);
        self.type_infos.len() as u32
    }

    /// Returns true if there are no call sites (no exception handling needed).
    pub fn is_empty(&self) -> bool {
        self.call_sites.is_empty()
    }
}

impl Default for ExceptionTable {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// LEB128 encoding helpers
// ---------------------------------------------------------------------------

/// Encode a value as ULEB128 (unsigned LEB128).
///
/// Returns the encoded bytes as a Vec. This is the public, allocating
/// interface; use `encode_uleb128_into` for the append-to-buffer variant.
pub fn encode_uleb128(value: u64) -> Vec<u8> {
    let mut out = Vec::new();
    encode_uleb128_into(value, &mut out);
    out
}

/// Encode a value as SLEB128 (signed LEB128).
///
/// Returns the encoded bytes as a Vec. This is the public, allocating
/// interface; use `encode_sleb128_into` for the append-to-buffer variant.
pub fn encode_sleb128(value: i64) -> Vec<u8> {
    let mut out = Vec::new();
    encode_sleb128_into(value, &mut out);
    out
}

/// Encode a value as ULEB128, appending to `out`.
fn encode_uleb128_into(mut value: u64, out: &mut Vec<u8>) {
    loop {
        let mut byte = (value & 0x7F) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80; // more bytes follow
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Encode a value as SLEB128, appending to `out`.
fn encode_sleb128_into(mut value: i64, out: &mut Vec<u8>) {
    let mut more = true;
    while more {
        let mut byte = (value & 0x7F) as u8;
        value >>= 7;
        // If the sign bit of the current byte matches the remaining value,
        // we're done.
        if (value == 0 && byte & 0x40 == 0) || (value == -1 && byte & 0x40 != 0) {
            more = false;
        } else {
            byte |= 0x80;
        }
        out.push(byte);
    }
}

/// Return the exact number of bytes [`encode_sleb128_into`] emits without
/// allocating a temporary buffer.
fn sleb128_encoded_len(mut value: i64) -> usize {
    let mut len = 0;
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        len += 1;
        if (value == 0 && byte & 0x40 == 0) || (value == -1 && byte & 0x40 != 0) {
            return len;
        }
    }
}

/// Return the exact number of bytes [`encode_uleb128_into`] emits.
fn uleb128_encoded_len(mut value: u64) -> usize {
    let mut len = 1;
    while value >= 0x80 {
        value >>= 7;
        len += 1;
    }
    len
}

/// Compute a self-consistent type-table padding and TType base offset.
///
/// The padding depends on the encoded length of `ttype_base`, while
/// `ttype_base` itself includes the padding. In particular, adding alignment
/// bytes can cross a ULEB128 width boundary such as 127 -> 128. A one-pass
/// estimate therefore produces a misaligned table for reachable table sizes.
fn type_table_layout(pre_type_len: usize, type_data_len: usize) -> (usize, usize) {
    const HEADER_BEFORE_BASE: usize = 2; // LPStart encoding + TType encoding

    // Once a ULEB width boundary has been crossed, at most three additional
    // bytes are needed to find the next 4-byte-aligned address. Searching the
    // actual encoded layout is both simpler and correct at every boundary.
    let mut pad = 0usize;
    loop {
        let ttype_base = pre_type_len
            .checked_add(pad)
            .and_then(|value| value.checked_add(type_data_len))
            .expect("allocated LSDA components must fit in usize");
        let encoded_base =
            u64::try_from(ttype_base).expect("supported targets have at most 64-bit usize");
        let type_table_start = HEADER_BEFORE_BASE
            .checked_add(uleb128_encoded_len(encoded_base))
            .and_then(|value| value.checked_add(pre_type_len))
            .and_then(|value| value.checked_add(pad))
            .expect("allocated LSDA components must fit in usize");
        if type_table_start.is_multiple_of(4) {
            return (pad, ttype_base);
        }
        pad = pad.checked_add(1).expect("LSDA alignment padding overflow");
    }
}

// ---------------------------------------------------------------------------
// Call site table emission
// ---------------------------------------------------------------------------

/// Emit the call site table as raw bytes.
///
/// Each entry is encoded according to `encoding`:
/// - `DwEhPe::UData4`: each field is a 4-byte unsigned little-endian value
/// - Other encodings: currently only UData4 is supported for AArch64
///
/// The action index is always ULEB128-encoded per the Itanium ABI.
fn emit_call_site_table(call_sites: &[CallSiteEntry], encoding: DwEhPe) -> Vec<u8> {
    let mut data = Vec::new();

    for cs in call_sites {
        match encoding {
            DwEhPe::Uleb128 => {
                // Clang/LLVM's canonical AArch64 macOS call-site encoding. The
                // region start/length/landing-pad are all function-relative
                // offsets that fit comfortably in ULEB128, producing a more
                // compact (and host-`__gxx_personality_v0`-matching) table.
                encode_uleb128_into(cs.region_start as u64, &mut data);
                encode_uleb128_into(cs.region_length as u64, &mut data);
                encode_uleb128_into(cs.landing_pad as u64, &mut data);
            }
            _ => {
                // udata4: each field is a fixed 4-byte little-endian value.
                data.extend_from_slice(&cs.region_start.to_le_bytes());
                data.extend_from_slice(&cs.region_length.to_le_bytes());
                data.extend_from_slice(&cs.landing_pad.to_le_bytes());
            }
        }
        // Action index is always ULEB128 per Itanium ABI.
        encode_uleb128_into(cs.action_idx as u64, &mut data);
    }

    data
}

// ---------------------------------------------------------------------------
// Action table emission
// ---------------------------------------------------------------------------

/// Emit the action table as raw bytes.
///
/// Each action entry consists of two SLEB128 values:
/// 1. Type filter index (positive = catch, 0 = cleanup, negative = filter)
/// 2. Next action offset (byte displacement to next action, 0 = end of chain)
fn emit_action_table(actions: &[ActionEntry]) -> Vec<u8> {
    let mut data = Vec::new();

    for action in actions {
        encode_sleb128_into(action.type_filter as i64, &mut data);
        encode_sleb128_into(action.next_action_offset as i64, &mut data);
    }

    data
}

// ---------------------------------------------------------------------------
// Type table emission
// ---------------------------------------------------------------------------

/// Emit the type table as raw bytes.
///
/// Type info entries are emitted in reverse order (the Itanium ABI
/// specifies that the type table grows backward from the TType base).
/// Each entry is a 4-byte value (for DW_EH_PE_udata4 encoding).
///
/// The entries are emitted in the order they appear in the `type_infos`
/// slice, but the personality routine indexes them backwards from the
/// TType base offset. Entry at index 1 is the last 4 bytes before the
/// TType base, entry 2 is 8 bytes before, etc.
fn emit_type_table(type_infos: &[TypeInfo]) -> Vec<u8> {
    let mut data = Vec::new();

    // Type table entries are stored in reverse order so that
    // type_info[1] is at (TType_base - 4), type_info[2] at (TType_base - 8), etc.
    for ti in type_infos.iter().rev() {
        data.extend_from_slice(&ti.type_info_index.to_le_bytes());
    }

    data
}

// ---------------------------------------------------------------------------
// LSDA generation — main entry point
// ---------------------------------------------------------------------------

/// Generate a complete LSDA (Language-Specific Data Area) for one function.
///
/// The output bytes are intended for the `__TEXT,__gcc_except_tab` Mach-O
/// section. The personality routine reads this data to dispatch exceptions
/// to the correct landing pad.
///
/// # Binary layout
///
/// See the module-level documentation for the full LSDA layout.
///
/// # Arguments
///
/// * `table` — The exception table containing call sites, actions, and type info.
///
/// # Returns
///
/// A `Vec<u8>` containing the serialized LSDA bytes.
fn generate_lsda(table: &ExceptionTable) -> Vec<u8> {
    // Match clang/LLVM's AArch64 macOS call-site encoding (ULEB128). The
    // encoding byte is self-describing, so the host `__gxx_personality_v0`
    // decodes it the same way it decodes its own emitted tables.
    let call_site_encoding = DwEhPe::Uleb128;
    let has_type_table = !table.type_infos.is_empty();

    // Pre-emit the call site table, action table, and type table to compute sizes.
    let call_site_data = emit_call_site_table(&table.call_sites, call_site_encoding);
    let action_data = emit_action_table(&table.actions);
    let type_data = emit_type_table(&table.type_infos);

    let mut lsda = Vec::new();

    // --- Header ---

    // LPStart encoding: DW_EH_PE_omit (0xFF) = use function start as LPStart.
    lsda.push(DwEhPe::Omit as u8);

    if has_type_table {
        // TType encoding. C++ type tables on AArch64 macOS hold typeinfo
        // *pointers*, encoded as `DW_EH_PE_indirect | DW_EH_PE_pcrel |
        // DW_EH_PE_sdata4` (0x9b) — matching what clang/LLVM emit, which is
        // what the host `__gxx_personality_v0` expects when decoding entries.
        // The catch-all slot is a literal NULL (4 zero bytes); the personality
        // treats a NULL typeinfo as "match any type" without applying the
        // pcrel adjustment, so no relocation is needed for `catch(...)`.
        const DW_EH_PE_INDIRECT_PCREL_SDATA4: u8 = 0x9b;
        lsda.push(DW_EH_PE_INDIRECT_PCREL_SDATA4);

        // The type table is built from 4-byte sdata4 entries and must be
        // 4-byte aligned. After the action table we may need one or more
        // padding bytes so the type table starts on a 4-byte boundary,
        // exactly as clang lays it out. Compute that padding now.
        //
        // Bytes that precede the type table, counted from the byte *after* the
        // TType base offset field (which is where the offset is measured from):
        //   call_site_encoding (1) + call_site_length (ULEB128)
        //   + call_site_data + action_data
        let cs_length_encoded = encode_uleb128(call_site_data.len() as u64);
        let pre_type_len = 1 // call site encoding byte
            + cs_length_encoded.len()
            + call_site_data.len()
            + action_data.len();

        // The base field's ULEB128 width and the padding are interdependent at
        // width boundaries, so derive them from the final layout rather than
        // assuming that adding 0..3 bytes leaves the field width unchanged.
        let (pad, ttype_base) = type_table_layout(pre_type_len, type_data.len());

        encode_uleb128_into(
            u64::try_from(ttype_base).expect("supported targets have at most 64-bit usize"),
            &mut lsda,
        );
        lsda.push(call_site_encoding as u8);
        encode_uleb128_into(call_site_data.len() as u64, &mut lsda);
        lsda.extend_from_slice(&call_site_data);
        lsda.extend_from_slice(&action_data);
        lsda.extend(std::iter::repeat_n(0u8, pad));
        lsda.extend_from_slice(&type_data);
        return lsda;
    }

    // --- No type table (cleanup-only): TType encoding = DW_EH_PE_omit. ---
    lsda.push(DwEhPe::Omit as u8);

    // Call site encoding.
    lsda.push(call_site_encoding as u8);

    // Call site table length (ULEB128).
    encode_uleb128_into(call_site_data.len() as u64, &mut lsda);

    // --- Call site table ---
    lsda.extend_from_slice(&call_site_data);

    // --- Action table ---
    lsda.extend_from_slice(&action_data);

    lsda
}

// ---------------------------------------------------------------------------
// Checked canonical EH-to-LSDA bridge
// ---------------------------------------------------------------------------
//
// `trust_cg_lower::function::EhFunctionInfo` is the sole semantic EH
// authority. Target pipelines authenticate it against Invoke/LandingPad/Resume
// opcodes, resolve final code offsets, and pass that projection through the
// checked builder below. There is intentionally no raw public LSDA bridge.

/// Build an `ExceptionTable` from landing pad metadata.
///
/// This is a higher-level builder that takes landing pad descriptors and
/// automatically constructs the call site table, action table, and type
/// table. It handles:
///
/// - **Catch typed**: Fails closed until typeinfo-symbol relocations are carried
///   alongside the LSDA bytes
/// - **Catch-all**: Creates a positive action filter referencing a NULL
///   type-table slot (distinct from cleanup filter 0)
/// - **Cleanup**: Creates cleanup call sites (action_idx = 0, landing pad set)
/// - **Action chains**: When a landing pad has multiple catch types, chains
///   them via next_action_offset
///
/// # Arguments
///
/// * `personality` — Personality function symbol name
/// * `landing_pads` — Landing pad descriptors
/// * `call_site_ranges` — PC ranges mapping to landing pads. Each tuple is
///   `(start_offset, length, landing_pad_offset)`.
///
/// # Returns
///
/// A fully populated `ExceptionTable` ready for `generate_lsda()`, or a typed
/// error when the metadata cannot form an ordered, referentially closed LSDA.
fn build_exception_table_from_pads(
    personality: &str,
    landing_pads: &[LandingPadDesc],
    call_site_ranges: &[(u32, u32, u32)],
) -> Result<ExceptionTable, ExceptionTableBuildError> {
    let mut table = ExceptionTable::new();
    table.personality = Some(required_personality_symbol(Some(personality))?.to_string());

    let mut landing_pad_offsets = std::collections::BTreeSet::new();
    for (index, lp) in landing_pads.iter().enumerate() {
        if lp.landing_pad_offset == 0 {
            return Err(ExceptionTableBuildError::ZeroLandingPadOffset { index });
        }
        if !landing_pad_offsets.insert(lp.landing_pad_offset) {
            return Err(ExceptionTableBuildError::DuplicateLandingPadOffset {
                offset: lp.landing_pad_offset,
            });
        }
        if !lp.is_cleanup && lp.catch_type_indices.is_empty() {
            return Err(ExceptionTableBuildError::EmptyLandingPad {
                offset: lp.landing_pad_offset,
            });
        }
        let mut catch_types = std::collections::HashSet::new();
        if let Some(type_index) = lp
            .catch_type_indices
            .iter()
            .copied()
            .find(|type_index| !catch_types.insert(*type_index))
        {
            return Err(ExceptionTableBuildError::DuplicateCatchType {
                offset: lp.landing_pad_offset,
                type_index,
            });
        }
        if let Some(&type_index) = lp.catch_type_indices.iter().find(|&&index| index != 0) {
            return Err(ExceptionTableBuildError::TypedCatchRelocationUnsupported {
                offset: lp.landing_pad_offset,
                type_index,
            });
        }
    }

    // Collect all distinct catch type indices, mapping each to a 1-based slot
    // in the type table. A `catch(...)` (catch-all) is encoded the way the
    // Itanium C++ ABI / `__gxx_personality_v0` expects: a **positive** action
    // type-filter that points at a type-table slot whose typeinfo pointer is
    // NULL. The personality treats a NULL typeinfo as "match any type" and
    // installs the handler. This is the critical distinction from a *cleanup*
    // action (type-filter 0): a cleanup runs destructors but never stops the
    // unwind, so encoding a catch-all as type-filter 0 makes the personality
    // report "no handler", the exception unwinds past the landing pad, and the
    // program calls `std::terminate()` (the catch silently fails / aborts).
    //
    // The reserved index 0 (`type_info_index == 0`) is used as that NULL slot.
    // We assign each distinct catch index (including the catch-all sentinel 0)
    // its 1-based type-table slot at insertion time and remember it, so the
    // action type-filter always matches the real table position regardless of
    // the order catch-all vs. typed catches first appear.
    let mut slot_of: std::collections::HashMap<u32, i32> = std::collections::HashMap::new();
    for lp in landing_pads {
        for &ti in &lp.catch_type_indices {
            if let std::collections::hash_map::Entry::Vacant(entry) = slot_of.entry(ti) {
                if ti == 0 {
                    table.add_type_info(TypeInfo::catch_all());
                } else {
                    table.add_type_info(TypeInfo::new(ti));
                }
                let slot = i32::try_from(table.type_infos.len())
                    .map_err(|_| ExceptionTableBuildError::TypeTableTooLarge)?;
                entry.insert(slot); // 1-based slot index
            }
        }
    }

    // Build action entries for each landing pad.
    // Each landing pad gets an action chain. The first action's 1-based index
    // is stored in the call site entry.
    let mut lp_to_first_action: std::collections::HashMap<u32, u32> =
        std::collections::HashMap::new();
    let mut action_table_len = 0usize;

    for lp in landing_pads {
        if lp.is_cleanup && lp.catch_type_indices.is_empty() {
            // Cleanup-only: action_idx = 0 in the call site (no action chain).
            lp_to_first_action.insert(lp.landing_pad_offset, 0);
            continue;
        }

        // Build the action chain for this landing pad's catch types.
        // `CallSiteEntry::action_idx` is a 1-based BYTE OFFSET into the
        // serialized action table, not a 1-based action-vector index.
        let chain_start = u32::try_from(action_table_len)
            .ok()
            .and_then(|offset| offset.checked_add(1))
            .ok_or(ExceptionTableBuildError::ActionTableTooLarge)?;
        let num_catches = lp.catch_type_indices.len();

        for (i, &catch_idx) in lp.catch_type_indices.iter().enumerate() {
            // Positive type-filter into the type table (catch-all uses the NULL
            // slot; see the comment above). Never 0, which would be a cleanup.
            let type_filter = slot_of
                .get(&catch_idx)
                .copied()
                .expect("every validated catch type has a type-table slot");

            // libc++abi advances from the address of the encoded displacement
            // field (immediately after `type_filter`), not from the action
            // record start. Every chain we construct is contiguous, so the next
            // record begins immediately after this one-byte SLEB128 value: the
            // correct displacement is exactly 1 even when `type_filter` itself
            // needs multiple SLEB128 bytes.
            let is_last = i == num_catches - 1;
            let next_offset = if is_last && !lp.is_cleanup {
                0 // end of chain
            } else {
                1
            };

            table.actions.push(ActionEntry {
                type_filter,
                next_action_offset: next_offset,
            });
            action_table_len = action_table_len
                .checked_add(sleb128_encoded_len(i64::from(type_filter)))
                .and_then(|len| len.checked_add(1)) // next offset is 0 or 1
                .ok_or(ExceptionTableBuildError::ActionTableTooLarge)?;
        }

        // If the landing pad has both catches and cleanup, add a cleanup action
        // at the end of the chain.
        if lp.is_cleanup && !lp.catch_type_indices.is_empty() {
            table.actions.push(ActionEntry {
                type_filter: 0,        // cleanup
                next_action_offset: 0, // end of chain
            });
            action_table_len = action_table_len
                .checked_add(2)
                .ok_or(ExceptionTableBuildError::ActionTableTooLarge)?;
        }

        lp_to_first_action.insert(lp.landing_pad_offset, chain_start);
    }

    // Build call site entries.
    let mut previous_end = 0u32;
    let mut referenced_landing_pads = std::collections::BTreeSet::new();
    for (index, &(start, length, lp_offset)) in call_site_ranges.iter().enumerate() {
        if length == 0 {
            return Err(ExceptionTableBuildError::EmptyCallSite { index, start });
        }
        let end =
            start
                .checked_add(length)
                .ok_or(ExceptionTableBuildError::CallSiteRangeOverflow {
                    index,
                    start,
                    length,
                })?;
        if index != 0 && start < previous_end {
            return Err(ExceptionTableBuildError::OverlappingOrUnsortedCallSites {
                index,
                start,
                previous_end,
            });
        }
        previous_end = end;

        let action_idx = if lp_offset == 0 {
            0 // no landing pad
        } else {
            referenced_landing_pads.insert(lp_offset);
            lp_to_first_action.get(&lp_offset).copied().ok_or(
                ExceptionTableBuildError::UnknownLandingPadOffset {
                    index,
                    offset: lp_offset,
                },
            )?
        };

        table.add_call_site(CallSiteEntry::new(start, length, lp_offset, action_idx));
    }

    if let Some(offset) = landing_pad_offsets
        .difference(&referenced_landing_pads)
        .next()
        .copied()
    {
        return Err(ExceptionTableBuildError::OrphanLandingPadOffset { offset });
    }

    Ok(table)
}

/// The sole production LSDA-byte boundary.
///
/// Raw [`ExceptionTable`] serialization remains private because a manually
/// assembled table can contain unchecked byte displacements or positive typed
/// catches without the object relocations they require. Target emitters pass
/// resolved landing-pad/range metadata through this checked constructor.
pub(crate) fn generate_lsda_from_pads(
    personality: &str,
    landing_pads: &[LandingPadDesc],
    call_site_ranges: &[(u32, u32, u32)],
) -> Result<Vec<u8>, ExceptionTableBuildError> {
    let table = build_exception_table_from_pads(personality, landing_pads, call_site_ranges)?;
    Ok(generate_lsda(&table))
}

/// Descriptor for a landing pad, used by `build_exception_table_from_pads`.
#[derive(Debug, Clone)]
pub(crate) struct LandingPadDesc {
    /// Offset of the landing pad from the function start.
    pub landing_pad_offset: u32,
    /// Type indices this landing pad catches. 0 = catch-all.
    pub catch_type_indices: Vec<u32>,
    /// Whether this landing pad runs cleanup (destructors/drops).
    pub is_cleanup: bool,
}

#[cfg(test)]
impl LandingPadDesc {
    /// Create a catch-all landing pad.
    pub fn catch_all(offset: u32) -> Self {
        Self {
            landing_pad_offset: offset,
            catch_type_indices: vec![0],
            is_cleanup: false,
        }
    }

    /// Create a typed catch landing pad descriptor.
    ///
    /// The current byte-only high-level LSDA builder rejects this descriptor
    /// until object emission can carry the required typeinfo-symbol relocation.
    pub fn catch_typed(offset: u32, type_index: u32) -> Self {
        Self {
            landing_pad_offset: offset,
            catch_type_indices: vec![type_index],
            is_cleanup: false,
        }
    }

    /// Create a cleanup-only landing pad.
    pub fn cleanup(offset: u32) -> Self {
        Self {
            landing_pad_offset: offset,
            catch_type_indices: Vec::new(),
            is_cleanup: true,
        }
    }

    /// Create a landing pad that catches a type and also runs cleanup.
    pub fn catch_and_cleanup(offset: u32, type_index: u32) -> Self {
        Self {
            landing_pad_offset: offset,
            catch_type_indices: vec![type_index],
            is_cleanup: true,
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- ULEB128 encoding tests ---

    #[test]
    fn test_encode_uleb128_zero() {
        assert_eq!(encode_uleb128(0), vec![0x00]);
    }

    #[test]
    fn test_encode_uleb128_single_byte() {
        assert_eq!(encode_uleb128(1), vec![0x01]);
        assert_eq!(encode_uleb128(63), vec![63]);
        assert_eq!(encode_uleb128(127), vec![0x7F]);
    }

    #[test]
    fn test_encode_uleb128_multi_byte() {
        // 128 = 0x80 => [0x80, 0x01]
        assert_eq!(encode_uleb128(128), vec![0x80, 0x01]);
        // 624485 = 0x98765 => [0xE5, 0x8E, 0x26]
        assert_eq!(encode_uleb128(624485), vec![0xE5, 0x8E, 0x26]);
    }

    #[test]
    fn test_encode_uleb128_large() {
        // 256 = 0x100 => [0x80, 0x02]
        assert_eq!(encode_uleb128(256), vec![0x80, 0x02]);
        // 16384 = 0x4000 => [0x80, 0x80, 0x01]
        assert_eq!(encode_uleb128(16384), vec![0x80, 0x80, 0x01]);
    }

    // --- SLEB128 encoding tests ---

    #[test]
    fn test_encode_sleb128_zero() {
        assert_eq!(encode_sleb128(0), vec![0x00]);
    }

    #[test]
    fn test_encode_sleb128_positive() {
        assert_eq!(encode_sleb128(1), vec![0x01]);
        assert_eq!(encode_sleb128(63), vec![63]);
        // 64 needs 2 bytes because bit 6 (sign bit) would be set in a single byte.
        assert_eq!(encode_sleb128(64), vec![0xC0, 0x00]);
    }

    #[test]
    fn test_encode_sleb128_negative() {
        // -1 => [0x7F]
        assert_eq!(encode_sleb128(-1), vec![0x7F]);
        // -8 => [0x78]
        assert_eq!(encode_sleb128(-8), vec![0x78]);
        // -64 => [0x40]
        assert_eq!(encode_sleb128(-64), vec![0x40]);
        // -65 => [0xBF, 0x7F]
        assert_eq!(encode_sleb128(-65), vec![0xBF, 0x7F]);
    }

    // --- DwEhPe tests ---

    #[test]
    fn test_dw_eh_pe_encoded_size() {
        assert_eq!(DwEhPe::UData2.encoded_size(), Some(2));
        assert_eq!(DwEhPe::UData4.encoded_size(), Some(4));
        assert_eq!(DwEhPe::SData4.encoded_size(), Some(4));
        assert_eq!(DwEhPe::UData8.encoded_size(), Some(8));
        assert_eq!(DwEhPe::AbsPtr.encoded_size(), None);
        assert_eq!(DwEhPe::Omit.encoded_size(), None);
    }

    #[test]
    fn test_dw_eh_pe_values() {
        assert_eq!(DwEhPe::AbsPtr as u8, 0x00);
        assert_eq!(DwEhPe::UData4 as u8, 0x03);
        assert_eq!(DwEhPe::Omit as u8, 0xFF);
    }

    // --- CallSiteEntry tests ---

    #[test]
    fn test_call_site_entry_constructors() {
        let cs = CallSiteEntry::new(0x10, 0x20, 0x100, 1);
        assert_eq!(cs.region_start, 0x10);
        assert_eq!(cs.region_length, 0x20);
        assert_eq!(cs.landing_pad, 0x100);
        assert_eq!(cs.action_idx, 1);

        let no_lp = CallSiteEntry::no_landing_pad(0x10, 0x20);
        assert_eq!(no_lp.landing_pad, 0);
        assert_eq!(no_lp.action_idx, 0);

        let cleanup = CallSiteEntry::cleanup(0x10, 0x20, 0x100);
        assert_eq!(cleanup.landing_pad, 0x100);
        assert_eq!(cleanup.action_idx, 0);
    }

    // --- ActionEntry tests ---

    #[test]
    fn test_action_entry_catch() {
        let action = ActionEntry::catch(1);
        assert_eq!(action.type_filter, 1);
        assert_eq!(action.next_action_offset, 0);
    }

    #[test]
    fn test_action_entry_cleanup() {
        let action = ActionEntry::cleanup();
        assert_eq!(action.type_filter, 0);
        assert_eq!(action.next_action_offset, 0);
    }

    #[test]
    fn test_action_entry_chain() {
        // An action chain: catch type 1, then cleanup.
        let mut action1 = ActionEntry::catch(1);
        action1.next_action_offset = 1; // next record follows this one-byte displacement field
        let action2 = ActionEntry::cleanup();

        let data = emit_action_table(&[action1, action2]);
        // action1: SLEB128(1) = [0x01], SLEB128(1) = [0x01]
        // action2: SLEB128(0) = [0x00], SLEB128(0) = [0x00]
        assert_eq!(data, vec![0x01, 0x01, 0x00, 0x00]);
    }

    // --- TypeInfo tests ---

    #[test]
    fn test_type_info_entries() {
        let ti = TypeInfo::new(42);
        assert_eq!(ti.type_info_index, 42);

        let catch_all = TypeInfo::catch_all();
        assert_eq!(catch_all.type_info_index, 0);
    }

    #[test]
    fn test_type_table_emission_order() {
        // Type infos are emitted in reverse order.
        let type_infos = vec![TypeInfo::new(1), TypeInfo::new(2), TypeInfo::new(3)];
        let data = emit_type_table(&type_infos);

        // Reverse order: 3, 2, 1 — each 4 bytes LE.
        assert_eq!(data.len(), 12);
        assert_eq!(u32::from_le_bytes(data[0..4].try_into().unwrap()), 3);
        assert_eq!(u32::from_le_bytes(data[4..8].try_into().unwrap()), 2);
        assert_eq!(u32::from_le_bytes(data[8..12].try_into().unwrap()), 1);
    }

    // --- ExceptionTable tests ---

    #[test]
    fn test_exception_table_new() {
        let table = ExceptionTable::new();
        assert!(table.is_empty());
        assert!(table.personality.is_none());
    }

    #[test]
    fn test_exception_table_with_cxx_personality() {
        let table = ExceptionTable::with_cxx_personality();
        assert_eq!(table.personality.as_deref(), Some("__gxx_personality_v0"));
    }

    #[test]
    fn test_exception_table_with_rust_personality() {
        let table = ExceptionTable::with_rust_personality();
        assert_eq!(table.personality.as_deref(), Some("rust_eh_personality"));
    }

    #[test]
    fn test_rust_personality_aliases_normalize_without_touching_custom_or_cxx_names() {
        for alias in [
            "rust_eh_personality",
            "_rust_eh_personality",
            "__rust_eh_personality",
        ] {
            assert_eq!(canonical_personality_symbol(alias), "rust_eh_personality");
        }
        assert_eq!(
            canonical_personality_symbol("__gxx_personality_v0"),
            "__gxx_personality_v0"
        );
        assert_eq!(
            canonical_personality_symbol("__my_custom_personality"),
            "__my_custom_personality"
        );
    }

    #[test]
    fn required_personality_rejects_unrepresentable_symbols_and_preserves_custom_names() {
        assert_eq!(
            required_personality_symbol(None),
            Err(PersonalitySymbolError::Missing)
        );
        assert_eq!(
            required_personality_symbol(Some("")),
            Err(PersonalitySymbolError::Empty)
        );
        assert_eq!(
            required_personality_symbol(Some("custom\0truncated")),
            Err(PersonalitySymbolError::EmbeddedNul)
        );
        assert_eq!(
            required_personality_symbol(Some("_rust_eh_personality")),
            Ok(RUST_EH_PERSONALITY_SYMBOL)
        );
        assert_eq!(
            required_personality_symbol(Some("__my_custom_personality")),
            Ok("__my_custom_personality")
        );
    }

    #[test]
    fn test_exception_table_add_entries() {
        let mut table = ExceptionTable::new();

        table.add_call_site(CallSiteEntry::new(0, 16, 32, 1));
        assert_eq!(table.call_sites.len(), 1);

        let action_idx = table.add_action(ActionEntry::catch(1));
        assert_eq!(action_idx, 1);

        let type_idx = table.add_type_info(TypeInfo::new(42));
        assert_eq!(type_idx, 1);

        assert!(!table.is_empty());
    }

    #[test]
    fn test_exception_table_default() {
        let table = ExceptionTable::default();
        assert!(table.is_empty());
    }

    // --- LSDA generation tests ---

    #[test]
    fn test_empty_lsda() {
        // Empty exception table: no call sites, no actions, no type infos.
        let table = ExceptionTable::new();
        let lsda = generate_lsda(&table);

        // Header:
        // [0]: LPStart encoding = 0xFF (omit)
        // [1]: TType encoding = 0xFF (omit, no type table)
        // [2]: Call site encoding = 0x01 (uleb128, clang-canonical)
        // [3]: Call site table length = 0x00 (ULEB128, zero entries)
        assert_eq!(lsda.len(), 4);
        assert_eq!(lsda[0], 0xFF); // LPStart = omit
        assert_eq!(lsda[1], 0xFF); // TType = omit
        assert_eq!(lsda[2], 0x01); // call site encoding = uleb128
        assert_eq!(lsda[3], 0x00); // call site table length = 0
    }

    #[test]
    fn test_lsda_header_layout() {
        // LSDA with call sites but no type table.
        let mut table = ExceptionTable::new();
        table.add_call_site(CallSiteEntry::cleanup(0, 16, 32));

        let lsda = generate_lsda(&table);

        // Header check:
        assert_eq!(lsda[0], 0xFF); // LPStart = omit
        assert_eq!(lsda[1], 0xFF); // TType = omit (no type infos)
        assert_eq!(lsda[2], 0x01); // call site encoding = uleb128

        // Call site table length: one entry with uleb128 encoding.
        // region_start=0 (1) + region_length=16 (1) + landing_pad=32 (1)
        // + action_idx=0 (1) = 4 bytes.
        assert_eq!(lsda[3], 4); // call site table length
    }

    #[test]
    fn test_single_call_site_with_landing_pad() {
        let mut table = ExceptionTable::new();
        table.add_call_site(CallSiteEntry::new(0x10, 0x08, 0x50, 1));
        table.add_action(ActionEntry::catch(1));
        table.add_type_info(TypeInfo::new(100));

        let lsda = generate_lsda(&table);

        // Should have a non-empty LSDA with type table.
        assert!(lsda.len() > 4);

        // LPStart = omit.
        assert_eq!(lsda[0], 0xFF);

        // TType encoding should be the C++ indirect|pcrel|sdata4 form (0x9b),
        // not omit, since we have a type table.
        assert_eq!(lsda[1], 0x9b);

        // Verify the LSDA contains the call site region_start (0x10) as a
        // single ULEB128 byte (fits in 7 bits).
        assert!(
            lsda.contains(&0x10),
            "LSDA should contain region_start as a ULEB128 byte"
        );
    }

    #[test]
    fn test_multiple_call_sites() {
        let mut table = ExceptionTable::new();
        table.add_call_site(CallSiteEntry::new(0x00, 0x10, 0x80, 1));
        table.add_call_site(CallSiteEntry::new(0x10, 0x08, 0x90, 1));
        table.add_call_site(CallSiteEntry::no_landing_pad(0x18, 0x04));
        table.add_action(ActionEntry::catch(1));
        table.add_type_info(TypeInfo::new(1));

        let lsda = generate_lsda(&table);

        // Should produce a valid LSDA.
        assert!(lsda.len() > 4);
        assert_eq!(lsda[0], 0xFF); // LPStart = omit
    }

    #[test]
    fn test_cleanup_only() {
        // Landing pad with action_idx = 0 means cleanup-only (no catch clause).
        let mut table = ExceptionTable::new();
        table.add_call_site(CallSiteEntry::cleanup(0x00, 0x20, 0x100));

        let lsda = generate_lsda(&table);

        // No type table (no type_infos).
        assert_eq!(lsda[1], 0xFF); // TType = omit

        // Parse back the call site table.
        // Header: [0xFF, 0xFF, 0x01, <cs_len>]
        assert_eq!(lsda[2], 0x01); // uleb128 call-site encoding
        let cs_len = lsda[3] as usize;
        let cs_start = 4;
        let cs_data = &lsda[cs_start..cs_start + cs_len];

        // Call site: region_start, region_length, landing_pad, action — all
        // ULEB128. The chosen values each fit in a single byte.
        let (region_start, n0) = decode_test_uleb128(cs_data);
        let (region_length, n1) = decode_test_uleb128(&cs_data[n0..]);
        let (landing_pad, n2) = decode_test_uleb128(&cs_data[n0 + n1..]);
        let (action_idx, _n3) = decode_test_uleb128(&cs_data[n0 + n1 + n2..]);
        assert_eq!(region_start, 0);
        assert_eq!(region_length, 0x20);
        assert_eq!(landing_pad, 0x100);
        assert_eq!(action_idx, 0); // cleanup
    }

    #[test]
    fn test_lsda_with_type_table_offset() {
        // Verify the TType base offset is correctly computed when type infos exist.
        let mut table = ExceptionTable::new();
        table.add_call_site(CallSiteEntry::new(0, 8, 16, 1));
        table.add_action(ActionEntry::catch(1));
        table.add_type_info(TypeInfo::new(42));

        let lsda = generate_lsda(&table);

        // Header:
        // [0]: 0xFF (LPStart omit)
        // [1]: 0x9b (TType = indirect|pcrel|sdata4, C++ convention)
        // [2..]: ULEB128 TType base offset
        assert_eq!(lsda[0], 0xFF);
        assert_eq!(lsda[1], 0x9b);

        // Decode the TType base offset (ULEB128 starting at byte 2).
        let (ttype_offset, ttype_offset_len) = decode_test_uleb128(&lsda[2..]);

        // After the TType base offset field, the remaining data is:
        // call_site_enc(1) + cs_length(ULEB128) + cs_data + action_data
        //   + alignment padding + type_data
        // The TType base offset measures exactly from the byte after the base
        // field to the end of the (4-byte-aligned) type table — i.e. the rest
        // of the LSDA.
        let after_ttype_offset = 2 + ttype_offset_len;
        let remaining_len = lsda.len() - after_ttype_offset;

        // TType base offset should equal the total remaining bytes.
        assert_eq!(
            ttype_offset as usize, remaining_len,
            "TType base offset ({}) should equal remaining LSDA size ({})",
            ttype_offset, remaining_len
        );

        // The type table must be 4-byte aligned within the LSDA.
        let type_table_start = lsda.len() - 4; // single 4-byte type entry
        assert_eq!(
            type_table_start % 4,
            0,
            "type table must start on a 4-byte boundary"
        );
    }

    #[test]
    fn type_table_layout_remains_aligned_when_padding_grows_the_base_uleb() {
        // A one-pass calculation sees base 127 (one-byte ULEB), chooses two
        // bytes of padding, and thereby grows the final base to 129 (two-byte
        // ULEB), moving the type table off alignment. The final-layout search
        // instead finds the self-consistent one-byte pad / base-128 layout.
        assert_eq!(type_table_layout(123, 4), (1, 128));

        for pre_type_len in 115..=140 {
            let (pad, ttype_base) = type_table_layout(pre_type_len, 4);
            assert_eq!(ttype_base, pre_type_len + pad + 4);
            assert_eq!(
                (2 + uleb128_encoded_len(ttype_base as u64) + pre_type_len + pad) % 4,
                0,
                "misaligned layout at pre_type_len={pre_type_len}, pad={pad}, base={ttype_base}"
            );
        }

        // Exercise the same boundary through the complete serializer, not
        // only through the layout helper.
        let mut crossed_boundary = false;
        for call_site_count in 1..=64 {
            let mut table = ExceptionTable::new();
            for _ in 0..call_site_count {
                table.add_call_site(CallSiteEntry::no_landing_pad(0, 1));
            }
            table.add_type_info(TypeInfo::catch_all());
            let lsda = generate_lsda(&table);
            let (ttype_offset, field_len) = decode_test_uleb128(&lsda[2..]);
            if field_len > 1 {
                crossed_boundary = true;
                assert_eq!(2 + field_len + ttype_offset as usize, lsda.len());
                assert_eq!((lsda.len() - 4) % 4, 0);
                break;
            }
        }
        assert!(
            crossed_boundary,
            "test fixture never crossed a TType ULEB width boundary"
        );
    }

    #[test]
    fn test_lsda_roundtrip_structure() {
        // Build a complete exception table and verify LSDA structural integrity.
        let mut table = ExceptionTable::with_cxx_personality();
        table.add_call_site(CallSiteEntry::new(0, 12, 24, 1));
        table.add_call_site(CallSiteEntry::cleanup(12, 8, 36));
        table.add_action(ActionEntry::catch(1));
        table.add_type_info(TypeInfo::new(7));

        let lsda = generate_lsda(&table);

        // Basic structural checks.
        assert!(lsda.len() > 10, "LSDA too short: {} bytes", lsda.len());
        assert_eq!(lsda[0], 0xFF); // LPStart omit
        assert_ne!(lsda[1], 0xFF); // TType NOT omit (has type infos)

        // The type info (7) should appear somewhere in the LSDA as a 4-byte LE value.
        let type_bytes = 7u32.to_le_bytes();
        assert!(
            lsda.windows(4).any(|w| w == type_bytes),
            "Type info value 7 should appear in LSDA"
        );
    }

    #[test]
    fn test_call_site_table_encoding() {
        // Verify the raw call site table bytes.
        let call_sites = vec![CallSiteEntry::new(0x04, 0x08, 0x20, 1)];
        let data = emit_call_site_table(&call_sites, DwEhPe::UData4);

        // 3 udata4 fields + 1 ULEB128 action index.
        // region_start = 4, region_length = 8, landing_pad = 0x20, action = 1
        assert_eq!(u32::from_le_bytes(data[0..4].try_into().unwrap()), 4);
        assert_eq!(u32::from_le_bytes(data[4..8].try_into().unwrap()), 8);
        assert_eq!(u32::from_le_bytes(data[8..12].try_into().unwrap()), 0x20);
        assert_eq!(data[12], 1); // action index = 1 (ULEB128)
        assert_eq!(data.len(), 13);
    }

    #[test]
    fn test_empty_call_site_table() {
        let data = emit_call_site_table(&[], DwEhPe::UData4);
        assert!(data.is_empty());
    }

    #[test]
    fn test_empty_action_table() {
        let data = emit_action_table(&[]);
        assert!(data.is_empty());
    }

    #[test]
    fn test_empty_type_table() {
        let data = emit_type_table(&[]);
        assert!(data.is_empty());
    }

    #[test]
    fn test_action_table_single_entry() {
        let data = emit_action_table(&[ActionEntry::catch(2)]);
        // SLEB128(2) = [0x02], SLEB128(0) = [0x00]
        assert_eq!(data, vec![0x02, 0x00]);
    }

    #[test]
    fn test_action_table_negative_filter() {
        // Exception specification filter (negative type_filter).
        let action = ActionEntry {
            type_filter: -1,
            next_action_offset: 0,
        };
        let data = emit_action_table(&[action]);
        // SLEB128(-1) = [0x7F], SLEB128(0) = [0x00]
        assert_eq!(data, vec![0x7F, 0x00]);
    }

    #[test]
    fn test_type_table_single_entry() {
        let data = emit_type_table(&[TypeInfo::new(42)]);
        // Single entry: 42 as u32 LE.
        assert_eq!(data, 42u32.to_le_bytes().to_vec());
    }

    #[test]
    fn test_multiple_call_sites_byte_layout() {
        let call_sites = vec![
            CallSiteEntry::new(0, 4, 8, 0),
            CallSiteEntry::new(4, 4, 0, 0),
        ];
        let data = emit_call_site_table(&call_sites, DwEhPe::UData4);

        // Entry 1: 0(4) + 4(4) + 8(4) + ULEB(0) = 13 bytes
        // Entry 2: 4(4) + 4(4) + 0(4) + ULEB(0) = 13 bytes
        assert_eq!(data.len(), 26);

        // Verify entry 2 region_start = 4.
        assert_eq!(u32::from_le_bytes(data[13..17].try_into().unwrap()), 4);
        // Verify entry 2 landing_pad = 0.
        assert_eq!(u32::from_le_bytes(data[21..25].try_into().unwrap()), 0);
    }

    // --- Helper: ULEB128 decoder for testing ---

    /// Decode a ULEB128 value from a byte slice. Returns (value, bytes_consumed).
    fn decode_test_uleb128(data: &[u8]) -> (u64, usize) {
        let mut result: u64 = 0;
        let mut shift = 0;
        for (i, &byte) in data.iter().enumerate() {
            result |= ((byte & 0x7F) as u64) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                return (result, i + 1);
            }
        }
        (result, data.len())
    }

    // =======================================================================
    // build_exception_table_from_pads tests
    // =======================================================================

    #[test]
    fn test_from_pads_cleanup_only() {
        let table = build_exception_table_from_pads(
            "__rust_eh_personality",
            &[LandingPadDesc::cleanup(0x100)],
            &[(0x00, 0x20, 0x100)],
        )
        .unwrap();

        assert_eq!(table.personality.as_deref(), Some("rust_eh_personality"));
        assert_eq!(table.call_sites.len(), 1);
        assert_eq!(table.call_sites[0].landing_pad, 0x100);
        assert_eq!(table.call_sites[0].action_idx, 0); // cleanup = action 0
        assert!(table.actions.is_empty()); // no action chain for cleanup-only
        assert!(table.type_infos.is_empty());

        let lsda = generate_lsda(&table);
        assert!(lsda.len() > 4);
    }

    #[test]
    fn from_pads_typed_catch_fails_without_typeinfo_relocation_authority() {
        let error = build_exception_table_from_pads(
            "__gxx_personality_v0",
            &[LandingPadDesc::catch_typed(0x50, 1)],
            &[(0x10, 0x08, 0x50)],
        )
        .unwrap_err();
        assert_eq!(
            error,
            ExceptionTableBuildError::TypedCatchRelocationUnsupported {
                offset: 0x50,
                type_index: 1,
            }
        );
    }

    #[test]
    fn test_from_pads_catch_all() {
        let table = build_exception_table_from_pads(
            "__gxx_personality_v0",
            &[LandingPadDesc::catch_all(0x40)],
            &[(0x00, 0x10, 0x40)],
        )
        .unwrap();

        assert_eq!(table.call_sites.len(), 1);
        assert_ne!(table.call_sites[0].action_idx, 0); // non-zero = has action
        assert_eq!(table.actions.len(), 1);
        // Catch-all is encoded as a POSITIVE type-filter pointing at a NULL
        // type-table slot — NOT type-filter 0 (which would be a cleanup, so the
        // personality would never catch and the program would terminate).
        assert_ne!(
            table.actions[0].type_filter, 0,
            "catch-all must use a positive type-filter (NULL slot), not cleanup"
        );
        assert_eq!(table.type_infos.len(), 1);
        assert_eq!(
            table.type_infos[0].type_info_index, 0,
            "catch-all type-table slot must be NULL"
        );
        assert_eq!(
            table.actions[0].type_filter as u32,
            table.type_infos.len() as u32,
            "type-filter must index the (1-based) NULL catch-all slot"
        );
    }

    #[test]
    fn test_from_pads_catch_and_cleanup() {
        let table = build_exception_table_from_pads(
            "__gxx_personality_v0",
            &[LandingPadDesc::catch_and_cleanup(0x60, 0)],
            &[(0x00, 0x10, 0x60)],
        )
        .unwrap();

        // Should have catch action + cleanup action chained.
        assert_eq!(table.actions.len(), 2);
        assert_eq!(table.actions[0].type_filter, 1); // catch-all NULL slot
        assert_eq!(table.actions[0].next_action_offset, 1); // displacement-field -> cleanup
        assert_eq!(table.actions[1].type_filter, 0); // cleanup
        assert_eq!(table.actions[1].next_action_offset, 0); // end
        assert_eq!(emit_action_table(&table.actions), vec![1, 1, 0, 0]);
    }

    #[test]
    fn test_from_pads_multiple_landing_pads() {
        let table = build_exception_table_from_pads(
            "__gxx_personality_v0",
            &[
                LandingPadDesc::catch_all(0x80),
                LandingPadDesc::cleanup(0xC0),
            ],
            &[
                (0x00, 0x10, 0x80),
                (0x10, 0x08, 0xC0),
                (0x18, 0x04, 0), // no landing pad
            ],
        )
        .unwrap();

        assert_eq!(table.call_sites.len(), 3);
        // First call site -> catch-all landing pad
        assert_ne!(table.call_sites[0].action_idx, 0);
        // Second call site -> cleanup landing pad
        assert_eq!(table.call_sites[1].action_idx, 0);
        // Third call site -> no landing pad
        assert_eq!(table.call_sites[2].landing_pad, 0);
    }

    #[test]
    fn test_from_pads_end_to_end_lsda() {
        // Build a complete C++-style exception table and generate LSDA.
        let table = build_exception_table_from_pads(
            "__gxx_personality_v0",
            &[
                LandingPadDesc::catch_all(0x50),
                LandingPadDesc::catch_all(0x80),
            ],
            &[(0x00, 0x10, 0x50), (0x10, 0x08, 0x80)],
        )
        .unwrap();

        let lsda = generate_lsda(&table);
        assert!(lsda.len() > 10);
        assert_eq!(lsda[0], 0xFF); // LPStart omit
        assert_ne!(lsda[1], 0xFF); // TType present

        // Both catch-all pads share one NULL type-table slot.
        assert_eq!(table.type_infos.len(), 1);
        assert_eq!(table.call_sites[0].action_idx, 1);
        assert_eq!(
            table.call_sites[1].action_idx, 3,
            "the second chain starts at byte 2 + the LSDA's one-based bias"
        );
    }

    #[test]
    fn from_pads_uses_encoded_byte_offsets_across_action_chains() {
        let table = build_exception_table_from_pads(
            "__gxx_personality_v0",
            &[
                LandingPadDesc::catch_and_cleanup(0x80, 0),
                LandingPadDesc::catch_all(0xc0),
            ],
            &[(0, 4, 0x80), (4, 4, 0xc0)],
        )
        .unwrap();

        // The first catch-all+cleanup chain is exactly four encoded bytes:
        // [filter=1,next=1, filter=0,next=0]. Therefore the next pad's chain
        // starts at byte offset 4 plus the LSDA's one-based action bias.
        assert_eq!(table.call_sites[0].action_idx, 1);
        assert_eq!(table.call_sites[1].action_idx, 5);
        assert_eq!(emit_action_table(&table.actions), vec![1, 1, 0, 0, 1, 0]);
    }

    #[test]
    fn from_pads_rejects_malformed_references_ranges_and_descriptors() {
        assert!(matches!(
            build_exception_table_from_pads("", &[], &[(0, 4, 0)]),
            Err(ExceptionTableBuildError::InvalidPersonality(
                PersonalitySymbolError::Empty
            ))
        ));
        assert!(matches!(
            build_exception_table_from_pads(
                "rust_eh_personality",
                &[LandingPadDesc::cleanup(0)],
                &[(0, 4, 0)]
            ),
            Err(ExceptionTableBuildError::ZeroLandingPadOffset { .. })
        ));
        assert!(matches!(
            build_exception_table_from_pads(
                "rust_eh_personality",
                &[LandingPadDesc::cleanup(8), LandingPadDesc::catch_all(8)],
                &[(0, 4, 8)]
            ),
            Err(ExceptionTableBuildError::DuplicateLandingPadOffset { offset: 8 })
        ));
        assert!(matches!(
            build_exception_table_from_pads(
                "rust_eh_personality",
                &[LandingPadDesc {
                    landing_pad_offset: 8,
                    catch_type_indices: vec![],
                    is_cleanup: false,
                }],
                &[(0, 4, 8)]
            ),
            Err(ExceptionTableBuildError::EmptyLandingPad { offset: 8 })
        ));
        assert!(matches!(
            build_exception_table_from_pads(
                "rust_eh_personality",
                &[LandingPadDesc {
                    landing_pad_offset: 8,
                    catch_type_indices: vec![0, 0],
                    is_cleanup: false,
                }],
                &[(0, 4, 8)]
            ),
            Err(ExceptionTableBuildError::DuplicateCatchType {
                offset: 8,
                type_index: 0
            })
        ));
        assert!(matches!(
            build_exception_table_from_pads(
                "rust_eh_personality",
                &[LandingPadDesc::cleanup(8)],
                &[(0, 4, 12)]
            ),
            Err(ExceptionTableBuildError::UnknownLandingPadOffset { offset: 12, .. })
        ));
        assert!(matches!(
            build_exception_table_from_pads(
                "rust_eh_personality",
                &[LandingPadDesc::cleanup(8)],
                &[(0, 4, 0)]
            ),
            Err(ExceptionTableBuildError::OrphanLandingPadOffset { offset: 8 })
        ));
        assert!(matches!(
            build_exception_table_from_pads("rust_eh_personality", &[], &[(0, 0, 0)]),
            Err(ExceptionTableBuildError::EmptyCallSite { .. })
        ));
        assert!(matches!(
            build_exception_table_from_pads("rust_eh_personality", &[], &[(u32::MAX, 2, 0)]),
            Err(ExceptionTableBuildError::CallSiteRangeOverflow { .. })
        ));
        assert!(matches!(
            build_exception_table_from_pads("rust_eh_personality", &[], &[(4, 4, 0), (6, 4, 0)]),
            Err(ExceptionTableBuildError::OverlappingOrUnsortedCallSites { .. })
        ));
    }

    #[test]
    fn test_landing_pad_desc_constructors() {
        let ca = LandingPadDesc::catch_all(0x40);
        assert_eq!(ca.landing_pad_offset, 0x40);
        assert_eq!(ca.catch_type_indices, vec![0]);
        assert!(!ca.is_cleanup);

        let ct = LandingPadDesc::catch_typed(0x50, 3);
        assert_eq!(ct.catch_type_indices, vec![3]);
        assert!(!ct.is_cleanup);

        let cl = LandingPadDesc::cleanup(0x60);
        assert!(cl.catch_type_indices.is_empty());
        assert!(cl.is_cleanup);

        let cc = LandingPadDesc::catch_and_cleanup(0x70, 5);
        assert_eq!(cc.catch_type_indices, vec![5]);
        assert!(cc.is_cleanup);
    }
}
