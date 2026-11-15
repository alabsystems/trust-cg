// trust-cg-codegen/macho/codesign.rs - Independent embedded ad-hoc code-signature verifier
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Independent reader and verifier for the embedded ad-hoc code signature of
//! a thin 64-bit Mach-O image.
//!
//! Apple Silicon kernels refuse to run arm64 code without a valid code
//! signature, so every linked arm64 Darwin executable and dylib must carry
//! `LC_CODE_SIGNATURE` naming a signature SuperBlob whose CodeDirectory hashes
//! every page of the file before the signature. [`verify_ad_hoc_signature`]
//! re-reads a finished image from its bytes alone, with its own constants and
//! parser rather than the standalone linker's layout state, and accepts it only
//! when all of the following hold:
//!
//! - the image is a thin little-endian `MH_MAGIC_64` Mach-O whose load
//!   commands lie inside `sizeofcmds`, and it has exactly one
//!   `LC_CODE_SIGNATURE`, whose payload lies inside `__LINKEDIT` and ends the
//!   file;
//! - the payload is a well-formed `CSMAGIC_EMBEDDED_SIGNATURE` SuperBlob whose
//!   blob index names each slot once, with every blob inside the SuperBlob;
//! - slot 0 holds a CodeDirectory, and it and every alternate CodeDirectory use
//!   SHA-256, 4 KiB or 16 KiB code pages, no scatter vector, no encryption and
//!   no linkage fields, carry `CS_ADHOC`, cover exactly the bytes before the
//!   signature through the 32-bit `codeLimit` (a nonzero `codeLimit64` must
//!   agree with it), and hold one matching SHA-256 hash per page. The page-size
//!   and code-limit rules are stricter than `codesign --verify`, which accepts
//!   0, 8, 32 and 64 KiB pages and a `codeLimit64` that disagrees with
//!   `codeLimit`: the macOS 26.6 arm64 kernel kills such images at exec
//!   (measured in `tests/macho_code_signature_native.rs`), so an image whose
//!   signed prefix exceeds 4 GiB is refused;
//! - every special slot either binds a blob present in the SuperBlob (whose
//!   hash matches) or is zero; bound external data (an `Info.plist` or sealed
//!   resources) is refused, and every special blob must be bound;
//! - the CodeDirectory executable segment starts at the `__TEXT` segment's
//!   file offset and lies inside its file range, and only an `MH_EXECUTE`
//!   image is marked as the main binary. Signers differ on its limit: this
//!   repository's standalone linker and `codesign` record the `__TEXT` file
//!   size, while the Xcode 27 ld64 records the `__text` section size (both
//!   measured on macOS 26.6), so containment rather than equality is checked;
//! - any CMS blob is the empty wrapper of an ad-hoc signature.
//!
//! Certificate (CMS) signatures, SHA-1 and other hash types, detached
//! signatures, universal (fat) files and bundles are refused by name, never
//! accepted unverified. The verifier establishes byte-level consistency of the
//! signature with the image. Whether the kernel runs the image is also policy
//! (the hardened runtime, library validation, entitlements, launch
//! constraints and notarization), which this reader does not decide.

use sha2::{Digest, Sha256};
use thiserror::Error;

/// `mach_header_64` magic (little-endian).
const MH_MAGIC_64: u32 = 0xFEED_FACF;
/// `LC_SEGMENT_64` load command.
const LC_SEGMENT_64: u32 = 0x19;
/// `LC_CODE_SIGNATURE` load command.
const LC_CODE_SIGNATURE: u32 = 0x1D;

/// `MH_EXECUTE` file type.
pub const MH_EXECUTE: u32 = 0x2;

/// Embedded signature SuperBlob magic.
pub const CSMAGIC_EMBEDDED_SIGNATURE: u32 = 0xFADE_0CC0;
/// CodeDirectory blob magic.
pub const CSMAGIC_CODEDIRECTORY: u32 = 0xFADE_0C02;
/// Internal requirements blob magic.
pub const CSMAGIC_REQUIREMENTS: u32 = 0xFADE_0C01;
/// XML entitlements blob magic.
pub const CSMAGIC_EMBEDDED_ENTITLEMENTS: u32 = 0xFADE_7171;
/// DER entitlements blob magic.
pub const CSMAGIC_EMBEDDED_DER_ENTITLEMENTS: u32 = 0xFADE_7172;
/// CMS signature wrapper blob magic.
pub const CSMAGIC_BLOBWRAPPER: u32 = 0xFADE_0B01;

/// SuperBlob slot of the primary CodeDirectory.
pub const CSSLOT_CODEDIRECTORY: u32 = 0;
/// Special slot binding an external `Info.plist`.
pub const CSSLOT_INFOSLOT: u32 = 1;
/// Special slot binding the internal requirements blob.
pub const CSSLOT_REQUIREMENTS: u32 = 2;
/// Special slot binding external sealed resources.
pub const CSSLOT_RESOURCEDIR: u32 = 3;
/// Special slot binding the XML entitlements blob.
pub const CSSLOT_ENTITLEMENTS: u32 = 5;
/// Special slot binding the DER entitlements blob.
pub const CSSLOT_DER_ENTITLEMENTS: u32 = 7;
/// First SuperBlob slot of an alternate CodeDirectory.
pub const CSSLOT_ALTERNATE_CODEDIRECTORIES: u32 = 0x1000;
/// Number of alternate CodeDirectory slots the format reserves.
pub const CSSLOT_ALTERNATE_CODEDIRECTORY_MAX: u32 = 5;
/// SuperBlob slot of the CMS signature wrapper.
pub const CSSLOT_SIGNATURESLOT: u32 = 0x1_0000;

/// CodeDirectory flag: ad-hoc signed (no certificate chain).
pub const CS_ADHOC: u32 = 0x0000_0002;
/// CodeDirectory flag: hardened runtime requested.
pub const CS_RUNTIME: u32 = 0x0001_0000;
/// CodeDirectory flag: signed automatically by the linker.
pub const CS_LINKER_SIGNED: u32 = 0x0002_0000;
/// Executable-segment flag marking the main binary.
pub const CS_EXECSEG_MAIN_BINARY: u64 = 0x1;

/// CodeDirectory hash type: SHA-256.
pub const CS_HASHTYPE_SHA256: u8 = 2;
const SHA256_LEN: usize = 32;

/// Oldest CodeDirectory version the kernel accepts.
const CS_SUPPORTSNONE: u32 = 0x2_0001;
const CS_SUPPORTSSCATTER: u32 = 0x2_0100;
const CS_SUPPORTSTEAMID: u32 = 0x2_0200;
const CS_SUPPORTSCODELIMIT64: u32 = 0x2_0300;
const CS_SUPPORTSEXECSEG: u32 = 0x2_0400;
const CS_SUPPORTSRUNTIME: u32 = 0x2_0500;
const CS_SUPPORTSLINKAGE: u32 = 0x2_0600;

/// Header bytes of a mach_header_64.
const MACH_HEADER_64_SIZE: usize = 32;
/// Size of a linkedit_data_command.
const LINKEDIT_DATA_COMMAND_SIZE: u32 = 16;
/// Page-size exponents the arm64 kernel runs (4 KiB and 16 KiB). The format
/// also admits `0` (one page spanning the whole code limit) and other powers
/// of two, which `codesign` writes on request, but the macOS 26.6 arm64 kernel
/// kills such images at exec.
const PAGE_SHIFTS: [u8; 2] = [12, 14];

/// One byte range an image read needed.
fn range_error(context: &'static str, start: u64, end: u64, len: usize) -> CodeSignatureError {
    CodeSignatureError::Truncated {
        context,
        start,
        end,
        len: len as u64,
    }
}

/// Why an image's embedded code signature was refused.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum CodeSignatureError {
    /// A structure extends beyond the bytes that contain it.
    #[error("{context} needs bytes {start}..{end} but only {len} are available")]
    Truncated {
        context: &'static str,
        start: u64,
        end: u64,
        len: u64,
    },
    /// The image is not a thin little-endian 64-bit Mach-O.
    #[error("not a thin little-endian 64-bit Mach-O image (magic {magic:#010x})")]
    NotMachO64 { magic: u32 },
    /// A load command is malformed.
    #[error("malformed load command at offset {offset}: {detail}")]
    MalformedLoadCommand { offset: u64, detail: String },
    /// The image carries no `LC_CODE_SIGNATURE`.
    #[error("the image has no LC_CODE_SIGNATURE: it is unsigned")]
    Unsigned,
    /// More than one `LC_CODE_SIGNATURE`.
    #[error("the image has {count} LC_CODE_SIGNATURE commands; exactly one is required")]
    DuplicateSignatureCommand { count: usize },
    /// The signature payload is not the final part of `__LINKEDIT`.
    #[error(
        "LC_CODE_SIGNATURE payload {offset}..{end} must lie inside __LINKEDIT and end the \
         {image_len}-byte image: {detail}"
    )]
    SignaturePlacement {
        offset: u64,
        end: u64,
        image_len: u64,
        detail: &'static str,
    },
    /// The SuperBlob or its index is malformed.
    #[error("malformed signature SuperBlob: {detail}")]
    MalformedSuperBlob { detail: String },
    /// A SuperBlob slot this verifier does not know.
    #[error("signature SuperBlob slot {slot:#x} is not a supported ad-hoc signature component")]
    UnsupportedBlob { slot: u32 },
    /// Slot 0 holds no CodeDirectory.
    #[error("the signature has no CodeDirectory in slot 0")]
    MissingCodeDirectory,
    /// A CodeDirectory is malformed.
    #[error("CodeDirectory in slot {slot:#x} is malformed: {detail}")]
    MalformedCodeDirectory { slot: u32, detail: String },
    /// A CodeDirectory version outside the supported range.
    #[error("CodeDirectory in slot {slot:#x} has unsupported version {version:#x}")]
    UnsupportedVersion { slot: u32, version: u32 },
    /// A hash type other than SHA-256.
    #[error(
        "CodeDirectory in slot {slot:#x} uses hash type {hash_type} with {hash_size}-byte hashes; \
         only SHA-256 is verified"
    )]
    UnsupportedHashType {
        slot: u32,
        hash_type: u8,
        hash_size: u8,
    },
    /// A page size outside the supported range.
    #[error("CodeDirectory in slot {slot:#x} uses unsupported page-size exponent {shift}")]
    UnsupportedPageSize { slot: u32, shift: u8 },
    /// A CodeDirectory feature this verifier does not check.
    #[error("CodeDirectory in slot {slot:#x} uses {feature}, which is not verified")]
    UnsupportedFeature { slot: u32, feature: &'static str },
    /// The CodeDirectory is not ad-hoc.
    #[error(
        "CodeDirectory in slot {slot:#x} has flags {flags:#x} without CS_ADHOC; only ad-hoc \
         signatures are verified"
    )]
    NotAdHoc { slot: u32, flags: u32 },
    /// The CodeDirectory does not cover exactly the bytes before the signature.
    #[error(
        "CodeDirectory in slot {slot:#x} covers {code_limit} bytes but the signature starts at \
         byte {signature_offset}"
    )]
    CodeLimitMismatch {
        slot: u32,
        code_limit: u64,
        signature_offset: u64,
    },
    /// The number of code slots does not match the covered pages.
    #[error(
        "CodeDirectory in slot {slot:#x} has {actual} code slots; {expected} pages need hashes"
    )]
    CodeSlotCountMismatch {
        slot: u32,
        expected: u64,
        actual: u32,
    },
    /// A code page hash does not match the image.
    #[error("code page {page} does not match its hash in CodeDirectory slot {slot:#x}")]
    CodePageHashMismatch { slot: u32, page: u32 },
    /// A special slot hash does not match its blob.
    #[error("special slot {special_slot} does not match its hash in CodeDirectory slot {slot:#x}")]
    SpecialSlotHashMismatch { slot: u32, special_slot: u32 },
    /// A special slot binds data outside the image.
    #[error(
        "special slot {special_slot} of CodeDirectory slot {slot:#x} binds external data \
         (an Info.plist or sealed resources), which is not verified"
    )]
    UnsupportedExternalSpecialSlot { slot: u32, special_slot: u32 },
    /// A special blob that no CodeDirectory binds.
    #[error("signature blob in slot {blob_slot} is not bound by CodeDirectory slot {slot:#x}")]
    UnboundBlob { slot: u32, blob_slot: u32 },
    /// The executable segment leaves `__TEXT` or disagrees with the file type.
    #[error(
        "CodeDirectory in slot {slot:#x} declares executable segment {base}+{limit} with flags \
         {flags:#x}, outside __TEXT {text_offset}+{text_size} or wrong for file type {filetype:#x}"
    )]
    ExecSegmentMismatch {
        slot: u32,
        base: u64,
        limit: u64,
        flags: u64,
        text_offset: u64,
        text_size: u64,
        filetype: u32,
    },
    /// A CMS blob that is not the empty ad-hoc wrapper.
    #[error(
        "the signature carries a {length}-byte CMS blob; certificate signatures are not verified"
    )]
    CmsSignaturePresent { length: u32 },
}

/// The executable-segment fields of a CodeDirectory (version `0x20400`+).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExecSegment {
    /// File offset of the executable segment.
    pub base: u64,
    /// File size of the executable segment.
    pub limit: u64,
    /// `CS_EXECSEG_*` flags.
    pub flags: u64,
}

/// One verified CodeDirectory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeDirectoryInfo {
    /// SuperBlob slot holding it (`0` or an alternate slot).
    pub slot: u32,
    /// CodeDirectory version.
    pub version: u32,
    /// `CS_*` CodeDirectory flags.
    pub flags: u32,
    /// Hash type (always [`CS_HASHTYPE_SHA256`] once verified).
    pub hash_type: u8,
    /// Code page size in bytes (4096 or 16384).
    pub page_size: u64,
    /// Number of bytes the code slots cover.
    pub code_limit: u64,
    /// Number of code slots.
    pub code_slots: u32,
    /// Number of special slots.
    pub special_slots: u32,
    /// Signing identifier.
    pub identifier: String,
    /// Team identifier, when present.
    pub team_identifier: Option<String>,
    /// Executable-segment fields, when the version carries them.
    pub exec_segment: Option<ExecSegment>,
    /// Hardened-runtime SDK version, when the version carries it.
    pub runtime_version: Option<u32>,
}

impl CodeDirectoryInfo {
    /// Whether the linker produced this signature.
    pub fn is_linker_signed(&self) -> bool {
        self.flags & CS_LINKER_SIGNED != 0
    }

    /// Whether the signature requests the hardened runtime.
    pub fn has_hardened_runtime(&self) -> bool {
        self.flags & CS_RUNTIME != 0
    }
}

/// A verified embedded ad-hoc signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdHocSignature {
    /// Mach-O file type of the signed image.
    pub filetype: u32,
    /// Mach-O CPU type of the signed image.
    pub cputype: u32,
    /// File offset of the signature payload (the code limit).
    pub signature_offset: u64,
    /// Size `LC_CODE_SIGNATURE` reserves for the payload.
    pub signature_size: u32,
    /// The primary CodeDirectory (slot 0).
    pub code_directory: CodeDirectoryInfo,
    /// Alternate CodeDirectories, in slot order.
    pub alternate_code_directories: Vec<CodeDirectoryInfo>,
    /// Special slots bound to a blob whose hash matched, ascending.
    pub bound_special_slots: Vec<u32>,
    /// The XML entitlements the signature binds, when present.
    pub entitlements_xml: Option<String>,
    /// Whether the signature binds DER entitlements.
    pub has_der_entitlements: bool,
    /// Whether the signature carries the empty ad-hoc CMS wrapper.
    pub has_empty_cms_wrapper: bool,
}

#[derive(Debug, Clone, Copy)]
struct Segment {
    fileoff: u64,
    filesize: u64,
}

#[derive(Debug, Clone, Copy)]
struct Blob {
    slot: u32,
    /// Offset of the blob within the image.
    offset: usize,
    /// Byte length from the blob header.
    length: usize,
    magic: u32,
}

fn slice<'a>(
    bytes: &'a [u8],
    start: usize,
    len: usize,
    context: &'static str,
) -> Result<&'a [u8], CodeSignatureError> {
    let end = start
        .checked_add(len)
        .ok_or_else(|| range_error(context, start as u64, u64::MAX, bytes.len()))?;
    bytes
        .get(start..end)
        .ok_or_else(|| range_error(context, start as u64, end as u64, bytes.len()))
}

fn le_u32(bytes: &[u8], at: usize, context: &'static str) -> Result<u32, CodeSignatureError> {
    let raw = slice(bytes, at, 4, context)?;
    Ok(u32::from_le_bytes([raw[0], raw[1], raw[2], raw[3]]))
}

fn le_u64(bytes: &[u8], at: usize, context: &'static str) -> Result<u64, CodeSignatureError> {
    let raw = slice(bytes, at, 8, context)?;
    let mut word = [0u8; 8];
    word.copy_from_slice(raw);
    Ok(u64::from_le_bytes(word))
}

fn be_u32(bytes: &[u8], at: usize, context: &'static str) -> Result<u32, CodeSignatureError> {
    let raw = slice(bytes, at, 4, context)?;
    Ok(u32::from_be_bytes([raw[0], raw[1], raw[2], raw[3]]))
}

fn be_u64(bytes: &[u8], at: usize, context: &'static str) -> Result<u64, CodeSignatureError> {
    let raw = slice(bytes, at, 8, context)?;
    let mut word = [0u8; 8];
    word.copy_from_slice(raw);
    Ok(u64::from_be_bytes(word))
}

fn sha256(bytes: &[u8]) -> [u8; SHA256_LEN] {
    Sha256::digest(bytes).into()
}

/// The load-command facts the signature is checked against.
struct MachOFacts {
    cputype: u32,
    filetype: u32,
    text: Option<Segment>,
    linkedit: Option<Segment>,
    signature: Option<(u64, u32)>,
}

fn read_macho_facts(image: &[u8]) -> Result<MachOFacts, CodeSignatureError> {
    let magic = le_u32(image, 0, "mach_header_64")?;
    if magic != MH_MAGIC_64 {
        return Err(CodeSignatureError::NotMachO64 { magic });
    }
    slice(image, 0, MACH_HEADER_64_SIZE, "mach_header_64")?;
    let cputype = le_u32(image, 4, "mach_header_64")?;
    let filetype = le_u32(image, 12, "mach_header_64")?;
    let ncmds = le_u32(image, 16, "mach_header_64")?;
    let sizeofcmds = le_u32(image, 20, "mach_header_64")? as usize;
    slice(image, MACH_HEADER_64_SIZE, sizeofcmds, "load commands")?;
    let commands_end = MACH_HEADER_64_SIZE + sizeofcmds;

    let mut facts = MachOFacts {
        cputype,
        filetype,
        text: None,
        linkedit: None,
        signature: None,
    };
    let mut signature_commands = 0usize;
    let mut offset = MACH_HEADER_64_SIZE;
    for _ in 0..ncmds {
        let at = offset as u64;
        let malformed =
            move |detail: String| CodeSignatureError::MalformedLoadCommand { offset: at, detail };
        if offset + 8 > commands_end {
            return Err(malformed("load command header exceeds sizeofcmds".into()));
        }
        let cmd = le_u32(image, offset, "load command")?;
        let cmdsize = le_u32(image, offset + 4, "load command")? as usize;
        if cmdsize < 8 || !cmdsize.is_multiple_of(8) || offset + cmdsize > commands_end {
            return Err(malformed(format!(
                "cmdsize {cmdsize} is not a multiple of 8 inside sizeofcmds"
            )));
        }
        match cmd {
            LC_SEGMENT_64 => {
                if cmdsize < 72 {
                    return Err(malformed(format!("LC_SEGMENT_64 cmdsize {cmdsize} < 72")));
                }
                let name = slice(image, offset + 8, 16, "segment name")?;
                let fileoff = le_u64(image, offset + 40, "LC_SEGMENT_64")?;
                let filesize = le_u64(image, offset + 48, "LC_SEGMENT_64")?;
                let segment = Segment { fileoff, filesize };
                let slot = if name == b"__TEXT\0\0\0\0\0\0\0\0\0\0" {
                    Some(&mut facts.text)
                } else if name == b"__LINKEDIT\0\0\0\0\0\0" {
                    Some(&mut facts.linkedit)
                } else {
                    None
                };
                if let Some(slot) = slot {
                    if slot.is_some() {
                        return Err(malformed("duplicate __TEXT or __LINKEDIT segment".into()));
                    }
                    *slot = Some(segment);
                }
            }
            LC_CODE_SIGNATURE => {
                if cmdsize as u32 != LINKEDIT_DATA_COMMAND_SIZE {
                    return Err(malformed(format!(
                        "LC_CODE_SIGNATURE cmdsize {cmdsize} is not {LINKEDIT_DATA_COMMAND_SIZE}"
                    )));
                }
                signature_commands += 1;
                let dataoff = le_u32(image, offset + 8, "LC_CODE_SIGNATURE")?;
                let datasize = le_u32(image, offset + 12, "LC_CODE_SIGNATURE")?;
                facts.signature = Some((u64::from(dataoff), datasize));
            }
            _ => {}
        }
        offset += cmdsize;
    }
    if offset != commands_end {
        return Err(CodeSignatureError::MalformedLoadCommand {
            offset: offset as u64,
            detail: format!(
                "{ncmds} load commands end at {offset}, sizeofcmds ends at {commands_end}"
            ),
        });
    }
    match signature_commands {
        0 => Err(CodeSignatureError::Unsigned),
        1 => Ok(facts),
        count => Err(CodeSignatureError::DuplicateSignatureCommand { count }),
    }
}

/// Parse the SuperBlob at `start..start + size` and return its blobs.
fn read_super_blob(
    image: &[u8],
    start: usize,
    size: usize,
) -> Result<Vec<Blob>, CodeSignatureError> {
    let malformed = |detail: String| CodeSignatureError::MalformedSuperBlob { detail };
    let magic = be_u32(image, start, "SuperBlob header")?;
    if magic != CSMAGIC_EMBEDDED_SIGNATURE {
        return Err(malformed(format!(
            "magic {magic:#010x} is not CSMAGIC_EMBEDDED_SIGNATURE"
        )));
    }
    let length = be_u32(image, start + 4, "SuperBlob header")? as usize;
    let count = be_u32(image, start + 8, "SuperBlob header")? as usize;
    if length > size {
        return Err(malformed(format!(
            "length {length} exceeds the {size} bytes LC_CODE_SIGNATURE reserves"
        )));
    }
    let index_end = count
        .checked_mul(8)
        .and_then(|bytes| bytes.checked_add(12))
        .filter(|&end| end <= length)
        .ok_or_else(|| malformed(format!("{count} index entries exceed length {length}")))?;
    let mut blobs: Vec<Blob> = Vec::with_capacity(count);
    for entry in 0..count {
        let slot = be_u32(image, start + 12 + entry * 8, "SuperBlob index")?;
        let blob_offset = be_u32(image, start + 16 + entry * 8, "SuperBlob index")? as usize;
        if blobs.iter().any(|blob| blob.slot == slot) {
            return Err(malformed(format!("slot {slot:#x} appears twice")));
        }
        if blob_offset < index_end || blob_offset.saturating_add(8) > length {
            return Err(malformed(format!(
                "slot {slot:#x} blob offset {blob_offset} is outside {index_end}..{length}"
            )));
        }
        let magic = be_u32(image, start + blob_offset, "signature blob header")?;
        let blob_length = be_u32(image, start + blob_offset + 4, "signature blob header")? as usize;
        if blob_length < 8 || blob_offset + blob_length > length {
            return Err(malformed(format!(
                "slot {slot:#x} blob length {blob_length} at {blob_offset} exceeds length {length}"
            )));
        }
        blobs.push(Blob {
            slot,
            offset: start + blob_offset,
            length: blob_length,
            magic,
        });
    }
    // Blobs must not overlap one another.
    let mut spans: Vec<(usize, usize)> = blobs
        .iter()
        .map(|blob| (blob.offset, blob.offset + blob.length))
        .collect();
    spans.sort_unstable();
    if spans.windows(2).any(|pair| pair[1].0 < pair[0].1) {
        return Err(malformed("signature blobs overlap".into()));
    }
    Ok(blobs)
}

/// Parse and verify one CodeDirectory blob against the image.
fn verify_code_directory(
    image: &[u8],
    blob: &Blob,
    blobs: &[Blob],
    facts: &MachOFacts,
    signature_offset: u64,
) -> Result<(CodeDirectoryInfo, Vec<u32>), CodeSignatureError> {
    let slot = blob.slot;
    let malformed = |detail: String| CodeSignatureError::MalformedCodeDirectory { slot, detail };
    let cd = slice(image, blob.offset, blob.length, "CodeDirectory")?;
    if blob.magic != CSMAGIC_CODEDIRECTORY {
        return Err(malformed(format!(
            "magic {:#010x} is not CSMAGIC_CODEDIRECTORY",
            blob.magic
        )));
    }
    let version = be_u32(cd, 8, "CodeDirectory header")?;
    if !(CS_SUPPORTSNONE..=CS_SUPPORTSLINKAGE).contains(&version) {
        return Err(CodeSignatureError::UnsupportedVersion { slot, version });
    }
    let header_size = if version >= CS_SUPPORTSLINKAGE {
        108
    } else if version >= CS_SUPPORTSRUNTIME {
        96
    } else if version >= CS_SUPPORTSEXECSEG {
        88
    } else if version >= CS_SUPPORTSCODELIMIT64 {
        64
    } else if version >= CS_SUPPORTSTEAMID {
        52
    } else if version >= CS_SUPPORTSSCATTER {
        48
    } else {
        44
    };
    if cd.len() < header_size {
        return Err(malformed(format!(
            "length {} is below the {header_size}-byte header of version {version:#x}",
            cd.len()
        )));
    }
    let flags = be_u32(cd, 12, "CodeDirectory header")?;
    let hash_offset = be_u32(cd, 16, "CodeDirectory header")? as usize;
    let ident_offset = be_u32(cd, 20, "CodeDirectory header")? as usize;
    let special_slots = be_u32(cd, 24, "CodeDirectory header")?;
    let code_slots = be_u32(cd, 28, "CodeDirectory header")?;
    let code_limit32 = be_u32(cd, 32, "CodeDirectory header")?;
    let hash_size = cd[36];
    let hash_type = cd[37];
    let page_shift = cd[39];
    if hash_type != CS_HASHTYPE_SHA256 || usize::from(hash_size) != SHA256_LEN {
        return Err(CodeSignatureError::UnsupportedHashType {
            slot,
            hash_type,
            hash_size,
        });
    }
    if !PAGE_SHIFTS.contains(&page_shift) {
        return Err(CodeSignatureError::UnsupportedPageSize {
            slot,
            shift: page_shift,
        });
    }
    if version >= CS_SUPPORTSSCATTER && be_u32(cd, 44, "CodeDirectory header")? != 0 {
        return Err(CodeSignatureError::UnsupportedFeature {
            slot,
            feature: "a scatter vector",
        });
    }
    let team_offset = if version >= CS_SUPPORTSTEAMID {
        be_u32(cd, 48, "CodeDirectory header")? as usize
    } else {
        0
    };
    let code_limit64 = if version >= CS_SUPPORTSCODELIMIT64 {
        be_u64(cd, 56, "CodeDirectory header")?
    } else {
        0
    };
    let exec_segment = if version >= CS_SUPPORTSEXECSEG {
        Some(ExecSegment {
            base: be_u64(cd, 64, "CodeDirectory header")?,
            limit: be_u64(cd, 72, "CodeDirectory header")?,
            flags: be_u64(cd, 80, "CodeDirectory header")?,
        })
    } else {
        None
    };
    let runtime_version = if version >= CS_SUPPORTSRUNTIME {
        if be_u32(cd, 92, "CodeDirectory header")? != 0 {
            return Err(CodeSignatureError::UnsupportedFeature {
                slot,
                feature: "pre-encryption hashes",
            });
        }
        Some(be_u32(cd, 88, "CodeDirectory header")?)
    } else {
        None
    };
    // Linkage hash type, application type/subtype, offset and size.
    if version >= CS_SUPPORTSLINKAGE
        && slice(cd, 96, 12, "CodeDirectory header")?
            .iter()
            .any(|&byte| byte != 0)
    {
        return Err(CodeSignatureError::UnsupportedFeature {
            slot,
            feature: "a linkage hash",
        });
    }
    if flags & CS_ADHOC == 0 {
        return Err(CodeSignatureError::NotAdHoc { slot, flags });
    }

    // Identifier and team identifier: NUL-terminated UTF-8 after the header.
    let c_string = |at: usize, what: &str| -> Result<String, CodeSignatureError> {
        if at < header_size || at >= cd.len() {
            return Err(malformed(format!(
                "{what} offset {at} is outside {header_size}..{}",
                cd.len()
            )));
        }
        let text = &cd[at..];
        let end = text
            .iter()
            .position(|&byte| byte == 0)
            .ok_or_else(|| malformed(format!("{what} is not NUL-terminated")))?;
        String::from_utf8(text[..end].to_vec())
            .map_err(|_| malformed(format!("{what} is not UTF-8")))
    };
    let identifier = c_string(ident_offset, "identifier")?;
    let team_identifier = if team_offset == 0 {
        None
    } else {
        Some(c_string(team_offset, "team identifier")?)
    };

    // Hash array bounds: special slots precede hash_offset, code slots follow.
    let special_bytes = (special_slots as usize).saturating_mul(SHA256_LEN);
    let code_bytes = (code_slots as usize).saturating_mul(SHA256_LEN);
    if hash_offset < header_size
        || hash_offset < special_bytes
        || hash_offset - special_bytes < header_size
        || hash_offset
            .checked_add(code_bytes)
            .is_none_or(|end| end > cd.len())
    {
        return Err(malformed(format!(
            "hash array {}..{} (with {special_slots} special slots) is outside {header_size}..{}",
            hash_offset.saturating_sub(special_bytes),
            hash_offset.saturating_add(code_bytes),
            cd.len()
        )));
    }

    // The code slots cover exactly the bytes before the signature. The kernel
    // judges the 32-bit codeLimit, so it must name the signature offset, and a
    // nonzero codeLimit64 must agree with it.
    let code_limit = u64::from(code_limit32);
    let disagreeing = if code_limit != signature_offset {
        Some(code_limit)
    } else if code_limit64 != 0 && code_limit64 != signature_offset {
        Some(code_limit64)
    } else {
        None
    };
    if let Some(claimed) = disagreeing {
        return Err(CodeSignatureError::CodeLimitMismatch {
            slot,
            code_limit: claimed,
            signature_offset,
        });
    }
    let page_size = 1u64 << page_shift;
    let expected_slots = code_limit.div_ceil(page_size);
    if u64::from(code_slots) != expected_slots {
        return Err(CodeSignatureError::CodeSlotCountMismatch {
            slot,
            expected: expected_slots,
            actual: code_slots,
        });
    }
    let covered = slice(image, 0, code_limit as usize, "signed code")?;
    for (page, chunk) in covered.chunks(page_size as usize).enumerate() {
        let at = hash_offset + page * SHA256_LEN;
        if cd[at..at + SHA256_LEN] != sha256(chunk) {
            return Err(CodeSignatureError::CodePageHashMismatch {
                slot,
                page: page as u32,
            });
        }
    }

    // Special slots: each binds its blob or is zero; external data is refused.
    let mut bound = Vec::new();
    for special_slot in 1..=special_slots {
        let at = hash_offset - special_slot as usize * SHA256_LEN;
        let stored = &cd[at..at + SHA256_LEN];
        match blobs
            .iter()
            .find(|candidate| candidate.slot == special_slot)
        {
            Some(bound_blob) => {
                let bytes = slice(image, bound_blob.offset, bound_blob.length, "special blob")?;
                if stored != sha256(bytes) {
                    return Err(CodeSignatureError::SpecialSlotHashMismatch { slot, special_slot });
                }
                bound.push(special_slot);
            }
            None if stored.iter().all(|&byte| byte == 0) => {}
            None if special_slot == CSSLOT_INFOSLOT || special_slot == CSSLOT_RESOURCEDIR => {
                return Err(CodeSignatureError::UnsupportedExternalSpecialSlot {
                    slot,
                    special_slot,
                });
            }
            None => {
                return Err(CodeSignatureError::SpecialSlotHashMismatch { slot, special_slot });
            }
        }
    }
    for blob in blobs {
        if (1..CSSLOT_ALTERNATE_CODEDIRECTORIES).contains(&blob.slot) && blob.slot > special_slots {
            return Err(CodeSignatureError::UnboundBlob {
                slot,
                blob_slot: blob.slot,
            });
        }
    }

    // The executable segment starts __TEXT and stays inside it; only a main
    // executable is marked as the main binary.
    if let Some(segment) = exec_segment {
        let text = facts.text.ok_or_else(|| {
            malformed("the image has no __TEXT segment for the executable-segment fields".into())
        })?;
        let main_binary = segment.flags & CS_EXECSEG_MAIN_BINARY != 0;
        if segment.base != text.fileoff
            || segment.limit > text.filesize
            || main_binary != (facts.filetype == MH_EXECUTE)
        {
            return Err(CodeSignatureError::ExecSegmentMismatch {
                slot,
                base: segment.base,
                limit: segment.limit,
                flags: segment.flags,
                text_offset: text.fileoff,
                text_size: text.filesize,
                filetype: facts.filetype,
            });
        }
    }

    Ok((
        CodeDirectoryInfo {
            slot,
            version,
            flags,
            hash_type,
            page_size,
            code_limit,
            code_slots,
            special_slots,
            identifier,
            team_identifier,
            exec_segment,
            runtime_version,
        },
        bound,
    ))
}

/// Verify the embedded ad-hoc code signature of a thin 64-bit Mach-O image.
///
/// Every check listed in the [module documentation](self) must pass; the
/// first failure is returned as a named [`CodeSignatureError`].
pub fn verify_ad_hoc_signature(image: &[u8]) -> Result<AdHocSignature, CodeSignatureError> {
    let facts = read_macho_facts(image)?;
    let (signature_offset, signature_size) = facts.signature.ok_or(CodeSignatureError::Unsigned)?;
    let end = signature_offset + u64::from(signature_size);
    let placement = |detail| CodeSignatureError::SignaturePlacement {
        offset: signature_offset,
        end,
        image_len: image.len() as u64,
        detail,
    };
    let linkedit = facts
        .linkedit
        .ok_or_else(|| placement("the image has no __LINKEDIT segment"))?;
    if signature_offset < linkedit.fileoff
        || linkedit
            .fileoff
            .checked_add(linkedit.filesize)
            .is_none_or(|linkedit_end| end > linkedit_end)
    {
        return Err(placement(
            "the payload is outside the __LINKEDIT file range",
        ));
    }
    if end != image.len() as u64 {
        return Err(placement(
            "bytes follow the signature, or the payload is truncated",
        ));
    }
    if !signature_offset.is_multiple_of(16) {
        return Err(placement("the payload is not 16-byte aligned"));
    }

    let blobs = read_super_blob(image, signature_offset as usize, signature_size as usize)?;
    let mut primary = None;
    let mut alternates = Vec::new();
    let mut bound_special_slots = Vec::new();
    let mut entitlements_xml = None;
    let mut has_der_entitlements = false;
    let mut has_empty_cms_wrapper = false;
    for blob in &blobs {
        match blob.slot {
            CSSLOT_CODEDIRECTORY => {
                primary = Some(verify_code_directory(
                    image,
                    blob,
                    &blobs,
                    &facts,
                    signature_offset,
                )?);
            }
            slot if (CSSLOT_ALTERNATE_CODEDIRECTORIES
                ..CSSLOT_ALTERNATE_CODEDIRECTORIES + CSSLOT_ALTERNATE_CODEDIRECTORY_MAX)
                .contains(&slot) =>
            {
                alternates
                    .push(verify_code_directory(image, blob, &blobs, &facts, signature_offset)?.0);
            }
            CSSLOT_SIGNATURESLOT => {
                if blob.magic != CSMAGIC_BLOBWRAPPER {
                    return Err(CodeSignatureError::MalformedSuperBlob {
                        detail: format!(
                            "the CMS slot holds magic {:#010x}, not a blob wrapper",
                            blob.magic
                        ),
                    });
                }
                if blob.length != 8 {
                    return Err(CodeSignatureError::CmsSignaturePresent {
                        length: blob.length as u32 - 8,
                    });
                }
                has_empty_cms_wrapper = true;
            }
            CSSLOT_REQUIREMENTS if blob.magic == CSMAGIC_REQUIREMENTS => {}
            CSSLOT_ENTITLEMENTS if blob.magic == CSMAGIC_EMBEDDED_ENTITLEMENTS => {
                let payload = slice(image, blob.offset + 8, blob.length - 8, "entitlements")?;
                entitlements_xml = Some(String::from_utf8(payload.to_vec()).map_err(|_| {
                    CodeSignatureError::MalformedSuperBlob {
                        detail: "the entitlements blob is not UTF-8".into(),
                    }
                })?);
            }
            CSSLOT_DER_ENTITLEMENTS if blob.magic == CSMAGIC_EMBEDDED_DER_ENTITLEMENTS => {
                has_der_entitlements = true;
            }
            slot => return Err(CodeSignatureError::UnsupportedBlob { slot }),
        }
    }
    let (code_directory, bound) = primary.ok_or(CodeSignatureError::MissingCodeDirectory)?;
    bound_special_slots.extend(bound);
    Ok(AdHocSignature {
        filetype: facts.filetype,
        cputype: facts.cputype,
        signature_offset,
        signature_size,
        code_directory,
        alternate_code_directories: alternates,
        bound_special_slots,
        entitlements_xml,
        has_der_entitlements,
        has_empty_cms_wrapper,
    })
}

/// Re-signing fixtures shared by this module's tests and the standalone
/// linker's signature-contract tests.
#[cfg(test)]
pub(crate) mod test_support {
    use super::*;

    /// One CodeDirectory [`resign`] writes. Its page hashes are always correct
    /// for the re-signed bytes, so a refusal comes from the field under test.
    #[derive(Clone)]
    pub(crate) struct CodeDirectorySpec {
        /// SuperBlob slot (`0` or an alternate slot).
        pub slot: u32,
        /// `0x20400`, `0x20500` or `0x20600`.
        pub version: u32,
        pub flags: u32,
        pub hash_type: u8,
        pub page_shift: u8,
        pub identifier: &'static str,
        /// `(codeLimit, codeLimit64)`; `None` writes `(signature offset, 0)`.
        pub code_limits: Option<(u32, u64)>,
        /// Header bytes from offset 88 (runtime, preEncryptOffset, linkage).
        pub extension: Vec<u8>,
        /// Code page whose hash is written wrong.
        pub corrupt_page: Option<usize>,
    }

    impl CodeDirectorySpec {
        /// The standalone linker's own CodeDirectory shape.
        pub(crate) fn linker_like() -> Self {
            Self {
                slot: CSSLOT_CODEDIRECTORY,
                version: CS_SUPPORTSEXECSEG,
                flags: CS_ADHOC | CS_LINKER_SIGNED,
                hash_type: CS_HASHTYPE_SHA256,
                page_shift: 12,
                identifier: "trust-cg",
                code_limits: None,
                extension: Vec::new(),
                corrupt_page: None,
            }
        }

        fn header_size(&self) -> usize {
            let header = match self.version {
                CS_SUPPORTSEXECSEG => 88,
                CS_SUPPORTSRUNTIME => 96,
                CS_SUPPORTSLINKAGE => 108,
                other => panic!("fixture does not build CodeDirectory version {other:#x}"),
            };
            assert_eq!(88 + self.extension.len(), header, "extension size");
            header
        }

        fn page_size(&self) -> usize {
            if self.page_shift == 0 {
                usize::MAX
            } else {
                1 << self.page_shift
            }
        }

        fn len(&self, code_limit: usize) -> usize {
            let pages = if self.page_shift == 0 {
                usize::from(code_limit > 0)
            } else {
                code_limit.div_ceil(self.page_size())
            };
            self.header_size() + self.identifier.len() + 1 + pages * SHA256_LEN
        }

        fn build(&self, signed: &[u8], exec: ExecSegment) -> Vec<u8> {
            let header = self.header_size();
            let hash_offset = header + self.identifier.len() + 1;
            let hashes: Vec<[u8; SHA256_LEN]> = if self.page_shift == 0 {
                (!signed.is_empty())
                    .then(|| sha256(signed))
                    .into_iter()
                    .collect()
            } else {
                signed.chunks(self.page_size()).map(sha256).collect()
            };
            let (limit32, limit64) = self.code_limits.unwrap_or((signed.len() as u32, 0));
            let mut cd = Vec::with_capacity(self.len(signed.len()));
            for word in [
                CSMAGIC_CODEDIRECTORY,
                self.len(signed.len()) as u32,
                self.version,
                self.flags,
                hash_offset as u32,
                header as u32,
                0,
                hashes.len() as u32,
                limit32,
            ] {
                cd.extend_from_slice(&word.to_be_bytes());
            }
            cd.extend_from_slice(&[SHA256_LEN as u8, self.hash_type, 0, self.page_shift]);
            cd.extend_from_slice(&[0; 16]); // spare2, scatter, team, spare3
            cd.extend_from_slice(&limit64.to_be_bytes());
            for field in [exec.base, exec.limit, exec.flags] {
                cd.extend_from_slice(&field.to_be_bytes());
            }
            cd.extend_from_slice(&self.extension);
            cd.extend_from_slice(self.identifier.as_bytes());
            cd.push(0);
            for (page, hash) in hashes.iter().enumerate() {
                let mut hash = *hash;
                if self.corrupt_page == Some(page) {
                    hash[0] ^= 0xFF;
                }
                cd.extend_from_slice(&hash);
            }
            assert_eq!(cd.len(), self.len(signed.len()));
            cd
        }
    }

    fn load_command_offset(image: &[u8], wanted: impl Fn(&[u8], usize) -> bool) -> usize {
        let le = |at: usize| u32::from_le_bytes(image[at..at + 4].try_into().unwrap());
        let mut offset = MACH_HEADER_64_SIZE;
        for _ in 0..le(16) {
            if wanted(image, offset) {
                return offset;
            }
            offset += le(offset + 4) as usize;
        }
        panic!("load command not found");
    }

    /// Replace the verified signature of `image` with a SuperBlob holding
    /// `directories` (in index order), keeping the original executable
    /// segment. `LC_CODE_SIGNATURE` and `__LINKEDIT` are resized first, so the
    /// page hashes cover the final load commands.
    pub(crate) fn resign(image: &[u8], directories: &[CodeDirectorySpec]) -> Vec<u8> {
        let old = verify_ad_hoc_signature(image).unwrap();
        let start = old.signature_offset as usize;
        let exec = old.code_directory.exec_segment.unwrap();
        let index_end = 12 + 8 * directories.len();
        let total = index_end + directories.iter().map(|cd| cd.len(start)).sum::<usize>();

        let mut signed = image[..start].to_vec();
        let command = load_command_offset(&signed, |image, at| {
            u32::from_le_bytes(image[at..at + 4].try_into().unwrap()) == LC_CODE_SIGNATURE
        });
        signed[command + 12..command + 16].copy_from_slice(&(total as u32).to_le_bytes());
        let linkedit = load_command_offset(&signed, |image, at| {
            u32::from_le_bytes(image[at..at + 4].try_into().unwrap()) == LC_SEGMENT_64
                && image[at + 8..at + 19] == *b"__LINKEDIT\0"
        });
        let fileoff = u64::from_le_bytes(signed[linkedit + 40..linkedit + 48].try_into().unwrap());
        let filesize = (start + total) as u64 - fileoff;
        signed[linkedit + 48..linkedit + 56].copy_from_slice(&filesize.to_le_bytes());

        let blobs: Vec<Vec<u8>> = directories
            .iter()
            .map(|cd| cd.build(&signed, exec))
            .collect();
        let mut out = signed.clone();
        for word in [
            CSMAGIC_EMBEDDED_SIGNATURE,
            total as u32,
            directories.len() as u32,
        ] {
            out.extend_from_slice(&word.to_be_bytes());
        }
        let mut offset = index_end;
        for (cd, blob) in directories.iter().zip(&blobs) {
            out.extend_from_slice(&cd.slot.to_be_bytes());
            out.extend_from_slice(&(offset as u32).to_be_bytes());
            offset += blob.len();
        }
        for blob in &blobs {
            out.extend_from_slice(blob);
        }
        assert_eq!(out.len(), start + total);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::macho::constants::LC_UUID;
    use crate::macho::linker::{DylibConfig, MachOParser, link, link_dylib, link_with_dylibs};
    use crate::macho::writer::MachOWriter;

    const MH_DYLIB: u32 = 0x6;
    const ALLOW_JIT: &str = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
        <plist version=\"1.0\"><dict><key>com.apple.security.cs.allow-jit</key>\
        <true/></dict></plist>\n";

    /// An object whose `_main` runs `mov x16, #1; mov x0, #42; svc #0x80`.
    fn exit42_object() -> Vec<u8> {
        text_object("_main", &[0xD280_0030, 0xD280_0540, 0xD400_1001])
    }

    fn text_object(symbol: &str, words: &[u32]) -> Vec<u8> {
        let code: Vec<u8> = words.iter().flat_map(|word| word.to_le_bytes()).collect();
        let mut writer = MachOWriter::new();
        writer.add_text_section(&code);
        writer.add_symbol(symbol, 1, 0, true).unwrap();
        writer.write().unwrap()
    }

    fn executable() -> Vec<u8> {
        link(&[MachOParser::parse(&exit42_object()).unwrap()]).unwrap()
    }

    /// A dylib exporting `_tcg_answer` (`mov w0, #42; ret`).
    fn dylib() -> Vec<u8> {
        let object = text_object("_tcg_answer", &[0x5280_0540, 0xD65F_03C0]);
        link_dylib(
            &[MachOParser::parse(&object).unwrap()],
            &DylibConfig::new(),
            "@rpath/libtcg_answer.dylib",
        )
        .unwrap()
    }

    fn le(bytes: &[u8], at: usize) -> u32 {
        u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
    }

    fn be(bytes: &[u8], at: usize) -> u32 {
        u32::from_be_bytes(bytes[at..at + 4].try_into().unwrap())
    }

    fn put_be(bytes: &mut [u8], at: usize, value: u32) {
        bytes[at..at + 4].copy_from_slice(&value.to_be_bytes());
    }

    /// `(SuperBlob offset, slot-0 CodeDirectory offset)` of a signed image.
    fn signature_layout(image: &[u8]) -> (usize, usize) {
        let start = verify_ad_hoc_signature(image).unwrap().signature_offset as usize;
        (start, start + be(image, start + 16) as usize)
    }

    /// File offset of the first load command `wanted` accepts.
    fn load_command(image: &[u8], wanted: impl Fn(&[u8], usize) -> bool) -> usize {
        let mut offset = MACH_HEADER_64_SIZE;
        for _ in 0..le(image, 16) {
            if wanted(image, offset) {
                return offset;
            }
            offset += le(image, offset + 4) as usize;
        }
        panic!("load command not found");
    }

    fn command_is(cmd: u32) -> impl Fn(&[u8], usize) -> bool {
        move |image, offset| le(image, offset) == cmd
    }

    fn segment_named(name: &'static [u8]) -> impl Fn(&[u8], usize) -> bool {
        move |image, offset| {
            le(image, offset) == LC_SEGMENT_64
                && image[offset + 8..offset + 8 + name.len()] == *name
        }
    }

    fn blob(magic: u32, payload: &[u8]) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(8 + payload.len());
        bytes.extend_from_slice(&magic.to_be_bytes());
        bytes.extend_from_slice(&((8 + payload.len()) as u32).to_be_bytes());
        bytes.extend_from_slice(payload);
        bytes
    }

    /// Replace `image`'s linker signature with a codesign-style ad-hoc one: a
    /// version 0x20500 CodeDirectory with the hardened-runtime flag, internal
    /// requirements and XML entitlements bound through special slots 2 and 5,
    /// and a CMS wrapper holding `cms_payload`. This mirrors the layout
    /// `codesign -s - --options runtime --entitlements` writes, which
    /// tests/macho_code_signature_native.rs checks against codesign itself.
    fn resign_with_special_slots(image: &[u8], entitlements: &str, cms_payload: &[u8]) -> Vec<u8> {
        let old = verify_ad_hoc_signature(image).unwrap();
        let start = old.signature_offset as usize;
        let text = old.code_directory.exec_segment.unwrap();
        let requirements = blob(CSMAGIC_REQUIREMENTS, &0u32.to_be_bytes());
        let entitlements = blob(CSMAGIC_EMBEDDED_ENTITLEMENTS, entitlements.as_bytes());
        let cms = blob(CSMAGIC_BLOBWRAPPER, cms_payload);
        let identifier = b"tcg-fixture\0";
        let special_slots = CSSLOT_ENTITLEMENTS;
        let header = 96usize;
        let pages = start.div_ceil(4096);
        let hash_offset = header + identifier.len() + special_slots as usize * SHA256_LEN;
        let cd_len = hash_offset + pages * SHA256_LEN;
        let index_end = 12 + 4 * 8;
        let total = index_end + cd_len + requirements.len() + entitlements.len() + cms.len();

        // The new sizes change the load commands, which page 0 hashes.
        let mut signed = image[..start].to_vec();
        let command = load_command(&signed, command_is(LC_CODE_SIGNATURE));
        signed[command + 12..command + 16].copy_from_slice(&(total as u32).to_le_bytes());
        let linkedit = load_command(&signed, segment_named(b"__LINKEDIT\0"));
        let fileoff = u64::from_le_bytes(signed[linkedit + 40..linkedit + 48].try_into().unwrap());
        let filesize = (start + total) as u64 - fileoff;
        signed[linkedit + 48..linkedit + 56].copy_from_slice(&filesize.to_le_bytes());

        let mut code_directory = Vec::with_capacity(cd_len);
        for word in [
            CSMAGIC_CODEDIRECTORY,
            cd_len as u32,
            CS_SUPPORTSRUNTIME,
            CS_ADHOC | CS_RUNTIME,
            hash_offset as u32,
            header as u32,
            special_slots,
            pages as u32,
            start as u32,
        ] {
            code_directory.extend_from_slice(&word.to_be_bytes());
        }
        code_directory.extend_from_slice(&[SHA256_LEN as u8, CS_HASHTYPE_SHA256, 0, 12]);
        code_directory.extend_from_slice(&[0; 16]); // spare2, scatter, team, spare3
        code_directory.extend_from_slice(&0u64.to_be_bytes()); // codeLimit64
        code_directory.extend_from_slice(&text.base.to_be_bytes());
        code_directory.extend_from_slice(&text.limit.to_be_bytes());
        code_directory.extend_from_slice(&text.flags.to_be_bytes());
        code_directory.extend_from_slice(&0x000E_0000u32.to_be_bytes()); // runtime
        code_directory.extend_from_slice(&0u32.to_be_bytes()); // preEncryptOffset
        assert_eq!(code_directory.len(), header);
        code_directory.extend_from_slice(identifier);
        for special_slot in (1..=special_slots).rev() {
            code_directory.extend_from_slice(&match special_slot {
                CSSLOT_REQUIREMENTS => sha256(&requirements),
                CSSLOT_ENTITLEMENTS => sha256(&entitlements),
                _ => [0; SHA256_LEN],
            });
        }
        for page in signed.chunks(4096) {
            code_directory.extend_from_slice(&sha256(page));
        }
        assert_eq!(code_directory.len(), cd_len);

        let entries = [
            (CSSLOT_CODEDIRECTORY, code_directory),
            (CSSLOT_REQUIREMENTS, requirements),
            (CSSLOT_ENTITLEMENTS, entitlements),
            (CSSLOT_SIGNATURESLOT, cms),
        ];
        for word in [
            CSMAGIC_EMBEDDED_SIGNATURE,
            total as u32,
            entries.len() as u32,
        ] {
            signed.extend_from_slice(&word.to_be_bytes());
        }
        let mut offset = index_end;
        for (slot, bytes) in &entries {
            signed.extend_from_slice(&slot.to_be_bytes());
            signed.extend_from_slice(&(offset as u32).to_be_bytes());
            offset += bytes.len();
        }
        for (_, bytes) in &entries {
            signed.extend_from_slice(bytes);
        }
        assert_eq!(signed.len(), start + total);
        signed
    }

    #[test]
    fn standalone_executables_and_dylibs_carry_verified_linker_signatures() {
        let with_libsystem = link_with_dylibs(
            &[MachOParser::parse(&exit42_object()).unwrap()],
            &DylibConfig::with_libsystem(),
        )
        .unwrap();
        for (image, filetype, exec_flags) in [
            (executable(), MH_EXECUTE, CS_EXECSEG_MAIN_BINARY),
            (with_libsystem, MH_EXECUTE, CS_EXECSEG_MAIN_BINARY),
            (dylib(), MH_DYLIB, 0),
        ] {
            let report = verify_ad_hoc_signature(&image).unwrap();
            let cd = &report.code_directory;
            assert_eq!(report.filetype, filetype);
            assert_eq!(report.cputype, crate::macho::constants::CPU_TYPE_ARM64);
            assert_eq!(cd.flags, CS_ADHOC | CS_LINKER_SIGNED);
            assert!(cd.is_linker_signed());
            assert!(!cd.has_hardened_runtime());
            assert_eq!(cd.version, CS_SUPPORTSEXECSEG);
            assert_eq!(cd.page_size, 4096);
            assert_eq!(cd.special_slots, 0);
            assert_eq!(cd.identifier, "trust-cg");
            assert_eq!(cd.code_limit, report.signature_offset);
            assert_eq!(u64::from(cd.code_slots), cd.code_limit.div_ceil(4096));
            assert_eq!(cd.exec_segment.unwrap().flags, exec_flags);
            assert!(report.alternate_code_directories.is_empty());
            assert!(report.bound_special_slots.is_empty());
            assert_eq!(report.entitlements_xml, None);
            assert!(!report.has_empty_cms_wrapper);
        }
    }

    #[test]
    fn a_changed_byte_anywhere_before_the_signature_breaks_its_page_hash() {
        let clean = executable();
        let report = verify_ad_hoc_signature(&clean).unwrap();
        let text = report.code_directory.exec_segment.unwrap();
        // mach_header_64.flags (page 0), the last __TEXT byte, and the last
        // byte before the signature.
        for at in [
            24,
            (text.base + text.limit - 1) as usize,
            report.signature_offset as usize - 1,
        ] {
            let mut image = clean.clone();
            image[at] ^= 0x01;
            assert_eq!(
                verify_ad_hoc_signature(&image),
                Err(CodeSignatureError::CodePageHashMismatch {
                    slot: 0,
                    page: (at / 4096) as u32
                }),
                "byte {at}"
            );
        }
    }

    #[test]
    fn unsigned_duplicate_and_misplaced_signatures_are_refused() {
        // Renaming the command leaves an unsigned image.
        let mut unsigned = executable();
        let command = load_command(&unsigned, command_is(LC_CODE_SIGNATURE));
        unsigned[command..command + 4].copy_from_slice(&0x7FFF_FFFFu32.to_le_bytes());
        assert_eq!(
            verify_ad_hoc_signature(&unsigned),
            Err(CodeSignatureError::Unsigned)
        );

        // A second LC_CODE_SIGNATURE appended in the header padding.
        let mut twin = executable();
        let command = load_command(&twin, command_is(LC_CODE_SIGNATURE));
        let sizeofcmds = le(&twin, 20) as usize;
        let end = MACH_HEADER_64_SIZE + sizeofcmds;
        assert!(twin[end..end + 16].iter().all(|&byte| byte == 0));
        let copy = twin[command..command + 16].to_vec();
        twin[end..end + 16].copy_from_slice(&copy);
        let ncmds = le(&twin, 16);
        twin[16..20].copy_from_slice(&(ncmds + 1).to_le_bytes());
        twin[20..24].copy_from_slice(&((sizeofcmds + 16) as u32).to_le_bytes());
        assert_eq!(
            verify_ad_hoc_signature(&twin),
            Err(CodeSignatureError::DuplicateSignatureCommand { count: 2 })
        );

        // A load command that overruns sizeofcmds.
        let mut overrun = executable();
        let uuid = load_command(&overrun, command_is(LC_UUID));
        overrun[uuid + 4..uuid + 8].copy_from_slice(&0x1_0000u32.to_le_bytes());
        assert!(matches!(
            verify_ad_hoc_signature(&overrun),
            Err(CodeSignatureError::MalformedLoadCommand { .. })
        ));

        // Bytes after the signature are unsigned, a cut signature is short,
        // and a payload may not move outside __LINKEDIT.
        let mut trailing = executable();
        trailing.extend_from_slice(&[0; 16]);
        let mut truncated = executable();
        truncated.truncate(truncated.len() - 8);
        let mut outside = executable();
        let command = load_command(&outside, command_is(LC_CODE_SIGNATURE));
        outside[command + 8..command + 12].copy_from_slice(&16u32.to_le_bytes());
        for image in [trailing, truncated, outside] {
            assert!(matches!(
                verify_ad_hoc_signature(&image),
                Err(CodeSignatureError::SignaturePlacement { .. })
            ));
        }

        // Not a thin 64-bit Mach-O, or too short to be one.
        let mut fat = executable();
        fat[0..4].copy_from_slice(&0xBEBA_FECAu32.to_le_bytes());
        assert_eq!(
            verify_ad_hoc_signature(&fat),
            Err(CodeSignatureError::NotMachO64 { magic: 0xBEBA_FECA })
        );
        assert!(matches!(
            verify_ad_hoc_signature(&[0xCF, 0xFA]),
            Err(CodeSignatureError::Truncated { .. })
        ));
    }

    #[test]
    fn malformed_superblobs_and_code_directories_are_refused_by_name() {
        let base = executable();
        let (start, cd) = signature_layout(&base);
        let mutate = |edit: &dyn Fn(&mut Vec<u8>)| {
            let mut image = base.clone();
            edit(&mut image);
            verify_ad_hoc_signature(&image)
        };
        let is_superblob = |result: Result<AdHocSignature, CodeSignatureError>| {
            matches!(result, Err(CodeSignatureError::MalformedSuperBlob { .. }))
        };
        let is_code_directory = |result: Result<AdHocSignature, CodeSignatureError>| {
            matches!(
                result,
                Err(CodeSignatureError::MalformedCodeDirectory { slot: 0, .. })
            )
        };

        assert!(is_superblob(mutate(&|image| put_be(
            image,
            start,
            0xFADE_0CC1
        ))));
        assert!(is_superblob(mutate(&|image| put_be(
            image,
            start + 4,
            0xFFFF
        ))));
        assert!(is_superblob(mutate(&|image| put_be(
            image,
            start + 8,
            0x1000
        ))));
        assert!(is_superblob(mutate(&|image| put_be(image, start + 16, 4))));
        assert_eq!(
            mutate(&|image| put_be(image, start + 12, 0x2_0000)),
            Err(CodeSignatureError::UnsupportedBlob { slot: 0x2_0000 })
        );
        assert_eq!(
            mutate(&|image| put_be(image, start + 12, CSSLOT_REQUIREMENTS)),
            Err(CodeSignatureError::UnsupportedBlob {
                slot: CSSLOT_REQUIREMENTS
            })
        );
        assert_eq!(
            mutate(&|image| put_be(image, start + 12, CSSLOT_ALTERNATE_CODEDIRECTORIES)),
            Err(CodeSignatureError::MissingCodeDirectory)
        );
        assert!(is_code_directory(mutate(&|image| put_be(
            image,
            cd,
            CSMAGIC_REQUIREMENTS
        ))));
        assert_eq!(
            mutate(&|image| put_be(image, cd + 8, 0x2_0700)),
            Err(CodeSignatureError::UnsupportedVersion {
                slot: 0,
                version: 0x2_0700
            })
        );
        assert_eq!(
            mutate(&|image| image[cd + 37] = 1),
            Err(CodeSignatureError::UnsupportedHashType {
                slot: 0,
                hash_type: 1,
                hash_size: 32
            })
        );
        assert_eq!(
            mutate(&|image| image[cd + 39] = 11),
            Err(CodeSignatureError::UnsupportedPageSize { slot: 0, shift: 11 })
        );
        assert_eq!(
            mutate(&|image| put_be(image, cd + 44, 88)),
            Err(CodeSignatureError::UnsupportedFeature {
                slot: 0,
                feature: "a scatter vector"
            })
        );
        assert_eq!(
            mutate(&|image| put_be(image, cd + 12, CS_LINKER_SIGNED)),
            Err(CodeSignatureError::NotAdHoc {
                slot: 0,
                flags: CS_LINKER_SIGNED
            })
        );
        let code_limit = be(&base, cd + 32);
        assert_eq!(
            mutate(&|image| put_be(image, cd + 32, code_limit - 16)),
            Err(CodeSignatureError::CodeLimitMismatch {
                slot: 0,
                code_limit: u64::from(code_limit - 16),
                signature_offset: start as u64
            })
        );
        let slots = be(&base, cd + 28);
        assert_eq!(
            mutate(&|image| put_be(image, cd + 28, slots - 1)),
            Err(CodeSignatureError::CodeSlotCountMismatch {
                slot: 0,
                expected: u64::from(slots),
                actual: slots - 1
            })
        );
        // Special-slot hashes that would overlap the header, an identifier
        // outside the CodeDirectory, and one without its terminator.
        assert!(is_code_directory(mutate(&|image| put_be(
            image,
            cd + 24,
            7
        ))));
        assert!(is_code_directory(mutate(&|image| put_be(
            image,
            cd + 20,
            0xFFFF
        ))));
        let hash_offset = be(&base, cd + 16) as usize;
        let hashes_end = cd + hash_offset + slots as usize * SHA256_LEN;
        assert!(is_code_directory(mutate(&|image| {
            let ident = cd + be(image, cd + 20) as usize;
            image[ident..hashes_end].fill(b'x');
        })));
        // An executable segment past __TEXT, one not starting it, and a
        // main-binary flag on the wrong file type. A limit inside __TEXT (the
        // Xcode 27 ld64 records the __text size) is accepted.
        assert!(matches!(
            mutate(&|image| image[cd + 79] ^= 0x10),
            Err(CodeSignatureError::ExecSegmentMismatch { slot: 0, .. })
        ));
        assert!(matches!(
            mutate(&|image| image[cd + 71] = 0x10),
            Err(CodeSignatureError::ExecSegmentMismatch { slot: 0, .. })
        ));
        assert!(matches!(
            mutate(&|image| image[cd + 87] = 0),
            Err(CodeSignatureError::ExecSegmentMismatch { slot: 0, .. })
        ));
        let section_limit = mutate(&|image| {
            image[cd + 72..cd + 80].copy_from_slice(&8u64.to_be_bytes());
        })
        .unwrap();
        assert_eq!(section_limit.code_directory.exec_segment.unwrap().limit, 8);
    }

    #[test]
    fn special_slots_bind_requirements_entitlements_and_the_empty_cms_wrapper() {
        let image = resign_with_special_slots(&executable(), ALLOW_JIT, &[]);
        let report = verify_ad_hoc_signature(&image).unwrap();
        let cd = &report.code_directory;
        assert_eq!(cd.version, CS_SUPPORTSRUNTIME);
        assert_eq!(cd.flags, CS_ADHOC | CS_RUNTIME);
        assert!(cd.has_hardened_runtime());
        assert!(!cd.is_linker_signed());
        assert_eq!(cd.special_slots, CSSLOT_ENTITLEMENTS);
        assert_eq!(cd.runtime_version, Some(0x000E_0000));
        assert_eq!(cd.identifier, "tcg-fixture");
        assert_eq!(
            report.bound_special_slots,
            vec![CSSLOT_REQUIREMENTS, CSSLOT_ENTITLEMENTS]
        );
        assert_eq!(report.entitlements_xml.as_deref(), Some(ALLOW_JIT));
        assert!(report.has_empty_cms_wrapper);
        assert!(!report.has_der_entitlements);

        let (start, cd_offset) = signature_layout(&image);
        let hash_offset = be(&image, cd_offset + 16) as usize;
        let special = |slot: u32| cd_offset + hash_offset - slot as usize * SHA256_LEN;
        let blobs = read_super_blob(&image, start, image.len() - start).unwrap();
        let find = |slot: u32| *blobs.iter().find(|blob| blob.slot == slot).unwrap();

        // Editing the entitlements after signing breaks special slot 5.
        let entitlements = find(CSSLOT_ENTITLEMENTS);
        let mut edited = image.clone();
        edited[entitlements.offset + entitlements.length - 3] ^= 0x20;
        assert_eq!(
            verify_ad_hoc_signature(&edited),
            Err(CodeSignatureError::SpecialSlotHashMismatch {
                slot: 0,
                special_slot: CSSLOT_ENTITLEMENTS
            })
        );
        // A nonzero Info.plist slot names external data.
        let mut info = image.clone();
        info[special(CSSLOT_INFOSLOT)] = 1;
        assert_eq!(
            verify_ad_hoc_signature(&info),
            Err(CodeSignatureError::UnsupportedExternalSpecialSlot {
                slot: 0,
                special_slot: CSSLOT_INFOSLOT
            })
        );
        // A nonzero hash for an internal slot with no blob is a mismatch.
        let mut application = image.clone();
        application[special(4)] = 1;
        assert_eq!(
            verify_ad_hoc_signature(&application),
            Err(CodeSignatureError::SpecialSlotHashMismatch {
                slot: 0,
                special_slot: 4
            })
        );
        // Fewer special slots leave the entitlements blob unbound.
        let mut unbound = image.clone();
        put_be(&mut unbound, cd_offset + 24, CSSLOT_REQUIREMENTS);
        assert_eq!(
            verify_ad_hoc_signature(&unbound),
            Err(CodeSignatureError::UnboundBlob {
                slot: 0,
                blob_slot: CSSLOT_ENTITLEMENTS
            })
        );
        // The CMS slot must hold a blob wrapper, and an empty one.
        let mut wrong_magic = image.clone();
        put_be(
            &mut wrong_magic,
            find(CSSLOT_SIGNATURESLOT).offset,
            CSMAGIC_REQUIREMENTS,
        );
        assert!(matches!(
            verify_ad_hoc_signature(&wrong_magic),
            Err(CodeSignatureError::MalformedSuperBlob { .. })
        ));
        let certificate = resign_with_special_slots(&executable(), ALLOW_JIT, &[0x30; 24]);
        assert_eq!(
            verify_ad_hoc_signature(&certificate),
            Err(CodeSignatureError::CmsSignaturePresent { length: 24 })
        );
    }

    fn resigned(
        spec: &test_support::CodeDirectorySpec,
    ) -> Result<AdHocSignature, CodeSignatureError> {
        verify_ad_hoc_signature(&test_support::resign(
            &executable(),
            std::slice::from_ref(spec),
        ))
    }

    /// `runtime` and `preEncryptOffset` header words (version 0x20500+).
    fn runtime_extension(pre_encrypt_offset: u32) -> Vec<u8> {
        let mut extension = 0x000E_0000u32.to_be_bytes().to_vec();
        extension.extend_from_slice(&pre_encrypt_offset.to_be_bytes());
        extension
    }

    /// Every page hash in these signatures matches, so each refusal is the
    /// header rule under test. The page-size and code-limit cases are ones
    /// `codesign --verify` accepts and the arm64 kernel kills
    /// (tests/macho_code_signature_native.rs).
    #[test]
    fn kernel_refused_page_sizes_code_limits_and_header_features_are_refused() {
        use test_support::CodeDirectorySpec;
        let start = verify_ad_hoc_signature(&executable())
            .unwrap()
            .signature_offset;
        let with = |edit: &dyn Fn(&mut CodeDirectorySpec)| {
            let mut spec = CodeDirectorySpec::linker_like();
            edit(&mut spec);
            resigned(&spec)
        };
        // The fixture reproduces the linker's signature; 16 KiB pages verify.
        assert_eq!(with(&|_| {}).unwrap().code_directory.page_size, 4096);
        assert_eq!(
            with(&|cd| cd.page_shift = 14)
                .unwrap()
                .code_directory
                .page_size,
            16384
        );
        for shift in [0, 13, 15, 16] {
            assert_eq!(
                with(&|cd| cd.page_shift = shift),
                Err(CodeSignatureError::UnsupportedPageSize { slot: 0, shift }),
                "page shift {shift}"
            );
        }

        // The 32-bit codeLimit must name the signature offset even when
        // codeLimit64 does, and a nonzero codeLimit64 must agree with it.
        let start32 = u32::try_from(start).unwrap();
        for (limits, claimed) in [
            ((0, start), 0),
            ((u32::MAX, start), u64::from(u32::MAX)),
            ((start32, start + 16), start + 16),
        ] {
            assert_eq!(
                with(&|cd| cd.code_limits = Some(limits)),
                Err(CodeSignatureError::CodeLimitMismatch {
                    slot: 0,
                    code_limit: claimed,
                    signature_offset: start
                }),
                "limits {limits:?}"
            );
        }
        with(&|cd| cd.code_limits = Some((start32, start))).unwrap();

        // Pre-encryption hashes (version 0x20500) and any linkage field
        // (version 0x20600) are refused; the zero forms verify.
        with(&|cd| {
            cd.version = CS_SUPPORTSRUNTIME;
            cd.extension = runtime_extension(0);
        })
        .unwrap();
        assert_eq!(
            with(&|cd| {
                cd.version = CS_SUPPORTSRUNTIME;
                cd.extension = runtime_extension(0x100);
            }),
            Err(CodeSignatureError::UnsupportedFeature {
                slot: 0,
                feature: "pre-encryption hashes"
            })
        );
        let linkage = |field: Option<usize>| {
            let mut extension = runtime_extension(0);
            let mut fields = [0u8; 12];
            if let Some(at) = field {
                fields[at] = 1;
            }
            extension.extend_from_slice(&fields);
            extension
        };
        with(&|cd| {
            cd.version = CS_SUPPORTSLINKAGE;
            cd.extension = linkage(None);
        })
        .unwrap();
        // Hash type, application type, subtype, offset, size.
        for at in [0, 1, 3, 7, 11] {
            assert_eq!(
                with(&|cd| {
                    cd.version = CS_SUPPORTSLINKAGE;
                    cd.extension = linkage(Some(at));
                }),
                Err(CodeSignatureError::UnsupportedFeature {
                    slot: 0,
                    feature: "a linkage hash"
                }),
                "linkage byte {at}"
            );
        }
    }

    #[test]
    fn alternate_code_directories_are_verified_like_the_primary() {
        use test_support::{CodeDirectorySpec, resign};
        let primary = CodeDirectorySpec::linker_like();
        let alternate = CodeDirectorySpec {
            slot: CSSLOT_ALTERNATE_CODEDIRECTORIES,
            page_shift: 14,
            ..primary.clone()
        };
        let pair = |edit: &dyn Fn(&mut CodeDirectorySpec)| {
            let mut alternate = alternate.clone();
            edit(&mut alternate);
            verify_ad_hoc_signature(&resign(&executable(), &[primary.clone(), alternate]))
        };
        let report = pair(&|_| {}).unwrap();
        assert_eq!(report.code_directory.page_size, 4096);
        assert_eq!(report.alternate_code_directories.len(), 1);
        assert_eq!(
            report.alternate_code_directories[0].slot,
            CSSLOT_ALTERNATE_CODEDIRECTORIES
        );
        assert_eq!(report.alternate_code_directories[0].page_size, 16384);

        let last = CSSLOT_ALTERNATE_CODEDIRECTORIES + CSSLOT_ALTERNATE_CODEDIRECTORY_MAX - 1;
        assert_eq!(
            pair(&|cd| cd.corrupt_page = Some(0)),
            Err(CodeSignatureError::CodePageHashMismatch {
                slot: CSSLOT_ALTERNATE_CODEDIRECTORIES,
                page: 0
            })
        );
        assert_eq!(
            pair(&|cd| {
                cd.slot = last;
                cd.corrupt_page = Some(0);
            }),
            Err(CodeSignatureError::CodePageHashMismatch {
                slot: last,
                page: 0
            })
        );
        assert_eq!(
            pair(&|cd| cd.hash_type = 1),
            Err(CodeSignatureError::UnsupportedHashType {
                slot: CSSLOT_ALTERNATE_CODEDIRECTORIES,
                hash_type: 1,
                hash_size: 32
            })
        );
        assert_eq!(
            pair(&|cd| cd.flags = CS_LINKER_SIGNED),
            Err(CodeSignatureError::NotAdHoc {
                slot: CSSLOT_ALTERNATE_CODEDIRECTORIES,
                flags: CS_LINKER_SIGNED
            })
        );
        assert_eq!(
            pair(&|cd| cd.page_shift = 13),
            Err(CodeSignatureError::UnsupportedPageSize {
                slot: CSSLOT_ALTERNATE_CODEDIRECTORIES,
                shift: 13
            })
        );
        // One past the reserved alternate slots is not a signature component.
        assert_eq!(
            pair(&|cd| cd.slot = last + 1),
            Err(CodeSignatureError::UnsupportedBlob { slot: last + 1 })
        );
        // A corrupt primary is refused even when the alternate is sound, and
        // an alternate alone is no signature.
        let mut corrupt_primary = primary.clone();
        corrupt_primary.corrupt_page = Some(0);
        assert_eq!(
            verify_ad_hoc_signature(&resign(
                &executable(),
                &[corrupt_primary, alternate.clone()]
            )),
            Err(CodeSignatureError::CodePageHashMismatch { slot: 0, page: 0 })
        );
        assert_eq!(
            verify_ad_hoc_signature(&resign(&executable(), &[alternate])),
            Err(CodeSignatureError::MissingCodeDirectory)
        );
    }
}
