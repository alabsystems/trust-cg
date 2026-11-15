// trust-cg-codegen/macho/linked_image.rs - linked-image evidence record for arm64 Mach-O
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Linked-image evidence: bind a linked arm64 Mach-O executable or dylib to
//! the trust-cg objects it was linked from.
//!
//! [`record_linked_image`] reads the final image and every input object with
//! its own readers (written from `<mach-o/loader.h>`, `<mach-o/nlist.h>`,
//! `<mach-o/reloc.h>` and `<mach-o/fixup-chains.h>`; they import neither the
//! object writer's nor the standalone linker's layout code), then replays
//! every relocation record of every object against the image, except those
//! of the sections the linker consumes (counted below):
//!
//! - **Placement.** Each object section is split into the atoms a static
//!   linker may place independently (`MH_SUBSECTIONS_VIA_SYMBOLS`). An
//!   atom's image address comes from the image's own symbol table (ld64
//!   images, [`AtomPlacement::ImageSymbolTable`]) or from the linker's
//!   section addresses (the in-repo standalone linker, which writes no
//!   symbol table, [`AtomPlacement::SectionAddresses`]). Either is a claim:
//!   it is accepted only when every byte of every placed atom outside its
//!   relocation fields equals the object's, no two atoms overlap, each atom
//!   lies in one image section, and the entry point, exports trie and symbol
//!   table agree with the placed definitions.
//! - **Replay.** Each `ARM64_RELOC_*` site must encode the address the
//!   image's resolution of its target gives: a `BRANCH26` lands on the
//!   definition, or on a `__stubs` entry whose slot dyld binds to the import
//!   (or to the weak-definition lookup of a coalescable weak definition); a
//!   `PAGE21`/`PAGEOFF12` pair addresses the definition with the load or
//!   store scale the instruction needs; a `GOT_LOAD`/`TLVP_LOAD` pair
//!   addresses the one GOT or TLV-pointer slot of its target (its fixup binds
//!   the import or rebases to the definition), or, where ld64 relaxed the
//!   `LDR` into an `ADD`, the definition itself with the registers kept; an
//!   `UNSIGNED` pointer carries a rebase to the definition or a bind to the
//!   import with the object's addend, except a TLV descriptor's template
//!   offset, which holds the offset from the image's thread-local template
//!   with no fixup; a `SUBTRACTOR` pair holds the difference with no fixup.
//! - **Fixups.** Every chained-fixup entry or `LC_DYLD_INFO` rebase, bind,
//!   lazy bind and weak bind is decoded. A fixup inside object content that
//!   no relocation explains, outside object content and outside the
//!   linker's GOT, lazy and TLV pointer-slot sections, or in a segment dyld
//!   cannot write, is refused; the rest are recorded as the linker's own
//!   slots.
//! - **Accounting.** Every nonzero byte of a file-backed image section the
//!   linker does not synthesize (`__stubs`, `__stub_helper`,
//!   `__unwind_info` and the pointer slots) must lie in a placed object
//!   atom: code or data from a link input the request does not name (a
//!   `-Wl` object or an archive member) is refused.
//! - **Binding.** Every bind names a dylib by two-level ordinal; the dylib
//!   at that ordinal must export the name according to a supplied export
//!   list ([`ProviderExports`]: an independently read dylib image, a TAPI
//!   stub, or the standalone linker's declared set), the weak-import flag
//!   must equal the objects' `N_WEAK_REF` intent, a name the objects
//!   define must not be bound to another image, and every dependent dylib
//!   but libSystem must be named by a bind. A reference to a weak
//!   definition the image exports for dyld coalescing must go through
//!   dyld's weak-definition lookup; a static resolution of it is refused.
//! - **Protection.** Object `__DATA,__const` and `__DATA_CONST` content must
//!   land in `__DATA_CONST` with `SG_READ_ONLY` (dyld makes it read-only
//!   once its fixups are applied), code in an executable segment, other data
//!   in a writable one, and thread-local templates and descriptors in
//!   sections of their type.
//! - **Exports.** The entry point names the objects' `_main`; every export
//!   of an object definition carries its placed address, kind and weakness;
//!   no name an object defines hidden (`N_PEXT`), and no local another
//!   object does not define globally, is exported; a dylib exports every
//!   default-visibility definition (an exported-symbols list that hides one
//!   is refused).
//! - **Identity.** The record carries the image's SHA-256, `LC_UUID`,
//!   `LC_BUILD_VERSION` (and the linker version it records), the ad-hoc code
//!   signature (verified by [`super::codesign::verify_ad_hoc_signature`];
//!   its CodeDirectory hash), the declared linker identity, every object's
//!   SHA-256 and a digest of its relocation inventory.
//!
//! Any disagreement refuses the record with named findings
//! ([`LinkedImageRefusal`]); a record is produced only when there are none.
//!
//! This is an independent replay (redundancy evidence), not a proof. It
//! binds the image bytes and dyld's documented fixup semantics as decoded
//! here; it does not model dyld's run-time behaviour beyond them (load
//! order, which image a weak lookup or an interposition selects, lazy-binding
//! helpers, `__unwind_info`, `__eh_frame` rewriting), the exports of dylibs
//! whose export lists were not supplied, the linker's own code (stub
//! helpers), or zero bytes outside the object atoms. Sections the linker
//! consumes (`__LD,__compact_unwind`, `S_ATTR_DEBUG`) are counted, not
//! replayed. Objects with `__eh_frame`, literal sections, section-relative
//! (`r_extern = 0`) relocations or linker optimization hints,
//! flat-namespace images, arm64e images and universal files are refused by
//! name.

mod abi;
mod image;
mod object;
mod replay;
mod tbd;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

use serde::Serialize;

/// Schema identifier written into every record.
pub const LINKED_IMAGE_RECORD_SCHEMA: &str = "trust-cg.macho-linked-image/v1";

/// Suffix of the record written next to a linked artifact.
pub const LINKED_IMAGE_RECORD_SUFFIX: &str = ".linked-image.json";

/// The image, an input object or a dylib export list could not be read.
pub const CODE_PARSE: &str = "TCG-IMAGE-PARSE";
/// The ad-hoc code signature does not verify.
pub const CODE_SIGNATURE: &str = "TCG-IMAGE-SIGNATURE";
/// An atom cannot be placed, or its placement disagrees with the image.
pub const CODE_PLACEMENT: &str = "TCG-IMAGE-PLACEMENT";
/// Image bytes outside relocation fields differ from the object's.
pub const CODE_CONTENT: &str = "TCG-IMAGE-CONTENT";
/// A `BRANCH26` site does not reach its target.
pub const CODE_BRANCH26: &str = "TCG-IMAGE-BRANCH26";
/// A `PAGE21`/`PAGEOFF12` site does not address its target.
pub const CODE_PAGE: &str = "TCG-IMAGE-PAGE";
/// A `GOT_LOAD_*` or `POINTER_TO_GOT` site does not reach its GOT slot.
pub const CODE_GOT: &str = "TCG-IMAGE-GOT";
/// A `TLVP_LOAD_*` site or a TLV descriptor field disagrees.
pub const CODE_TLV: &str = "TCG-IMAGE-TLV";
/// An `UNSIGNED` pointer's fixup disagrees with its target.
pub const CODE_POINTER: &str = "TCG-IMAGE-POINTER";
/// A `SUBTRACTOR` difference disagrees.
pub const CODE_DIFFERENCE: &str = "TCG-IMAGE-DIFFERENCE";
/// A coalescable weak definition is resolved statically.
pub const CODE_WEAK_DIRECT: &str = "TCG-IMAGE-WEAK-DIRECT";
/// A bind's ordinal, weak-import flag or target disagrees with intent.
pub const CODE_IMPORT_BINDING: &str = "TCG-IMAGE-IMPORT-BINDING";
/// No export list was supplied for the dylib a bind names.
pub const CODE_IMPORT_PROVIDER: &str = "TCG-IMAGE-IMPORT-PROVIDER";
/// A fixup inside object content that no relocation explains, or outside
/// object content and outside the linker's pointer-slot sections.
pub const CODE_UNEXPLAINED_FIXUP: &str = "TCG-IMAGE-UNEXPLAINED-FIXUP";
/// Nonzero image bytes that no input object atom and no linker-synthesized
/// section accounts for (content from a link input the request does not name).
pub const CODE_UNACCOUNTED_CONTENT: &str = "TCG-IMAGE-UNACCOUNTED-CONTENT";
/// A dependent dylib other than libSystem that no bind uses.
pub const CODE_UNUSED_DYLIB: &str = "TCG-IMAGE-UNUSED-DYLIB";
/// Read-only-after-fixup data in a segment dyld leaves writable.
pub const CODE_CONST_WRITABLE: &str = "TCG-IMAGE-CONST-WRITABLE";
/// Code, data or thread-local content in a segment or section of the wrong kind.
pub const CODE_PROTECTION: &str = "TCG-IMAGE-PROTECTION";
/// The exports trie disagrees with the objects' definitions.
pub const CODE_EXPORT: &str = "TCG-IMAGE-EXPORT";
/// `LC_MAIN` does not name the objects' `_main`.
pub const CODE_ENTRY: &str = "TCG-IMAGE-ENTRY";
/// A header flag or required load command disagrees with the image content.
pub const CODE_HEADER: &str = "TCG-IMAGE-HEADER";
/// A retained definition is missing, or a live reference names a missing one.
pub const CODE_DEAD_STRIP: &str = "TCG-IMAGE-DEAD-STRIP";
/// A construct this replay does not model.
pub const CODE_UNSUPPORTED: &str = "TCG-IMAGE-UNSUPPORTED";

/// One relocatable object given to the linker, in link order.
#[derive(Debug, Clone, Copy)]
pub struct LinkedObject<'a> {
    /// Name recorded for the object (a path or a label).
    pub name: &'a str,
    /// The object's bytes.
    pub bytes: &'a [u8],
}

/// How each object atom's image address is established.
#[derive(Debug, Clone, Copy)]
pub enum AtomPlacement<'a> {
    /// The image's symbol table names every placed atom (ld64 images).
    ImageSymbolTable,
    /// The address the linker placed each object section at, per object
    /// and section in object order; `None` for a section it did not load.
    SectionAddresses(&'a [Vec<Option<u64>>]),
}

/// The names one dylib exports, for checking the binds that name it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProviderExports {
    /// The dylib's install name (`LC_ID_DYLIB`).
    pub install_name: String,
    /// Every exported name.
    pub symbols: BTreeSet<String>,
    /// The exported names that are thread-local variable descriptors, when
    /// the source says (`None` for a declared list).
    pub thread_local_symbols: Option<BTreeSet<String>>,
    /// Where the list came from.
    pub source: String,
}

impl ProviderExports {
    /// A declared export list (for example a standalone link's
    /// [`super::linker::DylibConfig`]).
    pub fn declared(
        install_name: impl Into<String>,
        symbols: impl IntoIterator<Item = String>,
        source: impl Into<String>,
    ) -> Self {
        Self {
            install_name: install_name.into(),
            symbols: symbols.into_iter().collect(),
            thread_local_symbols: None,
            source: source.into(),
        }
    }

    /// The install name and exports trie of a dylib image, read
    /// independently.
    pub fn from_dylib_image(bytes: &[u8], source: impl Into<String>) -> Result<Self, String> {
        let (install_name, symbols, thread_locals) = image::dylib_exports(bytes)?;
        Ok(Self {
            install_name,
            symbols,
            thread_local_symbols: Some(thread_locals),
            source: format!("{} (exports trie)", source.into()),
        })
    }

    /// The first document of a TAPI v4 text stub (`.tbd`) and every library
    /// it re-exports from the same file.
    pub fn from_tbd(text: &str, source: impl Into<String>) -> Result<Self, String> {
        let (install_name, symbols, thread_locals) = tbd::tbd_exports(text)?;
        Ok(Self {
            install_name,
            symbols,
            thread_local_symbols: Some(thread_locals),
            source: format!("{} (TAPI v4 stub)", source.into()),
        })
    }

    /// The declared dylibs of a standalone link.
    pub fn from_dylib_config(config: &super::linker::DylibConfig) -> Vec<Self> {
        config
            .dylibs
            .iter()
            .map(|dylib| {
                Self::declared(
                    dylib.install_name.clone(),
                    dylib.symbols.iter().cloned(),
                    "standalone linker DylibConfig (declared)",
                )
            })
            .collect()
    }
}

/// Everything [`record_linked_image`] replays.
#[derive(Debug, Clone)]
pub struct LinkedImageRequest<'a> {
    /// Name recorded for the image (its path or a label).
    pub image_name: &'a str,
    /// The linked image's bytes.
    pub image: &'a [u8],
    /// Every relocatable object the linker was given, in link order.
    pub objects: Vec<LinkedObject<'a>>,
    /// How atoms are placed.
    pub placement: AtomPlacement<'a>,
    /// Export lists of the dylibs the image may bind to.
    pub providers: Vec<ProviderExports>,
    /// The linker's declared identity (recorded, not verified).
    pub linker: String,
}

/// One named disagreement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImageFinding {
    /// One of the `CODE_*` constants.
    pub code: &'static str,
    /// What disagreed, where.
    pub detail: String,
}

impl fmt::Display for ImageFinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}", self.code, self.detail)
    }
}

/// The replay disagreed: no record is produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkedImageRefusal {
    /// The image the request named.
    pub image_name: String,
    /// Every finding, in replay order.
    pub findings: Vec<ImageFinding>,
}

impl LinkedImageRefusal {
    /// Whether any finding carries `code`.
    pub fn has(&self, code: &str) -> bool {
        self.findings.iter().any(|finding| finding.code == code)
    }

    /// The distinct codes of the findings.
    pub fn codes(&self) -> BTreeSet<&'static str> {
        self.findings.iter().map(|finding| finding.code).collect()
    }
}

impl fmt::Display for LinkedImageRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "linked image {} is not bound to its objects ({} finding{}):",
            self.image_name,
            self.findings.len(),
            if self.findings.len() == 1 { "" } else { "s" }
        )?;
        for finding in &self.findings {
            write!(f, "\n  {finding}")?;
        }
        Ok(())
    }
}

impl std::error::Error for LinkedImageRefusal {}

/// Identity of the linked image.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ImageIdentity {
    pub name: String,
    pub size: u64,
    pub sha256: String,
    pub filetype: String,
    pub flags: String,
    pub uuid: Option<String>,
    pub install_name: Option<String>,
    /// Unslid entry address (`LC_MAIN`).
    pub entry: Option<String>,
    pub dylinker: Option<String>,
    pub rpaths: Vec<String>,
    pub load_commands: Vec<String>,
    pub code_signature: CodeSignatureRecord,
}

/// The verified ad-hoc signature.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CodeSignatureRecord {
    pub identifier: String,
    /// SHA-256 of the CodeDirectory, truncated to 20 bytes.
    pub cdhash: String,
    pub code_limit: u64,
    pub page_size: u64,
    pub linker_signed: bool,
}

/// The linker's identity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct LinkerRecord {
    /// As the caller declared it (not verified).
    pub declared: String,
    /// `LC_BUILD_VERSION` tools recorded in the image.
    pub image_tools: Vec<String>,
    /// `LC_BUILD_VERSION` platform, minimum OS and SDK.
    pub build_version: Option<String>,
}

/// One input object.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ObjectRecord {
    pub index: usize,
    /// The object's `LC_BUILD_VERSION`.
    pub build_version: Option<String>,
    pub name: String,
    pub size: u64,
    pub sha256: String,
    pub relocations: usize,
    /// SHA-256 over the canonical relocation rows
    /// (`section|offset|type|pcrel|length|extern|symbol`).
    pub inventory_digest: String,
    /// Relocation count per `ObjectRelocationKind` inventory label.
    pub inventory: BTreeMap<String, usize>,
}

/// One segment.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SegmentRecord {
    pub name: String,
    pub vmaddr: String,
    pub vmsize: String,
    pub fileoff: u64,
    pub filesize: u64,
    pub maxprot: String,
    pub initprot: String,
    pub read_only_after_fixups: bool,
}

/// One dependent dylib.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DylibRecord {
    pub ordinal: usize,
    pub command: String,
    pub install_name: String,
    pub provider: Option<String>,
}

/// Summary of the fixups dyld applies.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FixupsRecord {
    pub format: String,
    pub locations: usize,
    pub rebases: usize,
    pub binds: usize,
    pub lazy_binds: usize,
    pub weak_lookups: usize,
    /// SHA-256 over every location and its resolution, in address order.
    pub digest: String,
}

/// One imported name and how it is bound.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ImportRecord {
    pub symbol: String,
    pub ordinal: i32,
    pub library: String,
    pub weak_import: bool,
    pub provider: String,
    /// Pointer locations dyld binds to it.
    pub locations: usize,
}

/// One export.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ExportRecord {
    pub symbol: String,
    pub address: String,
    pub kind: String,
    pub weak: bool,
    /// `object index` of the definition, or `None` for a linker symbol.
    pub object: Option<usize>,
}

/// One atom and where it lies.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AtomRecord {
    pub object: usize,
    pub section: String,
    pub symbol: String,
    pub offset: u64,
    pub size: u64,
    pub address: Option<String>,
    pub image_section: Option<String>,
    pub placement: String,
}

/// One replayed relocation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RelocationRecord {
    pub object: usize,
    pub section: String,
    pub offset: u64,
    pub kind: String,
    pub symbol: String,
    pub addend: i64,
    pub site: String,
    pub target: String,
    pub resolution: String,
}

/// A fixup outside object content (the linker's own slots).
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct LinkerFixupRecord {
    pub address: String,
    pub section: String,
    pub resolution: String,
    pub used_by_replay: bool,
}

/// Counts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ReplaySummary {
    pub relocations_replayed: usize,
    /// `ARM64_RELOC_ADDEND` and `ARM64_RELOC_SUBTRACTOR` records replayed
    /// with the relocation they pair with.
    pub relocations_paired: usize,
    pub relocations_by_kind: BTreeMap<String, usize>,
    /// Relocations in sections the linker consumes (`__LD,__compact_unwind`).
    pub relocations_consumed: usize,
    /// Relocations in atoms the image does not contain.
    pub relocations_not_in_image: usize,
    pub atoms_placed: usize,
    pub atoms_not_in_image: usize,
    pub object_fixups: usize,
    pub linker_fixups: usize,
    pub read_only_after_fixup_atoms: usize,
}

/// The linked-image evidence record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct LinkedImageRecord {
    pub schema: String,
    /// The evidence strength this record carries.
    pub evidence: String,
    pub image: ImageIdentity,
    pub linker: LinkerRecord,
    pub objects: Vec<ObjectRecord>,
    pub placement: String,
    pub segments: Vec<SegmentRecord>,
    pub dylibs: Vec<DylibRecord>,
    pub fixups: FixupsRecord,
    pub imports: Vec<ImportRecord>,
    pub exports: Vec<ExportRecord>,
    pub atoms: Vec<AtomRecord>,
    pub relocations: Vec<RelocationRecord>,
    pub linker_fixups: Vec<LinkerFixupRecord>,
    pub summary: ReplaySummary,
    /// What the record does not bind.
    pub boundary: Vec<String>,
}

impl LinkedImageRecord {
    /// Pretty JSON, deterministic for a given image and inputs.
    pub fn to_json(&self) -> String {
        let mut json = serde_json::to_string_pretty(self).expect("record serializes");
        json.push('\n');
        json
    }

    /// Write the record next to `output` ([`linked_image_record_path`]).
    pub fn write_next_to(&self, output: &Path) -> std::io::Result<PathBuf> {
        let path = linked_image_record_path(output);
        std::fs::write(&path, self.to_json())?;
        Ok(path)
    }
}

/// `<output>.linked-image.json`.
pub fn linked_image_record_path(output: &Path) -> PathBuf {
    let mut path = output.as_os_str().to_owned();
    path.push(LINKED_IMAGE_RECORD_SUFFIX);
    PathBuf::from(path)
}

/// Replay `request` and produce its record, or every finding.
pub fn record_linked_image(
    request: &LinkedImageRequest<'_>,
) -> Result<LinkedImageRecord, LinkedImageRefusal> {
    replay::run(request).map_err(|findings| LinkedImageRefusal {
        image_name: request.image_name.to_string(),
        findings,
    })
}
