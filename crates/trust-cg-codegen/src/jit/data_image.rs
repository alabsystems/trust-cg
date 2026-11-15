//! JIT-owned data image for module globals.
//!
//! The raw AArch64 JIT publishes code into a read-execute mapping. A module
//! global (`Inst::GlobalAddr` -> `Opcode::GlobalRef`: a string constant, a
//! `static mut`, a vtable) needs addressable storage that the code reaches
//! with the same `ADRP`/`ADD` pair (`Page21`/`Pageoff12`) the object path
//! relocates, or through a GOT slot (`GotLoadPage21`/`GotLoadPageoff12`) for
//! a preemptible definition or an import. This module lays the module's data
//! definitions out in one image, owns the read-write mapping that holds it,
//! and records the identity manifest of the image and its relocation list.
//!
//! Boundaries. This is unchecked execution evidence: no proof obligation
//! models a JIT data image, so a verifying request refuses every data or GOT
//! fixup by name (`JitError::JitDataRelocationProofUnavailable`). Immutable
//! globals share the writable mapping (the object path's read-only
//! `__TEXT,__const` placement has no JIT counterpart). A thread-local, an
//! explicit section and a weak undefined reference are not placed; a fixup
//! that names one is refused with the recorded reason, while an unreferenced
//! one is ignored exactly as every global was before the image existed.

use std::collections::{BTreeMap, HashMap};

use super::{JitError, sys};
use crate::pipeline::{GlobalSymbolRef, ObjectGlobal};

/// Pointer slot width of every supported 64-bit target.
pub(super) const POINTER_SIZE: u64 = 8;

/// Largest data image the JIT publishes. `ADRP` reaches +-4 GiB from the
/// code; the mapping is requested adjacent to the code mapping, and this
/// bound keeps a placed image well inside that reach even when the kernel
/// honors the placement hint only approximately.
pub(super) const MAX_IMAGE_BYTES: u64 = 1 << 30;

/// One definition placed in the image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct PlacedGlobal {
    pub(super) name: String,
    /// Byte offset of the definition inside the image.
    pub(super) offset: u64,
    pub(super) size: u64,
    pub(super) align: u32,
    pub(super) mutable: bool,
    pub(super) is_external: bool,
    /// Pointer slots relocated once the code and data bases are known.
    pub(super) symbol_refs: Vec<GlobalSymbolRef>,
}

/// The planned image: placements, initial bytes (a pointer slot holds its
/// addend until relocation), imports that resolve through the caller's
/// symbol map or the process, and the globals this lane does not place.
#[derive(Debug, Clone, Default)]
pub(super) struct JitDataImageLayout {
    pub(super) placed: Vec<PlacedGlobal>,
    offsets: HashMap<String, u64>,
    pub(super) bytes: Vec<u8>,
    imports: Vec<String>,
    /// Globals the JIT cannot place, by name, with the reason a fixup that
    /// names one is refused.
    refused: BTreeMap<String, String>,
    /// Strictest placed alignment (a power of two).
    pub(super) align: u32,
}

impl JitDataImageLayout {
    /// Lay `globals` out. `None` when the module defines no global at all.
    pub(super) fn plan(
        globals: &[ObjectGlobal],
        is_function: impl Fn(&str) -> bool,
    ) -> Result<Option<Self>, JitError> {
        if globals.is_empty() {
            return Ok(None);
        }
        crate::pipeline::validate_aarch64_object_globals(globals)?;
        let mut layout = Self {
            align: 1,
            ..Self::default()
        };
        for global in globals {
            if is_function(&global.name) {
                return Err(JitError::DuplicateSymbol(global.name.clone()));
            }
            if global.is_thread_local {
                layout.refused.insert(
                    global.name.clone(),
                    "a thread-local has no JIT TLV descriptor or TPIDR_EL0 layout path".into(),
                );
                continue;
            }
            if let Some(section) = &global.section {
                layout.refused.insert(
                    global.name.clone(),
                    format!("explicit section `{section}` has no JIT placement"),
                );
                continue;
            }
            if global.is_import {
                if global.is_weak {
                    layout.refused.insert(
                        global.name.clone(),
                        "a weak undefined data reference has no JIT null-on-missing binding".into(),
                    );
                } else {
                    layout.imports.push(global.name.clone());
                }
                continue;
            }
            let overflow = || JitError::JitDataImageUnsupported {
                global: global.name.clone(),
                reason: format!("the image would exceed {MAX_IMAGE_BYTES} bytes"),
            };
            let align = u64::from(global.align.max(1));
            let start = layout.bytes.len() as u64;
            let placed_at = start
                .checked_add(align - 1)
                .map(|value| value & !(align - 1))
                .ok_or_else(overflow)?;
            let end = placed_at
                .checked_add(global.data.len() as u64)
                .filter(|end| *end <= MAX_IMAGE_BYTES)
                .ok_or_else(overflow)?;
            layout.bytes.resize(placed_at as usize, 0);
            layout.bytes.extend_from_slice(&global.data);
            debug_assert_eq!(layout.bytes.len() as u64, end);
            // Bake each addend into its slot now; the symbol address is added
            // at relocation time, exactly as the object emitters do.
            for sref in &global.symbol_refs {
                let slot = (placed_at + sref.offset) as usize;
                let bytes = layout
                    .bytes
                    .get_mut(slot..slot + POINTER_SIZE as usize)
                    .ok_or_else(|| JitError::JitDataImageUnsupported {
                        global: global.name.clone(),
                        reason: format!(
                            "pointer slot at byte {} exceeds its {} initializer bytes",
                            sref.offset,
                            global.data.len()
                        ),
                    })?;
                bytes.copy_from_slice(&sref.addend.to_le_bytes());
            }
            layout.align = layout.align.max(global.align.max(1));
            layout.offsets.insert(global.name.clone(), placed_at);
            layout.placed.push(PlacedGlobal {
                name: global.name.clone(),
                offset: placed_at,
                size: global.data.len() as u64,
                align: global.align.max(1),
                mutable: global.mutable,
                is_external: global.is_external,
                symbol_refs: global.symbol_refs.clone(),
            });
        }
        Ok(Some(layout))
    }

    /// Image offset of a placed definition.
    pub(super) fn offset_of(&self, name: &str) -> Option<u64> {
        self.offsets.get(name).copied()
    }

    /// Whether `name` is a data import (initializer-less external global).
    pub(super) fn is_import(&self, name: &str) -> bool {
        self.imports.iter().any(|import| import == name)
    }

    /// Data imports the image resolves through the symbol map or process.
    pub(super) fn import_count(&self) -> usize {
        self.imports.len()
    }

    /// Why a fixup naming `name` is refused, when the global was not placed.
    pub(super) fn refusal(&self, name: &str) -> Option<&str> {
        self.refused.get(name).map(String::as_str)
    }

    /// Whether `name` is any global this layout knows (placed, import or
    /// refused), so a fixup against it never falls through to the process
    /// symbol table.
    pub(super) fn knows(&self, name: &str) -> bool {
        self.offsets.contains_key(name) || self.is_import(name) || self.refused.contains_key(name)
    }

    /// Placed definitions and their offsets.
    pub(super) fn symbol_offsets(&self) -> HashMap<String, u64> {
        self.offsets.clone()
    }

    /// Number of pointer slots the image relocates.
    pub(super) fn relocation_count(&self) -> usize {
        self.placed
            .iter()
            .map(|global| global.symbol_refs.len())
            .sum()
    }

    /// Canonical identity bytes of the image: every placement, its initial
    /// bytes, its pointer slots (offset, target, addend) and the import list.
    /// Bound into each function's certificate-cache identity and into the
    /// buffer's live replay identity.
    pub(super) fn manifest(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(b"trust-cg.jit.aarch64-data-image.v1\0");
        out.extend_from_slice(&(self.placed.len() as u64).to_be_bytes());
        for global in &self.placed {
            push_part(&mut out, b"name", global.name.as_bytes());
            out.extend_from_slice(&global.offset.to_be_bytes());
            out.extend_from_slice(&global.size.to_be_bytes());
            out.extend_from_slice(&global.align.to_be_bytes());
            out.push(u8::from(global.mutable));
            out.push(u8::from(global.is_external));
            out.extend_from_slice(&(global.symbol_refs.len() as u64).to_be_bytes());
            for sref in &global.symbol_refs {
                out.extend_from_slice(&sref.offset.to_be_bytes());
                push_part(&mut out, b"target", sref.symbol.as_bytes());
                out.extend_from_slice(&sref.addend.to_be_bytes());
            }
        }
        out.extend_from_slice(&(self.imports.len() as u64).to_be_bytes());
        for import in &self.imports {
            push_part(&mut out, b"import", import.as_bytes());
        }
        push_part(&mut out, b"bytes", &self.bytes);
        out
    }
}

fn push_part(out: &mut Vec<u8>, label: &[u8], bytes: &[u8]) {
    out.extend_from_slice(&(label.len() as u64).to_be_bytes());
    out.extend_from_slice(label);
    out.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
    out.extend_from_slice(bytes);
}

/// Publisher record of a buffer's data image (identity only).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JitDataImageRecord {
    /// SHA-256 (lowercase hex) of the image manifest: placements, initial
    /// bytes, pointer-slot relocation list and imports.
    pub manifest_sha256: String,
    /// Bytes of the published image.
    pub image_len: usize,
    /// Placed definitions.
    pub global_count: usize,
    /// Data imports resolved through the symbol map or the process.
    pub import_count: usize,
    /// Pointer slots relocated inside the image.
    pub relocation_count: usize,
    /// Code sites patched against the image (direct `ADRP`/`ADD` pairs).
    pub direct_site_count: usize,
    /// GOT slots the code loads through (`ADRP`/`LDR` pairs).
    pub got_slot_count: usize,
}

/// The read-write mapping that holds a published data image.
///
/// Requested immediately after the code mapping so the image stays inside
/// `ADRP` reach; the direct-site patcher checks the actual distance and the
/// mapping is released by `ExecutableBuffer` teardown after the code that
/// addresses it is unmapped.
pub(super) struct JitDataRegion {
    ptr: *mut u8,
    len: usize,
}

// SAFETY: the region is an exclusively owned anonymous mapping; moving the
// owner between threads moves only that ownership.
unsafe impl Send for JitDataRegion {}
unsafe impl Sync for JitDataRegion {}

impl JitDataRegion {
    /// Map `image_len` bytes read-write, asking the kernel for the pages that
    /// follow the code mapping at `code_base`.
    pub(super) fn allocate_after(
        code_base: *mut u8,
        code_alloc_len: usize,
        image_len: usize,
    ) -> Result<Self, JitError> {
        let len = sys::page_align(image_len.max(1));
        let hint = (code_base as usize).saturating_add(code_alloc_len);
        // SAFETY: requesting a fresh anonymous RW data mapping; the hint is
        // advisory and the returned pages are owned by `self` until `Drop`.
        let ptr = unsafe { sys::mmap_data_rw(hint, len) }
            .map_err(|source| JitError::DataImageMap { len, source })?;
        Ok(Self { ptr, len })
    }

    pub(super) fn base(&self) -> u64 {
        self.ptr as u64
    }

    pub(super) fn len(&self) -> usize {
        self.len
    }

    /// Copy the relocated image into the mapping.
    pub(super) fn publish(&self, image: &[u8]) -> Result<(), JitError> {
        if image.len() > self.len {
            return Err(JitError::InvalidDataRelocation {
                offset: 0,
                detail: format!(
                    "data image of {} bytes exceeds its {}-byte mapping",
                    image.len(),
                    self.len
                ),
            });
        }
        // SAFETY: `ptr` is a live RW mapping of `len >= image.len()` bytes
        // owned by `self`; `image` is distinct heap memory.
        unsafe { std::ptr::copy_nonoverlapping(image.as_ptr(), self.ptr, image.len()) };
        Ok(())
    }
}

impl Drop for JitDataRegion {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            // SAFETY: `ptr`/`len` are the exact extent returned by
            // `mmap_data_rw`, still owned by this value.
            unsafe { sys::munmap(self.ptr, self.len) };
            self.ptr = std::ptr::null_mut();
        }
    }
}

/// A direct `ADRP`/`ADD` site that addresses a placed definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct DataAddressSite {
    pub(super) offset: u32,
    pub(super) kind: crate::macho::reloc::AArch64RelocKind,
    pub(super) symbol: String,
    /// Image offset of the addressed definition.
    pub(super) target_offset: u64,
    pub(super) addend: i64,
}

/// An `ADRP`/`LDR` site that loads a symbol address from a JIT GOT slot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct GotLoadSite {
    pub(super) offset: u32,
    pub(super) kind: crate::macho::reloc::AArch64RelocKind,
    pub(super) symbol: String,
}

/// Patch one direct data site in the heap image at its final addresses.
///
/// `ADRP`: the page delta between the site and the target. `ADD`: the
/// target's low 12 bits. The pre-patch word must be a general-register
/// `ADRP` or an unshifted 64-bit `ADD`, as the local function-address path
/// requires; every other bit is preserved.
pub(super) fn patch_data_address_site(
    image: &mut [u8],
    site: &DataAddressSite,
    code_base: u64,
    data_base: u64,
) -> Result<(), JitError> {
    use crate::macho::fixup::{apply_page21, apply_pageoff12};
    use crate::macho::reloc::AArch64RelocKind;

    let invalid = |detail: String| JitError::InvalidDataRelocation {
        offset: site.offset,
        detail,
    };
    if site.offset & 3 != 0 {
        return Err(invalid("patch site is not 4-byte aligned".into()));
    }
    let start = site.offset as usize;
    let bytes: &mut [u8; 4] = image
        .get_mut(start..start.saturating_add(4))
        .and_then(|bytes| bytes.try_into().ok())
        .ok_or_else(|| invalid("patch site is outside the image".into()))?;
    let site_address = code_base
        .checked_add(u64::from(site.offset))
        .ok_or_else(|| invalid("site address overflows".into()))?;
    let target = data_base
        .checked_add(site.target_offset)
        .and_then(|address| address.checked_add_signed(site.addend))
        .ok_or_else(|| invalid("target address overflows".into()))?;
    let word = u32::from_le_bytes(*bytes);
    match site.kind {
        AArch64RelocKind::Page21 => {
            if word & 0x9f00_0000 != 0x9000_0000 || word & 31 == 31 {
                return Err(invalid(
                    "Page21 requires ADRP to a general-purpose register".into(),
                ));
            }
            let pages = (target >> 12) as i64 - (site_address >> 12) as i64;
            apply_page21(bytes, pages).map_err(|error| JitError::JitDataRelocationOutOfRange {
                symbol: site.symbol.clone(),
                site: site_address,
                target,
                detail: error.to_string(),
            })?;
        }
        AArch64RelocKind::Pageoff12 => {
            if word & 0xffc0_0000 != 0x9100_0000 || word & 31 == 31 || (word >> 5) & 31 == 31 {
                return Err(invalid(
                    "Pageoff12 requires unshifted 64-bit ADD with general-purpose registers".into(),
                ));
            }
            apply_pageoff12(bytes, (target & 0xfff) as u32, 0);
        }
        other => return Err(invalid(format!("unsupported data address kind {other:?}"))),
    }
    Ok(())
}

/// Patch one GOT-load site in image space (position independent given a
/// 4 KiB-aligned base): `ADRP` to the slot's page, `LDR Xt, [Xn, #lo12]`
/// with the 8-byte-scaled slot offset.
pub(super) fn patch_got_load_site(
    code: &mut [u8],
    site: &GotLoadSite,
    slot_offset: u64,
) -> Result<(), JitError> {
    use crate::macho::fixup::apply_page21;
    use crate::macho::reloc::AArch64RelocKind;

    let invalid = |detail: String| JitError::InvalidDataRelocation {
        offset: site.offset,
        detail,
    };
    if site.offset & 3 != 0 {
        return Err(invalid("patch site is not 4-byte aligned".into()));
    }
    if !slot_offset.is_multiple_of(POINTER_SIZE) {
        return Err(invalid("GOT slot is not 8-byte aligned".into()));
    }
    let start = site.offset as usize;
    let bytes: &mut [u8; 4] = code
        .get_mut(start..start.saturating_add(4))
        .and_then(|bytes| bytes.try_into().ok())
        .ok_or_else(|| invalid("patch site is outside the image".into()))?;
    let word = u32::from_le_bytes(*bytes);
    match site.kind {
        AArch64RelocKind::GotLoadPage21 => {
            if word & 0x9f00_0000 != 0x9000_0000 || word & 31 == 31 {
                return Err(invalid(
                    "GotLoadPage21 requires ADRP to a general-purpose register".into(),
                ));
            }
            let pages = (slot_offset >> 12) as i64 - (u64::from(site.offset) >> 12) as i64;
            apply_page21(bytes, pages).map_err(|error| invalid(error.to_string()))?;
        }
        AArch64RelocKind::GotLoadPageoff12 => {
            // LDR Xt, [Xn, #imm12] (64-bit, unsigned scaled offset).
            if word & 0xffc0_0000 != 0xf940_0000 || (word >> 5) & 31 == 31 {
                return Err(invalid(
                    "GotLoadPageoff12 requires a 64-bit unsigned-offset LDR from a general-purpose base"
                        .into(),
                ));
            }
            let imm12 = ((slot_offset & 0xfff) / POINTER_SIZE) as u32;
            let patched = (word & !(0xfff << 10)) | (imm12 << 10);
            *bytes = patched.to_le_bytes();
        }
        other => return Err(invalid(format!("unsupported GOT load kind {other:?}"))),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::macho::reloc::AArch64RelocKind;

    fn global(name: &str, data: Vec<u8>, align: u32) -> ObjectGlobal {
        ObjectGlobal {
            name: name.into(),
            data,
            mutable: true,
            is_external: true,
            symbol_refs: vec![],
            is_thread_local: false,
            is_import: false,
            is_weak: false,
            align,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            section: None,
            comdat: false,
        }
    }

    #[test]
    fn plan_places_globals_at_their_alignment_and_bakes_addends() {
        let mut table = global("table", vec![0; 16], 8);
        table.symbol_refs = vec![GlobalSymbolRef {
            offset: 8,
            symbol: "f".into(),
            addend: 24,
        }];
        let globals = [
            global("bytes", b"hello".to_vec(), 1),
            global("word", 7u64.to_le_bytes().to_vec(), 8),
            table,
        ];
        let layout = JitDataImageLayout::plan(&globals, |_| false)
            .unwrap()
            .unwrap();
        assert_eq!(layout.offset_of("bytes"), Some(0));
        assert_eq!(layout.offset_of("word"), Some(8));
        assert_eq!(layout.offset_of("table"), Some(16));
        assert_eq!(&layout.bytes[0..5], b"hello");
        assert_eq!(&layout.bytes[8..16], &7u64.to_le_bytes());
        assert_eq!(&layout.bytes[24..32], &24i64.to_le_bytes());
        assert_eq!(layout.align, 8);
        assert_eq!(layout.relocation_count(), 1);
        let manifest = layout.manifest();
        assert!(manifest.starts_with(b"trust-cg.jit.aarch64-data-image.v1\0"));
        let mut other = layout.clone();
        other.placed[2].symbol_refs[0].addend = 25;
        assert_ne!(manifest, other.manifest());
    }

    #[test]
    fn plan_records_refusals_imports_and_function_collisions() {
        let mut tls = global("tls", vec![0; 8], 8);
        tls.is_thread_local = true;
        let mut import = global("imported", vec![], 8);
        import.is_import = true;
        let mut weak = global("weak", vec![], 8);
        weak.is_import = true;
        weak.is_weak = true;
        let layout = JitDataImageLayout::plan(&[tls, import, weak], |_| false)
            .unwrap()
            .unwrap();
        assert!(layout.refusal("tls").unwrap().contains("thread-local"));
        assert!(layout.is_import("imported"));
        assert!(layout.refusal("weak").unwrap().contains("weak undefined"));
        assert!(layout.knows("tls") && layout.knows("imported") && layout.knows("weak"));
        assert!(!layout.knows("elsewhere"));
        assert!(layout.placed.is_empty());
        assert!(matches!(
            JitDataImageLayout::plan(&[global("f", vec![1], 1)], |name| name == "f"),
            Err(JitError::DuplicateSymbol(name)) if name == "f"
        ));
        assert!(JitDataImageLayout::plan(&[], |_| false).unwrap().is_none());
    }

    /// A pointer slot naming a thread-local is refused by the shared object
    /// global validator before any placement, even though the thread-local
    /// itself would only be recorded as a lazy per-name refusal.
    #[test]
    fn plan_refuses_a_pointer_slot_naming_a_thread_local() {
        let mut tls = global("tls", vec![0; 8], 8);
        tls.is_thread_local = true;
        let mut table = global("table", vec![0; 8], 8);
        table.symbol_refs = vec![GlobalSymbolRef {
            offset: 0,
            symbol: "tls".into(),
            addend: 0,
        }];
        let error = JitDataImageLayout::plan(&[tls, table], |_| false)
            .expect_err("a data slot naming a thread-local is refused")
            .to_string();
        assert!(
            error.contains("[TCG-TLS-SLOT-TARGET]")
                && error.contains("`table`")
                && error.contains("thread-local `tls`"),
            "unexpected diagnostic: {error}"
        );
    }

    #[test]
    fn direct_site_patches_adrp_and_add_at_real_addresses() {
        let mut image = vec![0u8; 16];
        image[4..8].copy_from_slice(&0x9000_0007u32.to_le_bytes());
        image[8..12].copy_from_slice(&0x9100_00e9u32.to_le_bytes());
        let adrp = DataAddressSite {
            offset: 4,
            kind: AArch64RelocKind::Page21,
            symbol: "g".into(),
            target_offset: 0x18,
            addend: 4,
        };
        let add = DataAddressSite {
            offset: 8,
            kind: AArch64RelocKind::Pageoff12,
            ..adrp.clone()
        };
        let code_base = 0x1_0000_4000;
        let data_base = 0x1_0001_8000;
        patch_data_address_site(&mut image, &adrp, code_base, data_base).unwrap();
        patch_data_address_site(&mut image, &add, code_base, data_base).unwrap();
        let word = u32::from_le_bytes(image[4..8].try_into().unwrap());
        let immediate = (((word >> 5) & 0x7ffff) << 2) | ((word >> 29) & 3);
        // page(0x1_0001_801c) - page(0x1_0000_4004) = 0x14 pages.
        assert_eq!(immediate, 0x14);
        assert_eq!(word & 31, 7);
        let word = u32::from_le_bytes(image[8..12].try_into().unwrap());
        assert_eq!((word >> 10) & 0xfff, 0x1c);
        assert_eq!(word & 31, 9);
        assert_eq!((word >> 5) & 31, 7);
        // Out of ADRP reach fails closed by name.
        assert!(matches!(
            patch_data_address_site(&mut image, &adrp, code_base, code_base + (1 << 33)),
            Err(JitError::JitDataRelocationOutOfRange { .. })
        ));
        // A non-ADRP word at a Page21 site is refused.
        image[4..8].copy_from_slice(&0x1000_0007u32.to_le_bytes());
        assert!(matches!(
            patch_data_address_site(&mut image, &adrp, code_base, data_base),
            Err(JitError::InvalidDataRelocation { offset: 4, .. })
        ));
    }

    #[test]
    fn got_site_patches_adrp_and_scaled_ldr_in_image_space() {
        let mut code = vec![0u8; 0x2010];
        code[0x1000..0x1004].copy_from_slice(&0x9000_0008u32.to_le_bytes());
        code[0x1004..0x1008].copy_from_slice(&0xf940_0108u32.to_le_bytes());
        let adrp = GotLoadSite {
            offset: 0x1000,
            kind: AArch64RelocKind::GotLoadPage21,
            symbol: "g".into(),
        };
        let ldr = GotLoadSite {
            offset: 0x1004,
            kind: AArch64RelocKind::GotLoadPageoff12,
            symbol: "g".into(),
        };
        patch_got_load_site(&mut code, &adrp, 0x2008).unwrap();
        patch_got_load_site(&mut code, &ldr, 0x2008).unwrap();
        let word = u32::from_le_bytes(code[0x1000..0x1004].try_into().unwrap());
        let immediate = (((word >> 5) & 0x7ffff) << 2) | ((word >> 29) & 3);
        assert_eq!(immediate, 1, "one page forward");
        let word = u32::from_le_bytes(code[0x1004..0x1008].try_into().unwrap());
        assert_eq!((word >> 10) & 0xfff, 1, "slot 8 -> scaled imm12 of 1");
        assert_eq!(word & 31, 8);
        assert!(matches!(
            patch_got_load_site(&mut code, &ldr, 0x2004),
            Err(JitError::InvalidDataRelocation { .. })
        ));
        code[0x1004..0x1008].copy_from_slice(&0xb940_0108u32.to_le_bytes());
        assert!(matches!(
            patch_got_load_site(&mut code, &ldr, 0x2008),
            Err(JitError::InvalidDataRelocation { .. })
        ));
    }
}
