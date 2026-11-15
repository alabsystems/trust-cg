//! Independent replay of the local ADRP/ADD *relocation effect*.
//!
//! The immutable inventory is captured from pre-patch words and resolved local
//! entry points, not from the patcher's output. Replay decodes the final words
//! without using the relocation encoders. This is a publication invariant, NOT
//! a source-to-machine certificate: ADD's incoming register is a premise, and
//! neither callback value flow nor function/ABI correctness is established here.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use super::{
    Fixup, JitError, validate_local_function_address_image, validate_local_function_address_ranges,
};
use crate::macho::reloc::AArch64RelocKind;

#[derive(Clone, Copy)]
enum AddressPart {
    Page,
    Offset,
}

impl AddressPart {
    fn immediate_mask(self) -> u32 {
        match self {
            Self::Page => 0x60ff_ffe0,
            Self::Offset => 0x003f_fc00,
        }
    }
}

struct RelocationRow {
    offset: u32,
    original_word: u32,
    target: u64,
    part: AddressPart,
}

/// Private, live-resolution inventory. It carries no proof or cache authority.
pub(super) struct LocalAddressReplay {
    function_image_len: usize,
    rows: Vec<RelocationRow>,
}

/// One captured row in a plain, persistable form: the pre-patch word, the
/// image-relative site and target, and which half of the ADRP/ADD pair it is.
/// A [`super::RelocatableImage`] carries these so a later process can re-run
/// [`LocalAddressReplay::replay`] at ITS mapped base; the words themselves are
/// already patched image-relative (page arithmetic is base-invariant for any
/// 4 KiB-aligned base, which `replay` checks).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ExportedAddressRow {
    pub(super) offset: u32,
    pub(super) original_word: u32,
    pub(super) target: u64,
    pub(super) page: bool,
}

fn valid_original_word(part: AddressPart, original_word: u32) -> bool {
    match part {
        AddressPart::Page => original_word & 0x9f00_0000 == 0x9000_0000 && original_word & 31 != 31,
        AddressPart::Offset => {
            original_word & 0xffc0_0000 == 0x9100_0000
                && original_word & 31 != 31
                && (original_word >> 5) & 31 != 31
        }
    }
}

#[cfg(test)]
thread_local! {
    pub(super) static CORRUPT_RELOCATED_WORD: std::cell::Cell<Option<u32>> = const { std::cell::Cell::new(None) };
}

fn rejected(offset: u32, detail: impl Into<String>) -> JitError {
    JitError::LocalFunctionAddressReplayRejected {
        offset,
        detail: detail.into(),
    }
}

fn word_at(image: &[u8], offset: u32) -> Result<u32, JitError> {
    let start = offset as usize;
    let end = start
        .checked_add(4)
        .ok_or_else(|| rejected(offset, "instruction extent overflows"))?;
    let bytes = image
        .get(start..end)
        .and_then(|bytes| <[u8; 4]>::try_from(bytes).ok())
        .ok_or_else(|| rejected(offset, "instruction is outside the image"))?;
    Ok(u32::from_le_bytes(bytes))
}

/// Only 4-byte instruction patches and 8-byte literal patches exist on this
/// raw path. At most three aligned words intersect one such patch; width never
/// becomes a queued range or an image-sized bitmap.
fn reject_overlapping_patch(
    local_words: &HashMap<u64, usize>,
    start: u64,
    width: u64,
    own_fixup: Option<usize>,
) -> Result<(), JitError> {
    let end = start
        .checked_add(width)
        .ok_or_else(|| rejected(0, "patch extent overflows"))?;
    for word in (start / 4)..=((end - 1) / 4) {
        if let Some(&owner) = local_words.get(&(word * 4))
            && Some(owner) != own_fixup
        {
            return Err(rejected(
                (word * 4) as u32,
                "another instruction or literal patch overlaps a local address relocation",
            ));
        }
    }
    Ok(())
}

impl LocalAddressReplay {
    #[cfg(test)]
    pub(super) fn corrupt_image_if_requested(&self, image: &mut [u8]) {
        if let Some(mask) = CORRUPT_RELOCATED_WORD.with(|slot| slot.take()) {
            let offset = self.rows[0].offset;
            let word = word_at(image, offset).expect("test relocation site exists");
            image[offset as usize..offset as usize + 4]
                .copy_from_slice(&(word ^ mask).to_le_bytes());
        }
    }

    /// Capture ALL local address fixups before ANY code patch. Symbol resolution
    /// is supplied by the existing JIT resolver and performed once per row.
    /// Its result must be an exact retained entry, not merely an in-image byte;
    /// `Ok(None)` marks a page site that belongs to another patcher (a
    /// data-image address), which is kept out of the rows but still counted
    /// as a 4-byte patch for the overlap check.
    /// Capture costs O(functions + fixups + literal patches) expected work and
    /// O(functions + local address fixups) temporary scratch. Only rows survive.
    pub(super) fn capture(
        code: &[u8],
        fixups: &[Fixup],
        ranges: &[(String, Range<u64>)],
        empty_body: Option<String>,
        literal_sites: impl Iterator<Item = usize>,
        mut resolve: impl FnMut(&Fixup) -> Result<Option<u64>, JitError>,
    ) -> Result<Self, JitError> {
        validate_local_function_address_ranges(ranges, code.len(), empty_body)?;
        let mut entries = HashSet::with_capacity(ranges.len());
        let mut previous_end = 0;
        for (_, range) in ranges {
            if range.start != previous_end || !entries.insert(range.start) {
                return Err(rejected(
                    0,
                    "function ranges overlap, leave a gap or repeat an entry",
                ));
            }
            previous_end = range.end;
        }
        if previous_end != code.len() as u64 {
            return Err(rejected(
                0,
                "function ranges do not cover the pre-patch image",
            ));
        }
        let mut rows = Vec::new();
        let mut local_words = HashMap::new();
        for (index, fixup) in fixups.iter().enumerate() {
            let part = match fixup.kind {
                AArch64RelocKind::Page21 => AddressPart::Page,
                AArch64RelocKind::Pageoff12 => AddressPart::Offset,
                _ => continue,
            };
            let offset = fixup.offset;
            let Some(target) = resolve(fixup)? else {
                continue;
            };
            if offset & 3 != 0 || fixup.addend != 0 || fixup.tls_model.is_some() {
                return Err(rejected(
                    offset,
                    "local address relocation requires an aligned site, zero addend and no TLS",
                ));
            }
            if !entries.contains(&target) {
                return Err(rejected(
                    offset,
                    "resolved target is not an exact retained function entry",
                ));
            }
            let original_word = word_at(code, offset)?;
            if !valid_original_word(part, original_word) {
                return Err(rejected(
                    offset,
                    "pre-patch word is not a supported general-register ADRP or unshifted 64-bit ADD",
                ));
            }
            if local_words.insert(u64::from(offset), index).is_some() {
                return Err(rejected(offset, "duplicate local address relocation site"));
            }
            rows.push(RelocationRow {
                offset,
                original_word,
                target,
                part,
            });
        }
        // Include branch fixups (even unaligned malformed ones), not just
        // address rows. Otherwise a later branch patch could change a word
        // whose original value had already been captured.
        for (index, fixup) in fixups.iter().enumerate() {
            reject_overlapping_patch(&local_words, u64::from(fixup.offset), 4, Some(index))?;
        }
        for offset in literal_sites {
            let end = offset
                .checked_add(8)
                .ok_or_else(|| rejected(0, "literal extent overflows"))?;
            if end > code.len() {
                return Err(rejected(0, "profile literal is outside the function image"));
            }
            reject_overlapping_patch(&local_words, offset as u64, 8, None)?;
        }
        Ok(Self {
            function_image_len: code.len(),
            rows,
        })
    }

    /// Length of the function image the rows were captured against.
    pub(super) fn function_image_len(&self) -> usize {
        self.function_image_len
    }

    /// The captured rows, in capture order, for a relocatable image.
    pub(super) fn export_rows(&self) -> Vec<ExportedAddressRow> {
        self.rows
            .iter()
            .map(|row| ExportedAddressRow {
                offset: row.offset,
                original_word: row.original_word,
                target: row.target,
                page: matches!(row.part, AddressPart::Page),
            })
            .collect()
    }

    /// Rebuild an inventory from persisted rows. Every structural premise
    /// `capture` established is re-checked here, because the rows come from
    /// outside this process: aligned in-image sites, no duplicate site,
    /// targets inside the function image, and pre-patch words of the one
    /// supported ADRP / unshifted 64-bit ADD shape. What `capture` proved
    /// about the RESOLUTION (an exact retained entry) is re-proved by the
    /// caller against the image's function ranges.
    pub(super) fn from_exported_rows(
        function_image_len: usize,
        rows: &[ExportedAddressRow],
    ) -> Result<Self, JitError> {
        let mut seen = HashSet::with_capacity(rows.len());
        let mut out = Vec::with_capacity(rows.len());
        for row in rows {
            let part = if row.page {
                AddressPart::Page
            } else {
                AddressPart::Offset
            };
            let end = (row.offset as usize).checked_add(4);
            if row.offset & 3 != 0 || end.is_none_or(|end| end > function_image_len) {
                return Err(rejected(
                    row.offset,
                    "persisted relocation site is unaligned or outside the function image",
                ));
            }
            if row.target >= function_image_len as u64 {
                return Err(rejected(
                    row.offset,
                    "persisted relocation target is outside the function image",
                ));
            }
            if !valid_original_word(part, row.original_word) {
                return Err(rejected(
                    row.offset,
                    "persisted pre-patch word is not a supported ADRP or unshifted 64-bit ADD",
                ));
            }
            if !seen.insert(row.offset) {
                return Err(rejected(row.offset, "duplicate persisted relocation site"));
            }
            out.push(RelocationRow {
                offset: row.offset,
                original_word: row.original_word,
                target: row.target,
                part,
            });
        }
        Ok(Self {
            function_image_len,
            rows: out,
        })
    }

    /// Apply with the existing encoder only AFTER capture has completed. This
    /// method cannot modify the immutable originals replay will later consume.
    pub(super) fn patch(&self, code: &mut [u8]) -> Result<(), JitError> {
        for row in &self.rows {
            let kind = match row.part {
                AddressPart::Page => AArch64RelocKind::Page21,
                AddressPart::Offset => AArch64RelocKind::Pageoff12,
            };
            let start = row.offset as usize;
            let bytes: &mut [u8; 4] = code
                .get_mut(start..start.saturating_add(4))
                .and_then(|bytes| bytes.try_into().ok())
                .ok_or_else(|| rejected(row.offset, "patch site is outside the image"))?;
            super::patch_local_function_address_instruction(bytes, kind, row.offset, row.target)?;
        }
        Ok(())
    }

    /// Veneer literals are appended after the captured function image. Refuse
    /// any misplaced literal even when it would happen not to hit a page row.
    pub(super) fn check_appended_literal(
        &self,
        offset: usize,
        image_len: usize,
    ) -> Result<(), JitError> {
        if offset < self.function_image_len
            || offset.checked_add(8).is_none_or(|end| end > image_len)
        {
            return Err(rejected(
                0,
                "veneer literal is not wholly in the appended image",
            ));
        }
        Ok(())
    }

    /// Decode the final HEAP image at its actual allocated base, before copy
    /// and RX publication. The existing read-back hash subsequently binds these
    /// exact bytes to the mapping; that hash is integrity, not source equality.
    ///
    /// ADRP: the decoded operation writes page(exact local entry).
    /// ADD: the decoded operation adds low12(exact local entry), with Rn/Rd
    /// unchanged. That is CONDITIONAL address arithmetic; this checker does
    /// not assert Rn's incoming value or require an adjacent ADRP/ADD pair.
    pub(super) fn replay(&self, image: &[u8], base: u64) -> Result<(), JitError> {
        validate_local_function_address_image(base)?;
        if image.len() < self.function_image_len || base.checked_add(image.len() as u64).is_none() {
            return Err(rejected(
                0,
                "mapped image is truncated or its endpoint overflows",
            ));
        }
        for row in &self.rows {
            let word = word_at(image, row.offset)?;
            if word & !row.part.immediate_mask() != row.original_word & !row.part.immediate_mask() {
                return Err(rejected(
                    row.offset,
                    "relocation modified opcode, register, shift or other non-immediate bits",
                ));
            }
            // The whole image endpoint was checked above, so both additions
            // are safe. Use i128 for the decoded signed page arithmetic: no
            // wrapping host arithmetic may hide an out-of-address-space result.
            let target = base + row.target;
            match row.part {
                AddressPart::Page => {
                    let immediate = (((word >> 5) & 0x7ffff) << 2) | ((word >> 29) & 3);
                    let signed_pages = if immediate & (1 << 20) != 0 {
                        i128::from(immediate) - (1 << 21)
                    } else {
                        i128::from(immediate)
                    };
                    let pc_page = (base + u64::from(row.offset)) & !0xfff;
                    let decoded_page = i128::from(pc_page) + signed_pages * 4096;
                    if decoded_page != i128::from(target & !0xfff) {
                        return Err(rejected(
                            row.offset,
                            "decoded ADRP does not produce the resolved target page",
                        ));
                    }
                }
                AddressPart::Offset => {
                    if u64::from((word >> 10) & 0xfff) != target & 0xfff {
                        return Err(rejected(
                            row.offset,
                            "decoded ADD immediate is not the resolved target's low12",
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(site: u32, target: u64) -> (Vec<u8>, Vec<Fixup>, Vec<(String, Range<u64>)>) {
        let mut image = vec![0; 0x8000];
        // Different Rd/Rn is valid; the ADD input value is deliberately not
        // asserted here. Nonzero old immediates exercise clear-and-replace.
        image[site as usize..site as usize + 4].copy_from_slice(&0xf0ff_ffe7u32.to_le_bytes());
        image[site as usize + 4..site as usize + 8].copy_from_slice(&0x913f_fce9u32.to_le_bytes());
        let fixups = vec![Fixup::adrp(site, 1), Fixup::pageoff(site + 4, 1)];
        let ranges = vec![
            ("before".into(), 0..target),
            ("target".into(), target..image.len() as u64),
        ];
        (image, fixups, ranges)
    }

    fn capture(
        image: &[u8],
        fixups: &[Fixup],
        ranges: &[(String, Range<u64>)],
        target: u64,
    ) -> Result<LocalAddressReplay, JitError> {
        LocalAddressReplay::capture(image, fixups, ranges, None, std::iter::empty(), |_| {
            Ok(Some(target))
        })
    }

    #[test]
    fn replay_decodes_signed_pages_at_actual_aligned_bases_and_preserves_registers() {
        for (site, target) in [(0x1004, 0x6234), (0x5004, 0x1234), (0x1004, 0x1234)] {
            let (mut image, fixups, ranges) = fixture(site, target);
            let mut resolutions = 0;
            let replay = LocalAddressReplay::capture(
                &image,
                &fixups,
                &ranges,
                None,
                std::iter::empty(),
                |_| {
                    resolutions += 1;
                    Ok(Some(target))
                },
            )
            .unwrap();
            assert_eq!(resolutions, 2, "one resolution per fixup");
            replay.patch(&mut image).unwrap();
            for base in [0, 0x1000, 0x4000, 0x1_2345_0000] {
                replay.replay(&image, base).unwrap();
            }
            assert_eq!(word_at(&image, site).unwrap() & 31, 7);
            assert_eq!((word_at(&image, site + 4).unwrap() >> 5) & 31, 7);
            assert_eq!(word_at(&image, site + 4).unwrap() & 31, 9);
        }
    }

    #[test]
    fn replay_rejects_every_single_bit_corruption_and_unapplied_relocations() {
        let (mut image, fixups, ranges) = fixture(0x1004, 0x6234);
        let replay = capture(&image, &fixups, &ranges, 0x6234).unwrap();
        assert!(replay.replay(&image, 0x4000).is_err());
        replay.patch(&mut image).unwrap();
        for site in [0x1004u32, 0x1008] {
            let original = word_at(&image, site).unwrap();
            for bit in 0..32 {
                image[site as usize..site as usize + 4]
                    .copy_from_slice(&(original ^ (1 << bit)).to_le_bytes());
                assert!(
                    matches!(
                        replay.replay(&image, 0x4000),
                        Err(JitError::LocalFunctionAddressReplayRejected { .. })
                    ),
                    "site={site:#x}, bit={bit}"
                );
            }
            image[site as usize..site as usize + 4].copy_from_slice(&original.to_le_bytes());
        }
        replay.replay(&image, 0x4000).unwrap();
    }

    #[test]
    fn capture_rejects_non_entries_bad_ranges_addends_tls_sites_and_opcodes() {
        let (image, fixups, ranges) = fixture(0x1004, 0x6234);
        for target in [0x6235, 0x6238, image.len() as u64, u64::MAX] {
            assert!(capture(&image, &fixups, &ranges, target).is_err());
        }
        for invalid in [
            vec![("empty".into(), 0..0)],
            vec![("past".into(), 0..0x8004)],
            vec![("truncated".into(), 0..0x7ffc)],
            vec![("prefix_gap".into(), 4..0x8000)],
            vec![("a".into(), 0..0x6230), ("gap".into(), 0x6234..0x8000)],
            vec![("a".into(), 0..0x7000), ("b".into(), 0x6234..0x8000)],
        ] {
            assert!(capture(&image, &fixups, &invalid, 0).is_err());
        }
        assert!(
            LocalAddressReplay::capture(
                &image,
                &fixups,
                &ranges,
                Some("empty".into()),
                std::iter::empty(),
                |_| Ok(Some(0x6234))
            )
            .is_err()
        );
        for addend in [-1, 1, i64::MIN, i64::MAX] {
            let mut bad = fixups.clone();
            bad[0].addend = addend;
            assert!(capture(&image, &bad, &ranges, 0x6234).is_err());
        }
        let mut bad = fixups.clone();
        bad[1].tls_model = Some(trust_cg_ir::TlsModel::Tlv);
        assert!(capture(&image, &bad, &ranges, 0x6234).is_err());
        for site in [2, image.len() as u32, u32::MAX] {
            let mut bad = fixups.clone();
            bad[0].offset = site;
            assert!(capture(&image, &bad, &ranges, 0x6234).is_err());
        }
        for (index, word) in [
            (0, 0x1000_0007u32),
            (0, 0x9000_001f),
            (1, 0x9140_00e9),
            (1, 0x1100_00e9),
            (1, 0x9100_03e9),
            (1, 0x9100_00ff),
        ] {
            let mut bad_image = image.clone();
            let site = fixups[index].offset as usize;
            bad_image[site..site + 4].copy_from_slice(&word.to_le_bytes());
            assert!(capture(&bad_image, &fixups, &ranges, 0x6234).is_err());
        }
    }

    #[test]
    fn capture_rejects_duplicate_and_partial_branch_or_literal_overlap() {
        let (image, fixups, ranges) = fixture(0x1004, 0x6234);
        let mut duplicate = fixups.clone();
        duplicate.push(fixups[0].clone());
        assert!(capture(&image, &duplicate, &ranges, 0x6234).is_err());
        for offset in 0x1001..0x100c {
            let mut collision = fixups.clone();
            collision.push(Fixup::branch(offset, 1));
            assert!(
                capture(&image, &collision, &ranges, 0x6234).is_err(),
                "branch {offset:#x}"
            );
        }
        for offset in 0x0ffd..0x100c {
            assert!(
                LocalAddressReplay::capture(
                    &image,
                    &fixups,
                    &ranges,
                    None,
                    std::iter::once(offset),
                    |_| Ok(Some(0x6234))
                )
                .is_err(),
                "literal {offset:#x}"
            );
        }
        LocalAddressReplay::capture(
            &image,
            &fixups,
            &ranges,
            None,
            [0x0ffc, 0x100c].into_iter(),
            |_| Ok(Some(0x6234)),
        )
        .unwrap();
        for offset in [usize::MAX, image.len() - 4] {
            assert!(
                LocalAddressReplay::capture(
                    &image,
                    &fixups,
                    &ranges,
                    None,
                    std::iter::once(offset),
                    |_| Ok(Some(0x6234))
                )
                .is_err()
            );
        }
    }

    #[test]
    fn replay_checks_image_extent_alignment_and_appended_veneer_literals() {
        let (mut image, fixups, ranges) = fixture(0x1004, 0x6234);
        let replay = capture(&image, &fixups, &ranges, 0x6234).unwrap();
        replay.patch(&mut image).unwrap();
        assert!(replay.replay(&image[..image.len() - 1], 0x4000).is_err());
        for base in [1, 0x1004, !0xfff_u64] {
            assert!(replay.replay(&image, base).is_err());
        }
        let original_len = image.len();
        image.extend_from_slice(&[0; 16]);
        replay.replay(&image, 0x4000).unwrap();
        replay
            .check_appended_literal(original_len, image.len())
            .unwrap();
        replay
            .check_appended_literal(original_len + 8, image.len())
            .unwrap();
        for offset in [0x1004, original_len - 4, original_len + 12, usize::MAX] {
            assert!(replay.check_appended_literal(offset, image.len()).is_err());
        }
    }

    #[test]
    fn add_replay_preserves_distinct_registers_without_asserting_input_dataflow() {
        let (mut image, fixups, ranges) = fixture(0x1004, 0x6234);
        // Rn=x11 rather than ADRP's x7: valid conditional ADD semantics, NOT
        // proof of a complete address materialization. Core/proof gates remain
        // closed because that separate value-flow premise is not checked here.
        image[0x1008..0x100c].copy_from_slice(&0x9100_0169u32.to_le_bytes());
        let replay = capture(&image, &fixups, &ranges, 0x6234).unwrap();
        replay.patch(&mut image).unwrap();
        replay.replay(&image, 0x4000).unwrap();
        assert_eq!((word_at(&image, 0x1008).unwrap() >> 5) & 31, 11);
    }
}
