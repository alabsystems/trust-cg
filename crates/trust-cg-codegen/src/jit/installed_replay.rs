// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Independent replay at the installed-artifact boundary (ledger `L11-P2`).
//!
//! A verifying AArch64 JIT publication (`JitConfig::verify`, the route
//! `AlwaysVerify` and `CachedVerified` select) is sealed read-execute, its
//! instruction-cache maintenance walk has run and every function has its
//! certificate. Before any function pointer is handed out, this replay reads
//! the bytes the process will execute back FROM THE EXECUTABLE MAPPING and
//! re-checks them against what was certified:
//!
//! * **Certified words.** Every installed word of a certified function's
//!   range must equal the word at the same offset of the publisher's image
//!   buffer, except the 64-bit runtime literals below. The function's
//!   certificate digest (`JitCertificate::normalized_machine_code_sha256`)
//!   is computed in this publication over that buffer's range, after the
//!   image-internal branch and veneer patches (a cache hit is keyed by the
//!   same digest of the same range). The replay re-hashes the range and
//!   requires that digest, which ties the compared baseline to the bytes
//!   the certificate names. On the publisher's own path both hashes come
//!   from the same buffer, so this check cannot fail there: it refuses only
//!   a baseline other than the certified one (a construction error, reached
//!   by a unit fixture). The independent content is the re-read of the
//!   sealed mapping and the decoder checks below, not the digest.
//! * **Branch relocations.** At every `BRANCH26` site inside a certified
//!   range the INSTALLED word is decoded by the verifier's A64 field decoder
//!   (`trust_cg_verify::aarch64_instruction_word_proofs::decode_word`,
//!   written from the Arm ARM encoding tables, not by inverting this crate's
//!   encoder or its patcher). Its class (B or BL) must be the certified
//!   word's, and the target it encodes at the ACTUAL mapped address must be
//!   the entry the relocation inventory names: a module function's entry, or
//!   the veneer of the named external.
//! * **Veneers.** Every veneer such a branch reaches must decode, word by
//!   word, as `LDR X16, <literal at +8>` and `BR X16` (fields extracted here
//!   from the Arm ARM `LDR (literal)` and `BR` encodings), and its installed
//!   literal must hold the address resolved for that external.
//! * **Runtime literals.** Every 64-bit literal the publisher patched inside
//!   a certified range (profile counter and timing-state pointers) must hold
//!   the value the publisher was given.
//! * **Relocation coverage.** A relocation of any other kind inside a
//!   certified range is refused by name: this replay re-derives only branch
//!   targets, and the verifying publisher already refuses address, data and
//!   GOT relocations before mapping.
//!
//! A disagreement is a [`JitError::InstalledArtifactReplayRejected`] naming
//! the function and the image offset; the mapping is then unmapped and no
//! function pointer exists.
//!
//! What this does not establish: any semantic claim of the certificate (that
//! is the verifier's, and its strength is the certificate's); that a named
//! external is the right function (its address is what the extern table or
//! the process resolver supplied); the bytes outside certified ranges and
//! their veneers (bound only by the read-back hash of the sealed image); the
//! cache state of other cores or later writes to the pages; execution on
//! silicon. The replay reads the bytes the mapping holds after the walk; it
//! cannot observe the instruction cache itself.

// The source-defined-call publisher also supplies range digests from a private
// genuine checked aggregate-image owner. This readback still establishes only
// exact installed bytes/targets; it manufactures no per-function certificate
// or semantic verdict for either evidence class.

use std::collections::BTreeMap;
use std::ops::Range;

use super::JitError;
use crate::macho::reloc::AArch64RelocKind;
use trust_cg_verify::aarch64_instruction_word_proofs::{DecodedWord, decode_word};

/// The register a veneer loads its target into and branches through (IP0).
const VENEER_REGISTER: u32 = 16;
/// Byte offset of a veneer's 64-bit literal from the veneer's first word.
const VENEER_LITERAL_OFFSET: u64 = 8;
/// Bytes of one veneer: two instruction words and the literal.
const VENEER_BYTES: u64 = 16;

/// The target one branch relocation must reach.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum BranchTarget {
    /// A module function's entry, at this image offset.
    Function { name: String, entry: u64 },
    /// The veneer of the named external, at this image offset.
    Veneer { symbol: String, veneer: u64 },
}

impl BranchTarget {
    fn image_offset(&self) -> u64 {
        match self {
            Self::Function { entry, .. } => *entry,
            Self::Veneer { veneer, .. } => *veneer,
        }
    }

    fn describe(&self) -> String {
        match self {
            Self::Function { name, entry } => format!("function `{name}` at {entry:#x}"),
            Self::Veneer { symbol, veneer } => {
                format!("the veneer of external `{symbol}` at {veneer:#x}")
            }
        }
    }
}

/// The relocations, veneers and runtime literals of one verifying
/// publication, captured from the fixup inventory and the resolver BEFORE
/// any byte is installed.
#[derive(Debug, Default)]
pub(super) struct InstalledReplayInventory {
    /// Branch relocation sites by image offset.
    branches: BTreeMap<u64, BranchTarget>,
    /// Relocations this replay does not re-derive, by image offset.
    other_relocations: BTreeMap<u64, AArch64RelocKind>,
    /// Veneer image offset -> (external symbol, resolved address).
    veneers: BTreeMap<u64, (String, u64)>,
    /// 64-bit runtime literal image offset -> (what it is, value).
    literals: BTreeMap<u64, (&'static str, u64)>,
}

impl InstalledReplayInventory {
    /// Record a branch relocation at `offset` that must reach `target`.
    pub(super) fn branch(&mut self, offset: u32, target: BranchTarget) {
        self.branches.insert(u64::from(offset), target);
    }

    /// Whether a branch relocation is recorded at `offset`.
    pub(super) fn has_branch(&self, offset: u32) -> bool {
        self.branches.contains_key(&u64::from(offset))
    }

    /// Record a relocation of a kind this replay does not re-derive.
    pub(super) fn other_relocation(&mut self, offset: u32, kind: AArch64RelocKind) {
        self.other_relocations.insert(u64::from(offset), kind);
    }

    /// Record the veneer at `veneer` for `symbol` and the address its literal
    /// must hold.
    pub(super) fn veneer(&mut self, veneer: u64, symbol: &str, address: u64) {
        self.veneers.insert(veneer, (symbol.to_owned(), address));
    }

    /// Record a 64-bit runtime literal the publisher patches at `offset`.
    pub(super) fn literal(&mut self, offset: usize, what: &'static str, value: u64) {
        self.literals.insert(offset as u64, (what, value));
    }

    /// The first branch relocation site, if any (test fault injection).
    #[cfg(test)]
    pub(super) fn first_branch_site(&self) -> Option<u64> {
        self.branches.keys().next().copied()
    }

    /// The first veneer literal offset, if any (test fault injection).
    #[cfg(test)]
    pub(super) fn first_veneer_literal(&self) -> Option<u64> {
        self.veneers
            .keys()
            .next()
            .map(|veneer| veneer + VENEER_LITERAL_OFFSET)
    }
}

/// One authenticated proof range: name, image range and exact baseline digest.
/// Production takes this from a real function certificate or from the private
/// checked aggregate-image transport; the descriptor itself grants no proof.
pub(super) struct CertifiedRange<'a> {
    pub(super) name: &'a str,
    pub(super) range: Range<u64>,
    pub(super) certified_sha256: &'a str,
}

/// What the installed-artifact replay checked for one publication.
///
/// Present on every verifying AArch64 publication; the proof-required
/// compiler route refuses a buffer without it. Counts, not a proof: the
/// replay is a byte- and relocation-level check of the installed mapping
/// against the certificate-bound words (see the module documentation of
/// `jit::installed_replay` for what it does not establish).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstalledArtifactReplayRecord {
    functions: Vec<String>,
    words_compared: usize,
    branch_sites: usize,
    veneers: usize,
    literals: usize,
    installed_image_sha256: String,
}

impl InstalledArtifactReplayRecord {
    /// The certified functions whose installed bytes were replayed, in image
    /// order.
    pub fn functions(&self) -> &[String] {
        &self.functions
    }

    /// Installed instruction words compared, equal, with their certified
    /// words (relocation sites and runtime literals excluded).
    pub fn words_compared(&self) -> usize {
        self.words_compared
    }

    /// Branch relocation sites whose installed word was independently
    /// decoded and whose target was re-derived at the mapped address.
    pub fn branch_sites(&self) -> usize {
        self.branch_sites
    }

    /// Veneers whose two installed words were decoded and whose installed
    /// literal held the resolved external address.
    pub fn veneers(&self) -> usize {
        self.veneers
    }

    /// 64-bit runtime literals inside certified ranges that held the value
    /// the publisher was given.
    pub fn literals(&self) -> usize {
        self.literals
    }

    /// SHA-256 (hex) of the published image as re-read from the executable
    /// mapping by the replay.
    pub fn installed_image_sha256(&self) -> &str {
        &self.installed_image_sha256
    }

    /// Whether the replay covered exactly `names`, in order.
    pub fn covers_exactly<'a>(&self, names: impl IntoIterator<Item = &'a str>) -> bool {
        self.functions.iter().map(String::as_str).eq(names)
    }
}

fn refused(function: &str, offset: u64, detail: impl Into<String>) -> JitError {
    JitError::InstalledArtifactReplayRejected {
        function: function.to_owned(),
        offset,
        detail: detail.into(),
    }
}

fn word_at(bytes: &[u8], offset: u64) -> Option<u32> {
    let start = usize::try_from(offset).ok()?;
    let word = bytes.get(start..start.checked_add(4)?)?;
    Some(u32::from_le_bytes(word.try_into().ok()?))
}

fn literal_at(bytes: &[u8], offset: u64) -> Option<u64> {
    let start = usize::try_from(offset).ok()?;
    let literal = bytes.get(start..start.checked_add(8)?)?;
    Some(u64::from_le_bytes(literal.try_into().ok()?))
}

/// `(is_bl, signed word displacement)` of a B/BL word, by the verifier's
/// independent field decoder.
fn decode_branch(word: u32) -> Option<(bool, i64)> {
    match decode_word(word)? {
        DecodedWord::BranchImm { op, imm26 } => {
            let displacement = (i64::from(imm26) << 38) >> 38;
            Some((op == 1, displacement))
        }
        _ => None,
    }
}

/// `LDR Xt, <label>` (Arm ARM C6.2, `LDR (literal)`, 64-bit variant:
/// `opc=01 011 V=0 00 imm19 Rt`): `(Rt, signed byte displacement)`.
fn decode_ldr_literal_x(word: u32) -> Option<(u32, i64)> {
    if word & 0xff00_0000 != 0x5800_0000 {
        return None;
    }
    let imm19 = (word >> 5) & 0x7_ffff;
    let displacement = (i64::from(imm19) << 45) >> 43;
    Some((word & 31, displacement))
}

/// `BR Xn` (Arm ARM C6.2, `1101011 0 0 00 11111 0000 0 0 Rn 00000`): `Rn`.
fn decode_br(word: u32) -> Option<u32> {
    (word & 0xffff_fc1f == 0xd61f_0000).then_some((word >> 5) & 31)
}

impl InstalledReplayInventory {
    /// Replay the installed image `installed`, mapped at `base`, against the
    /// certified image `certified` and the certified functions `functions`.
    pub(super) fn replay(
        &self,
        certified: &[u8],
        installed: &[u8],
        base: u64,
        functions: &[CertifiedRange<'_>],
    ) -> Result<InstalledArtifactReplayRecord, JitError> {
        let mut record = InstalledArtifactReplayRecord {
            functions: Vec::with_capacity(functions.len()),
            words_compared: 0,
            branch_sites: 0,
            veneers: 0,
            literals: 0,
            installed_image_sha256: crate::jit_diagnostics::sha256_hex(installed),
        };
        // Veneer offset -> (external symbol, the first function reaching it).
        let mut veneers_reached: BTreeMap<u64, (&str, &str)> = BTreeMap::new();
        for function in functions {
            let name = function.name;
            let Range { start, end } = function.range.clone();
            if start > end
                || start % 4 != 0
                || end % 4 != 0
                || end > certified.len() as u64
                || end > installed.len() as u64
            {
                return Err(refused(
                    name,
                    start,
                    format!(
                        "certified range {start:#x}..{end:#x} is not a word-aligned extent of the \
                         {}-byte certified and {}-byte installed images",
                        certified.len(),
                        installed.len()
                    ),
                ));
            }
            let certified_range = &certified[start as usize..end as usize];
            let digest = crate::jit_diagnostics::sha256_hex(certified_range);
            if digest != function.certified_sha256 {
                return Err(refused(
                    name,
                    start,
                    format!(
                        "the certified bytes hash to {digest}, not the certificate's machine-code \
                         digest {}",
                        function.certified_sha256
                    ),
                ));
            }
            if let Some((offset, kind)) = self.other_relocations.range(start..end).next() {
                return Err(refused(
                    name,
                    *offset,
                    format!(
                        "a {kind:?} relocation inside a certified range has no installed-artifact \
                         replay (only BRANCH26 targets are re-derived)"
                    ),
                ));
            }
            // A runtime literal covers exactly two words of the range, which
            // are checked as one 64-bit value instead of word by word.
            let mut literal_words: BTreeMap<u64, u64> = BTreeMap::new();
            for (&offset, &(what, value)) in self.literals.range(start..end) {
                if offset % 4 != 0 {
                    return Err(refused(
                        name,
                        offset,
                        format!("the {what} literal is not word-aligned"),
                    ));
                }
                if offset + 8 > end {
                    return Err(refused(
                        name,
                        offset,
                        format!("the {what} literal runs past the certified range"),
                    ));
                }
                let installed_value = literal_at(installed, offset).ok_or_else(|| {
                    refused(
                        name,
                        offset,
                        format!("the {what} literal is outside the image"),
                    )
                })?;
                if installed_value != value {
                    return Err(refused(
                        name,
                        offset,
                        format!(
                            "the installed {what} literal is {installed_value:#x}, not the \
                             published {value:#x}"
                        ),
                    ));
                }
                literal_words.insert(offset, offset);
                literal_words.insert(offset + 4, offset);
                record.literals += 1;
            }
            let mut offset = start;
            while offset < end {
                if literal_words.contains_key(&offset) {
                    offset += 4;
                    continue;
                }
                let (Some(installed_word), Some(certified_word)) =
                    (word_at(installed, offset), word_at(certified, offset))
                else {
                    return Err(refused(name, offset, "word outside the image"));
                };
                if let Some(target) = self.branches.get(&offset) {
                    let Some((installed_bl, displacement)) = decode_branch(installed_word) else {
                        return Err(refused(
                            name,
                            offset,
                            format!(
                                "the installed word {installed_word:#010x} at a BRANCH26 \
                                 relocation does not decode as B or BL"
                            ),
                        ));
                    };
                    let certified_bl = decode_branch(certified_word).map(|(bl, _)| bl);
                    if certified_bl != Some(installed_bl) {
                        return Err(refused(
                            name,
                            offset,
                            format!(
                                "the installed word {installed_word:#010x} is a {} but the \
                                 certified word {certified_word:#010x} is not",
                                if installed_bl { "BL" } else { "B" }
                            ),
                        ));
                    }
                    let reached = (offset as i64)
                        .checked_add(displacement * 4)
                        .filter(|target| (0..installed.len() as i64).contains(target));
                    let reached_address = reached.map(|target| base.wrapping_add(target as u64));
                    let expected_address = base.wrapping_add(target.image_offset());
                    if reached_address != Some(expected_address) {
                        return Err(refused(
                            name,
                            offset,
                            format!(
                                "the installed {} at {:#x} reaches {}, not {} ({expected_address:#x})",
                                if installed_bl { "BL" } else { "B" },
                                base.wrapping_add(offset),
                                reached_address.map_or_else(
                                    || "a target outside the image".to_owned(),
                                    |address| format!("{address:#x}")
                                ),
                                target.describe()
                            ),
                        ));
                    }
                    if installed_word != certified_word {
                        return Err(refused(
                            name,
                            offset,
                            format!(
                                "the installed relocation word {installed_word:#010x} reaches the \
                                 named target but differs from the certified word \
                                 {certified_word:#010x}"
                            ),
                        ));
                    }
                    if let BranchTarget::Veneer { symbol, veneer } = target {
                        veneers_reached
                            .entry(*veneer)
                            .or_insert((symbol.as_str(), name));
                    }
                    record.branch_sites += 1;
                } else if installed_word != certified_word {
                    return Err(refused(
                        name,
                        offset,
                        format!(
                            "the installed word {installed_word:#010x} differs from the certified \
                             word {certified_word:#010x}"
                        ),
                    ));
                } else {
                    record.words_compared += 1;
                }
                offset += 4;
            }
            record.functions.push(name.to_owned());
        }
        for (&veneer, &(symbol, caller)) in &veneers_reached {
            let Some((_, address)) = self.veneers.get(&veneer) else {
                return Err(refused(
                    caller,
                    veneer,
                    format!("no resolved address is recorded for the veneer of `{symbol}`"),
                ));
            };
            if veneer + VENEER_BYTES > installed.len() as u64 {
                return Err(refused(
                    caller,
                    veneer,
                    format!("the veneer of `{symbol}` runs past the image"),
                ));
            }
            for word_offset in [veneer, veneer + 4] {
                if word_at(installed, word_offset) != word_at(certified, word_offset) {
                    return Err(refused(
                        caller,
                        word_offset,
                        format!(
                            "an installed word of the veneer of `{symbol}` differs from the published stub"
                        ),
                    ));
                }
            }
            let load = word_at(installed, veneer).and_then(decode_ldr_literal_x);
            if load != Some((VENEER_REGISTER, VENEER_LITERAL_OFFSET as i64)) {
                return Err(refused(
                    caller,
                    veneer,
                    format!(
                        "the veneer of `{symbol}` does not begin with LDR X16, <literal at +8> \
                         (decoded {load:?})"
                    ),
                ));
            }
            let branch = word_at(installed, veneer + 4).and_then(decode_br);
            if branch != Some(VENEER_REGISTER) {
                return Err(refused(
                    caller,
                    veneer + 4,
                    format!(
                        "the veneer of `{symbol}` does not branch through X16 (decoded {branch:?})"
                    ),
                ));
            }
            let literal = literal_at(installed, veneer + VENEER_LITERAL_OFFSET);
            if literal != Some(*address) {
                return Err(refused(
                    caller,
                    veneer + VENEER_LITERAL_OFFSET,
                    format!(
                        "the installed literal of the veneer of `{symbol}` is {}, not the resolved \
                         address {address:#x}",
                        literal
                            .map_or_else(|| "outside the image".to_owned(), |v| format!("{v:#x}"))
                    ),
                ));
            }
            record.veneers += 1;
        }
        Ok(record)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const RET: u32 = 0xd65f_03c0;
    const NOP: u32 = 0xd503_201f;

    fn bl(from: u64, to: u64) -> u32 {
        let words = ((to as i64 - from as i64) / 4) as u32 & 0x03ff_ffff;
        0x9400_0000 | words
    }

    fn b(from: u64, to: u64) -> u32 {
        bl(from, to) & !0x8000_0000
    }

    fn image(words: &[u32]) -> Vec<u8> {
        words.iter().flat_map(|word| word.to_le_bytes()).collect()
    }

    /// `caller: BL callee; B ext-veneer; callee: NOP; RET; veneer: LDR X16,
    /// #8; BR X16; .quad ext`.
    fn fixture(external: u64) -> (Vec<u8>, InstalledReplayInventory) {
        let mut bytes = image(&[bl(0, 8), b(4, 16), NOP, RET, 0x5800_0050, 0xd61f_0200]);
        bytes.extend_from_slice(&0u64.to_le_bytes());
        let mut inventory = InstalledReplayInventory::default();
        inventory.branch(
            0,
            BranchTarget::Function {
                name: "callee".into(),
                entry: 8,
            },
        );
        inventory.branch(
            4,
            BranchTarget::Veneer {
                symbol: "ext".into(),
                veneer: 16,
            },
        );
        inventory.veneer(16, "ext", external);
        (bytes, inventory)
    }

    fn installed(certified: &[u8], external: u64) -> Vec<u8> {
        let mut installed = certified.to_vec();
        installed[24..32].copy_from_slice(&external.to_le_bytes());
        installed
    }

    fn functions<'a>(certified: &[u8], digests: &'a [String; 2]) -> [CertifiedRange<'a>; 2] {
        let _ = certified;
        [
            CertifiedRange {
                name: "caller",
                range: 0..8,
                certified_sha256: &digests[0],
            },
            CertifiedRange {
                name: "callee",
                range: 8..16,
                certified_sha256: &digests[1],
            },
        ]
    }

    fn certified_digests(certified: &[u8]) -> [String; 2] {
        [
            crate::jit_diagnostics::sha256_hex(&certified[0..8]),
            crate::jit_diagnostics::sha256_hex(&certified[8..16]),
        ]
    }

    #[test]
    fn faithful_installation_replays_every_word_branch_and_veneer() {
        let external = 0x0000_7fff_1234_5678;
        let (certified, inventory) = fixture(external);
        let digests = certified_digests(&certified);
        let record = inventory
            .replay(
                &certified,
                &installed(&certified, external),
                0x1_0000_0000,
                &functions(&certified, &digests),
            )
            .expect("faithful installation replays");
        assert!(record.covers_exactly(["caller", "callee"]));
        assert_eq!(
            (
                record.words_compared(),
                record.branch_sites(),
                record.veneers(),
                record.literals()
            ),
            (2, 2, 1, 0)
        );
    }

    fn refusal(result: Result<InstalledArtifactReplayRecord, JitError>) -> (String, u64, String) {
        match result {
            Err(JitError::InstalledArtifactReplayRejected {
                function,
                offset,
                detail,
            }) => (function, offset, detail),
            other => panic!("expected an installed-artifact replay refusal, got {other:?}"),
        }
    }

    #[test]
    fn a_flipped_byte_is_refused_naming_function_and_offset() {
        let external = 0x4000;
        let (certified, inventory) = fixture(external);
        let digests = certified_digests(&certified);
        let mut tampered = installed(&certified, external);
        tampered[13] ^= 0x01;
        let (function, offset, detail) = refusal(inventory.replay(
            &certified,
            &tampered,
            0x10_0000,
            &functions(&certified, &digests),
        ));
        assert_eq!((function.as_str(), offset), ("callee", 12));
        assert!(
            detail.contains("differs from the certified word"),
            "{detail}"
        );
    }

    #[test]
    fn a_branch_retargeted_to_a_valid_wrong_entry_is_refused() {
        let external = 0x4000;
        let (certified, inventory) = fixture(external);
        let digests = certified_digests(&certified);
        let mut tampered = installed(&certified, external);
        // Still a BL, now reaching the callee's RET instead of its entry.
        tampered[0..4].copy_from_slice(&bl(0, 12).to_le_bytes());
        let (function, offset, detail) = refusal(inventory.replay(
            &certified,
            &tampered,
            0x10_0000,
            &functions(&certified, &digests),
        ));
        assert_eq!((function.as_str(), offset), ("caller", 0));
        assert!(detail.contains("not function `callee`"), "{detail}");
        // A branch turned into a call is refused before its target.
        let mut tampered = installed(&certified, external);
        tampered[4..8].copy_from_slice(&bl(4, 16).to_le_bytes());
        let (_, offset, detail) = refusal(inventory.replay(
            &certified,
            &tampered,
            0x10_0000,
            &functions(&certified, &digests),
        ));
        assert_eq!(offset, 4);
        assert!(
            detail.contains("is a BL but the certified word"),
            "{detail}"
        );
    }

    #[test]
    fn a_wrong_veneer_literal_or_word_is_refused() {
        let external = 0x4000;
        let (certified, inventory) = fixture(external);
        let digests = certified_digests(&certified);
        let (_, offset, detail) = refusal(inventory.replay(
            &certified,
            &installed(&certified, external + 4),
            0x10_0000,
            &functions(&certified, &digests),
        ));
        assert_eq!(offset, 24);
        assert!(detail.contains("not the resolved address"), "{detail}");
        let mut tampered = installed(&certified, external);
        tampered[20..24].copy_from_slice(&0xd61f_0220u32.to_le_bytes()); // BR X17
        let (_, offset, _) = refusal(inventory.replay(
            &certified,
            &tampered,
            0x10_0000,
            &functions(&certified, &digests),
        ));
        assert_eq!(offset, 20);
    }

    #[test]
    fn certified_bytes_must_carry_the_certificate_digest() {
        let external = 0x4000;
        let (certified, inventory) = fixture(external);
        let mut digests = certified_digests(&certified);
        digests[1] = crate::jit_diagnostics::sha256_hex(b"another body");
        let (function, offset, detail) = refusal(inventory.replay(
            &certified,
            &installed(&certified, external),
            0x10_0000,
            &functions(&certified, &digests),
        ));
        assert_eq!((function.as_str(), offset), ("callee", 8));
        assert!(
            detail.contains("not the certificate's machine-code digest"),
            "{detail}"
        );
    }

    #[test]
    fn unreplayed_relocation_kinds_and_bad_literals_are_refused() {
        let external = 0x4000;
        let (certified, mut inventory) = fixture(external);
        inventory.other_relocation(8, AArch64RelocKind::Page21);
        let digests = certified_digests(&certified);
        let (function, offset, detail) = refusal(inventory.replay(
            &certified,
            &installed(&certified, external),
            0x10_0000,
            &functions(&certified, &digests),
        ));
        assert_eq!((function.as_str(), offset), ("callee", 8));
        assert!(detail.contains("Page21"), "{detail}");

        // A runtime literal spanning the callee's two words.
        let (certified, mut inventory) = fixture(external);
        inventory.literal(8, "profile counter", 0xdead_beef);
        let digests = certified_digests(&certified);
        let mut good = installed(&certified, external);
        good[8..16].copy_from_slice(&0xdead_beefu64.to_le_bytes());
        let record = inventory
            .replay(
                &certified,
                &good,
                0x10_0000,
                &functions(&certified, &digests),
            )
            .expect("the patched literal replays");
        assert_eq!((record.literals(), record.words_compared()), (1, 0));
        let mut unaligned = InstalledReplayInventory::default();
        unaligned.literal(9, "profile counter", 0);
        let (_, offset, detail) = refusal(unaligned.replay(
            &certified,
            &good,
            0x10_0000,
            &functions(&certified, &digests),
        ));
        assert_eq!(offset, 9);
        assert!(detail.contains("not word-aligned"), "{detail}");
        good[8] ^= 1;
        let (_, offset, detail) = refusal(inventory.replay(
            &certified,
            &good,
            0x10_0000,
            &functions(&certified, &digests),
        ));
        assert_eq!(offset, 8);
        assert!(detail.contains("profile counter"), "{detail}");
    }

    #[test]
    fn independent_veneer_field_decoders_match_the_arm_encodings() {
        assert_eq!(decode_ldr_literal_x(0x5800_0050), Some((16, 8)));
        assert_eq!(decode_ldr_literal_x(0x58ff_fff0), Some((16, -4)));
        // LDR Wt (literal) and LDRSW are other classes.
        assert_eq!(decode_ldr_literal_x(0x1800_0050), None);
        assert_eq!(decode_ldr_literal_x(0x9800_0050), None);
        assert_eq!(decode_br(0xd61f_0200), Some(16));
        // BLR X16 and RET are not BR.
        assert_eq!(decode_br(0xd63f_0200), None);
        assert_eq!(decode_br(RET), None);
        assert_eq!(decode_branch(bl(8, 0)), Some((true, -2)));
        assert_eq!(
            decode_branch(b(0, 0x7ff_fffc)),
            Some((false, (1 << 25) - 1))
        );
        assert_eq!(decode_branch(NOP), None);
    }
}
