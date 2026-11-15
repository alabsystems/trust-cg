// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bounded actual-word control for the existing scalar byte evaluator.
//!
//! No MachIR layout, CFG metadata or source predicate chooses an edge. PC is
//! the address of the branch word itself; signed imm19/imm26 encode multiples
//! of four bytes. CBZ/CBNZ read their actual W/X carrier and neither consume nor
//! modify NZCV. B.cond snapshots the latest modeled flags before either path.
//! Reference: Arm A64 ISA v2021-06, B.cond p49, B p50, CBNZ p83, CBZ p84:
//! <https://documentation-service.arm.com/static/60df18dc0320e92fa40b7e59>.
//!
//! The sole conditional fork returns a flat integer selection. Both complete
//! paths use the parent's unchanged scalar word evaluator and reach the same
//! exact frame footer. This is a bounded Rust semantic check, not a proof or
//! permission to publish, mutate, relocate or cache the checked bytes.

use super::super::super::{CompareKind, Predicate};
use super::*;

const MAX_WORDS: usize = 256;
const RET: u32 = 0xd65f03c0;
const SAVE: u32 = 0xa9bf7bfd;
const ESTABLISH: u32 = 0x910003fd;
const RESTORE: u32 = 0xa8c17bfd;

#[derive(Clone, Copy)]
enum Condition {
    Flags(u8),
    Zero {
        register: usize,
        bits: u32,
        nonzero: bool,
    },
}

#[derive(Clone, Copy)]
enum Edge {
    Jump(usize),
    Fork { condition: Condition, taken: usize },
}

struct Stream<'a> {
    code: &'a [u8],
    count: usize,
    start: usize,
    footer: usize,
    ret: usize,
    private_stack_bytes: usize,
}

struct Path {
    /// Only scalar words. Direct edges are decoded by the layout walker, not
    /// passed off as inert instructions to the scalar evaluator.
    words: Vec<usize>,
    covered: Vec<bool>,
}

pub(super) fn has_direct_control(code: &[u8]) -> bool {
    code.as_chunks::<4>().0.iter().any(|bytes| {
        let instruction = u32::from_le_bytes(*bytes);
        instruction & 0xfc000000 == 0x14000000 // B, not BL.
            || instruction & 0xff000000 == 0x54000000 // B.cond, including reserved bit4.
            || instruction & 0x7e000000 == 0x34000000 // CBZ/CBNZ W or X.
    })
}

impl<'a> Stream<'a> {
    fn new(code: &'a [u8]) -> Result<Self, AffineByteError> {
        if code.is_empty() || !code.len().is_multiple_of(4) {
            return Err(invalid(code.len(), "nonempty complete A64 words required"));
        }
        let count = code.len() / 4;
        // Before any path/coverage allocation or state fork. Existing linear
        // streams retain their previous evaluator and do not acquire this cap.
        if count > MAX_WORDS {
            return Err(invalid(
                code.len(),
                "direct control exceeds the 256-word budget",
            ));
        }
        let mut ret = None;
        for index in 0..count {
            if word(code, index) == RET && ret.replace(index).is_some() {
                return Err(invalid(index * 4, "requires one common RET X30"));
            }
        }
        let ret = ret.ok_or_else(|| invalid(code.len() - 4, "requires one common RET X30"))?;
        let (start, footer, private_stack_bytes) = if word(code, 0) == SAVE {
            if count < 4 || word(code, 1) != ESTABLISH || ret < 3 || word(code, ret - 1) != RESTORE
            {
                return Err(invalid(0, "unmatched sixteen-byte frame envelope"));
            }
            (2, ret - 1, 16)
        } else {
            (0, ret, 0)
        };
        Ok(Self {
            code,
            count,
            start,
            footer,
            ret,
            private_stack_bytes,
        })
    }

    fn body_index(&self, index: usize, offset: usize) -> Result<(), AffineByteError> {
        if index < self.start || index >= self.count {
            return Err(invalid(
                offset,
                "direct edge leaves the body or enters the frame prologue",
            ));
        }
        if index == self.ret && self.footer != self.ret {
            return Err(invalid(
                offset,
                "direct edge bypasses the common frame restore",
            ));
        }
        Ok(())
    }

    fn target(&self, index: usize, field: u32, bits: u32) -> Result<usize, AffineByteError> {
        let shift = 64 - bits;
        let displacement = (i64::from(field) << shift) >> shift;
        // Work in complete-word units. The signed ISA displacement is relative
        // to this branch's PC, not its fallthrough or any recorded block start.
        let destination = (index as i64)
            .checked_add(displacement)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| invalid(index * 4, "direct edge target is outside the word stream"))?;
        self.body_index(destination, index * 4)?;
        Ok(destination)
    }

    fn edge(&self, index: usize) -> Result<Option<Edge>, AffineByteError> {
        let instruction = word(self.code, index);
        let offset = index * 4;
        if instruction & 0xfc000000 == 0x14000000 {
            return Ok(Some(Edge::Jump(self.target(
                index,
                instruction & 0x03ffffff,
                26,
            )?)));
        }
        if instruction & 0xff000000 == 0x54000000 {
            let cc = (instruction & 15) as u8;
            if instruction & 16 != 0 || cc >= 14 {
                return Err(AffineByteError::UnsupportedBytes {
                    offset,
                    word: instruction,
                });
            }
            return Ok(Some(Edge::Fork {
                condition: Condition::Flags(cc),
                taken: self.target(index, (instruction >> 5) & 0x7ffff, 19)?,
            }));
        }
        if instruction & 0x7e000000 == 0x34000000 {
            return Ok(Some(Edge::Fork {
                condition: Condition::Zero {
                    register: (instruction & 31) as usize,
                    bits: if instruction >> 31 == 0 { 32 } else { 64 },
                    nonzero: instruction & (1 << 24) != 0,
                },
                taken: self.target(index, (instruction >> 5) & 0x7ffff, 19)?,
            }));
        }
        Ok(None)
    }

    fn walk_arm(&self, mut index: usize, prefix: &[bool]) -> Result<Path, AffineByteError> {
        let mut covered = prefix.to_vec();
        let mut words = Vec::new();
        while index != self.footer {
            self.body_index(index, index * 4)?;
            if std::mem::replace(&mut covered[index], true) {
                return Err(invalid(
                    index * 4,
                    "cyclic direct control or return to the prefix",
                ));
            }
            match self.edge(index)? {
                Some(Edge::Jump(target)) => index = target,
                Some(Edge::Fork { .. }) => {
                    return Err(AffineByteError::UnsupportedBytes {
                        offset: index * 4,
                        word: word(self.code, index),
                    });
                }
                None => {
                    words.push(index);
                    index += 1;
                }
            }
        }
        covered[self.footer] = true;
        covered[self.ret] = true;
        Ok(Path { words, covered })
    }

    fn full_coverage(
        &self,
        first: &[bool],
        second: Option<&[bool]>,
    ) -> Result<(), AffineByteError> {
        if let Some(index) = (0..self.count)
            .find(|index| !first[*index] && !second.is_some_and(|covered| covered[*index]))
        {
            return Err(invalid(
                index * 4,
                "word is outside both complete execution paths",
            ));
        }
        Ok(())
    }
}

fn predicate(
    state: &ByteState,
    condition: Condition,
    offset: usize,
) -> Result<Predicate, AffineByteError> {
    match condition {
        Condition::Flags(cc) => {
            let flags = state
                .comparison_flags
                .ok_or_else(|| invalid(offset, "B.cond lacks modeled reaching CMP flags"))?;
            flags.condition(cc).ok_or_else(|| {
                invalid(
                    offset,
                    "B.cond condition is outside the modeled NZCV relations",
                )
            })
        }
        Condition::Zero {
            register,
            bits,
            nonzero,
        } => {
            let value = state.registers.read(register, bits, offset)?;
            let zero = if let Some(predicate) = value.as_bool() {
                predicate.inverted()
            } else {
                let value = value.as_affine(bits).ok_or_else(|| {
                    invalid(
                        offset,
                        "compare branch needs affine or canonical Boolean input",
                    )
                })?;
                Predicate::compare(
                    CompareKind::Equal,
                    value,
                    Affine::constant(0, width_mask(bits)),
                    false,
                    bits,
                )
            };
            Ok(if nonzero { zero.inverted() } else { zero })
        }
    }
}

pub(super) fn evaluate(
    code: &[u8],
    bits: u32,
    parameter_count: usize,
    return_type: Option<ScalarType>,
) -> Result<(Option<ScalarValue>, usize), AffineByteError> {
    let stream = Stream::new(code)?;
    let mut covered = vec![false; stream.count];
    covered[..stream.start].fill(true);
    let mut state = ByteState::new(bits, parameter_count)?;
    let mut index = stream.start;
    while index != stream.footer {
        stream.body_index(index, index * 4)?;
        if std::mem::replace(&mut covered[index], true) {
            return Err(invalid(index * 4, "cyclic direct control"));
        }
        match stream.edge(index)? {
            Some(Edge::Jump(target)) => index = target,
            Some(Edge::Fork { condition, taken }) => {
                let fallthrough = index + 1;
                stream.body_index(fallthrough, index * 4)?;
                let taken_path = stream.walk_arm(taken, &covered)?;
                let other_path = stream.walk_arm(fallthrough, &covered)?;
                stream.full_coverage(&taken_path.covered, Some(&other_path.covered))?;
                let branch_predicate = predicate(&state, condition, index * 4)?;
                let Some(ScalarType::Integer(width)) = return_type else {
                    return Err(AffineByteError::UnsupportedBytes {
                        offset: index * 4,
                        word: word(code, index),
                    });
                };
                if width != bits {
                    return Err(invalid(
                        index * 4,
                        "conditional return width differs from source domain",
                    ));
                }
                // The word cap and complete acyclic paths were checked before
                // either fixed-size scalar state is cloned. Every scalar word
                // of both paths is checked, even for a constant predicate.
                let arm = |path: &Path| -> Result<Affine, AffineByteError> {
                    let mut arm_state = state.clone();
                    for position in &path.words {
                        arm_state.step_word(*position * 4, word(code, *position))?;
                    }
                    arm_state
                        .result(return_type, stream.ret * 4)?
                        .and_then(|value| value.as_affine(bits))
                        .ok_or_else(|| {
                            invalid(
                                stream.ret * 4,
                                "conditional arm must return a flat integer value",
                            )
                        })
                };
                let result = ScalarValue::select(
                    bits,
                    branch_predicate,
                    arm(&taken_path)?,
                    arm(&other_path)?,
                );
                return Ok((Some(result), stream.private_stack_bytes));
            }
            None => {
                state.step_word(index * 4, word(code, index))?;
                index += 1;
            }
        }
    }
    covered[stream.footer] = true;
    covered[stream.ret] = true;
    stream.full_coverage(&covered, None)?;
    Ok((
        state.result(return_type, stream.ret * 4)?,
        stream.private_stack_bytes,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes(words: &[u32]) -> Vec<u8> {
        words.iter().flat_map(|word| word.to_le_bytes()).collect()
    }

    fn diamond(bits: u32, cc: u32, footer_first: bool) -> Vec<u32> {
        let sf = if bits == 64 { 1 << 31 } else { 0 };
        let cmp = 0x6b01001f | sf;
        let add = 0x11000440 | sf;
        let sub = 0x51000460 | sf;
        if footer_first {
            vec![
                SAVE,
                ESTABLISH,
                cmp,
                0x54000080 | cc,
                sub,
                RESTORE,
                RET,
                add,
                0x17fffffd,
            ]
        } else {
            vec![
                SAVE,
                ESTABLISH,
                cmp,
                0x54000060 | cc,
                sub,
                0x14000003,
                add,
                0x14000001,
                RESTORE,
                RET,
            ]
        }
    }

    fn expected(bits: u32, cc: u32) -> ScalarValue {
        let (kind, swap, negated) = match cc {
            0 => (CompareKind::Equal, false, false),
            1 => (CompareKind::Equal, false, true),
            2 => (CompareKind::UnsignedLess, false, true),
            3 => (CompareKind::UnsignedLess, false, false),
            8 => (CompareKind::UnsignedLess, true, false),
            9 => (CompareKind::UnsignedLess, true, true),
            10 => (CompareKind::SignedLess, false, true),
            11 => (CompareKind::SignedLess, false, false),
            12 => (CompareKind::SignedLess, true, false),
            13 => (CompareKind::SignedLess, true, true),
            _ => panic!("integer comparison condition"),
        };
        let (a, b) = (Affine::parameter(0), Affine::parameter(1));
        let (a, b) = if swap { (b, a) } else { (a, b) };
        let mask = width_mask(bits);
        ScalarValue::select(
            bits,
            Predicate::compare(kind, a, b, negated, bits),
            Affine::parameter(2).combine(Affine::constant(1, mask), false, mask),
            Affine::parameter(3).combine(Affine::constant(1, mask), true, mask),
        )
    }

    fn result(words: &[u32], bits: u32) -> Result<(Option<ScalarValue>, usize), AffineByteError> {
        byte_result(&bytes(words), bits, 4, Some(ScalarType::Integer(bits)))
    }

    #[test]
    fn literal_conditional_words_cover_all_integer_conditions_widths_and_footer_layouts() {
        for bits in [32, 64] {
            for cc in [0, 1, 2, 3, 8, 9, 10, 11, 12, 13] {
                for footer_first in [false, true] {
                    assert_eq!(
                        result(&diamond(bits, cc, footer_first), bits).unwrap(),
                        (Some(expected(bits, cc)), 16)
                    );
                }
                let mut unframed = diamond(bits, cc, false);
                unframed.drain(..2);
                unframed.remove(unframed.len() - 2);
                assert_eq!(
                    result(&unframed, bits).unwrap(),
                    (Some(expected(bits, cc)), 0)
                );
            }
        }
    }

    #[test]
    fn materialized_boolean_compare_branches_accept_equivalent_w_and_x_carriers() {
        for bits in [32, 64] {
            let sf = if bits == 64 { 1 << 31 } else { 0 };
            for cset_sf in [0, 1 << 31] {
                for branch_sf in [0, 1 << 31] {
                    for nonzero in [false, true] {
                        let add = 0x11000440 | sf;
                        let sub = 0x51000460 | sf;
                        let words = [
                            SAVE,
                            ESTABLISH,
                            0x6b01001f | sf,
                            0x1a9f27e4 | cset_sf,
                            0x34000064 | branch_sf | (u32::from(nonzero) << 24),
                            if nonzero { sub } else { add },
                            0x14000002,
                            if nonzero { add } else { sub },
                            RESTORE,
                            RET,
                        ];
                        assert_eq!(result(&words, bits).unwrap(), (Some(expected(bits, 3)), 16));
                        // CBZ/CBNZ must not consume a later CMP's NZCV.
                        let mut changed = words.to_vec();
                        changed.insert(4, 0x6b02005f | sf); // CMP W/X2,W/X2.
                        assert_eq!(
                            result(&changed, bits).unwrap(),
                            (Some(expected(bits, 3)), 16)
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn conditional_flags_snapshot_and_latest_producer_are_both_observed() {
        for bits in [32, 64] {
            let sf = if bits == 64 { 1 << 31 } else { 0 };
            let original = diamond(bits, 11, false);
            let mut moved = original.clone();
            moved.insert(3, 0x2a0203e0 | sf); // MOV W/X0,W/X2 after CMP.
            assert_eq!(
                result(&moved, bits).unwrap(),
                (Some(expected(bits, 11)), 16)
            );
            let mut clobbered = original.clone();
            clobbered.insert(3, 0x6b02005f | sf); // CMP W/X2,W/X2 before B.lt.
            assert_ne!(
                result(&clobbered, bits).unwrap().0,
                Some(expected(bits, 11))
            );
            let mut changed_condition = original.clone();
            changed_condition[3] ^= 1; // Valid B.ge, the inverse condition.
            assert_ne!(
                result(&changed_condition, bits).unwrap().0,
                Some(expected(bits, 11))
            );
            let mut missing = original.clone();
            missing[2] = 0xd503201f;
            assert!(
                result(&missing, bits).is_err(),
                "B.cond cannot inherit entry NZCV"
            );
            for index in [4, 6] {
                let mut changed = original.clone();
                changed[index] ^= 1 << 30; // Flip the corresponding arm's ADD/SUB.
                assert_ne!(result(&changed, bits).unwrap().0, Some(expected(bits, 11)));
            }
        }
    }

    #[test]
    fn direct_targets_loops_nested_control_frames_and_uncovered_words_fail_closed() {
        let original = diamond(64, 3, false);
        for (index, replacement) in [
            (3, 0x54ffffa3),      // Target the frame prologue (PC3 -3).
            (3, 0x540000c3),      // Bypass restore and land on RET (PC3 +6).
            (3, 0x54000203),      // Target outside stream.
            (3, 0x54000063 | 16), // Reserved B.cond bit4 / outside this ISA profile.
            (3, 0x5400006e),      // AL is not an admitted conditional edge.
            (3, 0x5400006f),      // NV likewise.
            (5, 0x14000000),      // Loop on the false path.
            (7, 0x14000000),      // Loop on the true path.
            (4, 0x54000040),      // A second conditional fork.
            (4, 0x94000004),      // BL modifies LR; not an unconditional B.
            (4, 0xab010009),      // Unmodeled flag writer.
            (8, RESTORE ^ 1),     // Wrong exact footer.
        ] {
            let mut changed = original.clone();
            changed[index] = replacement;
            assert!(
                result(&changed, 64).is_err(),
                "word {index} -> {replacement:#010x}"
            );
        }
        let mut changed = diamond(64, 3, true);
        changed.push(0xd503201f);
        assert!(
            result(&changed, 64).is_err(),
            "unvisited trailing NOP is not full-stream coverage"
        );
        let mut changed = original;
        changed[3] = 0x540000a3; // True path jumps to restore, leaving its arm unvisited.
        assert!(result(&changed, 64).is_err());
    }

    #[test]
    fn incoming_unknown_high_bits_and_preallocation_control_budget_are_refused() {
        let mut words = diamond(32, 3, false);
        words[3] = 0xb5000060; // CBNZ X0 must not reuse only W0's known meaning.
        assert!(result(&words, 32).is_err());
        let mut words = diamond(64, 3, false);
        words[3] = 0x35000060; // CBNZ W0 must not reinterpret the I64 affine input.
        assert!(result(&words, 64).is_err());
        words.resize(MAX_WORDS + 1, 0xd503201f);
        assert!(
            matches!(result(&words, 64), Err(AffineByteError::InvalidBytes { reason, .. }) if reason.contains("256-word"))
        );
    }
}
