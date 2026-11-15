// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Private exact normal forms shared by the independent source, LIR, raw
//! machine and byte interpreters. This is not a proof/publication interface.
//! [`Affine`] is also reachable crate-wide (through
//! `source_bound_source::Affine`) for the x86-64 body owner's
//! solver-independent refusal check; it never grants credit there either.
//! Ordered predicates compare complete modular operands: subtracting or
//! cancelling a common modular offset does not preserve signed/unsigned order.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Affine(pub(super) [u64; 9]);

impl Affine {
    /// Exact finite substitution in Z/(2^width). No evaluation of a source
    /// program, ordering cancellation, allocation or proof credit occurs here.
    pub(super) fn substitute(self, arguments: &[Self], mask: u64) -> Option<Self> {
        if arguments.len() > 8 || self.0[arguments.len()..8].iter().any(|c| *c != 0) {
            return None;
        }
        let mut terms = [0u64; 9];
        terms[8] = self.0[8] & mask;
        for (coefficient, argument) in self.0.iter().zip(arguments) {
            for (out, input) in terms.iter_mut().zip(argument.0) {
                *out = out.wrapping_add(coefficient.wrapping_mul(input)) & mask;
            }
        }
        Some(Self(terms))
    }
    pub(crate) fn constant(value: u64, mask: u64) -> Self {
        let mut terms = [0; 9];
        terms[8] = value & mask;
        Self(terms)
    }

    pub(crate) fn parameter(index: usize) -> Self {
        let mut terms = [0; 9];
        terms[index] = 1;
        Self(terms)
    }

    pub(crate) fn combine(self, rhs: Self, subtract: bool, mask: u64) -> Self {
        let mut terms = [0; 9];
        for (i, term) in terms.iter_mut().enumerate() {
            *term = if subtract {
                self.0[i].wrapping_sub(rhs.0[i])
            } else {
                self.0[i].wrapping_add(rhs.0[i])
            } & mask;
        }
        Self(terms)
    }

    pub(crate) fn as_constant(self) -> Option<u64> {
        self.0[..8]
            .iter()
            .all(|term| *term == 0)
            .then_some(self.0[8])
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ScalarType {
    Integer(u32),
    Bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CompareKind {
    Equal,
    SignedLess,
    UnsignedLess,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Predicate {
    Constant(bool),
    Compare {
        bits: u32,
        kind: CompareKind,
        lhs: Affine,
        rhs: Affine,
        negated: bool,
    },
}

impl Predicate {
    pub(super) fn inverted(self) -> Self {
        match self {
            Self::Constant(value) => Self::Constant(!value),
            Self::Compare {
                bits,
                kind,
                lhs,
                rhs,
                negated,
            } => Self::Compare {
                bits,
                kind,
                lhs,
                rhs,
                negated: !negated,
            },
        }
    }

    pub(super) fn compare(
        kind: CompareKind,
        mut lhs: Affine,
        mut rhs: Affine,
        negated: bool,
        bits: u32,
    ) -> Self {
        // Callers establish the homogeneous 32/64-bit arithmetic domain.
        // Width remains in every nonconstant predicate's exact identity.
        if lhs == rhs {
            return Self::Constant((kind == CompareKind::Equal) ^ negated);
        }
        if let (Some(a), Some(b)) = (lhs.as_constant(), rhs.as_constant()) {
            let value = match kind {
                CompareKind::Equal => a == b,
                CompareKind::UnsignedLess => a < b,
                CompareKind::SignedLess => {
                    if bits == 32 {
                        (a as u32 as i32) < (b as u32 as i32)
                    } else {
                        (a as i64) < (b as i64)
                    }
                }
            };
            return Self::Constant(value ^ negated);
        }
        if kind == CompareKind::Equal && rhs < lhs {
            std::mem::swap(&mut lhs, &mut rhs);
        }
        Self::Compare {
            bits,
            kind,
            lhs,
            rhs,
            negated,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ScalarValue {
    Integer {
        bits: u32,
        value: Affine,
    },
    Bool(Predicate),
    /// A single decision over two complete affine values. Deliberately flat:
    /// nested decisions and arithmetic on selections need a richer domain.
    Select {
        bits: u32,
        predicate: Predicate,
        then_value: Affine,
        else_value: Affine,
    },
}

impl ScalarValue {
    /// Substitute homogeneous affine integer arguments into one previously
    /// checked scalar relation. Nested selection arguments are outside this
    /// finite domain; callers must not approximate them by fresh inputs.
    pub(super) fn substitute(self, arguments: &[Self], bits: u32) -> Option<Self> {
        if !matches!(bits, 32 | 64) || arguments.len() > 8 {
            return None;
        }
        let mask = if bits == 32 {
            u32::MAX as u64
        } else {
            u64::MAX
        };
        let mut affine = [Affine::constant(0, mask); 8];
        for (slot, value) in affine.iter_mut().zip(arguments) {
            *slot = value.as_affine(bits)?;
        }
        let arguments = &affine[..arguments.len()];
        let substitute = |value: Affine| value.substitute(arguments, mask);
        let predicate = |value: Predicate| match value {
            Predicate::Constant(value) => Some(Predicate::Constant(value)),
            Predicate::Compare {
                bits: width,
                kind,
                lhs,
                rhs,
                negated,
            } if width == bits => Some(Predicate::compare(
                kind,
                substitute(lhs)?,
                substitute(rhs)?,
                negated,
                bits,
            )),
            _ => None,
        };
        match self {
            Self::Integer { bits: width, value } if width == bits => Some(Self::Integer {
                bits,
                value: substitute(value)?,
            }),
            Self::Bool(value) => Some(Self::Bool(predicate(value)?)),
            Self::Select {
                bits: width,
                predicate: test,
                then_value,
                else_value,
            } if width == bits => Some(Self::select(
                bits,
                predicate(test)?,
                substitute(then_value)?,
                substitute(else_value)?,
            )),
            _ => None,
        }
    }
    pub(super) fn select(
        bits: u32,
        mut predicate: Predicate,
        mut then_value: Affine,
        mut else_value: Affine,
    ) -> Self {
        if let Predicate::Constant(value) = predicate {
            return Self::Integer {
                bits,
                value: if value { then_value } else { else_value },
            };
        }
        if then_value == else_value {
            return Self::Integer {
                bits,
                value: then_value,
            };
        }
        // Inverting the condition and swapping arms denotes the same function.
        // Normalize that identity without cancelling modular comparison terms.
        if matches!(predicate, Predicate::Compare { negated: true, .. }) {
            predicate = predicate.inverted();
            std::mem::swap(&mut then_value, &mut else_value);
        }
        Self::Select {
            bits,
            predicate,
            then_value,
            else_value,
        }
    }

    pub(super) fn ty(self) -> ScalarType {
        match self {
            Self::Integer { bits, .. } | Self::Select { bits, .. } => ScalarType::Integer(bits),
            Self::Bool(_) => ScalarType::Bool,
        }
    }

    pub(super) fn as_affine(self, expected_bits: u32) -> Option<Affine> {
        match self {
            Self::Integer { bits, value } if bits == expected_bits => Some(value),
            _ => None,
        }
    }

    pub(super) fn as_constant(self) -> Option<u64> {
        match self {
            Self::Integer { value, .. } => value.as_constant(),
            Self::Bool(Predicate::Constant(value)) => Some(u64::from(value)),
            Self::Bool(_) | Self::Select { .. } => None,
        }
    }

    /// Machine-only normalization: a fully known literal 0/1 implements a
    /// Boolean result. Source/LIR typing must use `ty`, not this coercion.
    pub(super) fn as_bool(self) -> Option<Predicate> {
        match self {
            Self::Bool(predicate) => Some(predicate),
            _ => match self.as_constant()? {
                0 => Some(Predicate::Constant(false)),
                1 => Some(Predicate::Constant(true)),
                _ => None,
            },
        }
    }

    /// Bool is fully known to occupy only bit zero in either hardware width.
    /// Integer affine coefficients never acquire a wider interpretation here.
    pub(super) fn at_width(self, expected_bits: u32) -> Option<Self> {
        if !matches!(expected_bits, 32 | 64) {
            return None;
        }
        match self {
            Self::Bool(_) => Some(self),
            Self::Integer { bits, .. } | Self::Select { bits, .. } if bits == expected_bits => {
                Some(self)
            }
            _ => None,
        }
    }

    pub(super) fn for_type(self, expected: ScalarType) -> Option<Self> {
        match expected {
            ScalarType::Bool => self.as_bool().map(Self::Bool),
            ScalarType::Integer(bits) => {
                if matches!(self, Self::Select { bits: width, .. } if width == bits) {
                    return Some(self);
                }
                let value = match self {
                    Self::Bool(Predicate::Constant(value)) if matches!(bits, 32 | 64) => {
                        Affine::constant(u64::from(value), u64::MAX)
                    }
                    Self::Bool(predicate) if matches!(bits, 32 | 64) => {
                        return Some(Self::select(
                            bits,
                            predicate,
                            Affine::constant(1, u64::MAX),
                            Affine::constant(0, u64::MAX),
                        ));
                    }
                    _ => self.as_affine(bits)?,
                };
                Some(Self::Integer { bits, value })
            }
        }
    }
}

/// Actual reaching SUBS/CMP inputs, captured before later register writes.
/// N=sign(a-b), Z=(a=b), C=(unsigned a>=b), and V is signed subtraction
/// overflow. The relational conditions below are the resulting identities;
/// there is deliberately no dependency on the selector's IntCC mapping.
#[derive(Debug, Clone, Copy)]
pub(super) enum ComparisonFlags {
    Integer { bits: u32, lhs: Affine, rhs: Affine },
    BooleanZero(Predicate),
}

impl ComparisonFlags {
    pub(super) fn new(bits: u32, lhs: Affine, rhs: Affine) -> Self {
        Self::Integer { bits, lhs, rhs }
    }

    /// CMP of a canonical 0/1 carrier against zero preserves the exact
    /// predicate that produced that carrier, even when W/X transport changes.
    pub(super) fn from_values(bits: u32, lhs: ScalarValue, rhs: ScalarValue) -> Option<Self> {
        if let ScalarValue::Bool(predicate) = lhs {
            return (rhs.as_constant() == Some(0)).then_some(Self::BooleanZero(predicate));
        }
        Some(Self::new(bits, lhs.as_affine(bits)?, rhs.as_affine(bits)?))
    }

    pub(super) fn condition(self, cc: u8) -> Option<Predicate> {
        let Self::Integer {
            bits,
            lhs: left,
            rhs: right,
        } = self
        else {
            let Self::BooleanZero(predicate) = self else {
                unreachable!()
            };
            return match cc {
                0 | 9 | 13 => Some(predicate.inverted()),
                1 | 8 | 12 => Some(predicate),
                2 | 10 => Some(Predicate::Constant(true)),
                3 | 11 => Some(Predicate::Constant(false)),
                _ => None,
            };
        };
        use CompareKind::{Equal, SignedLess, UnsignedLess};
        let (kind, swap, negated) = match cc {
            0 => (Equal, false, false),        // EQ: Z
            1 => (Equal, false, true),         // NE: !Z
            2 => (UnsignedLess, false, true),  // HS: C
            3 => (UnsignedLess, false, false), // LO: !C
            8 => (UnsignedLess, true, false),  // HI: C && !Z
            9 => (UnsignedLess, true, true),   // LS: !C || Z
            10 => (SignedLess, false, true),   // GE: N == V
            11 => (SignedLess, false, false),  // LT: N != V
            12 => (SignedLess, true, false),   // GT: !Z && N == V
            13 => (SignedLess, true, true),    // LE: Z || N != V
            // MI/PL/VS/VC are not general integer relations. AL/NV are
            // noninvertible and are not legal source CSET alias conditions.
            _ => return None,
        };
        let (lhs, rhs) = if swap { (right, left) } else { (left, right) };
        Some(Predicate::compare(kind, lhs, rhs, negated, bits))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn comparison_flags_match_independent_subtraction_nzcv_edges() {
        for bits in [32, 64] {
            let mask = if bits == 32 {
                u32::MAX as u64
            } else {
                u64::MAX
            };
            let sign = 1_u64 << (bits - 1);
            let values = [0, 1, 2, sign - 1, sign, sign + 1, mask - 1, mask];
            for a in values {
                for b in values {
                    let result = a.wrapping_sub(b) & mask;
                    let n = result & sign != 0;
                    let z = result == 0;
                    let c = a >= b;
                    let v = ((a ^ b) & (a ^ result) & sign) != 0;
                    let expected = [
                        (0, z),
                        (1, !z),
                        (2, c),
                        (3, !c),
                        (8, c && !z),
                        (9, !c || z),
                        (10, n == v),
                        (11, n != v),
                        (12, !z && n == v),
                        (13, z || n != v),
                    ];
                    let flags = ComparisonFlags::new(
                        bits,
                        Affine::constant(a, mask),
                        Affine::constant(b, mask),
                    );
                    for (cc, expected) in expected {
                        assert_eq!(flags.condition(cc), Some(Predicate::Constant(expected)));
                    }
                    for cc in [4, 5, 6, 7, 14, 15, 16, 255] {
                        assert_eq!(flags.condition(cc), None);
                    }
                }
            }
        }
    }

    #[test]
    fn exact_predicates_preserve_width_orientation_and_wrapped_operands() {
        let a = Affine::parameter(0);
        let b = Affine::parameter(1);
        let eq = |a, b, bits| Predicate::compare(CompareKind::Equal, a, b, false, bits);
        assert_eq!(eq(a, b, 32), eq(b, a, 32));
        assert_ne!(eq(a, b, 32), eq(a, b, 64));
        for kind in [CompareKind::SignedLess, CompareKind::UnsignedLess] {
            let p = Predicate::compare(kind, a, b, false, 32);
            assert_ne!(p, Predicate::compare(kind, b, a, false, 32));
            let one = Affine::constant(1, u32::MAX as u64);
            assert_ne!(
                p,
                Predicate::compare(
                    kind,
                    a.combine(one, false, u32::MAX as u64),
                    b.combine(one, false, u32::MAX as u64),
                    false,
                    32
                )
            );
            assert_eq!(
                Predicate::compare(kind, a, a, false, 32),
                Predicate::Constant(false)
            );
        }
    }

    #[test]
    fn boolean_transport_never_reinterprets_numeric_affine_width_or_source_type() {
        let number = ScalarValue::Integer {
            bits: 32,
            value: Affine::parameter(0),
        };
        assert!(number.at_width(64).is_none());
        assert!(number.for_type(ScalarType::Bool).is_none());
        let predicate = ScalarValue::Bool(Predicate::compare(
            CompareKind::SignedLess,
            Affine::parameter(0),
            Affine::parameter(1),
            false,
            32,
        ));
        assert_eq!(predicate.at_width(32), Some(predicate));
        assert_eq!(predicate.at_width(64), Some(predicate));
        assert!(matches!(
            predicate.for_type(ScalarType::Integer(32)),
            Some(ScalarValue::Select { bits: 32, .. })
        ));
        // The numeric interpretation is a machine carrier conversion; source
        // typing still observes Bool and cannot use it as an integer operand.
        assert_eq!(predicate.ty(), ScalarType::Bool);
        for n in [0, 1, 2, u32::MAX as u64] {
            let value = ScalarValue::Integer {
                bits: 32,
                value: Affine::constant(n, u32::MAX as u64),
            };
            assert_eq!(value.ty(), ScalarType::Integer(32));
            assert_eq!(value.as_bool().is_some(), n <= 1);
            assert!(value.at_width(64).is_none());
        }
    }

    #[test]
    fn exact_select_normalizes_inverted_conditions_and_preserves_widths_and_arms() {
        let a = Affine::parameter(0);
        let b = Affine::parameter(1);
        for bits in [32, 64] {
            let p = Predicate::compare(CompareKind::SignedLess, a, b, false, bits);
            let selected = ScalarValue::select(bits, p, a, b);
            assert_eq!(selected, ScalarValue::select(bits, p.inverted(), b, a));
            assert_ne!(selected, ScalarValue::select(bits, p, b, a));
            assert_eq!(
                ScalarValue::select(bits, p, a, a),
                ScalarValue::Integer { bits, value: a }
            );
            assert!(selected.as_affine(bits).is_none());
            assert!(selected.as_bool().is_none());
            assert!(
                selected
                    .at_width(if bits == 32 { 64 } else { 32 })
                    .is_none()
            );
        }
    }

    #[test]
    fn boolean_cmp_zero_conditions_match_actual_zero_one_subtraction() {
        for bits in [32, 64] {
            for truth in [false, true] {
                let value = ScalarValue::Bool(Predicate::Constant(truth));
                let zero = ScalarValue::Integer {
                    bits,
                    value: Affine::constant(0, u64::MAX),
                };
                let flags = ComparisonFlags::from_values(bits, value, zero).unwrap();
                let ordinary = ComparisonFlags::new(
                    bits,
                    Affine::constant(u64::from(truth), u64::MAX),
                    Affine::constant(0, u64::MAX),
                );
                for cc in 0..=15 {
                    assert_eq!(flags.condition(cc), ordinary.condition(cc));
                }
                let one = ScalarValue::Integer {
                    bits,
                    value: Affine::constant(1, u64::MAX),
                };
                assert!(ComparisonFlags::from_values(bits, value, one).is_none());
            }
        }
    }
}
