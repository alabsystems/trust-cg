# Stage 2 (OD-188) mutants, loaded by mutate.py (M, OWNER and SPLIT are its).
#   fold-sub-as-add          a constant `bvsub` folds to the sum
#   fold-shift-modulo        a constant shift by the width or more folds as a
#                            shift by the amount modulo the width
#   fold-udiv-zero           a constant division by zero folds to 0 (the
#                            crate sampler's convention, not SMT-LIB's)
#   fold-equal-false         an equation of two equal constants folds to false
#   subz-through-extract     the bvsub-zero identity also rewrites a difference
#                            compared with zero through an extract of its low
#                            bits (an equation of the operands: wrong when they
#                            differ above the extract)
#   subz-any-constant        a difference compared with any constant is an
#                            equation of its operands
#   claims-drop-true-guard   folded_claims drops an item whose guard has a
#                            literal folded to `true` (instead of `false`)
#   claims-drop-equations    folded_claims drops every equation claim, not only
#                            an equation of one term with itself
#   no-fold-cascade          a folded spelling that empties goes straight to
#                            the plain spelling (no slice-17 or slice-16 step)
#   fold-off                 the folded step is never taken (the rule removed)
EDITS = [
    ("fold-sub-as-add", SPLIT,
     '            (a.wrapping_sub(b), *width)\n',
     f'            (if {M.format("fold-sub-as-add")} {{ a.wrapping_add(b) }} else {{ a.wrapping_sub(b) }}, *width)\n'),
    ("fold-shift-modulo", SPLIT,
     '            (if b >= u128::from(*width) { 0 } else { a << b }, *width)\n',
     f'            (if {M.format("fold-shift-modulo")} {{ a << (b % u128::from(*width)) }} else if b >= u128::from(*width) {{ 0 }} else {{ a << b }}, *width)\n'),
    ("fold-udiv-zero", SPLIT,
     '            low_bits(u128::MAX, width)\n',
     f'            if {M.format("fold-udiv-zero")} {{ 0 }} else {{ low_bits(u128::MAX, width) }}\n'),
    ("fold-equal-false", SPLIT,
     '            return (a != b).then(|| E::bool_const(false));\n',
     f'            return (a != b || {M.format("fold-equal-false")}).then(|| E::bool_const(false));\n'),
    ("subz-through-extract", SPLIT,
     '''            for (difference, zero) in [(lhs, rhs), (rhs, lhs)] {
                if let (E::BvSub { lhs: x, rhs: y, .. }, E::BvConst { value: 0, .. }) =
                    (difference.as_ref(), zero.as_ref())
                {''',
     f'''            for (difference, zero) in [(lhs, rhs), (rhs, lhs)] {{
                let difference = match difference.as_ref() {{
                    E::Extract {{ low: 0, operand, .. }}
                        if {M.format("subz-through-extract")}
                            && matches!(operand.as_ref(), E::BvSub {{ .. }}) =>
                    {{
                        operand
                    }}
                    _ => difference,
                }};
                if let (E::BvSub {{ lhs: x, rhs: y, .. }}, E::BvConst {{ value: 0, .. }}) =
                    (difference.as_ref(), zero.as_ref())
                {{'''),
    ("subz-any-constant", SPLIT,
     '''                if let (E::BvSub { lhs: x, rhs: y, .. }, E::BvConst { value: 0, .. }) =
                    (difference.as_ref(), zero.as_ref())
                {''',
     f'''                if let (E::BvSub {{ lhs: x, rhs: y, .. }}, E::BvConst {{ value, .. }}) =
                    (difference.as_ref(), zero.as_ref())
                    && (*value == 0 || {M.format("subz-any-constant")})
                {{'''),
    ("claims-drop-true-guard", SPLIT,
     '                if literals.contains(&E::bool_const(false)) {\n',
     f'                if literals.contains(&E::bool_const(false))\n'
     f'                    || ({M.format("claims-drop-true-guard")} && literals.contains(&E::bool_const(true)))\n'
     '                {\n'),
    ("claims-drop-equations", SPLIT,
     '                if lhs == rhs {\n',
     f'                if lhs == rhs || {M.format("claims-drop-equations")} {{\n'),
    ("no-fold-cascade", OWNER,
     '            ValueNumbering::Every if self.fold => Self {\n',
     f'            ValueNumbering::Every if self.fold && {M.format("no-fold-cascade")} => Self {{\n'
     '                value_number: ValueNumbering::Off,\n                ..self\n            },\n'
     '            ValueNumbering::Every if self.fold => Self {\n'),
    ("fold-off", OWNER,
     '    let folds = value_numbered && encoding.value_number == ValueNumbering::Every && encoding.fold;\n',
     f'    let folds = value_numbered\n        && encoding.value_number == ValueNumbering::Every\n'
     f'        && encoding.fold\n        && !{M.format("fold-off")};\n'),
]
