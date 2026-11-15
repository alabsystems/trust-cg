# Stage 3 (OD-189) mutants, loaded by mutate.py (M, OWNER and SPLIT are its).
#   respell-off              no part is spelled a second time (the rule removed)
#   respell-no-bit-moves     the second spelling skips the bit moves
#   respell-drop-equations   the second spelling drops every equation claim
#   respell-fail-dropped     a part whose second spelling fails the part check
#                            is dropped instead of keeping its first spelling
#   respell-empty-kept       a part whose second spelling empties keeps its
#                            first spelling instead of being no part
EDITS = [
    ("respell-off", SPLIT,
     '        match respelled_part(first_definitions, first_claims) {\n',
     f'        if {M.format("respell-off")} {{\n            spelled.push(Spelled::Part(first));\n            continue;\n        }}\n'
     '        match respelled_part(first_definitions, first_claims) {\n'),
    ("respell-no-bit-moves", SPLIT,
     '    let (moved, claims) = substitute_bit_moves(definitions, claims);\n'
     '    let (unified, claims) = unify_definitions(moved, claims);\n'
     '    let (mut kept, _, mut stated) = inline_single_use(unified, E::bool_const(true), claims);\n'
     '    loop {\n        match drop_identities(&stated)? {\n',
     f'    let (moved, claims) = if {M.format("respell-no-bit-moves")} {{\n'
     '        (definitions, claims)\n    } else {\n        substitute_bit_moves(definitions, claims)\n    };\n'
     '    let (unified, claims) = unify_definitions(moved, claims);\n'
     '    let (mut kept, _, mut stated) = inline_single_use(unified, E::bool_const(true), claims);\n'
     '    loop {\n'
     f'        let dropped = if {M.format("respell-drop-equations")} {{\n'
     '            let mut terms = Vec::new();\n            let mut rest = &stated;\n'
     '            while let E::And { lhs, rhs } = rest {\n                terms.push(lhs.as_ref().clone());\n                rest = rhs.as_ref();\n            }\n'
     '            terms.push(rest.clone());\n            let count = terms.len();\n'
     '            let kept_terms: Vec<E> = terms.into_iter().filter(|term| !matches!(term, E::Eq { .. })).collect();\n'
     '            let changed = kept_terms.len() != count;\n'
     '            kept_terms.into_iter().rev().reduce(|tail, term| term.and_expr(tail)).map(|claims| (claims, changed))\n'
     '        } else {\n            drop_identities(&stated)\n        };\n'
     '        match dropped? {\n'),
    ("respell-fail-dropped", SPLIT,
     '                } else {\n                    spelled.push(Spelled::Part(first));\n                }\n',
     f'                }} else if !{M.format("respell-fail-dropped")} {{\n                    spelled.push(Spelled::Part(first));\n                }}\n'),
    ("respell-empty-kept", SPLIT,
     '            None => spelled.push(Spelled::Empty(cone, claim)),\n',
     f'            None if {M.format("respell-empty-kept")} => spelled.push(Spelled::Part(first)),\n'
     '            None => spelled.push(Spelled::Empty(cone, claim)),\n'),
]
