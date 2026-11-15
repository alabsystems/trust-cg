// trust-cg-verify/tests/wasm_local_tv_control.rs - the wasm control-cleanup validator
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`trust_cg_verify::wasm_local_tv::validate_control`] on hand-built
//! function bodies. Each cleanup the emission pass makes (`wasm/opt/
//! control.rs`) is accepted: a `br` or `return` that falling through already
//! does, dead code after a transfer or after a construct no path leaves (with
//! the `unreachable` filler validation needs), a `block` or `loop` no branch
//! names, an empty `else` arm, an `if; br; end` arm as `br_if`. Each rule has
//! negative controls the validator refuses with their class: a branch whose
//! fall-through goes elsewhere or discards a value, a `br` to a `loop`
//! deleted, a `return` that drops values below its results, reachable code
//! deleted, a named block unwrapped or unwrapped without renumbering its
//! branches, a non-empty `else` deleted, a `br_if` at the old depth or over
//! an arm that pushes a value; so are swapped arms and `br_table` entries,
//! a changed instruction or relocation, a relocation on a control
//! instruction, the filler or an unreached `end` (on either side), changed
//! locals, post code the
//! simulation never reaches, a misplaced filler, an unreached `end` whose
//! heights differ, a typed block and an unreached function end with results.
//!
//! The entry `validate_control`, its request and report are provisional
//! surfaces (docs/wasm32_perf_roadmap.md, "Pending owner sign-off").

use trust_cg_verify::wasm_cfg_proofs::{FuncSig, ValKind};
use trust_cg_verify::wasm_local_tv::{
    ControlTvReport, ControlTvRequest, TvBody, TvFailure, TvFailureKind, TvReloc, TvTypes,
    validate_control,
};

const UNREACHABLE: u8 = 0x00;
const BLOCK: u8 = 0x02;
const LOOP: u8 = 0x03;
const IF: u8 = 0x04;
const ELSE: u8 = 0x05;
const END: u8 = 0x0b;
const BR: u8 = 0x0c;
const BR_IF: u8 = 0x0d;
const BR_TABLE: u8 = 0x0e;
const RETURN: u8 = 0x0f;
const CALL: u8 = 0x10;
const DROP: u8 = 0x1a;
const GET: u8 = 0x20;
const SET: u8 = 0x21;
const I32_CONST: u8 = 0x41;
const I32_ADD: u8 = 0x6a;
const I32_SUB: u8 = 0x6b;
const VOID: u8 = 0x40;
const I32_TY: u8 = 0x7f;

use ValKind::I32;

/// Function 0 is `(i32) -> (i32)`; nothing else has a type.
struct OneCallee;

impl TvTypes for OneCallee {
    fn func(&self, index: u32) -> Option<FuncSig> {
        (index == 0).then(|| FuncSig {
            params: vec![I32],
            results: vec![I32],
        })
    }
    fn type_at(&self, _: u32) -> Option<FuncSig> {
        None
    }
    fn global(&self, _: u32) -> Option<ValKind> {
        None
    }
}

struct Case<'a> {
    results: usize,
    pre_locals: &'a [ValKind],
    pre: &'a [u8],
    pre_relocs: &'a [TvReloc],
    post_locals: &'a [ValKind],
    post: &'a [u8],
    post_relocs: &'a [TvReloc],
}

fn case<'a>(results: usize, pre: &'a [u8], post: &'a [u8]) -> Case<'a> {
    Case {
        results,
        pre_locals: &[I32],
        pre,
        pre_relocs: &[],
        post_locals: &[I32],
        post,
        post_relocs: &[],
    }
}

fn run(c: Case<'_>) -> Result<ControlTvReport, TvFailure> {
    validate_control(&ControlTvRequest {
        results: c.results,
        pre: TvBody {
            locals: c.pre_locals,
            code: c.pre,
            relocs: c.pre_relocs,
        },
        post: TvBody {
            locals: c.post_locals,
            code: c.post,
            relocs: c.post_relocs,
        },
        types: &OneCallee,
        max_work: 1 << 20,
    })
}

#[track_caller]
fn accepts(c: Case<'_>) -> ControlTvReport {
    run(c).unwrap_or_else(|f| panic!("refused: {f}"))
}

#[track_caller]
fn refuses(c: Case<'_>, kind: TvFailureKind) {
    match run(c) {
        Ok(r) => panic!("accepted a wrong cleanup: {r:?}"),
        Err(f) => assert_eq!(f.kind, kind, "refused for another reason: {f}"),
    }
}

// ---- Fall-through branches and returns ----

/// `block; (if p0 { l1 = 1; br 1 } else { l1 = 2 }); end; l1`: the `br 1`
/// leaves the `then` arm for the block's end, which falling through reaches.
const ARM_BR: &[u8] = &[
    BLOCK, VOID, GET, 0, IF, VOID, I32_CONST, 1, SET, 1, BR, 1, ELSE, I32_CONST, 2, SET, 1, END,
    END, GET, 1,
];

#[test]
fn a_branch_falling_through_reaches_is_removed() {
    // The `br` deleted, then the block no branch names unwrapped.
    let post = &[
        GET, 0, IF, VOID, I32_CONST, 1, SET, 1, ELSE, I32_CONST, 2, SET, 1, END, GET, 1,
    ];
    let r = accepts(case(1, ARM_BR, post));
    assert!(r.paired >= 5, "{r:?}");
    // Only the `br` deleted.
    accepts(case(
        1,
        ARM_BR,
        &[
            BLOCK, VOID, GET, 0, IF, VOID, I32_CONST, 1, SET, 1, ELSE, I32_CONST, 2, SET, 1, END,
            END, GET, 1,
        ],
    ));
}

#[test]
fn a_branch_whose_fall_through_goes_elsewhere_is_refused() {
    // `block; block; br 1; end; l1 = 7; end; l1`: falling through the inner
    // `end` runs `l1 = 7`, which the `br 1` skips.
    let pre = &[
        BLOCK, VOID, BLOCK, VOID, BR, 1, END, I32_CONST, 7, SET, 1, END, GET, 1,
    ];
    let post = &[
        BLOCK, VOID, BLOCK, VOID, END, I32_CONST, 7, SET, 1, END, GET, 1,
    ];
    refuses(case(1, pre, post), TvFailureKind::EffectMismatch);
}

#[test]
fn a_branch_that_discards_a_value_is_kept() {
    // `block; i32.const 5; br 0; end`: the `br` drops the 5. Without it the
    // block's end is reached with a value on the stack.
    let pre = &[BLOCK, VOID, I32_CONST, 5, BR, 0, END, GET, 0];
    let post = &[BLOCK, VOID, I32_CONST, 5, END, GET, 0];
    refuses(case(1, pre, post), TvFailureKind::StackMismatch);
}

#[test]
fn a_branch_to_a_loop_is_never_a_fall_through() {
    // `loop; p0 = p0 - 1; p0; br_if 0... `: here `loop; ...; br_if 1 ...; br 0;
    // end` re-enters the loop; deleting the `br 0` leaves after one pass.
    let pre = &[
        BLOCK, VOID, LOOP, VOID, GET, 0, I32_CONST, 1, I32_SUB, SET, 0, GET, 0, BR_IF, 1, BR, 0,
        END, END, GET, 0,
    ];
    let post = &[
        BLOCK, VOID, LOOP, VOID, GET, 0, I32_CONST, 1, I32_SUB, SET, 0, GET, 0, BR_IF, 1, END, END,
        GET, 0,
    ];
    refuses(case(1, pre, post), TvFailureKind::StructureMismatch);
}

#[test]
fn a_final_return_is_removed_and_one_dropping_values_is_kept() {
    accepts(case(1, &[GET, 0, RETURN], &[GET, 0]));
    accepts(case(1, &[GET, 0, RETURN, UNREACHABLE], &[GET, 0]));
    // `p0; p0; return` returns the top value; without the `return` the
    // function ends with two values.
    refuses(
        case(1, &[GET, 0, GET, 0, RETURN], &[GET, 0, GET, 0]),
        TvFailureKind::StackMismatch,
    );
    // Dropping the value instead of returning it continues where the pre
    // body returns.
    refuses(
        case(
            1,
            &[GET, 0, I32_CONST, 1, RETURN],
            &[GET, 0, I32_CONST, 1, DROP],
        ),
        TvFailureKind::StructureMismatch,
    );
}

// ---- Dead code ----

#[test]
fn code_after_a_transfer_is_removed_and_reachable_code_is_not() {
    // `block; br 0; l1 = 3; end; l1`: the store to l1 never runs.
    let pre = &[BLOCK, VOID, BR, 0, I32_CONST, 3, SET, 1, END, GET, 1];
    accepts(case(1, pre, &[BLOCK, VOID, BR, 0, END, GET, 1]));
    accepts(case(1, pre, &[GET, 1]));
    // `p0; if; l1 = 3; end; l1`: the store runs when p0 is nonzero.
    let pre = &[GET, 0, IF, VOID, I32_CONST, 3, SET, 1, END, GET, 1];
    let post = &[GET, 0, IF, VOID, END, GET, 1];
    refuses(case(1, pre, post), TvFailureKind::EffectMismatch);
}

#[test]
fn post_code_the_simulation_never_reaches_is_refused() {
    // The dead store is still in the post body: the check never saw it run,
    // so it does not vouch for its validity.
    let pre = &[BLOCK, VOID, BR, 0, I32_CONST, 3, SET, 1, END, GET, 1];
    let post = &[BLOCK, VOID, BR, 0, I32_CONST, 3, SET, 1, END, GET, 1];
    refuses(case(1, pre, post), TvFailureKind::StructureMismatch);
}

/// `block; loop; p0; br_if 1; br 0; end; unreachable; end; 9`: no path
/// leaves the loop but through `br_if 1`.
const SPIN: &[u8] = &[
    BLOCK,
    VOID,
    LOOP,
    VOID,
    GET,
    0,
    BR_IF,
    1,
    BR,
    0,
    END,
    UNREACHABLE,
    END,
    I32_CONST,
    9,
];

#[test]
fn the_filler_after_a_construct_no_path_leaves_is_accepted_where_it_belongs() {
    // The `unreachable` after the loop is never executed; deleting it leaves
    // the block's `end` after the loop's, at the same height.
    accepts(case(1, SPIN, SPIN));
    accepts(case(
        1,
        SPIN,
        &[
            BLOCK, VOID, LOOP, VOID, GET, 0, BR_IF, 1, BR, 0, END, END, I32_CONST, 9,
        ],
    ));
    // A function with a result whose body ends with such a loop needs the
    // filler: without it the function's end is unreached with no transfer.
    let pre = &[LOOP, VOID, GET, 0, DROP, BR, 0, END, UNREACHABLE];
    accepts(case(1, pre, pre));
    refuses(
        case(1, pre, &[LOOP, VOID, GET, 0, DROP, BR, 0, END]),
        TvFailureKind::StructureMismatch,
    );
    // A loop whose body is only its back edge has no real instruction to
    // pair: the cycle is refused.
    let spin = &[LOOP, VOID, BR, 0, END, UNREACHABLE];
    refuses(case(1, spin, spin), TvFailureKind::StructureMismatch);
    // A filler that is not right after an unreached `end` is dead code the
    // check never saw.
    refuses(
        case(
            1,
            SPIN,
            &[
                BLOCK,
                VOID,
                LOOP,
                VOID,
                GET,
                0,
                BR_IF,
                1,
                BR,
                0,
                UNREACHABLE,
                END,
                UNREACHABLE,
                END,
                I32_CONST,
                9,
            ],
        ),
        TvFailureKind::StructureMismatch,
    );
}

#[test]
fn an_unreached_end_at_another_height_is_refused() {
    // `block; p0; loop; p0; br_if 1; br 0; end; unreachable; end; p0`: the
    // loop is entered one value above the block, so without the filler the
    // block's `end` would follow the loop's with a value it does not take.
    let pre = &[
        BLOCK,
        VOID,
        GET,
        0,
        LOOP,
        VOID,
        GET,
        0,
        BR_IF,
        1,
        BR,
        0,
        END,
        UNREACHABLE,
        END,
        GET,
        0,
    ];
    accepts(case(1, pre, pre));
    let post = &[
        BLOCK, VOID, GET, 0, LOOP, VOID, GET, 0, BR_IF, 1, BR, 0, END, END, GET, 0,
    ];
    refuses(case(1, pre, post), TvFailureKind::StructureMismatch);
}

// ---- Unnamed constructs ----

/// `block; block; p0; br_if 1; l1 = 4; end; l1 = l1 + 1; end; l1`.
const NESTED: &[u8] = &[
    BLOCK, VOID, BLOCK, VOID, GET, 0, BR_IF, 1, I32_CONST, 4, SET, 1, END, GET, 1, I32_CONST, 1,
    I32_ADD, SET, 1, END, GET, 1,
];

#[test]
fn an_unnamed_block_is_unwrapped_with_its_branches_renumbered() {
    // The inner block is named by nothing: unwrapped, `br_if 1` becomes
    // `br_if 0`.
    let post = &[
        BLOCK, VOID, GET, 0, BR_IF, 0, I32_CONST, 4, SET, 1, GET, 1, I32_CONST, 1, I32_ADD, SET, 1,
        END, GET, 1,
    ];
    accepts(case(1, NESTED, post));
    // Not renumbered: `br_if 1` now names the function and returns.
    let wrong = &[
        BLOCK, VOID, GET, 0, BR_IF, 1, I32_CONST, 4, SET, 1, GET, 1, I32_CONST, 1, I32_ADD, SET, 1,
        END, GET, 1,
    ];
    assert!(run(case(1, NESTED, wrong)).is_err());
    // The outer block is named by the `br_if`: unwrapping it changes where
    // the branch goes.
    let named = &[
        BLOCK, VOID, GET, 0, BR_IF, 0, I32_CONST, 4, SET, 1, END, GET, 1, I32_CONST, 1, I32_ADD,
        SET, 1, GET, 1,
    ];
    refuses(case(1, NESTED, named), TvFailureKind::StructureMismatch);
}

#[test]
fn an_unnamed_loop_is_unwrapped() {
    let pre = &[
        LOOP, VOID, GET, 0, I32_CONST, 1, I32_ADD, SET, 1, END, GET, 1,
    ];
    accepts(case(
        1,
        pre,
        &[GET, 0, I32_CONST, 1, I32_ADD, SET, 1, GET, 1],
    ));
}

// ---- Empty else arms and br_if ----

#[test]
fn an_empty_else_is_removed_and_a_full_one_is_not() {
    let pre = &[GET, 0, IF, VOID, I32_CONST, 3, SET, 1, ELSE, END, GET, 1];
    accepts(case(
        1,
        pre,
        &[GET, 0, IF, VOID, I32_CONST, 3, SET, 1, END, GET, 1],
    ));
    let pre = &[
        GET, 0, IF, VOID, I32_CONST, 3, SET, 1, ELSE, I32_CONST, 4, SET, 1, END, GET, 1,
    ];
    let post = &[
        GET, 0, IF, VOID, I32_CONST, 3, SET, 1, I32_CONST, 4, SET, 1, END, GET, 1,
    ];
    refuses(case(1, pre, post), TvFailureKind::EffectMismatch);
}

#[test]
fn swapped_arms_are_refused() {
    let pre = &[
        GET, 0, IF, VOID, I32_CONST, 3, SET, 1, ELSE, I32_CONST, 4, SET, 1, END, GET, 1,
    ];
    let post = &[
        GET, 0, IF, VOID, I32_CONST, 4, SET, 1, ELSE, I32_CONST, 3, SET, 1, END, GET, 1,
    ];
    refuses(case(1, pre, post), TvFailureKind::EffectMismatch);
}

/// `block; p0; if; br 1; end; l1 = 6; end; l1`.
const IF_BR: &[u8] = &[
    BLOCK, VOID, GET, 0, IF, VOID, BR, 1, END, I32_CONST, 6, SET, 1, END, GET, 1,
];

#[test]
fn a_one_branch_arm_becomes_br_if() {
    let post = &[
        BLOCK, VOID, GET, 0, BR_IF, 0, I32_CONST, 6, SET, 1, END, GET, 1,
    ];
    accepts(case(1, IF_BR, post));
    // The old depth names the function: the branch would return.
    let stale = &[
        BLOCK, VOID, GET, 0, BR_IF, 1, I32_CONST, 6, SET, 1, END, GET, 1,
    ];
    assert!(run(case(1, IF_BR, stale)).is_err());
    // An arm with more than the branch: the store before it is lost.
    let pre = &[
        BLOCK, VOID, GET, 0, IF, VOID, I32_CONST, 6, SET, 1, BR, 1, END, END, GET, 1,
    ];
    let post = &[
        BLOCK, VOID, GET, 0, BR_IF, 0, I32_CONST, 6, SET, 1, END, GET, 1,
    ];
    refuses(case(1, pre, post), TvFailureKind::EffectMismatch);
}

// ---- Tables, instructions, relocations, locals, block types ----

#[test]
fn br_table_entries_are_paired_by_position() {
    let pre = &[
        BLOCK, VOID, BLOCK, VOID, GET, 0, BR_TABLE, 1, 0, 1, END, I32_CONST, 1, SET, 1, END, GET, 1,
    ];
    accepts(case(1, pre, pre));
    let swapped = &[
        BLOCK, VOID, BLOCK, VOID, GET, 0, BR_TABLE, 1, 1, 0, END, I32_CONST, 1, SET, 1, END, GET, 1,
    ];
    refuses(case(1, pre, swapped), TvFailureKind::EffectMismatch);
}

#[test]
fn a_changed_instruction_relocation_or_local_is_refused() {
    let pre = &[GET, 0, CALL, 0x80, 0x80, 0x80, 0x80, 0x00, RETURN];
    let post_same = &[GET, 0, CALL, 0x80, 0x80, 0x80, 0x80, 0x00];
    let reloc = |offset| TvReloc {
        offset,
        kind: 0,
        target: 7,
        addend: 0,
    };
    let pre_r = [reloc(3)];
    accepts(Case {
        pre_relocs: &pre_r,
        post_relocs: &pre_r,
        ..case(1, pre, post_same)
    });
    let other = [TvReloc {
        target: 8,
        ..reloc(3)
    }];
    refuses(
        Case {
            pre_relocs: &pre_r,
            post_relocs: &other,
            ..case(1, pre, post_same)
        },
        TvFailureKind::RelocUnsupported,
    );
    refuses(
        case(
            1,
            &[GET, 0, I32_CONST, 1, I32_ADD],
            &[GET, 0, I32_CONST, 2, I32_ADD],
        ),
        TvFailureKind::EffectMismatch,
    );
    refuses(
        Case {
            post_locals: &[I32, I32],
            ..case(1, &[GET, 0], &[GET, 0])
        },
        TvFailureKind::StructureMismatch,
    );
}

#[test]
fn a_relocation_outside_a_paired_instruction_is_refused() {
    // The linker rewrites a relocated field, so a relocation on a depth, a
    // block type, the filler or an unreached `end` would change bytes the
    // simulation never compared; on either side it refuses the function.
    let at = |offset| {
        [TvReloc {
            offset,
            kind: 0,
            target: 7,
            addend: 0,
        }]
    };
    // `block; p0; br_if 0; l1 = 1; end; l1`: offsets 1 (block type) and 5
    // (`br_if` depth).
    let with_br_if = &[
        BLOCK, VOID, GET, 0, BR_IF, 0, I32_CONST, 1, SET, 1, END, GET, 1,
    ];
    accepts(case(1, with_br_if, with_br_if));
    for offset in [1, 5] {
        let r = at(offset);
        refuses(
            Case {
                post_relocs: &r,
                ..case(1, with_br_if, with_br_if)
            },
            TvFailureKind::RelocUnsupported,
        );
        refuses(
            Case {
                pre_relocs: &r,
                ..case(1, with_br_if, with_br_if)
            },
            TvFailureKind::RelocUnsupported,
        );
        refuses(
            Case {
                pre_relocs: &r,
                post_relocs: &r,
                ..case(1, with_br_if, with_br_if)
            },
            TvFailureKind::RelocUnsupported,
        );
    }
    // `block; p0; if; br 1; end; l1 = 1; end; l1`: offset 7 is the `br`
    // depth.
    let with_br = &[
        BLOCK, VOID, GET, 0, IF, VOID, BR, 1, END, I32_CONST, 1, SET, 1, END, GET, 1,
    ];
    accepts(case(1, with_br, with_br));
    let r = at(7);
    refuses(
        Case {
            post_relocs: &r,
            ..case(1, with_br, with_br)
        },
        TvFailureKind::RelocUnsupported,
    );
    // In SPIN, offset 10 is the loop's unreached `end` and 11 the filler.
    accepts(case(1, SPIN, SPIN));
    for offset in [10, 11] {
        let r = at(offset);
        refuses(
            Case {
                post_relocs: &r,
                ..case(1, SPIN, SPIN)
            },
            TvFailureKind::RelocUnsupported,
        );
    }
}

#[test]
fn a_typed_block_is_not_modelled() {
    let pre = &[BLOCK, I32_TY, GET, 0, END];
    refuses(case(1, pre, pre), TvFailureKind::Unsupported);
}
