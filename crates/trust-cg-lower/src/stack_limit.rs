// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! U10 prologue stack-limit request tags (`docs/u10-prologue-stack-limit.md`
//! §1-§2): the reserved trust-ir `ProofAnnotation::Custom` tags a producer
//! puts on a function, their canonical decoding, and the module-level checks
//! that bind a request to its overflow action.
//!
//! A tag only ever *adds* a check and a branch to a handler the module itself
//! names, so a forged tag can neither skip a check nor grant authority. Every
//! malformed, duplicate or conflicting combination is refused here with
//! [`StackLimitTagError`], before any lowering; nothing is silently dropped.
//! Target support (which backend can emit the check) is decided by the
//! backend, never here.

use trust_cg_ir::function::{
    STACK_LIMIT_MAX_POINTEE_OFFSET, StackLimitOverflow, StackLimitRequest, StackLimitSource,
};
use trust_ir::{CallingConv, Function as TrustIrFunction, Inst, Module, ProofAnnotation};

/// High half of every request tag: `0x534C_0000 | kind<<15 | k<<12 | off/8`.
pub const STACK_LIMIT_REQUEST_TAG_BASE: u32 = 0x534C_0000;
/// The bits of a tag that identify it as a request.
pub const STACK_LIMIT_REQUEST_TAG_MASK: u32 = 0xFFFF_0000;
/// Marks a function as the overflow handler for its `FuncTy` ("SLH").
pub const STACK_LIMIT_HANDLER_TAG: u32 = 0x0053_4C48;
/// On a requester: overflow executes `brk` instead of calling a handler ("SLT").
pub const STACK_LIMIT_TRAP_TAG: u32 = 0x0053_4C54;

/// Highest parameter index a request tag can name (3 bits).
pub const STACK_LIMIT_MAX_PARAM: u8 = 7;

/// Whether `tag` is one of the reserved U10 tags (a request, the handler tag
/// or the trap tag). These tags are consumed by [`decode_function_request`],
/// never reported as dropped proofs.
pub fn is_stack_limit_tag(tag: u32) -> bool {
    tag & STACK_LIMIT_REQUEST_TAG_MASK == STACK_LIMIT_REQUEST_TAG_BASE
        || tag == STACK_LIMIT_HANDLER_TAG
        || tag == STACK_LIMIT_TRAP_TAG
}

/// The canonical request tag for `param` and `source`, for producers and
/// tests. `None` when the request is not representable: a parameter above
/// [`STACK_LIMIT_MAX_PARAM`], or a `Pointee` offset that is unaligned or
/// above [`STACK_LIMIT_MAX_POINTEE_OFFSET`].
pub fn encode_request_tag(param: u8, source: StackLimitSource) -> Option<u32> {
    if param > STACK_LIMIT_MAX_PARAM {
        return None;
    }
    let (kind, off8) = match source {
        StackLimitSource::Value => (0u32, 0u32),
        StackLimitSource::Pointee { offset } => {
            if offset % 8 != 0 || offset > STACK_LIMIT_MAX_POINTEE_OFFSET {
                return None;
            }
            (1, u32::from(offset / 8))
        }
    };
    Some(STACK_LIMIT_REQUEST_TAG_BASE | (kind << 15) | (u32::from(param) << 12) | off8)
}

/// A refused U10 tag combination. Every variant names the canonical-encoding
/// rule it breaks (§1 of the design).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum StackLimitTagError {
    /// Kind 0 (`Value`) carries no offset; a nonzero offset field is not
    /// canonical.
    #[error("request tag {tag:#010x} is kind 0 (Value) with a nonzero offset field")]
    ValueWithOffset {
        /// The offending tag.
        tag: u32,
    },
    /// Two request tags on one function (duplicate or conflicting).
    #[error("two request tags ({first:#010x}, {second:#010x}) on one function")]
    DuplicateRequest {
        /// The first request tag.
        first: u32,
        /// The second request tag.
        second: u32,
    },
    /// The handler or trap tag appears twice.
    #[error("tag {tag:#010x} appears more than once")]
    DuplicateTag {
        /// The repeated tag.
        tag: u32,
    },
    /// A function is both a requester and a handler.
    #[error("a function cannot both request a stack limit and be an overflow handler")]
    RequestAndHandler,
    /// The trap tag without a request.
    #[error("the Trap tag {STACK_LIMIT_TRAP_TAG:#010x} needs a request tag on the same function")]
    TrapWithoutRequest,
    /// A tagged function that is not a definition.
    #[error("only a function definition can carry a stack-limit tag")]
    NotADefinition,
    /// The function's calling convention is outside v1.
    #[error(
        "calling convention {conv:?} is outside v1 (C, Fast, Cold and Rust only); its \
         register assignment is not the AAPCS64 one the check reads"
    )]
    UnsupportedConvention {
        /// The refused convention.
        conv: CallingConv,
    },
    /// A variadic function type.
    #[error("a variadic function cannot carry a stack-limit tag")]
    Variadic,
    /// The function type id does not name a module function type.
    #[error("function type id {0} is not in the module")]
    UnknownFuncTy(u32),
    /// The request names a parameter the function does not have.
    #[error("request names parameter {param}, but the function has {params} parameters")]
    NoSuchParam {
        /// The requested parameter index.
        param: u8,
        /// The function's parameter count.
        params: usize,
    },
    /// No handler is tagged for the requester's function type.
    #[error(
        "no function in the module is tagged as the overflow handler \
         ({STACK_LIMIT_HANDLER_TAG:#010x}) for this function's type and convention, and the \
         function is not tagged Trap ({STACK_LIMIT_TRAP_TAG:#010x})"
    )]
    NoHandler,
    /// More than one handler for the requester's function type.
    #[error("more than one overflow handler is tagged for this function's type: {0:?}")]
    AmbiguousHandler(Vec<String>),
    /// The handler would call: its overflow path runs on an exhausted stack.
    #[error("overflow handler `{handler}` contains a call; a handler must make no call")]
    HandlerCalls {
        /// The handler's name.
        handler: String,
    },
}

/// The reserved tags one function carries, decoded and checked for
/// canonical form, before any module-level binding.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct FunctionTags {
    request: Option<(u8, StackLimitSource)>,
    handler: bool,
    trap: bool,
}

fn decode_request_tag(tag: u32) -> Result<(u8, StackLimitSource), StackLimitTagError> {
    let kind = (tag >> 15) & 1;
    // Three bits, so the narrowing cannot truncate.
    let param = ((tag >> 12) & 0x7) as u8;
    let off8 = tag & 0xFFF;
    let source = if kind == 0 {
        if off8 != 0 {
            return Err(StackLimitTagError::ValueWithOffset { tag });
        }
        StackLimitSource::Value
    } else {
        // `off8 <= 4095`, so `off8 * 8 <= STACK_LIMIT_MAX_POINTEE_OFFSET`.
        StackLimitSource::Pointee {
            offset: (off8 * 8) as u16,
        }
    };
    Ok((param, source))
}

fn function_tags(func: &TrustIrFunction) -> Result<FunctionTags, StackLimitTagError> {
    let mut tags = FunctionTags::default();
    let mut request_tag = None;
    for annotation in &func.proofs {
        let ProofAnnotation::Custom(tag) = annotation else {
            continue;
        };
        let tag = tag.index();
        if tag & STACK_LIMIT_REQUEST_TAG_MASK == STACK_LIMIT_REQUEST_TAG_BASE {
            if let Some(first) = request_tag {
                return Err(StackLimitTagError::DuplicateRequest { first, second: tag });
            }
            request_tag = Some(tag);
            tags.request = Some(decode_request_tag(tag)?);
        } else if tag == STACK_LIMIT_HANDLER_TAG {
            if tags.handler {
                return Err(StackLimitTagError::DuplicateTag { tag });
            }
            tags.handler = true;
        } else if tag == STACK_LIMIT_TRAP_TAG {
            if tags.trap {
                return Err(StackLimitTagError::DuplicateTag { tag });
            }
            tags.trap = true;
        }
    }
    if tags.request.is_some() && tags.handler {
        return Err(StackLimitTagError::RequestAndHandler);
    }
    if tags.trap && tags.request.is_none() {
        return Err(StackLimitTagError::TrapWithoutRequest);
    }
    Ok(tags)
}

fn admitted_convention(conv: CallingConv) -> bool {
    matches!(
        conv,
        CallingConv::C | CallingConv::Fast | CallingConv::Cold | CallingConv::Rust
    )
}

/// Shared checks for any tagged function: a definition, a v1 convention and
/// a non-variadic type.
fn check_tagged_function(
    func: &TrustIrFunction,
    module: &Module,
) -> Result<(), StackLimitTagError> {
    if func.blocks.is_empty() {
        return Err(StackLimitTagError::NotADefinition);
    }
    if !admitted_convention(func.calling_conv) {
        return Err(StackLimitTagError::UnsupportedConvention {
            conv: func.calling_conv,
        });
    }
    let func_ty = module
        .func_types
        .get(func.ty.index() as usize)
        .ok_or(StackLimitTagError::UnknownFuncTy(func.ty.index()))?;
    if func_ty.is_vararg {
        return Err(StackLimitTagError::Variadic);
    }
    Ok(())
}

fn function_makes_call(func: &TrustIrFunction) -> bool {
    func.blocks
        .iter()
        .flat_map(|block| &block.body)
        .any(|node| {
            // Every instruction that may run another function's code counts:
            // since trust-ir v55 a drop (and its unwinding twin) IS a call of
            // its type's glue, v56's `InvokeIndirect` is an indirect call, and
            // a v54 sited check's failure calls its panic entry.
            matches!(
                node.inst,
                Inst::Call { .. }
                    | Inst::CallIndirect { .. }
                    | Inst::CallCannotUnwind { .. }
                    | Inst::CallIndirectCannotUnwind { .. }
                    | Inst::Invoke { .. }
                    | Inst::InvokeIndirect { .. }
                    | Inst::Drop { .. }
                    | Inst::DropInvoke { .. }
                    | Inst::Assert { site: Some(_), .. }
                    | Inst::AssertInvoke { .. }
            )
        })
}

/// Decode and bind `func`'s U10 request against `module`.
///
/// Returns `Ok(None)` for a function with no request (including a valid
/// handler), and the bound request otherwise. The overflow action is `Trap`
/// when the trap tag is present; otherwise exactly one handler must be tagged
/// for the requester's function type (structurally equal `FuncTy`) and
/// calling convention, and that handler must contain no call instruction.
///
/// The parameter's *register* is not resolved here: that is target
/// signature lowering, done by the backend that emits the check.
pub fn decode_function_request(
    func: &TrustIrFunction,
    module: &Module,
) -> Result<Option<StackLimitRequest>, StackLimitTagError> {
    let tags = function_tags(func)?;
    if tags.handler {
        check_tagged_function(func, module)?;
        if function_makes_call(func) {
            return Err(StackLimitTagError::HandlerCalls {
                handler: func.name.clone(),
            });
        }
        return Ok(None);
    }
    let Some((param, source)) = tags.request else {
        return Ok(None);
    };
    check_tagged_function(func, module)?;
    let func_ty = module
        .func_types
        .get(func.ty.index() as usize)
        .ok_or(StackLimitTagError::UnknownFuncTy(func.ty.index()))?;
    if usize::from(param) >= func_ty.params.len() {
        return Err(StackLimitTagError::NoSuchParam {
            param,
            params: func_ty.params.len(),
        });
    }
    let overflow = if tags.trap {
        StackLimitOverflow::Trap
    } else {
        let mut handlers = Vec::new();
        for candidate in &module.functions {
            if candidate.calling_conv != func.calling_conv {
                continue;
            }
            let Some(candidate_ty) = module.func_types.get(candidate.ty.index() as usize) else {
                continue;
            };
            if candidate_ty != func_ty {
                continue;
            }
            // A malformed candidate is refused when the adapter reaches it;
            // here it simply does not bind.
            if function_tags(candidate).is_ok_and(|candidate_tags| candidate_tags.handler) {
                handlers.push(candidate.name.clone());
            }
        }
        match handlers.len() {
            0 => return Err(StackLimitTagError::NoHandler),
            1 => StackLimitOverflow::Handler {
                symbol: handlers.remove(0),
            },
            _ => return Err(StackLimitTagError::AmbiguousHandler(handlers)),
        }
    };
    Ok(Some(StackLimitRequest {
        param,
        source,
        overflow,
    }))
}

/// Whether any function of `module` carries a U10 tag. A backend with no
/// stack-limit lowering refuses such a module instead of dropping the tags.
pub fn module_requests_stack_limits(module: &Module) -> bool {
    module.functions.iter().any(|func| {
        func.proofs.iter().any(|annotation| {
            matches!(annotation, ProofAnnotation::Custom(tag) if is_stack_limit_tag(tag.index()))
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn call_boundary_overflow_handlers_are_not_call_free() {
        use trust_ir::{Block, BlockId, FuncId, FuncTy, InstrNode, ProofTag, ValueId};
        let mut module = Module::new("boundary-stack-handler");
        let signature = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut handler =
            TrustIrFunction::new(FuncId::new(0), "overflow", signature, BlockId::new(0));
        handler.calling_conv = CallingConv::C;
        handler.proofs.push(ProofAnnotation::Custom(ProofTag::new(
            STACK_LIMIT_HANDLER_TAG,
        )));
        let mut entry = Block::new(BlockId::new(0));
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        handler.blocks.push(entry);
        assert_eq!(decode_function_request(&handler, &module), Ok(None));
        for inst in [
            Inst::CallCannotUnwind {
                callee: FuncId::new(1),
                args: vec![],
            },
            Inst::CallIndirectCannotUnwind {
                callee: ValueId::new(0),
                sig: signature,
                args: vec![],
                calling_conv: CallingConv::C,
            },
        ] {
            let mut calling_handler = handler.clone();
            // Scan the whole body, including an unreachable block. Dead code
            // does not authorize a handler advertised as structurally call-free.
            let mut unreachable = Block::new(BlockId::new(1));
            unreachable.body.push(InstrNode::new(inst));
            unreachable.body.push(InstrNode::new(Inst::Unreachable));
            calling_handler.blocks.push(unreachable);
            assert_eq!(
                decode_function_request(&calling_handler, &module),
                Err(StackLimitTagError::HandlerCalls {
                    handler: "overflow".to_string(),
                })
            );
        }
    }

    #[test]
    fn request_tags_round_trip_and_reject_non_canonical_forms() {
        for param in 0..=STACK_LIMIT_MAX_PARAM {
            for source in [
                StackLimitSource::Value,
                StackLimitSource::Pointee { offset: 0 },
                StackLimitSource::Pointee { offset: 8 },
                StackLimitSource::Pointee {
                    offset: STACK_LIMIT_MAX_POINTEE_OFFSET,
                },
            ] {
                let tag = encode_request_tag(param, source).unwrap();
                assert!(is_stack_limit_tag(tag));
                assert_eq!(decode_request_tag(tag), Ok((param, source)));
            }
        }
        assert_eq!(encode_request_tag(8, StackLimitSource::Value), None);
        assert_eq!(
            encode_request_tag(0, StackLimitSource::Pointee { offset: 4 }),
            None
        );
        assert_eq!(
            encode_request_tag(
                0,
                StackLimitSource::Pointee {
                    offset: STACK_LIMIT_MAX_POINTEE_OFFSET + 8
                }
            ),
            None
        );
        let value_with_offset = STACK_LIMIT_REQUEST_TAG_BASE | 1;
        assert_eq!(
            decode_request_tag(value_with_offset),
            Err(StackLimitTagError::ValueWithOffset {
                tag: value_with_offset
            })
        );
        assert!(is_stack_limit_tag(STACK_LIMIT_HANDLER_TAG));
        assert!(is_stack_limit_tag(STACK_LIMIT_TRAP_TAG));
        // The protector tags and the debug-provenance namespaces stay outside.
        for other in [
            0x0053_5350,
            0x0053_5351,
            0x004C_4D50,
            0x8000_0000,
            0x534D_0000,
        ] {
            assert!(!is_stack_limit_tag(other), "{other:#x}");
        }
    }
}
