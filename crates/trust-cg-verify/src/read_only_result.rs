// Copyright 2026 Andrew Yates | Apache-2.0
//! Expression construction from the actual independently replayed readonly
//! source result. No new memory evaluator, call summary or permission oracle.
use crate::smt::{SmtExpr as E, SmtSort};
use crate::source_bound_frame::ReadOnlySourceQueries;
use std::sync::Arc;

// A true ITE shares an arbitrary caller root without recursively copying its
// inline UF arguments once per occurrence. This is the existing SMT ITE, not
// a fresh opaque alias. The inserted roots are never recursively substituted.
fn shared(root: &Arc<E>) -> E {
    E::Ite {
        cond: Arc::new(E::BoolConst(true)),
        then_expr: root.clone(),
        else_expr: root.clone(),
    }
}

pub(super) fn instantiate(
    source: &ReadOnlySourceQueries<'_>,
    arguments: &[Arc<E>],
    memory: &Arc<E>,
) -> Result<Arc<E>, String> {
    let arity = source.original_parameter_count();
    if arguments.len() != arity || !(1..=8).contains(&arity) {
        return Err("readonly call argument arity differs from original source".into());
    }
    let mut roots = arguments.iter().map(Arc::as_ref).collect::<Vec<_>>();
    roots.push(memory.as_ref());
    roots.push(source.original_result().as_ref());
    let scan = crate::smt_raw_print::preflight_roots(&roots)
        .map_err(|e| format!("readonly call input inspection: {e}"))?;
    // Reserve a worst-case true-ITE wrapper at every source node BEFORE any
    // source/input clone or substitution. Inserted root DAGs remain shared.
    let n = scan.order.len();
    if scan
        .order
        .len()
        .saturating_add(n.saturating_mul(3))
        .saturating_add((arity + 2) * 3)
        > crate::smt_raw_print::MAX_NODES
        || scan
            .edges
            .saturating_add(n.saturating_mul(4))
            .saturating_add((arity + 2) * 4)
            > crate::smt_raw_print::MAX_EDGES
    {
        return Err("readonly combined call expression shape limit".into());
    }
    // The existing typed postorder view validates every child, rather than
    // trusting a top-level declared BV width or array sort on hostile input.
    let mut tuple_arguments = arguments.iter().map(shared).collect::<Vec<_>>();
    tuple_arguments.push(shared(memory));
    tuple_arguments.push(shared(source.original_result()));
    let tuple = E::UF {
        name: String::new(),
        args: tuple_arguments,
        ret_sort: SmtSort::Bool,
    };
    let typed = tuple
        .try_rewrite_dag(&mut |view| {
            let sort = crate::smt_raw_print::checked_sort(view)?;
            if matches!(view,E::UF{name,..} if name.is_empty()) {
                Ok(Some(view.clone()))
            } else {
                Ok(Some(E::UF {
                    name: "readonly-call-sort-view".into(),
                    args: vec![],
                    ret_sort: sort,
                }))
            }
        })
        .map_err(|e: crate::smt_raw_print::CompactPrintRefusal| {
            format!("readonly call input sorts: {e}")
        })?;
    let Some(E::UF { args, .. }) = typed else {
        return Err("readonly call input type view absent".into());
    };
    if args[..arity]
        .iter()
        .any(|a| a.sort() != SmtSort::BitVec(64))
        || args[arity].sort() != crate::memory_proofs::memory_sort()
        || args[arity + 1].sort() != SmtSort::BitVec(64)
    {
        return Err("readonly call requires original 64-bit arguments and byte array".into());
    }
    let result = source
        .original_result()
        .try_rewrite_dag(&mut |node| -> Result<Option<E>, String> {
            match node {
                E::Var { name, width: 64 } => {
                    let index = (0..arity)
                        .find(|i| name == &format!("abi_x{i}"))
                        .ok_or("readonly result contains a foreign formal argument")?;
                    Ok(Some(shared(&arguments[index])))
                }
                E::Var { .. } => Err("readonly result formal width differs".into()),
                E::UF {
                    name,
                    args,
                    ret_sort,
                } if name == "entry_memory"
                    && args.is_empty()
                    && *ret_sort == crate::memory_proofs::memory_sort() =>
                {
                    Ok(Some(shared(memory)))
                }
                E::UF { .. } => Err("readonly result contains a foreign source function".into()),
                _ => Ok(None),
            }
        })?;
    Ok(Arc::new(result.unwrap_or_else(|| {
        source.original_result().as_ref().clone()
    })))
}
