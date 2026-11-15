// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;

fn diamond(depth: usize) -> SmtExpr {
    let mut node = Arc::new(SmtExpr::var("x", 8));
    for _ in 0..depth {
        node = Arc::new(SmtExpr::BvAdd {
            lhs: node.clone(),
            rhs: node,
            width: 8,
        });
    }
    node.as_ref().clone()
}

#[test]
fn shared_diamond_is_visited_once_per_input_node() {
    let input = diamond(32); // An expanded tree would contain > 8 billion nodes.
    let mut visits = 0;
    let result = input
        .try_rewrite_dag::<Infallible>(&mut |node| {
            visits += 1;
            Ok(matches!(node, SmtExpr::Var { .. }).then(|| SmtExpr::bv_const(3, 8)))
        })
        .unwrap()
        .unwrap();
    assert_eq!(visits, 33);
    let mut node = &result;
    for _ in 0..32 {
        let SmtExpr::BvAdd { lhs, rhs, width } = node else {
            panic!("diamond shape changed")
        };
        assert_eq!(*width, 8);
        assert!(Arc::ptr_eq(lhs, rhs), "rewritten DAG edge lost sharing");
        node = lhs;
    }
    assert_eq!(node, &SmtExpr::bv_const(3, 8));
}

#[test]
fn unchanged_diamond_is_visited_once_without_a_replacement() {
    let input = diamond(32);
    let mut visits = 0;
    let result = input
        .try_rewrite_dag::<Infallible>(&mut |_| {
            visits += 1;
            Ok(None)
        })
        .unwrap();
    assert!(result.is_none());
    assert_eq!(visits, 33);
}

#[test]
fn equal_but_separately_allocated_nodes_are_not_identity_merged() {
    let input = SmtExpr::BvAdd {
        lhs: Arc::new(SmtExpr::var("x", 8)),
        rhs: Arc::new(SmtExpr::var("x", 8)),
        width: 8,
    };
    let mut visits = 0;
    let result = input
        .try_rewrite_dag::<Infallible>(&mut |node| {
            visits += 1;
            Ok(matches!(node, SmtExpr::Var { .. }).then(|| SmtExpr::bv_const(3, 8)))
        })
        .unwrap()
        .unwrap();
    assert_eq!(visits, 3);
    let SmtExpr::BvAdd { lhs, rhs, .. } = result else {
        panic!("addition changed")
    };
    assert!(!Arc::ptr_eq(&lhs, &rhs));
}

#[test]
fn visitor_error_is_returned_without_a_partial_result() {
    let input = diamond(32);
    let mut visits = 0;
    let result = input.try_rewrite_dag(&mut |_| {
        visits += 1;
        Err("refused")
    });
    assert_eq!(result.unwrap_err(), "refused");
    assert_eq!(visits, 1);
}

#[test]
fn replacements_are_not_visited_again() {
    let input = SmtExpr::var("x", 8);
    let mut visits = 0;
    let result = input
        .try_rewrite_dag::<Infallible>(&mut |_| {
            visits += 1;
            Ok(Some(SmtExpr::var("y", 8)))
        })
        .unwrap()
        .unwrap();
    assert_eq!(result, SmtExpr::var("y", 8));
    assert_eq!(visits, 1);
}

#[test]
fn inline_uf_arguments_keep_source_order_and_visit_identity() {
    let input = SmtExpr::uf(
        "ordered",
        vec![
            SmtExpr::var("left", 8),
            SmtExpr::var("middle", 8),
            SmtExpr::var("right", 8),
        ],
        SmtSort::BitVec(8),
    );
    let mut visited = Vec::new();
    let result = input
        .try_rewrite_dag::<Infallible>(&mut |node| {
            let SmtExpr::Var { name, .. } = node else {
                return Ok(None);
            };
            visited.push(name.clone());
            Ok(Some(SmtExpr::bv_const(visited.len() as u64, 8)))
        })
        .unwrap()
        .unwrap();
    assert_eq!(visited, ["left", "middle", "right"]);
    assert_eq!(
        result.to_string(),
        "(ordered (_ bv1 8) (_ bv2 8) (_ bv3 8))"
    );
    assert_eq!(input.to_string(), "(ordered left middle right)");
}

#[test]
fn moving_inline_results_keeps_shared_results_for_later_users() {
    let shared = Arc::new(SmtExpr::var("shared", 8));
    let input = SmtExpr::And {
        lhs: Arc::new(SmtExpr::uf(
            "predicate",
            vec![SmtExpr::BvAdd {
                lhs: shared.clone(),
                rhs: shared.clone(),
                width: 8,
            }],
            SmtSort::Bool,
        )),
        rhs: Arc::new(SmtExpr::Eq {
            lhs: shared.clone(),
            rhs: shared,
        }),
    };
    let mut visits = 0;
    let result = input
        .try_rewrite_dag::<Infallible>(&mut |node| {
            visits += 1;
            Ok(matches!(node, SmtExpr::Var { .. }).then(|| SmtExpr::bv_const(9, 8)))
        })
        .unwrap()
        .unwrap();
    assert_eq!(visits, 5);
    let SmtExpr::And { lhs, rhs } = result else {
        panic!("conjunction changed")
    };
    let SmtExpr::UF { args, .. } = lhs.as_ref() else {
        panic!("UF changed")
    };
    let SmtExpr::BvAdd { lhs: a, rhs: b, .. } = &args[0] else {
        panic!("argument changed")
    };
    let SmtExpr::Eq { lhs: c, rhs: d } = rhs.as_ref() else {
        panic!("equality changed")
    };
    assert!(Arc::ptr_eq(a, b) && Arc::ptr_eq(a, c) && Arc::ptr_eq(a, d));
    assert_eq!(a.as_ref(), &SmtExpr::bv_const(9, 8));
}

#[test]
fn inline_uf_errors_follow_source_child_order() {
    let input = SmtExpr::uf(
        "ordered",
        vec![SmtExpr::var("first", 8), SmtExpr::var("second", 8)],
        SmtSort::Bool,
    );
    let mut visited = Vec::new();
    let result = input.try_rewrite_dag(&mut |node| {
        if let SmtExpr::Var { name, .. } = node {
            visited.push(name.clone());
            return Err(name.clone());
        }
        Ok(None)
    });
    assert_eq!(result.unwrap_err(), "first");
    assert_eq!(visited, ["first"]);
}

// Iterative test cleanup isolates traversal/copying from SmtExpr's ordinary
// recursive drop glue. Deep input/result destruction is not the tested claim.
fn discard_inline_expression(input: SmtExpr) {
    let mut pending = vec![input];
    while let Some(node) = pending.pop() {
        if let SmtExpr::UF { args, .. } = node {
            pending.extend(args);
        }
    }
}

#[test]
fn unchanged_deep_inline_uf_sibling_is_copied_iteratively_and_keeps_arcs() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let depth = 4096;
            let shared = Arc::new(SmtExpr::var("keep", 8));
            let mut deep = SmtExpr::BvAdd {
                lhs: shared.clone(),
                rhs: shared.clone(),
                width: 8,
            };
            for _ in 0..depth {
                deep = SmtExpr::uf("wrapper", vec![deep], SmtSort::BitVec(8));
            }
            let input = SmtExpr::uf(
                "outer",
                vec![
                    SmtExpr::var("change", 8),
                    deep,
                    SmtExpr::BvAdd {
                        lhs: shared.clone(),
                        rhs: shared.clone(),
                        width: 8,
                    },
                ],
                SmtSort::BitVec(8),
            );
            let mut visits = 0;
            assert!(
                input
                    .try_rewrite_dag::<Infallible>(&mut |_| {
                        visits += 1;
                        Ok(None)
                    })
                    .unwrap()
                    .is_none()
            );
            assert_eq!(visits, depth + 5);
            visits = 0;
            let result = input
                .try_rewrite_dag::<Infallible>(&mut |node| {
                    visits += 1;
                    Ok(
                        matches!(node, SmtExpr::Var { name, .. } if name == "change")
                            .then(|| SmtExpr::bv_const(7, 8)),
                    )
                })
                .unwrap()
                .unwrap();
            assert_eq!(visits, depth + 5);
            let SmtExpr::UF {
                name,
                args,
                ret_sort,
            } = &result
            else {
                panic!("outer UF changed")
            };
            assert_eq!(name, "outer");
            assert_eq!(ret_sort, &SmtSort::BitVec(8));
            assert_eq!(args.len(), 3);
            assert_eq!(args[0], SmtExpr::bv_const(7, 8));
            let mut node = &args[1];
            for _ in 0..depth {
                let SmtExpr::UF {
                    name,
                    args,
                    ret_sort,
                } = node
                else {
                    panic!("deep UF changed")
                };
                assert_eq!(name, "wrapper");
                assert_eq!(ret_sort, &SmtSort::BitVec(8));
                assert_eq!(args.len(), 1);
                node = &args[0];
            }
            let SmtExpr::BvAdd { lhs, rhs, width } = node else {
                panic!("deep leaf changed")
            };
            assert_eq!(*width, 8);
            assert!(Arc::ptr_eq(lhs, &shared) && Arc::ptr_eq(rhs, &shared));
            let SmtExpr::BvAdd { lhs, rhs, .. } = &args[2] else {
                panic!("last argument changed")
            };
            assert!(Arc::ptr_eq(lhs, &shared) && Arc::ptr_eq(rhs, &shared));
            discard_inline_expression(result);
            discard_inline_expression(input);
        })
        .unwrap()
        .join()
        .expect("deep inline input/copy must not recurse");
}

#[test]
fn changed_deep_inline_uf_values_are_moved_without_recursive_clone() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let depth = 4096;
            let mut input = SmtExpr::var("change", 8);
            for _ in 0..depth {
                input = SmtExpr::uf("wrapper", vec![input], SmtSort::BitVec(8));
            }
            let mut visits = 0;
            let result = input
                .try_rewrite_dag::<Infallible>(&mut |node| {
                    visits += 1;
                    Ok(matches!(node, SmtExpr::Var { .. }).then(|| SmtExpr::bv_const(9, 8)))
                })
                .unwrap()
                .unwrap();
            assert_eq!(visits, depth + 1);
            let mut node = &result;
            for _ in 0..depth {
                let SmtExpr::UF { args, .. } = node else {
                    panic!("UF changed")
                };
                assert_eq!(args.len(), 1);
                node = &args[0];
            }
            assert_eq!(node, &SmtExpr::bv_const(9, 8));
            discard_inline_expression(result);
            discard_inline_expression(input);
        })
        .unwrap()
        .join()
        .expect("changed inline values must move iteratively");
}

fn discard_shared_diamond(input: SmtExpr) {
    let mut keepers = Vec::new();
    let mut node = &input;
    while let SmtExpr::BvAdd { lhs, rhs, .. } = node {
        assert!(Arc::ptr_eq(lhs, rhs));
        keepers.push(lhs.clone());
        node = lhs;
    }
    drop(input);
    // Keepers were collected parent first: release in that same order so
    // every child still has its own keeper while its parent is destroyed.
    for node in keepers {
        drop(node);
    }
}

#[test]
fn deep_non_uf_dag_rewrite_is_iterative_and_retains_sharing() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let depth = 4096;
            let input = diamond(depth);
            let mut visits = 0;
            assert!(
                input
                    .try_rewrite_dag::<Infallible>(&mut |_| {
                        visits += 1;
                        Ok(None)
                    })
                    .unwrap()
                    .is_none()
            );
            assert_eq!(visits, depth + 1);
            visits = 0;
            let result = input
                .try_rewrite_dag::<Infallible>(&mut |node| {
                    visits += 1;
                    Ok(matches!(node, SmtExpr::Var { .. }).then(|| SmtExpr::bv_const(9, 8)))
                })
                .unwrap()
                .unwrap();
            assert_eq!(visits, depth + 1);
            let mut node = &result;
            for _ in 0..depth {
                let SmtExpr::BvAdd { lhs, rhs, .. } = node else {
                    panic!("diamond changed")
                };
                assert!(Arc::ptr_eq(lhs, rhs));
                node = lhs;
            }
            assert_eq!(node, &SmtExpr::bv_const(9, 8));
            discard_shared_diamond(result);
            discard_shared_diamond(input);
        })
        .unwrap()
        .join()
        .expect("deep DAG traversal must not recurse");
}
