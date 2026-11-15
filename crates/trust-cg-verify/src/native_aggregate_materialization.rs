// Copyright 2026 Andrew Yates | Apache-2.0
//! Pending actual two-lane readback and local byte-effect statements. These
//! contain no source/product equality, provider fact, successful-access premise,
//! theorem token, permission, replay capability or complete-body conclusion.

use super::*;

/// Borrowed original occurrence and actual snapshots with three UNPROVED
/// statements. Geometry/initialization demands remain on `observations`, never
/// preconditions installed as facts. The byte-effect endpoint is immediately
/// after the second materialization store, before any later public stores.
pub struct PendingNativeAggregateMaterialization<'a> {
    observations: &'a NativeAggregateTargetObservations,
    source: &'a native_aggregates::PendingNativeAggregateEvent,
    call: &'a TargetCall,
    stores: [&'a TargetAccess; 2],
    loads: [&'a TargetAccess; 2],
    obligations: [ProofObligation; 3],
}

impl PendingNativeAggregateMaterialization<'_> {
    pub fn observations(&self) -> &NativeAggregateTargetObservations {
        self.observations
    }
    pub fn source_event(&self) -> &native_aggregates::PendingNativeAggregateEvent {
        self.source
    }
    pub fn call(&self) -> &TargetCall {
        self.call
    }
    pub fn stores(&self) -> &[&TargetAccess; 2] {
        &self.stores
    }
    pub fn loads(&self) -> &[&TargetAccess; 2] {
        &self.loads
    }
    pub fn snapshot_after_materialization(&self) -> &E {
        &self.stores[1].post_world
    }
    /// Lane0, lane1, then arbitrary outside-byte preservation. Every statement
    /// retains ALL original-source and actual-target semantic definitions.
    /// Actual access guards occur in conclusions; normality is never assumed.
    pub fn obligations(&self) -> &[ProofObligation; 3] {
        &self.obligations
    }
}

// Charge logical traversal/serialization, including repeated Arc children,
// before cloning complete definitions into each pending statement.
fn nodes(expr: &E) -> Result<usize, ReadOnlySourceError> {
    let mut pending = vec![(expr, 1usize)];
    let mut count = 0usize;
    while let Some((expr, depth)) = pending.pop() {
        count += 1;
        if count > MAX_QUERY_NODES || depth > crate::smt_raw_print::MAX_DEPTH {
            return Err(ReadOnlySourceError::Budget(
                "native materialization statement",
            ));
        }
        let mut excess = false;
        expr.for_each_child(&mut |child| {
            if pending.len() + count >= MAX_QUERY_NODES {
                excess = true;
            } else {
                pending.push((child, depth + 1));
            }
        });
        if excess {
            return Err(ReadOnlySourceError::Budget(
                "native materialization statement",
            ));
        }
    }
    Ok(count)
}

impl NativeAggregateTargetObservations {
    /// Bind only the observed actual pair stores and two original mapped field
    /// loads. Other source shapes stay unsupported; no original body is replaced
    /// by this local snapshot. All six source/ABI/storage requirements stay pending.
    pub fn local_materialization_queries(
        &self,
    ) -> Result<Vec<PendingNativeAggregateMaterialization<'_>>, ReadOnlySourceError> {
        if self.materializations.len() > MAX_READS {
            return Err(ReadOnlySourceError::Budget(
                "native materialization inventory",
            ));
        }
        let definitions = self.source.definitions().iter().chain(&self.definitions);
        let base_nodes = definitions.clone().try_fold(0usize, |n, e| {
            n.checked_add(nodes(e)?)
                .filter(|n| *n <= MAX_QUERY_NODES)
                .ok_or(ReadOnlySourceError::Budget(
                    "native materialization definitions",
                ))
        })?;
        let mut used = 0usize;
        let mut result = Vec::with_capacity(self.materializations.len());
        for mapped in &self.materializations {
            let plan = mapped.plan();
            if mapped.fields().len() != 2
                || mapped.fields()[0].plan().intent().field() != 0
                || mapped.fields()[1].plan().intent().field() != 1
            {
                return Err(refused("native materialization original field order"));
            }
            let call = self
                .effects
                .calls
                .iter()
                .find(|c| {
                    c.intent == *plan.intent()
                        && c.binding == plan.binding()
                        && c.site
                            == (ReadOnlySite {
                                block: plan.block().0,
                                instruction: plan.call_instruction(),
                            })
                })
                .ok_or(refused("native materialization call occurrence"))?;
            let mut sources = self
                .source
                .events()
                .iter()
                .filter(|s| s.intent() == call.intent() && s.binding() == call.binding());
            let source = sources
                .next()
                .ok_or(refused("native materialization source occurrence"))?;
            if sources.next().is_some() {
                return Err(refused(
                    "native materialization duplicate source occurrence",
                ));
            }
            let access = |id, load| {
                let position = self
                    .instructions
                    .iter()
                    .position(|(i, _)| *i == id)
                    .ok_or(refused("native materialization stale instruction"))?;
                let site = ReadOnlySite {
                    block: self.frontier.block,
                    instruction: position,
                };
                let mut found = self
                    .effects
                    .accesses
                    .iter()
                    .filter(|a| a.site == site && a.load == load);
                let a = found
                    .next()
                    .ok_or(refused("native materialization missing access"))?;
                if found.next().is_some() || a.byte_width != 8 {
                    return Err(refused("native materialization access width/identity"));
                }
                Ok(a)
            };
            let stores = [
                access(mapped.stores()[0], false)?,
                access(mapped.stores()[1], false)?,
            ];
            let loads = [
                access(mapped.fields()[0].load(), true)?,
                access(mapped.fields()[1].load(), true)?,
            ];
            let expected = [stores[0], stores[1], loads[0], loads[1]];
            let actual = self
                .effects
                .accesses
                .iter()
                .filter(|a| {
                    a.site.block == call.site.block
                        && a.site.instruction > call.site.instruction
                        && a.site.instruction <= loads[1].site.instruction
                })
                .collect::<Vec<_>>();
            if actual.len() != expected.len()
                || actual
                    .iter()
                    .zip(expected)
                    .any(|(a, b)| !std::ptr::eq(*a, b))
                || self.effects.calls.iter().any(|c| {
                    c.site.block == call.site.block
                        && c.site.instruction > call.site.instruction
                        && c.site.instruction <= loads[1].site.instruction
                })
            {
                return Err(refused("native materialization store/load order"));
            }
            if stores[0].prior_world != call.post_world
                || stores[1].prior_world != stores[0].post_world
                || loads[0].prior_world != stores[1].post_world
                || loads[0].post_world != loads[0].prior_world
                || loads[1].prior_world != loads[0].post_world
                || loads[1].post_world != loads[1].prior_world
            {
                return Err(refused("native materialization foreign world snapshot"));
            }
            let mut make = |name, parts: &[&E], build: &dyn Fn() -> E| {
                // Conservative admission BEFORE repeated definition/operand clones.
                let count = parts.iter().try_fold(base_nodes + 32, |n, e| {
                    n.checked_add(nodes(e)?.saturating_mul(2))
                        .filter(|n| *n <= MAX_QUERY_NODES)
                        .ok_or(ReadOnlySourceError::Budget("native materialization query"))
                })?;
                reserve_query(&mut used, count)?;
                Ok::<_, ReadOnlySourceError>(ProofObligation {
                    name,
                    trust_ir_expr: build(),
                    aarch64_expr: E::BoolConst(true),
                    inputs: (0..8)
                        .map(|i| (format!("abi_x{i}"), 64))
                        .chain(std::iter::once(("observe".into(), 64)))
                        .collect(),
                    preconditions: definitions.clone().cloned().collect(),
                    fp_inputs: vec![],
                    category: Some(TransvalCheckKind::MemoryModel),
                    machine_side_provenance: MachineSideProvenance::StaticDb,
                })
            };
            let registers = plan.return_registers().map(|r| r.encoding() as usize);
            if registers.iter().any(|r| *r >= 31) {
                return Err(refused("native materialization return register bank"));
            }
            let lane = |i: usize| {
                loads[i].guard.clone().not_expr().or_expr(
                    loads[i]
                        .value
                        .clone()
                        .eq_expr(call.after[registers[i]].clone()),
                )
            };
            let lane0 = make(
                format!("Pending actual aggregate {:?} lane0 readback", call.site),
                &[&loads[0].guard, &loads[0].value, &call.after[registers[0]]],
                &|| lane(0),
            )?;
            let lane1 = make(
                format!("Pending actual aggregate {:?} lane1 readback", call.site),
                &[&loads[1].guard, &loads[1].value, &call.after[registers[1]]],
                &|| lane(1),
            )?;
            let outside = make(
                format!(
                    "Pending actual aggregate {:?} post-store outside byte",
                    call.site
                ),
                &[
                    &stores[1].guard,
                    &stores[0].address,
                    &stores[1].post_world,
                    &call.post_world,
                ],
                &|| {
                    let q = E::var("observe", 64);
                    // Modular sixteen-byte interval: numeric nonwrap/alignment
                    // demands remain explicit on the observer, not assumed facts.
                    let inside = q
                        .clone()
                        .bvsub(stores[0].address.clone())
                        .bvult(E::bv_const(16, 64));
                    stores[1].guard.clone().not_expr().or_expr(
                        inside.or_expr(
                            E::select(stores[1].post_world.clone(), q.clone())
                                .eq_expr(E::select(call.post_world.clone(), q)),
                        ),
                    )
                },
            )?;
            result.push(PendingNativeAggregateMaterialization {
                observations: self,
                source,
                call,
                stores,
                loads,
                obligations: [lane0, lane1, outside],
            });
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn observed() -> NativeAggregateTargetObservations {
        let (m, l, c, s, t, b) = super::super::tests::fixture(1);
        observe_native_aggregate_target(&m, &l, &c.aggregate_call_intents, &s, &t, &b).unwrap()
    }
    #[test]
    fn pending_materialization_keeps_real_snapshots_guards_and_all_definitions() {
        let observed = observed();
        let rows = observed.local_materialization_queries().unwrap();
        assert_eq!(rows.len(), 1);
        let row = &rows[0];
        assert_ne!(row.call().post_world(), row.source_event().post_world());
        assert_eq!(
            row.snapshot_after_materialization(),
            &row.stores()[1].post_world
        );
        assert_eq!(row.loads()[0].prior_world, row.stores()[1].post_world);
        assert_eq!(row.call().outstanding_requirements().len(), 6);
        assert!(
            row.loads()
                .iter()
                .all(|a| a.initialization_coverage_demand.is_some())
        );
        for query in row.obligations() {
            assert_eq!(
                query.preconditions.len(),
                observed.source.definitions().len() + observed.definitions.len()
            );
            assert!(
                query.preconditions.iter().eq(observed
                    .source
                    .definitions()
                    .iter()
                    .chain(&observed.definitions))
            );
            assert_ne!(query.trust_ir_expr, E::BoolConst(true));
        }
    }
    #[test]
    fn pending_materialization_rejects_stale_order_width_and_foreign_snapshots() {
        for mutation in 0..4 {
            let mut observed = observed();
            match mutation {
                0 => {
                    observed.instructions.remove(0);
                }
                1 => observed.effects.accesses.swap(2, 3),
                2 => observed.effects.accesses[2].byte_width = 4,
                _ => {
                    observed.effects.accesses[1].post_world =
                        E::uf("foreign_world", vec![], memory_sort())
                }
            };
            assert!(
                observed.local_materialization_queries().is_err(),
                "mutation{mutation}"
            );
        }
    }
    #[test]
    fn pending_materialization_statement_budget_is_preclone() {
        let mut observed = observed();
        observed.definitions = vec![E::BoolConst(true); MAX_QUERY_NODES + 1];
        assert!(matches!(
            observed.local_materialization_queries(),
            Err(ReadOnlySourceError::Budget(
                "native materialization definitions"
            ))
        ));
    }
}
