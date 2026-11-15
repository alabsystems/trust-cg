// Copyright 2026 Andrew Yates | Apache-2.0
//! Required provider relations for the actual multi-result call observations.
//!
//! Regions are untrusted effect claims, including effects reached through TLS,
//! cleanup and other callees. Neither a region nor the derived framing formula
//! establishes that a native implementation confines its writes to it. The
//! required outcome, memory and preserved-register relations below must still
//! be proved against that implementation. There is no CheckedFrameBody,
//! SourceBoundReplay, provider, storage or installation conversion here.

use super::*;

/// An untrusted half-open byte-write region. The expression may describe a
/// runtime allocation, TLS object or callee-private stack; it grants no access.
/// Empty regions are permitted. Nonwrapping geometry is a separate demand.
pub struct NativeProviderWriteRegion {
    start: E,
    bytes: E,
}

impl NativeProviderWriteRegion {
    pub fn new(start: E, bytes: E) -> Result<Self, ReadOnlySourceError> {
        admit(&[&start, &bytes])?;
        if crate::smt_raw_print::checked_sort(&start).ok() != Some(crate::smt::SmtSort::BitVec(64))
            || crate::smt_raw_print::checked_sort(&bytes).ok()
                != Some(crate::smt::SmtSort::BitVec(64))
        {
            return Err(refused("provider write region requires two BV64 terms"));
        }
        Ok(Self { start, bytes })
    }
    pub fn start(&self) -> &E {
        &self.start
    }
    pub fn byte_length(&self) -> &E {
        &self.bytes
    }
    fn contains(&self, address: &E) -> E {
        address
            .clone()
            .bvsub(self.start.clone())
            .bvult(self.bytes.clone())
    }
    /// This is numeric geometry only, not ownership, successful access, or
    /// evidence that the region contains all implementation writes.
    pub fn nonwrapping_demand(&self) -> E {
        self.bytes.clone().eq_expr(E::bv_const(0, 64)).or_expr(
            self.start.clone().bvule(
                E::bv_const(u64::MAX, 64).bvsub(self.bytes.clone().bvsub(E::bv_const(1, 64))),
            ),
        )
    }
}

/// Actual source/native event pair and the requirements an implementation
/// witness must discharge. All normal statuses, including failure statuses,
/// retain BOTH return lanes and complete post-call byte worlds. Non-normal
/// behavior remains opaque. General vector/system-state fidelity is still an
/// external ABI obligation; the existing observation records GPRs and SP only.
pub struct PendingNativeProviderFootprint<'a> {
    observations: &'a NativeAggregateTargetObservations,
    source: &'a native_aggregates::PendingNativeAggregateEvent,
    call: &'a TargetCall,
    regions: &'a [NativeProviderWriteRegion],
    matching_inputs: E,
    outcome_relation: E,
    register_relation: E,
    outside_byte_relation: E,
}

impl PendingNativeProviderFootprint<'_> {
    pub fn observations(&self) -> &NativeAggregateTargetObservations {
        self.observations
    }
    pub fn source_event(&self) -> &native_aggregates::PendingNativeAggregateEvent {
        self.source
    }
    pub fn call(&self) -> &TargetCall {
        self.call
    }
    pub fn write_regions(&self) -> &[NativeProviderWriteRegion] {
        self.regions
    }
    pub fn matching_inputs(&self) -> &E {
        &self.matching_inputs
    }
    pub fn required_outcome_relation(&self) -> &E {
        &self.outcome_relation
    }
    pub fn required_register_preservation(&self) -> &E {
        &self.register_relation
    }
    /// Pointwise for the free arbitrary BV64 `observe`, not one sampled byte.
    pub fn required_outside_byte_relation(&self) -> &E {
        &self.outside_byte_relation
    }
    /// Frame one nonempty protected byte interval. Its mapping to an actual
    /// caller allocation must be established separately. The provider law,
    /// numeric nonwrap and disjointness are EXPLICIT unresolved premises; the
    /// query does not prove those premises or declare the interval owned.
    pub fn conditional_framing_obligation(
        &self,
        protected_start: E,
        byte_width: u32,
    ) -> Result<ProofObligation, ReadOnlySourceError> {
        if byte_width == 0 {
            return Err(refused("provider protected interval is empty"));
        }
        let protected = NativeProviderWriteRegion::new(
            protected_start,
            E::bv_const(u64::from(byte_width), 64),
        )?;
        let mut geometry = vec![protected.nonwrapping_demand()];
        let last = protected
            .start
            .clone()
            .bvadd(E::bv_const(u64::from(byte_width) - 1, 64));
        for region in self.regions {
            geometry.push(region.nonwrapping_demand());
            geometry.push(
                region.bytes.clone().eq_expr(E::bv_const(0, 64)).or_expr(
                    region
                        .start
                        .clone()
                        .bvadd(region.bytes.clone().bvsub(E::bv_const(1, 64)))
                        .bvult(protected.start.clone())
                        .or_expr(last.clone().bvult(region.start.clone())),
                ),
            );
        }
        let observe = E::var("observe", 64);
        let active = self.call.guard.clone().and_expr(self.call.normal.clone());
        let unchanged = E::select(self.call.prior_world.clone(), observe.clone())
            .eq_expr(E::select(self.call.post_world.clone(), observe.clone()));
        let statement = active
            .and_expr(protected.contains(&observe))
            .not_expr()
            .or_expr(unchanged);
        let definitions = self
            .observations
            .source()
            .definitions()
            .iter()
            .chain(self.observations.definitions());
        let roots: Vec<_> = definitions
            .clone()
            .chain(geometry.iter())
            .chain([&self.outside_byte_relation, &statement])
            .collect();
        admit(&roots)?;
        let inputs = query_inputs(&roots)?;
        Ok(ProofObligation {
            name: format!(
                "Conditional native provider {:?} protected byte",
                self.call.site
            ),
            trust_ir_expr: statement,
            aarch64_expr: E::BoolConst(true),
            inputs,
            preconditions: definitions
                .cloned()
                .chain(geometry)
                .chain(std::iter::once(self.outside_byte_relation.clone()))
                .collect(),
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::MemoryModel),
            machine_side_provenance: MachineSideProvenance::StaticDb,
        })
    }
}

fn admit(roots: &[&E]) -> Result<(), ReadOnlySourceError> {
    let mut work = 0usize;
    let mut payload = 0usize;
    for root in roots {
        let inspected = crate::smt_raw_print::preflight(root)
            .map_err(|_| ReadOnlySourceError::Budget("native provider footprint terms"))?;
        for node in &inspected.order {
            let name = match node {
                E::Var { name, .. } | E::UF { name, .. } | E::UFDecl { name, .. } => name,
                _ => continue,
            };
            if !crate::array_row_lowering::simple_read_symbol(name) {
                return Err(refused("native provider non-simple SMT symbol"));
            }
        }
        work = work
            .checked_add(inspected.order.len() + inspected.edges)
            .filter(|n| *n <= MAX_TOTAL_QUERY_NODES)
            .ok_or(ReadOnlySourceError::Budget(
                "native provider aggregate work",
            ))?;
        payload = payload
            .checked_add(inspected.payload)
            .filter(|n| *n <= crate::smt_raw_print::MAX_SCRIPT_BYTES)
            .ok_or(ReadOnlySourceError::Budget(
                "native provider aggregate payload",
            ))?;
    }
    Ok(())
}

fn query_inputs(roots: &[&E]) -> Result<Vec<(String, u32)>, ReadOnlySourceError> {
    let mut variables: std::collections::BTreeMap<String, u32> = (0..8)
        .map(|i| (format!("abi_x{i}"), 64))
        .chain(std::iter::once(("observe".into(), 64)))
        .collect();
    let mut functions = std::collections::BTreeSet::new();
    for root in roots {
        let scanned = crate::smt_raw_print::preflight(root)
            .map_err(|_| ReadOnlySourceError::Budget("native provider input terms"))?;
        for node in scanned.order {
            match node {
                E::Var { name, width } => {
                    if variables
                        .insert(name.clone(), *width)
                        .is_some_and(|old| old != *width)
                    {
                        return Err(refused("native provider conflicting input sort"));
                    }
                }
                E::UF { name, .. } | E::UFDecl { name, .. } => {
                    functions.insert(name.as_str());
                }
                _ => {}
            }
        }
    }
    if variables
        .keys()
        .any(|name| functions.contains(name.as_str()))
    {
        return Err(refused(
            "native provider input collides with a stored symbol",
        ));
    }
    Ok(variables.into_iter().collect())
}

impl NativeAggregateTargetObservations {
    /// Construct the required law for one existing actual call. The supplied
    /// write regions remain claims. Source and target outcomes are not equated
    /// as definitions; proofs of this conditional framing query cannot discharge
    /// the outcome, register, footprint or six original provider/ABI demands.
    pub fn provider_footprint_requirements<'a>(
        &'a self,
        site: ReadOnlySite,
        regions: &'a [NativeProviderWriteRegion],
    ) -> Result<PendingNativeProviderFootprint<'a>, ReadOnlySourceError> {
        if regions.len() > MAX_READS {
            return Err(ReadOnlySourceError::Budget("native provider write regions"));
        }
        let mut calls = self.calls().iter().filter(|c| c.site == site);
        let call = calls
            .next()
            .ok_or(refused("provider call occurrence missing"))?;
        if calls.next().is_some() || call.before.len() != 32 || call.after.len() != 32 {
            return Err(refused("provider call occurrence or register shape"));
        }
        let mut sources = self
            .source()
            .events()
            .iter()
            .filter(|s| s.intent() == call.intent() && s.binding() == call.binding());
        let source = sources
            .next()
            .ok_or(refused("provider source event missing"))?;
        if sources.next().is_some() || source.arguments().len() != call.arguments.len() {
            return Err(refused("provider source event or argument shape"));
        }
        let lanes = self
            .materializations()
            .iter()
            .find(|m| m.plan().intent() == call.intent() && m.plan().binding() == call.binding())
            .ok_or(refused("provider aggregate return mapping missing"))?
            .plan()
            .return_registers()
            .map(|r| r.encoding() as usize);
        if source.record().fields().len() != 2
            || lanes[0] >= 31
            || lanes[1] >= 31
            || lanes[0] == lanes[1]
        {
            return Err(refused("provider aggregate return register shape"));
        }
        // Bound all input work before structural comparisons/cloning. Existing
        // source/target owners already admitted their complete definitions.
        let roots: Vec<_> = self
            .source()
            .definitions()
            .iter()
            .chain(self.definitions())
            .chain(source.arguments())
            .chain(&call.arguments)
            .chain(source.record().fields())
            .chain(&call.before)
            .chain(&call.after)
            .chain([
                source.guard(),
                source.prior_world(),
                source.post_world(),
                source.returned_normally(),
                &call.guard,
                &call.prior_world,
                &call.post_world,
                &call.normal,
            ])
            .chain(regions.iter().flat_map(|r| [&r.start, &r.bytes]))
            .collect();
        admit(&roots)?;
        let mut matching_inputs = source
            .prior_world()
            .clone()
            .eq_expr(call.prior_world.clone());
        for (a, b) in source.arguments().iter().zip(&call.arguments) {
            matching_inputs = matching_inputs.and_expr(a.clone().eq_expr(b.clone()));
        }
        let both = source.guard().clone().and_expr(call.guard.clone());
        let mut returned = source.post_world().clone().eq_expr(call.post_world.clone());
        for (field, lane) in source.record().fields().iter().zip(lanes) {
            returned = returned.and_expr(field.clone().eq_expr(call.after[lane].clone()));
        }
        let outcome_relation = matching_inputs.clone().not_expr().or_expr(
            source.guard().clone().eq_expr(call.guard.clone()).and_expr(
                both.not_expr().or_expr(
                    source
                        .returned_normally()
                        .clone()
                        .eq_expr(call.normal.clone())
                        .and_expr(call.normal.clone().not_expr().or_expr(returned)),
                ),
            ),
        );
        let active = call.guard.clone().and_expr(call.normal.clone());
        let mut preserved = E::BoolConst(true);
        // Darwin reserves X18; X19..X29 and SP must survive. X30 is NOT
        // equated across BL. Neither return lane is accidentally preserved.
        for register in (18..30).chain(std::iter::once(31)) {
            preserved = preserved.and_expr(
                call.before[register]
                    .clone()
                    .eq_expr(call.after[register].clone()),
            );
        }
        let register_relation = active.clone().not_expr().or_expr(preserved);
        let observe = E::var("observe", 64);
        let mut inside = E::BoolConst(false);
        for region in regions {
            inside = inside.or_expr(region.contains(&observe));
        }
        let unchanged = E::select(call.prior_world.clone(), observe.clone())
            .eq_expr(E::select(call.post_world.clone(), observe));
        let outside_byte_relation = active
            .clone()
            .not_expr()
            .or_expr(inside.clone())
            .or_expr(unchanged.clone());
        admit(&[
            &outcome_relation,
            &register_relation,
            &outside_byte_relation,
        ])?;
        Ok(PendingNativeProviderFootprint {
            observations: self,
            source,
            call,
            regions,
            matching_inputs,
            outcome_relation,
            register_relation,
            outside_byte_relation,
        })
    }
}

#[cfg(test)]
#[path = "native_provider_footprint_tests.rs"]
mod tests;
