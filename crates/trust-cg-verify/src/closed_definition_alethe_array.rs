// Copyright 2026 Andrew Yates | Apache-2.0
//! Bounded untrusted literal-read selection and original-term array proofs.
//! A numeric match selects work only. Every alias, index comparison and
//! read-over-write step must independently check against the original query.
use super::*;

pub(super) enum ReadStep {
    Alias {
        definition: Definition,
    },
    Store {
        array: Id,
        base: Id,
        index: Id,
        value: Id,
        same: bool,
    },
}
pub(super) struct ReadPlan {
    index: Id,
    pub(super) value: Id,
    steps: Vec<ReadStep>,
}
impl ReadPlan {
    pub(super) fn dependencies(&self) -> Vec<Id> {
        let mut result = vec![self.index, self.value];
        result.extend(self.steps.iter().filter_map(|step| match step {
            ReadStep::Store { index, .. } => Some(*index),
            _ => None,
        }));
        result
    }
}

impl Graph<'_> {
    pub(super) fn read_plan(
        &self,
        id: Id,
        visits: &mut usize,
        edges: &mut usize,
    ) -> Result<Option<ReadPlan>, ClosedDefinitionRefusal> {
        let [array, index] = self.nodes[id].children.as_slice() else {
            return Ok(None);
        };
        let mut array = *array;
        let index = *index;
        let Some(E::BvConst {
            value: read,
            width: read_width,
        }) = self.nodes[index].literal.as_ref()
        else {
            return Ok(None);
        };
        let mut steps = Vec::new();
        loop {
            reserve_visits(visits, 1)?;
            if let Some(definition) = self.definitions.get(&array).copied() {
                reserve_work(&steps, edges, 2)?;
                steps.push(ReadStep::Alias { definition });
                array = definition.rhs;
                continue;
            }
            if !matches!(self.nodes[array].original, E::Store { .. }) {
                return Ok(None);
            }
            let [base, stored_index, value] = self.nodes[array].children.as_slice() else {
                return Err(ClosedDefinitionRefusal::Malformed("array store arity"));
            };
            let Some(E::BvConst {
                value: stored,
                width,
            }) = self.nodes[*stored_index].literal.as_ref()
            else {
                return Ok(None);
            };
            if width != read_width {
                return Ok(None);
            }
            let same = stored == read;
            reserve_work(&steps, edges, 4)?;
            steps.push(ReadStep::Store {
                array,
                base: *base,
                index: *stored_index,
                value: *value,
                same,
            });
            if same {
                return Ok(Some(ReadPlan {
                    index,
                    value: *value,
                    steps,
                }));
            }
            array = *base;
        }
    }
}

impl Composer<'_> {
    /// All prerequisites were scheduled by the iterative literal worklist.
    /// No recursive array evaluation, new assumption or rewritten query exists.
    pub(super) fn array_read_equality(
        &mut self,
        id: Id,
        plan: &ReadPlan,
    ) -> Result<Id, ClosedDefinitionRefusal> {
        let index = self.graph.nodes[plan.index].spelled().clone();
        let mut current = self.graph.nodes[id].spelled().clone();
        let mut proofs = Vec::new();
        for step in &plan.steps {
            reserve_visits(&mut self.visits, 1)?;
            reserve_work(&proofs, &mut self.edges, 12)?;
            match step {
                ReadStep::Alias { definition } => {
                    let next = E::select(
                        self.graph.nodes[definition.rhs].spelled().clone(),
                        index.clone(),
                    );
                    proofs.push(self.text.equality(
                        &current,
                        &next,
                        "cong",
                        &[definition.premise],
                    )?);
                    current = next;
                }
                ReadStep::Store {
                    array,
                    base,
                    index: stored_index,
                    value,
                    same,
                } => {
                    // Keep the exact actual Store endpoint in the proof, even
                    // when its proof-local spelling is a shared term macro.
                    let actual =
                        E::select(self.graph.nodes[*array].spelled().clone(), index.clone());
                    let store_index = self.graph.nodes[*stored_index].spelled().clone();
                    let condition = store_index.clone().eq_expr(index.clone());
                    let next = if *same {
                        self.graph.nodes[*value].spelled().clone()
                    } else {
                        E::select(self.graph.nodes[*base].spelled().clone(), index.clone())
                    };
                    let unit = if *same {
                        self.literal((*stored_index, plan.index))?.ok_or(
                            ClosedDefinitionRefusal::Unsupported(
                                "array matching index has no original equality",
                            ),
                        )?
                    } else {
                        let shallow = self.graph.nodes[*stored_index]
                            .literal
                            .as_ref()
                            .unwrap()
                            .clone()
                            .eq_expr(
                                self.graph.nodes[plan.index]
                                    .literal
                                    .as_ref()
                                    .unwrap()
                                    .clone(),
                            );
                        let lift = self.text.equality(
                            &condition,
                            &shallow,
                            "cong",
                            &[
                                self.literal_equalities[stored_index],
                                self.literal_equalities[&plan.index],
                            ],
                        )?;
                        let evaluated =
                            self.text
                                .equality(&shallow, &E::BoolConst(false), "evaluate", &[])?;
                        let equality = self.text.equality(
                            &condition,
                            &E::BoolConst(false),
                            "trans",
                            &[lift, evaluated],
                        )?;
                        let false_unit =
                            self.text
                                .unit(&E::BoolConst(false).not_expr(), "false", &[], None)?;
                        self.signed_transport(
                            &condition,
                            &E::BoolConst(false),
                            false_unit,
                            equality,
                            false,
                            false,
                        )?
                    };
                    // The captured Clean external checker uses its vendored
                    // Carcara `arrays_idx` and `arrays_row` rules. `arrays_idx` needs the SAME actual
                    // index, so transport the independently proved original
                    // index equality before applying that axiom. `arrays_row` consumes
                    // the actual negative index unit as a mandatory premise.
                    let proof = if *same {
                        let at_store_index = E::select(
                            self.graph.nodes[*array].spelled().clone(),
                            store_index.clone(),
                        );
                        let index_back =
                            self.text.equality(&index, &store_index, "symm", &[unit])?;
                        let transported =
                            self.text
                                .equality(&actual, &at_store_index, "cong", &[index_back])?;
                        let selected =
                            self.text
                                .equality(&at_store_index, &next, "arrays_idx", &[])?;
                        self.text
                            .equality(&current, &next, "trans", &[transported, selected])?
                    } else {
                        self.text.equality(&current, &next, "arrays_row", &[unit])?
                    };
                    proofs.push(proof);
                    current = next;
                }
            }
        }
        self.text.equality(
            self.graph.nodes[id].spelled(),
            self.graph.nodes[plan.value].spelled(),
            "trans",
            &proofs,
        )
    }
}
