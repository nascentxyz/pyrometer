use crate::GraphBackend;
use crate::{
    nodes::Concrete,
    range::elem::{Elem, RangeElem},
};
use shared::RangeArena;

pub trait RangeArenaLike<T> {
    fn debug_str(&self, analyzer: &impl GraphBackend) -> String;
    fn ranges(&self) -> &Vec<T>;
    fn ranges_mut(&mut self) -> &mut Vec<T>;
    fn idx_or_upsert(&mut self, elem: T, analyzer: &impl GraphBackend) -> usize;
    fn take_nonnull(&mut self, idx: usize) -> Option<T>;
    fn idx(&self, elem: &T) -> Option<usize>;
    fn to_graph(
        &mut self,
        analyzer: &impl GraphBackend,
    ) -> Result<petgraph::Graph<Elem<Concrete>, usize, petgraph::Directed, usize>, crate::GraphError>;
}

impl RangeArenaLike<Elem<Concrete>> for RangeArena<Elem<Concrete>> {
    fn debug_str(&self, analyzer: &impl GraphBackend) -> String {
        self.ranges
            .iter()
            .enumerate()
            .map(|(i, elem)| {
                fn fmt(elem: &Elem<Concrete>, analyzer: &impl GraphBackend) -> String {
                    match elem {
                        Elem::Reference(reference) => {
                            format!(
                                "node_{} -- {}",
                                reference.idx.index(),
                                crate::nodes::ContextVarNode::from(reference.idx)
                                    .display_name(analyzer)
                                    .unwrap()
                            )
                        }
                        Elem::Expr(expr) => {
                            format!(
                                "{} {} {}",
                                fmt(&expr.lhs, analyzer),
                                expr.op.to_string(),
                                fmt(&expr.rhs, analyzer)
                            )
                        }
                        _ => format!("{elem}"),
                    }
                };

                format!("{i}: {}", fmt(elem, analyzer))
            })
            .collect::<Vec<_>>()
            .join("\n\t")
    }

    fn to_graph(
        &mut self,
        analyzer: &impl GraphBackend,
    ) -> Result<petgraph::Graph<Elem<Concrete>, usize, petgraph::Directed, usize>, crate::GraphError>
    {
        let mut graph = petgraph::Graph::default();
        let mut added = vec![];
        let mut ids = vec![];

        fn get_children(
            elem: &Elem<Concrete>,
            analyzer: &impl GraphBackend,
        ) -> Result<Vec<Elem<Concrete>>, crate::GraphError> {
            match elem {
                Elem::Reference(r) => {
                    let cvar = crate::nodes::ContextVarNode::from(r.idx);
                    let range = cvar.ref_range(analyzer)?.unwrap();
                    let min = range.min.clone();
                    let max = range.max.clone();
                    Ok(vec![min, max])
                }
                _c @ Elem::Concrete(_) => Ok(vec![]),
                Elem::ConcreteDyn(d) => {
                    let mut v = vec![(*d.len).clone()];
                    v.extend(d.val.values().map(|(v, _)| v.clone()).collect::<Vec<_>>());
                    v.extend(d.val.keys().cloned().collect::<Vec<_>>());
                    Ok(v)
                }
                Elem::Expr(expr) => Ok(vec![(*expr.lhs).clone(), (*expr.rhs).clone()]),
                Elem::Null => Ok(vec![]),
                Elem::Arena(_) => Ok(vec![]),
            }
        }

        fn add_elem_and_children(
            graph: &mut petgraph::Graph<Elem<Concrete>, usize, petgraph::Directed, usize>,
            added: &mut Vec<Elem<Concrete>>,
            ids: &mut Vec<usize>,
            elem: &Elem<Concrete>,
            analyzer: &impl GraphBackend,
        ) -> Result<(), crate::GraphError> {
            assert!(added.len() == ids.len());

            if !added.contains(elem) {
                let new_elems: Vec<Elem<Concrete>> = get_children(elem, analyzer)?;
                let id = graph.add_node(elem.clone());
                added.push(elem.clone());
                ids.push(id.index());

                new_elems.into_iter().try_for_each(|elem| {
                    add_elem_and_children(graph, added, ids, &elem, analyzer)?;
                    let to_id = added.iter().position(|i| i == &elem).unwrap();
                    graph.add_edge(id, to_id.into(), 0);
                    Ok(())
                })?;
            }

            Ok(())
        }

        self.ranges.iter().try_for_each(|elem: &Elem<Concrete>| {
            add_elem_and_children(&mut graph, &mut added, &mut ids, elem, analyzer)
        })?;
        Ok(graph)
    }

    fn idx_or_upsert(&mut self, elem: Elem<Concrete>, analyzer: &impl GraphBackend) -> usize {
        if self.ranges.is_empty() {
            self.ranges.push(Elem::Null);
            self.map.insert(Elem::Null, 0);
        }

        let nulls = self.ranges.iter().fold(0, |mut acc, e| {
            if matches!(e, Elem::Null) {
                acc += 1;
            }
            acc
        });

        // println!(
        //     "{}\nhad cycle:\n{:?}",
        //     self.debug_str(analyzer),
        //     petgraph::dot::Dot::new(&self.to_graph(analyzer).unwrap()) // petgraph::algo::toposort(&self.to_graph(analyzer).unwrap(), None).is_err()
        // );
        match elem {
            Elem::Arena(idx) => return idx,
            Elem::Null => return 0,
            _ => {}
        }

        if let Some(idx) = self.idx(&elem) {
            let Some(existing) = self.take_nonnull(idx) else {
                self.ranges_mut()[idx] = elem;
                return idx;
            };

            let (min_cached, max_cached) = existing.is_min_max_cached(analyzer, self);
            let mut existing_count = 0;
            if min_cached {
                existing_count += 1;
            }
            if max_cached {
                existing_count += 1;
            }
            if existing.is_flatten_cached(analyzer, self) {
                existing_count += 1;
            }

            let (min_cached, max_cached) = elem.is_min_max_cached(analyzer, self);
            let mut new_count = 0;
            if min_cached {
                new_count += 1;
            }
            if max_cached {
                new_count += 1;
            }
            if elem.is_flatten_cached(analyzer, self) {
                new_count += 1;
            }

            if new_count >= existing_count {
                self.ranges_mut()[idx] = elem;
            } else {
                self.ranges_mut()[idx] = existing;
            }

            idx
        } else {
            let idx = self.ranges.len();
            self.ranges.push(elem.clone());
            self.map.insert(elem, idx);
            idx
        }
    }

    fn ranges(&self) -> &Vec<Elem<Concrete>> {
        &self.ranges
    }
    fn ranges_mut(&mut self) -> &mut Vec<Elem<Concrete>> {
        &mut self.ranges
    }

    fn take_nonnull(&mut self, idx: usize) -> Option<Elem<Concrete>> {
        if let Some(t) = self.ranges.get_mut(idx) {
            match t {
                Elem::Null => None,
                _ => Some(std::mem::take(t)),
            }
        } else {
            None
        }
    }

    fn idx(&self, elem: &Elem<Concrete>) -> Option<usize> {
        if let Elem::Arena(idx) = elem {
            Some(*idx)
        } else {
            self.map.get(elem).copied()
        }
    }
}
