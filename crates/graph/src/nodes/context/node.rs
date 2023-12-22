use crate::VarType;
use crate::range::Range;
use crate::range::elem::RangeElem;
use crate::nodes::ExprRet;
use crate::elem::Elem;
use crate::Edge;
use crate::ContextEdge;
use crate::{
    nodes::{Context, ContextVarNode, FunctionNode, FunctionParamNode, KilledKind},
    AnalyzerBackend, AsDotStr, GraphBackend, GraphError, Node,
};

use shared::NodeIdx;

use solang_parser::pt::Loc;
use std::collections::BTreeMap;

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
/// A wrapper of a node index that corresponds to a [`Context`]
pub struct ContextNode(pub usize);

impl AsDotStr for ContextNode {
    fn as_dot_str(&self, analyzer: &impl GraphBackend) -> String {
        format!("Context {{ {} }}", self.path(analyzer))
    }
}

impl ContextNode {
    pub fn join(
        &self,
        func: FunctionNode,
        mapping: &BTreeMap<String, (FunctionParamNode, ContextVarNode)>,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<bool, GraphError> {

        // ensure no modifiers (for now)
        // if pure function:
        //      grab requirements for context
        //      grab return node's simplified range
        //      replace fundamentals with function inputs
        //      update ctx name in place

        if func.is_pure(analyzer)? {
            // pure functions are guaranteed to not require the use of state, so
            // the only things we care about are function inputs and function outputs
            if let Some(body_ctx) = func.maybe_body_ctx(analyzer) {
                let inputs = body_ctx.input_variables(analyzer);
                // println!("inputs:");
                let mut replacement_map = BTreeMap::default();
                inputs.iter().for_each(|input| {
                    let name = input.name(analyzer).unwrap();
                    if let Some((param, replacement_input)) = mapping.get(&name) {
                        if let Some(param_ty) = VarType::try_from_idx(analyzer, param.ty(analyzer).unwrap())
                        {
                            if !replacement_input.ty_eq_ty(&param_ty, analyzer).unwrap() {
                                replacement_input.cast_from_ty(param_ty, analyzer).unwrap();
                            }
                        }
                        let mut replacement = Elem::from(*replacement_input);
                        replacement.arenaize(analyzer).unwrap();
                        
                        if let Some(next) = input.next_version(analyzer) {
                            replacement_map.insert(next.0, replacement.clone());
                        }
                        replacement_map.insert(input.0, replacement);
                        // a lot of time (all the time?) there is an extra version added on
                        
                    }
                    // println!("  name: {}", input.display_name(analyzer).unwrap());
                    // println!("  idx:  {}", input.0);
                });

                // println!("replacement map: {replacement_map:#?}");
                if body_ctx.underlying(analyzer)?.child.is_some() {
                    let edges = body_ctx.successful_edges(analyzer)?;
                    if edges.len() == 1 {
                        // let ret_nodes = edges[0].return_nodes(analyzer)?;
                        // println!("return nodes: {:#?}", ret_nodes);
                    } else {
                        // println!("multiple edges: {}", edges.len());
                    }
                } else {
                    // 1. Create a new variable with name `<func_name>.<return_number>`
                    // 2. Set the range to be the copy of the return's simplified range from the function
                    // 3. Replace the fundamentals with the input data
                    let ret: Vec<_> = body_ctx.return_nodes(analyzer)?.iter().enumerate().map(|(i, (_, ret_node))| {
                        // println!("original return:");
                        // println!("  name: {}", ret_node.display_name(analyzer).unwrap());
                        // println!("  range: {}", ret_node.simplified_range_string(analyzer).unwrap().unwrap());
                        let mut new_var = ret_node.underlying(analyzer).unwrap().clone();
                        let new_name = format!("{}.{i}", func.name(analyzer).unwrap());
                        new_var.name = new_name.clone();
                        new_var.display_name = new_name;
                        if let Some(mut range) = new_var.ty.take_range() {
                            replacement_map.iter().for_each(|(replace, replacement)| {
                                range.replace_dep((*replace).into(), replacement.clone(), analyzer);
                            });

                            range.cache_eval(analyzer).unwrap();

                            new_var.ty.set_range(range).unwrap();
                        }

                        let new_cvar = ContextVarNode::from(analyzer.add_node(Node::ContextVar(new_var)));
                        analyzer.add_edge(new_cvar, *self, Edge::Context(ContextEdge::Variable));
                        self.add_var(new_cvar, analyzer).unwrap();
                        // let new_range =  new_cvar.range(analyzer).unwrap().unwrap();

                        // println!("new return:");
                        // println!("  name: {}", new_cvar.display_name(analyzer).unwrap());
                        // println!("  range: {}", new_cvar.range_string(analyzer).unwrap().unwrap());
                        ExprRet::Single(new_cvar.into())
                    }).collect();



                    // println!("requires:");
                    body_ctx.ctx_deps(analyzer)?.iter().for_each(|dep| {
                        // println!("  name: {}", dep.display_name(analyzer).unwrap());
                        let mut new_var = dep.underlying(analyzer).unwrap().clone();
                        if let Some(mut range) = new_var.ty.take_range() {
                            replacement_map.iter().for_each(|(replace, replacement)| {
                                range.replace_dep((*replace).into(), replacement.clone(), analyzer);
                            });

                            range.cache_eval(analyzer).unwrap();
                            new_var.ty.set_range(range).unwrap();
                        }

                        let new_cvar = ContextVarNode::from(analyzer.add_node(Node::ContextVar(new_var)));
                        self.add_ctx_dep(new_cvar, analyzer).unwrap();
                    });

                    self.underlying_mut(analyzer)?.path = format!(
                        "{}.{}.resume{{ {} }}",
                        self.path(analyzer),
                        func.name(analyzer).unwrap(),
                        self.associated_fn_name(analyzer).unwrap()
                    );
                    self
                        .push_expr(ExprRet::Multi(ret), analyzer)?;
                    return Ok(true);
                }
            }

            // update path name to reflect that we called the function
        }

        Ok(false)
        // todo!("Joining not supported yet");
    }

    pub fn add_gas_cost(
        &self,
        analyzer: &mut impl GraphBackend,
        cost: u64,
    ) -> Result<(), GraphError> {
        self.associated_fn(analyzer)?.add_gas_cost(analyzer, cost)
    }

    /// Gets the total context width
    pub fn total_width(
        &self,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<usize, GraphError> {
        self.first_ancestor(analyzer)?
            .number_of_live_edges(analyzer)
    }

    /// Gets the total context depth
    pub fn depth(&self, analyzer: &impl GraphBackend) -> usize {
        self.underlying(analyzer).unwrap().depth
    }

    /// The path of the underlying context
    pub fn path(&self, analyzer: &impl GraphBackend) -> String {
        self.underlying(analyzer).unwrap().path.clone()
    }

    /// Gets a mutable reference to the underlying context in the graph
    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut (impl GraphBackend<Node = Node> + AnalyzerBackend),
    ) -> Result<&'a mut Context, GraphError> {
        match analyzer.node_mut(*self) {
            Node::Context(c) => Ok(c),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Context but it was: {e:?}"
            ))),
        }
    }

    /// Gets an immutable reference to the underlying context in the graph
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a Context, GraphError> {
        match analyzer.node(*self) {
            Node::Context(c) => Ok(c),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Context but it was: {e:?}"
            ))),
        }
    }

    /// Returns an option to where the context was killed
    pub fn killed_loc(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<(Loc, KilledKind)>, GraphError> {
        Ok(self.underlying(analyzer)?.killed)
    }

    /// Add a return node to the context
    pub fn add_return_node(
        &self,
        ret_stmt_loc: Loc,
        ret: ContextVarNode,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.ret.push((ret_stmt_loc, ret));
        self.propogate_end(analyzer)?;
        Ok(())
    }

    /// Propogate that this context has ended up the context graph
    pub fn propogate_end(
        &self,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<(), GraphError> {
        let underlying = &mut self.underlying_mut(analyzer)?;
        let curr_live = underlying.number_of_live_edges;
        underlying.number_of_live_edges = 0;
        if let Some(parent) = self.underlying(analyzer)?.parent_ctx {
            let live_edges = &mut parent.underlying_mut(analyzer)?.number_of_live_edges;
            *live_edges = live_edges.saturating_sub(1 + curr_live);
            parent.propogate_end(analyzer)?;
        }
        Ok(())
    }

    /// Gets the return nodes for this context
    pub fn return_nodes(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<(Loc, ContextVarNode)>, GraphError> {
        Ok(self.underlying(analyzer)?.ret.clone())
    }

    /// Returns a string for dot-string things
    pub fn as_string(&mut self) -> String {
        "Context".to_string()
    }
}

impl From<ContextNode> for NodeIdx {
    fn from(val: ContextNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for ContextNode {
    fn from(idx: NodeIdx) -> Self {
        ContextNode(idx.index())
    }
}
