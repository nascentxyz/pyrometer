use crate::Analyzer;
use graph::{
    elem::Elem,
    nodes::{
        BlockNode, Builtin, Concrete, ConcreteNode, ContextNode, ContextVar, ContextVarNode,
        ContractNode, FuncReconstructionReqs, Function, FunctionNode, FunctionParam,
        FunctionParamNode, FunctionReturn, KilledKind, MsgNode,
    },
    AnalyzerBackend, Edge, GraphBackend, Node, RepresentationInvariant, TypeNode, VarType,
};
use shared::{
    AnalyzerLike, ApplyStats, ExprErr, FlatExpr, GraphError, GraphLike, IntoExprErr, NodeIdx,
    RangeArena, RepresentationErr,
};

use ahash::AHashMap;
use ethers_core::types::U256;
use solang_parser::{
    helpers::CodeLocation,
    pt::{Expression, Loc},
};

use std::collections::BTreeMap;
use std::io::Write;

impl AnalyzerBackend for Analyzer {
    fn add_concrete_var(
        &mut self,
        ctx: graph::nodes::ContextNode,
        concrete: Concrete,
        loc: Loc,
    ) -> Result<graph::nodes::ContextVarNode, Self::ExprErr> {
        let cnode = self.add_node(concrete);
        let var = ContextVar::new_from_concrete(loc, ctx, cnode.into(), self);
        let cnode = self.add_node(var.into_expr_err(loc)?);
        Ok(cnode.into())
    }
}

impl AnalyzerLike for Analyzer {
    type Expr = Expression;
    type ExprErr = ExprErr;
    type MsgNode = MsgNode;
    type BlockNode = BlockNode;

    type Function = Function;
    type FunctionNode = FunctionNode;
    type FunctionParam = FunctionParam;
    type FunctionReturn = FunctionReturn;
    type ContextNode = ContextNode;
    type Builtin = Builtin;

    fn builtin_fn_nodes(&self) -> &AHashMap<String, NodeIdx> {
        &self.builtin_fn_nodes
    }

    fn builtin_fn_nodes_mut(&mut self) -> &mut AHashMap<String, NodeIdx> {
        &mut self.builtin_fn_nodes
    }

    fn max_depth(&self) -> usize {
        self.max_depth
    }

    fn max_width(&self) -> usize {
        self.max_width
    }

    fn minimize_err(&mut self, ctx: ContextNode) -> String {
        let genesis = ctx.genesis(self).unwrap();
        let mut family_tree = genesis.family_tree(self).unwrap();
        family_tree.push(genesis);
        let mut needed_functions = family_tree
            .iter()
            .map(|c| c.associated_fn(self).unwrap())
            .collect::<Vec<_>>();
        let applies = family_tree
            .into_iter()
            .flat_map(|c| c.underlying(self).unwrap().applies.clone())
            .collect::<Vec<_>>();
        needed_functions.extend(applies);
        needed_functions.sort_by(|a, b| a.0.cmp(&b.0));
        needed_functions.dedup();

        fn recurse_find(
            contract: ContractNode,
            target_contract: ContractNode,
            analyzer: &impl GraphBackend,
        ) -> Option<Vec<ContractNode>> {
            let mut inherited = contract.direct_inherited_contracts(analyzer);
            if inherited.contains(&target_contract) {
                Some(vec![contract])
            } else if inherited.is_empty() {
                None
            } else {
                while !inherited.is_empty() {
                    if let Some(mut c) =
                        recurse_find(inherited.pop().unwrap(), target_contract, analyzer)
                    {
                        c.push(contract);
                        return Some(c);
                    }
                }
                None
            }
        }

        let mut contract_to_funcs: BTreeMap<
            Option<ContractNode>,
            Vec<(FunctionNode, FuncReconstructionReqs)>,
        > = Default::default();

        let mut tys = vec![];
        let mut enums = vec![];
        let mut structs = vec![];
        let mut errs = vec![];
        needed_functions.into_iter().for_each(|func| {
            let maybe_func_contract = func.maybe_associated_contract(self);
            let reqs = func.reconstruction_requirements(self);
            reqs.usertypes.iter().for_each(|var| {
                let maybe_associated_contract = match var {
                    TypeNode::Contract(c) => Some(*c),
                    TypeNode::Enum(c) => c.maybe_associated_contract(self),
                    TypeNode::Error(c) => c.maybe_associated_contract(self),
                    TypeNode::Struct(c) => c.maybe_associated_contract(self),
                    TypeNode::Ty(c) => c.maybe_associated_contract(self),
                    TypeNode::Func(_) => None,
                    TypeNode::Unresolved(_) => None,
                };
                reqs.storage.iter().for_each(|var| {
                    if let Some(c) = var.maybe_associated_contract(self) {
                        contract_to_funcs.entry(Some(c)).or_default();

                        if let Some(func_c) = maybe_func_contract {
                            if let Some(needed) = recurse_find(func_c, c, self) {
                                needed.into_iter().for_each(|c| {
                                    contract_to_funcs.entry(Some(c)).or_default();
                                });
                            }
                        }
                    }
                });

                if let Some(c) = maybe_associated_contract {
                    contract_to_funcs.entry(Some(c)).or_default();

                    if let Some(func_c) = maybe_func_contract {
                        if let Some(needed) = recurse_find(func_c, c, self) {
                            needed.into_iter().for_each(|c| {
                                contract_to_funcs.entry(Some(c)).or_default();
                            });
                        }
                    }
                } else {
                    match var {
                        TypeNode::Enum(c) => enums.push(*c),
                        TypeNode::Error(c) => errs.push(*c),
                        TypeNode::Struct(c) => structs.push(*c),
                        TypeNode::Ty(c) => tys.push(*c),
                        _ => {}
                    }
                }
            });
            let entry = contract_to_funcs.entry(maybe_func_contract).or_default();
            entry.push((func, reqs));
        });

        let contracts = contract_to_funcs.keys().collect::<Vec<_>>();
        let contract_str = contracts
            .iter()
            .filter_map(|maybe_contract| {
                if let Some(contract) = maybe_contract {
                    Some(contract.reconstruct(self, &contract_to_funcs).ok()?)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("\n\n");
        let func_str = if let Some(free_floating_funcs) = contract_to_funcs.get(&None) {
            free_floating_funcs
                .iter()
                .map(|(func, _)| func.reconstruct_src(self).unwrap())
                .collect::<Vec<_>>()
                .join("\n")
        } else {
            "".to_string()
        };
        let enum_str = enums
            .iter()
            .map(|enu| enu.reconstruct_src(self).unwrap())
            .collect::<Vec<_>>()
            .join("\n");
        let enum_str = if enum_str.is_empty() {
            "".to_string()
        } else {
            format!("{enum_str}\n")
        };
        let struct_str = structs
            .iter()
            .map(|strukt| strukt.reconstruct_src(self).unwrap())
            .collect::<Vec<_>>()
            .join("\n");
        let struct_str = if struct_str.is_empty() {
            "".to_string()
        } else {
            format!("{struct_str}\n")
        };
        let ty_str = tys
            .iter()
            .map(|ty| ty.reconstruct_src(self).unwrap())
            .collect::<Vec<_>>()
            .join("\n");
        let ty_str = if ty_str.is_empty() {
            "".to_string()
        } else {
            format!("{ty_str}\n")
        };
        let err_str = errs
            .iter()
            .map(|err| err.reconstruct_src(self).unwrap())
            .collect::<Vec<_>>()
            .join("\n");
        let err_str = if err_str.is_empty() {
            "".to_string()
        } else {
            format!("{err_str}\n")
        };

        format!("{err_str}{ty_str}{enum_str}{struct_str}{func_str}\n{contract_str}")
    }

    fn add_expr_err(&mut self, err: ExprErr) {
        if self.debug_panic() {
            if let Some(path) = self.minimize_debug().clone() {
                let reconstruction_edge: ContextNode = self
                    .graph
                    .node_indices()
                    .find_map(|node| match self.node(node) {
                        Node::Context(context) => {
                            println!("context path: {}", context.path);
                            match context.killed {
                                Some((_, KilledKind::ParseError)) => {
                                    let edges = graph::nodes::ContextNode::from(node)
                                        .all_edges(self)
                                        .unwrap();
                                    let reconstruction_edge = *edges
                                        .iter()
                                        .filter(|c| c.underlying(self).unwrap().killed.is_some())
                                        .take(1)
                                        .next()
                                        .unwrap_or(&ContextNode::from(node));

                                    Some(reconstruction_edge)
                                }
                                _e => None,
                            }
                        }
                        _ => None,
                    })
                    .unwrap();

                let min_str = self.minimize_err(reconstruction_edge);

                let mut file = std::fs::OpenOptions::new()
                    .write(true)
                    .create(true) // Create the file if it doesn't exist
                    .truncate(true) // truncate if it does
                    .open(path)
                    .unwrap();

                file.write_all(min_str.as_bytes()).unwrap();
            }
            panic!("Encountered an error: {err:?}");
        }
        if !self.expr_errs.contains(&err) {
            self.expr_errs.push(err);
        }
    }

    fn expr_errs(&self) -> Vec<ExprErr> {
        self.expr_errs.clone()
    }

    fn entry(&self) -> NodeIdx {
        self.entry
    }

    fn parse_fn(&self) -> FunctionNode {
        self.parse_fn
    }

    fn msg(&mut self) -> MsgNode {
        self.msg
    }

    fn block(&mut self) -> BlockNode {
        self.block
    }

    fn builtin_fns(&self) -> &AHashMap<String, Function> {
        &self.builtin_fns
    }

    fn builtin_fn_inputs(&self) -> &AHashMap<String, (Vec<FunctionParam>, Vec<FunctionReturn>)> {
        &self.builtin_fn_inputs
    }

    fn builtins(&self) -> &AHashMap<Builtin, NodeIdx> {
        &self.builtins
    }
    fn builtins_mut(&mut self) -> &mut AHashMap<Builtin, NodeIdx> {
        &mut self.builtins
    }
    fn user_types(&self) -> &AHashMap<String, Vec<NodeIdx>> {
        &self.user_types
    }
    fn user_types_mut(&mut self) -> &mut AHashMap<String, Vec<NodeIdx>> {
        &mut self.user_types
    }

    fn parse_expr(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        expr: &Expression,
        parent: Option<NodeIdx>,
    ) -> NodeIdx {
        use Expression::*;
        match expr {
            Type(_loc, ty) => {
                if let Some(builtin) = Builtin::try_from_ty(ty.clone(), self, arena) {
                    if let Some(idx) = self.builtins.get(&builtin) {
                        *idx
                    } else {
                        let idx = self.add_node(Node::Builtin(builtin.clone()));
                        self.builtins.insert(builtin, idx);
                        idx
                    }
                } else if let Some(idx) = self.complicated_parse(arena, expr, parent) {
                    self.add_if_err(idx.expect_single().into_expr_err(expr.loc()))
                        .unwrap_or(0.into())
                } else {
                    0.into()
                }
            }
            Variable(ident) => {
                if let Some(idxs) = self.user_types.get(&ident.name) {
                    if idxs.len() == 1 {
                        idxs[0]
                    } else {
                        let contract = idxs.iter().find(|maybe_contract| {
                            matches!(self.node(**maybe_contract), Node::Contract(..))
                        });
                        let strukt = idxs.iter().find(|maybe_struct| {
                            matches!(self.node(**maybe_struct), Node::Struct(..))
                        });
                        match (contract, strukt) {
                            (Some(_), Some(strukt)) => *strukt,
                            _ => panic!("This should be invalid solidity"),
                        }
                    }
                } else {
                    let node = self.add_node(Node::Unresolved(ident.clone()));
                    let entry = self.user_types.entry(ident.name.clone()).or_default();
                    entry.push(node);
                    node
                }
            }
            ArraySubscript(_loc, ty_expr, None) => {
                let inner_ty = self.parse_expr(arena, ty_expr, parent);
                if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
                    let dyn_b = Builtin::Array(var_type);
                    if let Some(idx) = self.builtins.get(&dyn_b) {
                        *idx
                    } else {
                        let idx = self.add_node(Node::Builtin(dyn_b.clone()));
                        self.builtins.insert(dyn_b, idx);
                        idx
                    }
                } else {
                    inner_ty
                }
            }
            ArraySubscript(loc, ty_expr, Some(idx_expr)) => {
                let inner_ty = self.parse_expr(arena, ty_expr, parent);
                let idx = self.parse_expr(arena, idx_expr, parent);
                if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
                    let res = ConcreteNode::from(idx)
                        .underlying(self)
                        .into_expr_err(*loc)
                        .cloned();
                    if let Some(concrete) = self.add_if_err(res) {
                        if let Some(size) = concrete.uint_val() {
                            let dyn_b = Builtin::SizedArray(size, var_type);
                            if let Some(idx) = self.builtins.get(&dyn_b) {
                                *idx
                            } else {
                                let idx = self.add_node(Node::Builtin(dyn_b.clone()));
                                self.builtins.insert(dyn_b, idx);
                                idx
                            }
                        } else {
                            inner_ty
                        }
                    } else {
                        inner_ty
                    }
                } else {
                    inner_ty
                }
            }
            NumberLiteral(_loc, integer, exponent, _unit) => {
                let int = U256::from_dec_str(integer).unwrap();
                let val = if !exponent.is_empty() {
                    let exp = U256::from_dec_str(exponent).unwrap();
                    int * U256::from(10).pow(exp)
                } else {
                    int
                };

                self.add_node(Concrete::Uint(256, val))
            }
            _ => {
                if let Some(idx) = self.complicated_parse(arena, expr, parent) {
                    self.add_if_err(idx.expect_single().into_expr_err(expr.loc()))
                        .unwrap_or(0.into())
                } else {
                    0.into()
                }
            }
        }
    }

    fn builtin_or_add(&mut self, builtin: Builtin) -> NodeIdx {
        if let Some(idx) = self.builtins().get(&builtin) {
            *idx
        } else {
            let idx = self.add_node(Node::Builtin(builtin.clone()));
            self.builtins_mut().insert(builtin, idx);
            idx
        }
    }

    fn builtin_fn_or_maybe_add(&mut self, builtin_name: &str) -> Option<NodeIdx>
    where
        Self: std::marker::Sized,
    {
        if let Some(idx) = self.builtin_fn_nodes().get(builtin_name) {
            Some(*idx)
        } else if let Some(func) = self.builtin_fns().get(builtin_name) {
            let (inputs, outputs) = self
                .builtin_fn_inputs()
                .get(builtin_name)
                .expect("builtin func but no inputs")
                .clone();
            let func_node = self.add_node(Node::Function(func.clone()));
            let mut params_strs = vec![];
            inputs.into_iter().for_each(|input| {
                let input_node = self.add_node(input);
                params_strs.push(FunctionParamNode::from(input_node).ty_str(self).unwrap());
                self.add_edge(input_node, func_node, Edge::FunctionParam);
            });
            outputs.into_iter().for_each(|output| {
                let output_node = self.add_node(output);
                self.add_edge(output_node, func_node, Edge::FunctionReturn);
            });

            self.add_edge(func_node, self.entry(), Edge::Func);

            let underlying_mut = FunctionNode::from(func_node).underlying_mut(self).unwrap();
            let name = underlying_mut.name.as_mut().unwrap();
            let full_name = format!("{}({})", name, params_strs.join(", "));
            name.name.clone_from(&full_name);

            self.builtin_fn_nodes_mut()
                .insert(builtin_name.to_string(), func_node);
            Some(func_node)
        } else {
            None
        }
    }

    fn debug_panic(&self) -> bool {
        self.debug_panic
    }

    fn fn_calls_fns(&self) -> &BTreeMap<Self::FunctionNode, Vec<Self::FunctionNode>> {
        &self.fn_calls_fns
    }
    fn fn_calls_fns_mut(&mut self) -> &mut BTreeMap<Self::FunctionNode, Vec<Self::FunctionNode>> {
        &mut self.fn_calls_fns
    }

    fn apply_stats_mut(&mut self) -> &mut ApplyStats {
        &mut self.apply_stats
    }

    fn handled_funcs(&self) -> &[FunctionNode] {
        &self.handled_funcs
    }

    fn handled_funcs_mut(&mut self) -> &mut Vec<FunctionNode> {
        &mut self.handled_funcs
    }

    fn file_mapping(&self) -> BTreeMap<usize, &str> {
        let mut file_mapping: BTreeMap<usize, &str> = BTreeMap::new();
        for (_, sol, o_file_no, _) in self.sources.iter() {
            if let Some(file_no) = o_file_no {
                file_mapping.insert(*file_no, sol);
            }
        }
        file_mapping
    }
    fn minimize_debug(&self) -> &Option<String> {
        &self.minimize_debug
    }

    fn is_representation_ok(
        &mut self,
        arena: &RangeArena<<Self as GraphLike>::RangeElem>,
    ) -> Result<Vec<RepresentationErr>, GraphError> {
        let mut res = vec![];
        let dirty = self.take_dirty_nodes();
        for node in dirty {
            match self.node(node) {
                Node::Context(..) => {
                    if let Some(err) = ContextNode::from(node).is_representation_ok(self, arena)? {
                        res.push(err);
                    }
                }
                Node::ContextVar(..) => {
                    if ContextVarNode::from(node).maybe_ctx(self).is_some() {
                        if let Some(err) =
                            ContextVarNode::from(node).is_representation_ok(self, arena)?
                        {
                            res.push(err);
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(res)
    }

    type FlatExpr = FlatExpr;

    fn push_expr(&mut self, flat: FlatExpr) {
        self.flattened.push(flat);
    }

    fn decrement_asm_block(&mut self) {
        self.current_asm_block -= 1;
    }
    fn increment_asm_block(&mut self) {
        self.current_asm_block += 1;
    }

    fn current_asm_block(&self) -> usize {
        self.current_asm_block
    }

    fn expr_stack(&self) -> &[FlatExpr] {
        &self.flattened
    }

    fn expr_stack_mut(&mut self) -> &mut Vec<FlatExpr> {
        &mut self.flattened
    }

    fn debug_stack(&self) -> bool {
        self.debug_stack
    }

    fn increment_contract_id(&mut self) -> usize {
        let id = self.contract_id;
        self.contract_id += 1;
        id
    }
}
