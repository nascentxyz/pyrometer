use crate::context::exprs::Array;
use crate::context::exprs::MemberAccess;
use crate::context::exprs::Require;
use crate::context::ContextBuilder;
use crate::ExprRet;
use shared::analyzer::AsDotStr;
use shared::analyzer::GraphLike;
use shared::context::*;
use std::collections::BTreeMap;

use shared::range::elem_ty::Dynamic;

use shared::range::Range;
use shared::range::{elem_ty::Elem, SolcRange};
use solang_parser::pt::{Expression, Identifier, Loc, StorageLocation};

use crate::VarType;

use shared::{analyzer::AnalyzerLike, nodes::*, Edge, Node, NodeIdx};

impl<T> FuncCaller for T where T: AnalyzerLike<Expr = Expression> + Sized + GraphLike {}
pub trait FuncCaller: GraphLike + AnalyzerLike<Expr = Expression> + Sized {
    fn fn_call_expr(
        &mut self,
        ctx: ContextNode,
        loc: &Loc,
        func_expr: &Expression,
        input_exprs: &[Expression],
    ) -> ExprRet {
        use solang_parser::pt::Expression::*;
        match func_expr {
            MemberAccess(loc, member_expr, ident) => {
                let (mem_ctx, member) = self.parse_ctx_expr(member_expr, ctx).expect_single();

                let inputs = match ContextVarNode::from(member).underlying(self).ty {
                    VarType::User(TypeNode::Contract(_)) => input_exprs
                        .iter()
                        .map(|expr| self.parse_ctx_expr(expr, ctx))
                        .collect::<Vec<_>>(),
                    _ => {
                        let mut inputs = vec![ExprRet::Single((mem_ctx, member))];
                        inputs.extend(
                            input_exprs
                                .iter()
                                .map(|expr| self.parse_ctx_expr(expr, ctx))
                                .collect::<Vec<_>>(),
                        );
                        inputs
                    }
                };

                let inputs = ExprRet::Multi(inputs);
                if !inputs.has_literal() {
                    let as_input_str = inputs.try_as_func_input_str(self);

                    let (_func_ctx, func_idx) = match self.parse_ctx_expr(
                        &MemberAccess(
                            *loc,
                            member_expr.clone(),
                            Identifier {
                                loc: ident.loc,
                                name: format!("{}{}", ident.name, as_input_str),
                            },
                        ),
                        ctx,
                    ) {
                        ExprRet::Single((ctx, idx)) => (ctx, idx),
                        m @ ExprRet::Multi(_) => m.expect_single(),
                        ExprRet::CtxKilled => return ExprRet::CtxKilled,
                        e => todo!("got fork in func call: {:?}", e),
                    };

                    if matches!(self.node(func_idx), Node::Function(..)) {
                        // intrinsic
                        let mut inputs: Vec<Expression> = vec![*member_expr.clone()];
                        inputs.extend(input_exprs.to_vec());
                        self.intrinsic_func_call(loc, &inputs, func_idx, ctx)
                    } else {
                        self.func_call(
                            ctx,
                            *loc,
                            &inputs,
                            ContextVarNode::from(func_idx)
                                .ty(self)
                                .func_node(self)
                                .expect(""),
                        )
                    }
                } else {
                    // we need to disambiguate the literals
                    let ty = &ContextVarNode::from(member).underlying(self).ty;
                    let possible_funcs: Vec<FunctionNode> = match ty {
                        VarType::User(TypeNode::Contract(con_node)) => con_node.funcs(self),
                        VarType::BuiltIn(bn, _) => self
                            .possible_library_funcs(ctx, bn.0.into())
                            .into_iter()
                            .collect::<Vec<_>>(),
                        VarType::Concrete(cnode) => {
                            let b = cnode.underlying(self).as_builtin();
                            let bn = self.builtin_or_add(b);
                            self.possible_library_funcs(ctx, bn)
                                .into_iter()
                                .collect::<Vec<_>>()
                        }
                        VarType::User(TypeNode::Struct(sn)) => self
                            .possible_library_funcs(ctx, sn.0.into())
                            .into_iter()
                            .collect::<Vec<_>>(),
                        VarType::User(TypeNode::Enum(en)) => self
                            .possible_library_funcs(ctx, en.0.into())
                            .into_iter()
                            .collect::<Vec<_>>(),
                        VarType::User(TypeNode::Func(_)) => todo!(),
                    };
                    let lits = input_exprs
                        .iter()
                        .map(|expr| {
                            match expr {
                                Negate(_, expr) => {
                                    // negative number potentially
                                    matches!(**expr, NumberLiteral(..) | HexLiteral(..))
                                }
                                NumberLiteral(..) | HexLiteral(..) => true,
                                _ => false,
                            }
                        })
                        .collect();

                    if let Some(func) =
                        self.disambiguate_fn_call(&ident.name, lits, &inputs, &possible_funcs[..])
                    {
                        self.setup_fn_call(loc, &inputs, func.into(), ctx)
                    } else {
                        panic!(
                            "Could not disambiguate function call: {}, {:?}",
                            ident.name, inputs
                        )
                    }
                }
            }
            Variable(ident) => {
                // It is a function call, check if we have the ident in scope
                let funcs = ctx.visible_funcs(self);
                // filter down all funcs to those that match
                let possible_funcs = funcs
                    .iter()
                    .filter(|func| func.name(self).starts_with(&format!("{}(", ident.name)))
                    .copied()
                    .collect::<Vec<_>>();

                if possible_funcs.is_empty() {
                    // this is a builtin, cast, or unknown function?
                    let (func_ctx, func_idx) = match self.parse_ctx_expr(func_expr, ctx) {
                        ExprRet::Single((ctx, idx)) => (ctx, idx),
                        m @ ExprRet::Multi(_) => m.expect_single(),
                        ExprRet::CtxKilled => return ExprRet::CtxKilled,
                        e => todo!("got fork in func call: {:?}", e),
                    };
                    self.intrinsic_func_call(loc, input_exprs, func_idx, func_ctx)
                } else if possible_funcs.len() == 1 {
                    let inputs = ExprRet::Multi(
                        input_exprs
                            .iter()
                            .map(|expr| self.parse_ctx_expr(expr, ctx))
                            .collect(),
                    );
                    self.setup_fn_call(&ident.loc, &inputs, (possible_funcs[0]).into(), ctx)
                } else {
                    // this is the annoying case due to function overloading & type inference on number literals
                    let lits = input_exprs
                        .iter()
                        .map(|expr| {
                            match expr {
                                Negate(_, expr) => {
                                    // negative number potentially
                                    matches!(**expr, NumberLiteral(..) | HexLiteral(..))
                                }
                                NumberLiteral(..) | HexLiteral(..) => true,
                                _ => false,
                            }
                        })
                        .collect();
                    let inputs = ExprRet::Multi(
                        input_exprs
                            .iter()
                            .map(|expr| self.parse_ctx_expr(expr, ctx))
                            .collect(),
                    );

                    if let Some(func) =
                        self.disambiguate_fn_call(&ident.name, lits, &inputs, &possible_funcs)
                    {
                        self.setup_fn_call(loc, &inputs, func.into(), ctx)
                    } else {
                        ExprRet::CtxKilled
                    }
                }
            }
            _ => {
                let (func_ctx, func_idx) = match self.parse_ctx_expr(func_expr, ctx) {
                    ExprRet::Single((ctx, idx)) => (ctx, idx),
                    m @ ExprRet::Multi(_) => m.expect_single(),
                    ExprRet::CtxKilled => return ExprRet::CtxKilled,
                    e => todo!("got fork in func call: {:?}", e),
                };
                self.intrinsic_func_call(loc, input_exprs, func_idx, func_ctx)
            }
        }
    }

    /// Disambiguates a function call by their inputs (length & type)
    fn disambiguate_fn_call(
        &mut self,
        fn_name: &str,
        literals: Vec<bool>,
        input_paths: &ExprRet,
        funcs: &[FunctionNode],
    ) -> Option<FunctionNode> {
        // try to find the function based on naive signature
        // This doesnt do type inference on NumberLiterals (i.e. 100 could be uintX or intX, and there could
        // be a function that takes an int256 but we evaled as uint256)
        let fn_sig = format!("{}{}", fn_name, input_paths.try_as_func_input_str(self));
        if let Some(func) = funcs.iter().find(|func| func.name(self) == fn_sig) {
            return Some(*func);
        }

        // filter by input len
        let inputs = input_paths.as_flat_vec();
        let funcs: Vec<&FunctionNode> = funcs
            .iter()
            .filter(|func| func.params(self).len() == inputs.len())
            .collect();

        if funcs.len() == 1 {
            return Some(*funcs[0]);
        }

        if !literals.iter().any(|i| *i) {
            None
        } else {
            // println!("funcs: {:?}", funcs);
            let funcs = funcs
                .iter()
                .filter(|func| {
                    let params = func.params(self);
                    params
                        .iter()
                        .zip(&inputs)
                        .enumerate()
                        .all(|(i, (param, input))| {
                            if param.as_dot_str(self)
                                == ContextVarNode::from(*input).as_dot_str(self)
                            {
                                true
                            } else if literals[i] {
                                let as_concrete = ContextVarNode::from(*input).as_concrete(self);
                                let possibilities = as_concrete.possible_builtins_from_ty_inf();
                                let param_ty = param.ty(self);
                                match self.node(param_ty) {
                                    Node::Builtin(b) => possibilities.contains(b),
                                    _ => false,
                                }
                            } else {
                                false
                            }
                        })
                })
                .collect::<Vec<_>>();
            if funcs.len() == 1 {
                Some(**funcs[0])
            } else {
                // this would be invalid solidity, likely the user needs to perform a cast
                None
            }
        }
    }

    /// Setups up storage variables for a function call and calls it
    fn setup_fn_call(
        &mut self,
        loc: &Loc,
        inputs: &ExprRet,
        func_idx: NodeIdx,
        ctx: ContextNode,
    ) -> ExprRet {
        // if we have a single match thats our function
        let mut var = match ContextVar::maybe_from_user_ty(self, *loc, func_idx) {
            Some(v) => v,
            None => panic!(
                "Could not create context variable from user type: {:?}",
                self.node(func_idx)
            ),
        };

        // TODO: this is probably wrong
        if let Some(r) = var.fallback_range(self) {
            if var.storage.is_some() {
                if let Elem::Concrete(c) = r.range_max() {
                    if let Some(size) = c.val.int_size() {
                        var.set_range_max(Elem::from(Concrete::Uint(size, 0.into())), None)
                    }
                }
            }
        }
        let new_cvarnode = self.add_node(Node::ContextVar(var));
        self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
        if let Some(func_node) = ContextVarNode::from(new_cvarnode).ty(self).func_node(self) {
            self.func_call(ctx, *loc, inputs, func_node)
        } else {
            unreachable!()
        }
    }

    /// Calls an intrinsic/builtin function call (casts, require, etc.)
    fn intrinsic_func_call(
        &mut self,
        loc: &Loc,
        input_exprs: &[Expression],
        func_idx: NodeIdx,
        ctx: ContextNode,
    ) -> ExprRet {
        match self.node(func_idx) {
            Node::Function(underlying) => {
                if let Some(func_name) = &underlying.name {
                    match &*func_name.name {
                        "require" | "assert" => {
                            self.handle_require(input_exprs, ctx);
                            ExprRet::Multi(vec![])
                        }
                        "type" => ExprRet::Single(
                            self.parse_ctx_expr(&input_exprs[0], ctx).expect_single(),
                        ),
                        "push" => {
                            let (arr_ctx, arr) =
                                self.parse_ctx_expr(&input_exprs[0], ctx).expect_single();
                            let arr = ContextVarNode::from(arr).latest_version(self);
                            // get length
                            let len = self.tmp_length(arr, arr_ctx, *loc);

                            println!("array: {:?}", arr.underlying(self));

                            let len_as_idx = len.as_tmp(*loc, ctx, self);
                            // set length as index
                            let index = self.index_into_array_inner(
                                *loc,
                                ExprRet::Single((arr_ctx, arr.latest_version(self).into())),
                                ExprRet::Single((arr_ctx, len_as_idx.latest_version(self).into())),
                            );
                            // assign index to new_elem
                            let new_elem = self.parse_ctx_expr(&input_exprs[1], ctx);
                            self.match_assign_sides(*loc, &index, &new_elem)
                        }
                        "ecrecover" => {
                            input_exprs.iter().for_each(|expr| {
                                // we want to parse even though we dont need the variables here
                                let _ = self.parse_ctx_expr(expr, ctx);
                            });
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Address).into(),
                                self,
                            );
                            let cvar = self.add_node(Node::ContextVar(var));
                            ExprRet::Single((ctx, cvar))
                        }
                        "keccak256" => {
                            self.parse_ctx_expr(&input_exprs[0], ctx).expect_single();
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Bytes(32)).into(), 
                                self,
                            );
                            let cvar = self.add_node(Node::ContextVar(var));
                            ExprRet::Single((ctx, cvar))
                        },
                        e => todo!("builtin function: {:?}", e),
                    }
                } else {
                    panic!("unnamed builtin?")
                }
            }
            Node::Builtin(Builtin::Array(_)) => {
                // create a new list
                let (ctx, len_cvar) = self.parse_ctx_expr(&input_exprs[0], ctx).expect_single();
                let ty = VarType::try_from_idx(self, func_idx);

                let new_arr = ContextVar {
                    loc: Some(*loc),
                    name: format!("tmp_arr{}", ctx.new_tmp(self)),
                    display_name: "arr".to_string(),
                    storage: None,
                    is_tmp: true,
                    is_symbolic: false,
                    tmp_of: None,
                    ty: ty.expect("No type for node"),
                };

                let arr = ContextVarNode::from(self.add_node(Node::ContextVar(new_arr)));

                let len_var = ContextVar {
                    loc: Some(*loc),
                    name: arr.name(self) + ".length",
                    display_name: arr.display_name(self) + ".length",
                    storage: None,
                    is_tmp: true,
                    tmp_of: None,
                    is_symbolic: true,
                    ty: ContextVarNode::from(len_cvar).underlying(self).ty.clone(),
                };

                let len_cvar = self.add_node(Node::ContextVar(len_var));
                self.add_edge(arr, ctx, Edge::Context(ContextEdge::Variable));
                self.add_edge(len_cvar, ctx, Edge::Context(ContextEdge::Variable));
                self.add_edge(len_cvar, arr, Edge::Context(ContextEdge::AttrAccess));

                // update the length
                if let Some(r) = arr.range(self) {
                    let min = r.evaled_range_min(self);
                    let max = r.evaled_range_max(self);

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_cvar, *loc));
                        arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)));
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_cvar, *loc));
                        arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                    }
                }

                ExprRet::Single((ctx, arr.into()))
            }
            Node::Builtin(ty) => {
                // it is a cast
                let ty = ty.clone();
                let (ctx, cvar) = self.parse_ctx_expr(&input_exprs[0], ctx).expect_single();

                let new_var = ContextVarNode::from(cvar).as_cast_tmp(*loc, ctx, ty.clone(), self);

                new_var.underlying_mut(self).ty = VarType::try_from_idx(self, func_idx).expect("");

                // cast the ranges
                if let Some(r) = ContextVarNode::from(cvar).range(self) {
                    let curr_range = SolcRange::try_from_builtin(&ty).expect("No default range");
                    new_var.set_range_min(self, r.range_min().cast(curr_range.range_min()));
                    new_var.set_range_max(self, r.range_max().cast(curr_range.range_max()));
                    // cast the range exclusions - TODO: verify this is correct
                    let mut exclusions = r.range_exclusions();
                    exclusions.iter_mut().for_each(|range| {
                        *range = range.clone().cast(curr_range.range_min());
                    });
                    new_var.set_range_exclusions(self, exclusions);
                } else {
                    // todo!("unable to cast: {:?}, {ty:?}", self.node(cvar))
                }
                ExprRet::Single((ctx, new_var.into()))
            }
            Node::ContextVar(_c) => {
                // its a user type
                // TODO: figure out if we actually need to do anything?
                let _inputs: Vec<_> = input_exprs
                    .iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect();

                ExprRet::Single((ctx, func_idx))
            }
            Node::Contract(_) => {
                // TODO: figure out if we need to do anything
                let _inputs: Vec<_> = input_exprs
                    .iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect();

                ExprRet::Single((ctx, func_idx))
            }
            e => todo!("{:?}", e),
        }
    }

    /// Matches the input kinds and performs the call
    fn func_call(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        input_paths: &ExprRet,
        func: FunctionNode,
    ) -> ExprRet {
        let params = func.params(self);
        match input_paths {
            ExprRet::Single((_ctx, input_var)) => {
                // if we get a single var, we expect the func to only take a single
                // variable
                self.func_call_inner(
                    false,
                    ctx,
                    func,
                    loc,
                    vec![ContextVarNode::from(*input_var).latest_version(self)],
                    params,
                    None,
                )
            }
            ExprRet::Multi(inputs) => {
                // check if the inputs length matchs func params length
                // if they do, check that none are forks
                if inputs.len() == params.len() {
                    if !input_paths.has_fork() {
                        let input_vars = inputs
                            .iter()
                            .map(|expr_ret| {
                                let (_ctx, var) = expr_ret.expect_single();
                                ContextVarNode::from(var).latest_version(self)
                            })
                            .collect();
                        self.func_call_inner(false, ctx, func, loc, input_vars, params, None)
                    } else {
                        panic!("input has fork - need to flatten")
                    }
                } else {
                    panic!("Length mismatch: {inputs:?} {params:?}");
                }
            }
            _ => todo!("here"),
        }
    }

    /// Checks if there are any modifiers and executes them prior to executing the function
    fn func_call_inner(
        &mut self,
        entry_call: bool,
        ctx: ContextNode,
        func_node: FunctionNode,
        loc: Loc,
        inputs: Vec<ContextVarNode>,
        params: Vec<FunctionParamNode>,
        modifier_state: Option<ModifierState>,
    ) -> ExprRet {
        let fn_ext = ctx.is_fn_ext(func_node, self);
        let callee_ctx = if entry_call {
            ctx
        } else {
            let callee_ctx = ContextNode::from(self.add_node(Node::Context(Context::new_subctx(
                ctx,
                loc,
                false,
                Some(func_node),
                fn_ext,
                self,
                modifier_state.clone(),
            ))));
            ctx.add_child(callee_ctx, self);
            let ctx_fork = self.add_node(Node::FunctionCall);
            self.add_edge(ctx_fork, ctx, Edge::Context(ContextEdge::Subcontext));
            self.add_edge(ctx_fork, func_node, Edge::Context(ContextEdge::Call));
            self.add_edge(
                NodeIdx::from(callee_ctx.0),
                ctx_fork,
                Edge::Context(ContextEdge::Subcontext),
            );
            callee_ctx
        };

        let renamed_inputs = params
            .iter()
            .zip(inputs.iter())
            .filter_map(|(param, input)| {
                if !entry_call {
                    if let Some(name) = param.maybe_name(self) {
                        let mut new_cvar = input.latest_version(self).underlying(self).clone();
                        new_cvar.loc = Some(param.loc(self));
                        new_cvar.name = name.clone();
                        new_cvar.display_name = name;
                        new_cvar.is_tmp = false;
                        new_cvar.storage = if let Some(StorageLocation::Storage(_)) =
                            param.underlying(self).storage
                        {
                            new_cvar.storage
                        } else {
                            None
                        };

                        if let Some(param_ty) = VarType::try_from_idx(self, param.ty(self)) {
                            let ty = new_cvar.ty.clone();
                            if !ty.ty_eq(&param_ty, self) {
                                if let Some(new_ty) = ty.try_cast(&param_ty, self) {
                                    new_cvar.ty = new_ty;
                                }
                            }
                        }

                        let node = ContextVarNode::from(self.add_node(Node::ContextVar(new_cvar)));

                        if let (Some(r), Some(r2)) = (node.range(self), param.range(self)) {
                            let new_min = r.range_min().cast(r2.range_min());
                            let new_max = r.range_max().cast(r2.range_max());
                            node.try_set_range_min(self, new_min);
                            node.try_set_range_max(self, new_max);
                            node.try_set_range_exclusions(self, r.exclusions);
                        }
                        self.add_edge(node, callee_ctx, Edge::Context(ContextEdge::Variable));
                        Some((*input, node))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect::<BTreeMap<_, ContextVarNode>>();

        let mods = func_node.modifiers(self);
        if let Some(mod_state) = modifier_state {
            // we are iterating through modifiers
            if mod_state.num + 1 < mods.len() {
                // use the next modifier
                let mut mstate = mod_state;
                mstate.num += 1;
                self.call_modifier_for_fn(loc, callee_ctx, func_node, mstate)
            } else {
                // out of modifiers, execute the actual function call
                self.execute_call_inner(loc, ctx, callee_ctx, func_node, renamed_inputs)
            }
        } else if !mods.is_empty() {
            // we have modifiers and havent executed them, start the process of executing them
            let state = ModifierState::new(0, loc, func_node, callee_ctx, ctx, renamed_inputs);
            self.call_modifier_for_fn(loc, callee_ctx, func_node, state)
        } else {
            // no modifiers, just execute the function
            self.execute_call_inner(loc, ctx, callee_ctx, func_node, renamed_inputs)
        }
    }

    /// Actually executes the function
    fn execute_call_inner(
        &mut self,
        loc: Loc,
        caller_ctx: ContextNode,
        callee_ctx: ContextNode,
        func_node: FunctionNode,
        renamed_inputs: BTreeMap<ContextVarNode, ContextVarNode>,
    ) -> ExprRet {
        if let Some(body) = func_node.underlying(self).body.clone() {
            // add return nodes into the subctx
            func_node.returns(self).iter().for_each(|ret| {
                if let Some(var) =
                    ContextVar::maybe_new_from_func_ret(self, ret.underlying(self).clone())
                {
                    let cvar = self.add_node(Node::ContextVar(var));
                    self.add_edge(cvar, callee_ctx, Edge::Context(ContextEdge::Variable));
                }
            });

            self.parse_ctx_statement(&body, false, Some(callee_ctx));

            // update any requirements
            self.inherit_input_changes(loc, caller_ctx, callee_ctx, &renamed_inputs);
            self.inherit_storage_changes(caller_ctx, callee_ctx);

            ExprRet::Multi(
                callee_ctx
                    .underlying(self)
                    .ret
                    .clone()
                    .into_iter()
                    .map(|(_, node)| ExprRet::Single((callee_ctx, node.into())))
                    .collect(),
            )
        } else {
            self.inherit_input_changes(loc, caller_ctx, callee_ctx, &renamed_inputs);
            self.inherit_storage_changes(caller_ctx, callee_ctx);

            ExprRet::Multi(
                func_node
                    .returns(self)
                    .iter()
                    .filter_map(|ret| {
                        let underlying = ret.underlying(self);
                        let var = ContextVar::maybe_new_from_func_ret(self, underlying.clone())?;
                        let node = self.add_node(Node::ContextVar(var));
                        Some(ExprRet::Single((caller_ctx, node)))
                    })
                    .collect(),
            )
        }
    }

    /// Calls a modifier for a function
    fn call_modifier_for_fn(
        &mut self,
        loc: Loc,
        func_ctx: ContextNode,
        func_node: FunctionNode,
        mod_state: ModifierState,
    ) -> ExprRet {
        let mod_node = func_node.modifiers(self)[mod_state.num];
        let mod_ctx = ContextNode::from(self.add_node(Node::Context(Context::new_subctx(
            func_ctx,
            loc,
            false,
            Some(mod_node),
            false,
            self,
            Some(mod_state.clone()),
        ))));
        func_ctx.add_child(mod_ctx, self);
        let ctx_fork = self.add_node(Node::FunctionCall);
        self.add_edge(ctx_fork, func_ctx, Edge::Context(ContextEdge::Subcontext));
        self.add_edge(ctx_fork, mod_node, Edge::Context(ContextEdge::Call));
        self.add_edge(
            NodeIdx::from(mod_ctx.0),
            ctx_fork,
            Edge::Context(ContextEdge::Subcontext),
        );

        let input_exprs = func_node.modifier_input_vars(mod_state.num, self);
        let inputs: Vec<ContextVarNode> = input_exprs
            .iter()
            .map(|expr| {
                let (_ctx, input) = self.parse_ctx_expr(expr, mod_ctx).expect_single();
                input.into()
            })
            .collect();

        let params = mod_node.params(self);
        let renamed_inputs = params
            .iter()
            .zip(inputs.iter())
            .filter_map(|(param, input)| {
                if let Some(name) = param.maybe_name(self) {
                    let mut new_cvar = input.latest_version(self).underlying(self).clone();
                    new_cvar.loc = Some(param.loc(self));
                    new_cvar.name = name.clone();
                    new_cvar.display_name = name;
                    new_cvar.is_tmp = false;
                    new_cvar.storage =
                        if let Some(StorageLocation::Storage(_)) = param.underlying(self).storage {
                            new_cvar.storage
                        } else {
                            None
                        };

                    if let Some(param_ty) = VarType::try_from_idx(self, param.ty(self)) {
                        let ty = new_cvar.ty.clone();
                        if !ty.ty_eq(&param_ty, self) {
                            if let Some(new_ty) = ty.try_cast(&param_ty, self) {
                                new_cvar.ty = new_ty;
                            }
                        }
                    }

                    let node = ContextVarNode::from(self.add_node(Node::ContextVar(new_cvar)));

                    if let (Some(r), Some(r2)) = (node.range(self), param.range(self)) {
                        let new_min = r.range_min().cast(r2.range_min());
                        let new_max = r.range_max().cast(r2.range_max());
                        node.try_set_range_min(self, new_min);
                        node.try_set_range_max(self, new_max);
                        node.try_set_range_exclusions(self, r.exclusions);
                    }
                    self.add_edge(node, mod_ctx, Edge::Context(ContextEdge::Variable));
                    Some((*input, node))
                } else {
                    None
                }
            })
            .collect::<BTreeMap<_, ContextVarNode>>();

        self.execute_call_inner(
            mod_node.underlying(self).loc,
            func_ctx,
            mod_ctx,
            mod_node,
            renamed_inputs,
        )
    }

    /// Resumes the parent function of a modifier
    fn resume_from_modifier(&mut self, ctx: ContextNode, modifier_state: ModifierState) -> ExprRet {
        // pass up the variable changes
        self.inherit_input_changes(
            modifier_state.loc,
            modifier_state.parent_ctx,
            ctx,
            &modifier_state.renamed_inputs,
        );
        self.inherit_storage_changes(modifier_state.parent_ctx, ctx);

        // actually execute the parent function
        self.execute_call_inner(
            modifier_state.loc,
            modifier_state.parent_caller_ctx,
            modifier_state.parent_ctx,
            modifier_state.parent_fn,
            modifier_state.renamed_inputs,
        )
    }

    /// Inherit the input changes from a function call
    fn inherit_input_changes(
        &mut self,
        loc: Loc,
        caller_ctx: ContextNode,
        callee_ctx: ContextNode,
        renamed_inputs: &BTreeMap<ContextVarNode, ContextVarNode>,
    ) {
        if caller_ctx != callee_ctx {
            renamed_inputs.iter().for_each(|(input_var, updated_var)| {
                let new_input =
                    self.advance_var_in_ctx(input_var.latest_version(self), loc, caller_ctx);
                let latest_updated = updated_var.latest_version(self);
                if let Some(updated_var_range) = latest_updated.range(self) {
                    new_input.set_range_min(self, updated_var_range.range_min());
                    new_input.set_range_max(self, updated_var_range.range_max());
                    new_input.set_range_exclusions(self, updated_var_range.range_exclusions());
                }
            });
        }
    }

    /// Inherit the input changes from a function call
    fn modifier_inherit_return(&mut self, mod_ctx: ContextNode, fn_ctx: ContextNode) {
        let ret = fn_ctx.underlying(self).ret.clone();
        mod_ctx.underlying_mut(self).ret = ret;
    }

    /// Inherit the storage changes from a function call
    fn inherit_storage_changes(&mut self, inheritor_ctx: ContextNode, grantor_ctx: ContextNode) {
        if inheritor_ctx != grantor_ctx {
            let vars = grantor_ctx.local_vars(self);
            vars.iter().for_each(|old_var| {
                let var = old_var.latest_version(self);
                let underlying = var.underlying(self);
                if var.is_storage(self) {
                    // println!("{} -- {} --> {}", grantor_ctx.associated_fn_name(self), underlying.name, inheritor_ctx.associated_fn_name(self));
                    if let Some(inheritor_var) = inheritor_ctx.var_by_name(self, &underlying.name) {
                        let inheritor_var = inheritor_var.latest_version(self);
                        if let Some(r) = underlying.ty.range(self) {
                            let new_inheritor_var = self.advance_var_in_ctx(
                                inheritor_var,
                                underlying.loc.expect("No loc for val change"),
                                inheritor_ctx,
                            );
                            new_inheritor_var.set_range_min(self, r.range_min());
                            new_inheritor_var.set_range_max(self, r.range_max());
                            new_inheritor_var.set_range_exclusions(self, r.range_exclusions());
                        }
                    } else {
                        let new_in_inheritor = self.add_node(Node::ContextVar(underlying.clone()));
                        self.add_edge(
                            new_in_inheritor,
                            inheritor_ctx,
                            Edge::Context(ContextEdge::Variable),
                        );
                    }
                }
            });
        }
    }

    fn modifiers(&mut self, ctx: ContextNode, func: FunctionNode) -> Vec<FunctionNode> {
        use std::fmt::Write;
        let binding = func.underlying(self).clone();
        let modifiers = binding.modifiers_as_base();
        if modifiers.is_empty() {
            vec![]
        } else {
            let res = modifiers
                .iter()
                .filter_map(|modifier| {
                    assert_eq!(modifier.name.identifiers.len(), 1);
                    // construct arg string for function selector
                    let mut mod_name = format!("{}", modifier.name.identifiers[0]);
                    if let Some(args) = &modifier.args {
                        let args_str = args
                            .iter()
                            .map(|expr| {
                                let ret = self.parse_ctx_expr(expr, ctx);
                                ret.try_as_func_input_str(self)
                            })
                            .collect::<Vec<_>>()
                            .join(", ");
                        let _ = write!(mod_name, "{args_str}");
                    }
                    let _ = write!(mod_name, "");
                    self.user_types()
                        .get(&mod_name)
                        .map(|idx| FunctionNode::from(*idx))
                })
                .collect();
            res
        }
    }

    fn set_modifiers(&mut self, func: FunctionNode, ctx: ContextNode) {
        let modifiers = self.modifiers(ctx, func);
        modifiers
            .iter()
            .enumerate()
            .for_each(|(i, modifier)| self.add_edge(*modifier, func, Edge::FuncModifier(i)));
    }
}
