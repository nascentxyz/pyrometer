use crate::{context::exprs::variable::Variable, ContextBuilder, ExprRet, NodeIdx};
use shared::range::elem_ty::Dynamic;
use shared::range::elem_ty::Elem;
use shared::range::Range;
use shared::{
    analyzer::AnalyzerLike,
    context::*,
    nodes::*,
    range::SolcRange,
    {Edge, Node},
};

use ethers_core::types::{I256, U256};
use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::{Expression, Identifier, Loc};

impl<T> MemberAccess for T where T: AnalyzerLike<Expr = Expression> + Sized {}
pub trait MemberAccess: AnalyzerLike<Expr = Expression> + Sized {
    /// Gets the array type
    fn member_access(
        &mut self,
        loc: Loc,
        member_expr: &Expression,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> ExprRet {
        if ident.name == "length" {
            return self.length(loc, member_expr, ctx);
        }
        let (_, member_idx) = self.parse_ctx_expr(member_expr, ctx).expect_single();
        match self.node(member_idx) {
            Node::ContextVar(cvar) => match &cvar.ty {
                VarType::User(TypeNode::Struct(struct_node)) => {
                    let name = format!(
                        "{}.{}",
                        ContextVarNode::from(member_idx).name(self),
                        ident.name
                    );
                    if let Some(attr_var) = ctx.var_by_name_or_recurse(self, &name) {
                        return ExprRet::Single((ctx, attr_var.latest_version(self).into()));
                    } else {
                        let field = self
                            .graph()
                            .edges_directed(struct_node.0.into(), Direction::Incoming)
                            .filter(|edge| *edge.weight() == Edge::Field)
                            .map(|edge| FieldNode::from(edge.source()))
                            .collect::<Vec<FieldNode>>()
                            .iter()
                            .filter_map(|field_node| {
                                let field = field_node.underlying(self);
                                if field.name.as_ref().expect("field wasnt named").name
                                    == ident.name
                                {
                                    Some(field)
                                } else {
                                    None
                                }
                            })
                            .take(1)
                            .next()
                            .unwrap_or_else(|| {
                                panic!(
                                    "No field with name {:?} in struct: {:?}",
                                    ident.name,
                                    struct_node.name(self)
                                )
                            });
                        if let Some(field_cvar) =
                            ContextVar::maybe_new_from_field(self, loc, cvar, field.clone())
                        {
                            let fc_node = self.add_node(Node::ContextVar(field_cvar));
                            self.add_edge(
                                fc_node,
                                ContextVarNode::from(member_idx).first_version(self),
                                Edge::Context(ContextEdge::AttrAccess),
                            );
                            self.add_edge(fc_node, ctx, Edge::Context(ContextEdge::Variable));
                            return ExprRet::Single((ctx, fc_node));
                        }
                    }
                }
                VarType::User(TypeNode::Contract(con_node)) => {
                    // we can only access functions via this pattern
                    // println!(
                    //     "functions {:?}",
                    //     con_node
                    //         .funcs(self)
                    //         .iter()
                    //         .map(|func| func.name(self))
                    //         .collect::<Vec<_>>()
                    // );
                    let funcs = con_node
                        .funcs(self)
                        .into_iter()
                        .filter(|func_node| {
                            func_node
                                .name(self)
                                .starts_with(&format!("{}(", &ident.name))
                        })
                        .collect::<Vec<_>>();
                    if funcs.is_empty() {
                        panic!(
                            "No function with name {:?} in contract: {:?}",
                            ident.name,
                            con_node.name(self)
                        )
                    } else if funcs.len() > 1 {
                        panic!("Function lookup not unique")
                    } else if let Some(func_cvar) =
                        ContextVar::maybe_from_user_ty(self, loc, funcs[0].0.into())
                    {
                        let fn_node = self.add_node(Node::ContextVar(func_cvar));
                        self.add_edge(fn_node, member_idx, Edge::Context(ContextEdge::FuncAccess));
                        return ExprRet::Single((ctx, fn_node));
                    }
                }
                VarType::BuiltIn(..) => {
                    // println!("member access {}", self.dot_str_no_tmps());
                    todo!("member access {:?}", ident)
                }
                e => todo!("member access: {:?}, {:?}", e, ident),
            },
            Node::Msg(_msg) => {
                let name = format!("msg.{}", ident.name);
                if let Some(attr_var) = ctx.var_by_name_or_recurse(self, &name) {
                    return ExprRet::Single((ctx, attr_var.latest_version(self).into()));
                } else {
                    let (node, name) = match &*ident.name {
                        "data" => {
                            if let Some(d) = self.msg().underlying(self).data.clone() {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "msg.data".to_string(),
                                )
                            } else {
                                let b = Builtin::DynamicBytes;
                                let node = self.builtin_or_add(b);
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "msg.data".to_string();
                                var.display_name = "msg.data".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "sender" => {
                            if let Some(d) = self.msg().underlying(self).sender {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "msg.sender".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Address);
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "msg.sender".to_string();
                                var.display_name = "msg.sender".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "sig" => {
                            if let Some(d) = self.msg().underlying(self).sig {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "msg.sig".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Bytes(4));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "msg.sig".to_string();
                                var.display_name = "msg.sig".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "value" => {
                            if let Some(d) = self.msg().underlying(self).value {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "msg.value".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "msg.value".to_string();
                                var.display_name = "msg.value".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "origin" => {
                            if let Some(d) = self.msg().underlying(self).origin {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "tx.origin".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Address);
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "tx.origin".to_string();
                                var.display_name = "tx.origin".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "gasprice" => {
                            if let Some(d) = self.msg().underlying(self).gasprice {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "tx.gasprice".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(64));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "tx.gasprice".to_string();
                                var.display_name = "tx.gasprice".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "gaslimit" => {
                            if let Some(d) = self.msg().underlying(self).gaslimit {
                                let c = Concrete::from(d);
                                (self.add_node(Node::Concrete(c)).into(), "".to_string())
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(64));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        e => panic!("unknown msg attribute: {e:?}"),
                    };

                    let mut var = ContextVar::new_from_concrete(loc, node, self);
                    var.name = name.clone();
                    var.display_name = name;
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    let cvar = self.add_node(Node::ContextVar(var));
                    self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                    return ExprRet::Single((ctx, cvar));
                }
            }
            Node::Block(_b) => {
                let name = format!("msg.{}", ident.name);
                if let Some(attr_var) = ctx.var_by_name_or_recurse(self, &name) {
                    return ExprRet::Single((ctx, attr_var.latest_version(self).into()));
                } else {
                    let (node, name) = match &*ident.name {
                        "hash" => {
                            if let Some(d) = self.block().underlying(self).hash {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.blockhash".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Bytes(32));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "block.blockhash".to_string();
                                var.display_name = "block.blockhash".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "basefee" => {
                            if let Some(d) = self.block().underlying(self).basefee {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.basefee".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "block.basefee".to_string();
                                var.display_name = "block.basefee".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "chainid" => {
                            if let Some(d) = self.block().underlying(self).chainid {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.chainid".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "block.chainid".to_string();
                                var.display_name = "block.chainid".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "coinbase" => {
                            if let Some(d) = self.block().underlying(self).coinbase {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.coinbase".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Address);
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "block.coinbase".to_string();
                                var.display_name = "block.coinbase".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "difficulty" => {
                            if let Some(d) = self.block().underlying(self).difficulty {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.difficulty".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "block.difficulty".to_string();
                                var.display_name = "block.difficulty".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "gaslimit" => {
                            if let Some(d) = self.block().underlying(self).gaslimit {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.gaslimit".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "block.gaslimit".to_string();
                                var.display_name = "block.gaslimit".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "number" => {
                            if let Some(d) = self.block().underlying(self).number {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.number".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "block.number".to_string();
                                var.display_name = "block.number".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "prevrandao" => {
                            if let Some(d) = self.block().underlying(self).prevrandao {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.prevrandao".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "block.prevrandao".to_string();
                                var.display_name = "block.prevrandao".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        "timestamp" => {
                            if let Some(d) = self.block().underlying(self).timestamp {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.timestamp".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self);
                                var.name = "block.timestamp".to_string();
                                var.display_name = "block.timestamp".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return ExprRet::Single((ctx, cvar));
                            }
                        }
                        e => panic!("unknown block attribute: {e:?}"),
                    };
                    let mut var = ContextVar::new_from_concrete(loc, node, self);
                    var.name = name.clone();
                    var.display_name = name;
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    let cvar = self.add_node(Node::ContextVar(var));
                    self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                    return ExprRet::Single((ctx, cvar));
                }
            }
            Node::Builtin(ref b) => match b {
                Builtin::Address | Builtin::AddressPayable | Builtin::Payable => {
                    panic!("Unknown member access on address: {:?}", ident.name)
                }
                Builtin::Bool => panic!("Unknown member access on bool: {:?}", ident.name),
                Builtin::String => panic!("Unknown member access on string: {:?}", ident.name),
                Builtin::Bytes(size) => {
                    panic!("Unknown member access on bytes{}: {:?}", size, ident.name)
                }
                Builtin::Rational => panic!("Unknown member access on rational: {:?}", ident.name),
                Builtin::DynamicBytes => {
                    panic!("Unknown member access on bytes[]: {:?}", ident.name)
                }
                Builtin::Array(_) => panic!("Unknown member access on array[]: {:?}", ident.name),
                Builtin::Mapping(_, _) => {
                    panic!("Unknown member access on mapping: {:?}", ident.name)
                }
                Builtin::Func(_, _) => panic!("Unknown member access on func: {:?}", ident.name),
                Builtin::Int(size) => {
                    let size = *size;
                    let max = if size == 256 {
                        I256::MAX
                    } else {
                        I256::from_raw(U256::from(1u8) << U256::from(size - 1)) - 1.into()
                    };
                    match &*ident.name {
                        "max" => {
                            let c = Concrete::from(max);
                            let node = self.add_node(Node::Concrete(c)).into();
                            let mut var = ContextVar::new_from_concrete(loc, node, self);
                            var.name = format!("int{size}.max");
                            var.display_name = var.name.clone();
                            var.is_tmp = true;
                            var.is_symbolic = false;
                            let cvar = self.add_node(Node::ContextVar(var));
                            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        }
                        "min" => {
                            let min = max * I256::from(-1i32);
                            let c = Concrete::from(min);
                            let node = self.add_node(Node::Concrete(c)).into();
                            let mut var = ContextVar::new_from_concrete(loc, node, self);
                            var.name = format!("int{size}.min");
                            var.display_name = var.name.clone();
                            var.is_tmp = true;
                            var.is_symbolic = false;
                            let cvar = self.add_node(Node::ContextVar(var));
                            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        }
                        e => panic!("Unknown type attribute on int{size}: {e:?}"),
                    }
                }
                Builtin::Uint(size) => {
                    let size = *size;
                    match &*ident.name {
                        "max" => {
                            let max = if size == 256 {
                                U256::MAX
                            } else {
                                U256::from(2).pow(U256::from(size)) - 1
                            };
                            let c = Concrete::from(max);
                            let node = self.add_node(Node::Concrete(c)).into();
                            let mut var = ContextVar::new_from_concrete(loc, node, self);
                            var.name = format!("int{size}.max");
                            var.display_name = var.name.clone();
                            var.is_tmp = true;
                            var.is_symbolic = false;
                            let cvar = self.add_node(Node::ContextVar(var));
                            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                            return ExprRet::Single((ctx, cvar));
                        }
                        "min" => {
                            let min = U256::zero();
                            let c = Concrete::from(min);
                            let node = self.add_node(Node::Concrete(c)).into();
                            let mut var = ContextVar::new_from_concrete(loc, node, self);
                            var.name = format!("int{size}.min");
                            var.display_name = var.name.clone();
                            var.is_tmp = true;
                            var.is_symbolic = false;
                            let cvar = self.add_node(Node::ContextVar(var));
                            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                            return ExprRet::Single((ctx, cvar));
                        }
                        e => panic!("Unknown type attribute on int{size}: {e:?}"),
                    }
                }
            },
            e => todo!("{:?}", e),
        }
        ExprRet::Single((ctx, member_idx))
    }

    fn index_access(
        &mut self,
        loc: Loc,
        parent: NodeIdx,
        dyn_builtin: BuiltInNode,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> ExprRet {
        let index_paths = self.variable(ident, ctx);
        self.match_index_access(&index_paths, loc, parent.into(), dyn_builtin, ctx)
    }

    fn match_index_access(
        &mut self,
        index_paths: &ExprRet,
        loc: Loc,
        parent: ContextVarNode,
        dyn_builtin: BuiltInNode,
        ctx: ContextNode,
    ) -> ExprRet {
        // println!("match index access");
        match index_paths {
            ExprRet::CtxKilled => ExprRet::CtxKilled,
            ExprRet::Single((_index_ctx, idx)) => {
                let parent = parent.first_version(self);
                let parent_name = parent.name(self);
                let parent_display_name = parent.display_name(self);
                let parent_ty = dyn_builtin;
                let parent_stor = parent
                    .storage(self)
                    .as_ref()
                    .expect("parent didnt have a storage location?");
                let indexed_var = ContextVar::new_from_index(
                    self,
                    loc,
                    parent_name,
                    parent_display_name,
                    parent_stor.clone(),
                    &parent_ty,
                    ContextVarNode::from(*idx),
                );

                let idx_node = self.add_node(Node::ContextVar(indexed_var));
                self.add_edge(idx_node, parent, Edge::Context(ContextEdge::IndexAccess));
                self.add_edge(idx_node, ctx, Edge::Context(ContextEdge::Variable));
                self.add_edge(*idx, idx_node, Edge::Context(ContextEdge::Index));
                ExprRet::Single((ctx, idx_node))
            }
            _ => todo!("here"),
        }
    }

    fn length(&mut self, loc: Loc, input_expr: &Expression, ctx: ContextNode) -> ExprRet {
        let elem = self.parse_ctx_expr(input_expr, ctx);
        self.match_length(loc, elem, true)
    }

    fn tmp_length(
        &mut self,
        arr: ContextVarNode,
        array_ctx: ContextNode,
        loc: Loc,
    ) -> ContextVarNode {
        let arr = arr.first_version(self);
        let name = format!("{}.length", arr.name(self));
        if let Some(attr_var) = array_ctx.var_by_name_or_recurse(self, &name) {
            attr_var.latest_version(self)
        } else {
            let len_var = ContextVar {
                loc: Some(loc),
                name: arr.name(self) + ".length",
                display_name: arr.display_name(self) + ".length",
                storage: None,
                is_tmp: false,
                tmp_of: None,
                is_symbolic: true,
                ty: VarType::BuiltIn(
                    BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
                    SolcRange::try_from_builtin(&Builtin::Uint(256)),
                ),
            };
            let len_node = self.add_node(Node::ContextVar(len_var));
            let next_arr = self.advance_var_in_ctx(arr.latest_version(self), loc, array_ctx);
            if next_arr.underlying(self).ty.is_dyn_builtin(self) {
                if let Some(r) = next_arr.range(self) {
                    let min = r.evaled_range_min(self);
                    let max = r.evaled_range_max(self);

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_node, loc));
                        next_arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)));
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_node, loc));
                        next_arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                    }
                }
            }

            self.add_edge(len_node, arr, Edge::Context(ContextEdge::AttrAccess));
            self.add_edge(len_node, array_ctx, Edge::Context(ContextEdge::Variable));
            len_node.into()
        }
    }

    fn match_length(&mut self, loc: Loc, elem_path: ExprRet, update_len_bound: bool) -> ExprRet {
        match elem_path {
            ExprRet::CtxKilled => ExprRet::CtxKilled,
            ExprRet::Single((array_ctx, arr)) => {
                let next_arr = self.advance_var_in_ctx(
                    ContextVarNode::from(arr).latest_version(self),
                    loc,
                    array_ctx,
                );
                let arr = ContextVarNode::from(arr).first_version(self);
                let name = format!("{}.length", arr.name(self));
                if let Some(len_var) = array_ctx.var_by_name_or_recurse(self, &name) {
                    let len_var = len_var.latest_version(self);
                    let new_len = self.advance_var_in_ctx(len_var, loc, array_ctx);
                    if update_len_bound && next_arr.underlying(self).ty.is_dyn_builtin(self) {
                        if let Some(r) = next_arr.range(self) {
                            let min = r.evaled_range_min(self);
                            let max = r.evaled_range_max(self);

                            if let Some(mut rd) = min.maybe_range_dyn() {
                                rd.len = Elem::Dynamic(Dynamic::new(new_len.into(), loc));
                                next_arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)));
                            }

                            if let Some(mut rd) = max.maybe_range_dyn() {
                                rd.len = Elem::Dynamic(Dynamic::new(new_len.into(), loc));
                                next_arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                            }
                        }
                    }
                    ExprRet::Single((array_ctx, new_len.into()))
                } else {
                    let len_var = ContextVar {
                        loc: Some(loc),
                        name,
                        display_name: arr.display_name(self) + ".length",
                        storage: None,
                        is_tmp: false,
                        tmp_of: None,
                        is_symbolic: true,
                        ty: VarType::BuiltIn(
                            BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
                            SolcRange::try_from_builtin(&Builtin::Uint(256)),
                        ),
                    };
                    let len_node = self.add_node(Node::ContextVar(len_var));

                    if next_arr.underlying(self).ty.is_dyn_builtin(self) {
                        if let Some(r) = next_arr.range(self) {
                            let min = r.evaled_range_min(self);
                            let max = r.evaled_range_max(self);

                            if let Some(mut rd) = min.maybe_range_dyn() {
                                rd.len = Elem::Dynamic(Dynamic::new(len_node, loc));
                                next_arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)));
                            }

                            if let Some(mut rd) = max.maybe_range_dyn() {
                                rd.len = Elem::Dynamic(Dynamic::new(len_node, loc));
                                next_arr.set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                            }
                        }
                    }

                    self.add_edge(len_node, arr, Edge::Context(ContextEdge::AttrAccess));
                    self.add_edge(len_node, array_ctx, Edge::Context(ContextEdge::Variable));
                    ExprRet::Single((array_ctx, len_node))
                }
            }
            _ => todo!("here"),
        }
    }
}
