use crate::{ContextBuilder, ExprRet};
use petgraph::{visit::EdgeRef, Direction};
use shared::analyzer::AnalyzerLike;
use shared::context::*;
use shared::nodes::*;
use shared::{Edge, Node};

use solang_parser::pt::{Expression, Identifier, Loc};

impl<T> MemberAccess for T where T: AnalyzerLike + Sized {}
pub trait MemberAccess: AnalyzerLike + Sized {
    /// Gets the array type
    fn member_access(
        &mut self,
        loc: Loc,
        member_expr: &Expression,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> ExprRet {
        let (_, member_idx) = self.parse_ctx_expr(member_expr, ctx).expect_single();
        match self.node(member_idx) {
            Node::ContextVar(cvar) => match &cvar.ty {
                VarType::User(TypeNode::Struct(struct_node)) => {
                    let field = self
                        .graph()
                        .edges_directed(struct_node.0.into(), Direction::Incoming)
                        .filter(|edge| *edge.weight() == Edge::Field)
                        .map(|edge| FieldNode::from(edge.source()))
                        .collect::<Vec<FieldNode>>()
                        .iter()
                        .filter_map(|field_node| {
                            let field = field_node.underlying(self);
                            if field.name.as_ref().expect("field wasnt named").name == ident.name {
                                Some(field)
                            } else {
                                None
                            }
                        })
                        .take(1)
                        .next()
                        .expect(&format!(
                            "No field with name {:?} in struct: {:?}",
                            ident.name,
                            struct_node.name(self)
                        ));
                    if let Some(field_cvar) =
                        ContextVar::maybe_new_from_field(self, loc, cvar, field.clone())
                    {
                        let fc_node = self.add_node(Node::ContextVar(field_cvar));
                        self.add_edge(fc_node, member_idx, Edge::Context(ContextEdge::AttrAccess));
                        return ExprRet::Single((ctx, fc_node));
                    }
                }
                VarType::User(TypeNode::Contract(con_node)) => {
                    // we can only access functions via this pattern
                    let func = self
                        .graph()
                        .edges_directed(con_node.0.into(), Direction::Incoming)
                        .filter(|edge| *edge.weight() == Edge::Func)
                        .map(|edge| FunctionNode::from(edge.source()))
                        .collect::<Vec<FunctionNode>>()
                        .into_iter()
                        .filter_map(|func_node| {
                            let func = func_node.underlying(self);
                            if func.name.as_ref().expect("func wasnt named").name == ident.name {
                                Some(func_node)
                            } else {
                                None
                            }
                        })
                        .take(1)
                        .next()
                        .expect(&format!(
                            "No function with name {:?} in contract: {:?}",
                            ident.name,
                            con_node.name(self)
                        ));

                    if let Some(func_cvar) =
                        ContextVar::maybe_from_user_ty(self, loc, func.0.into())
                    {
                        let fn_node = self.add_node(Node::ContextVar(func_cvar));
                        self.add_edge(fn_node, member_idx, Edge::Context(ContextEdge::FuncAccess));
                        return ExprRet::Single((ctx, fn_node));
                    }
                }
                e => todo!("member access: {:?}", e),
            },
            e => todo!("{:?}", e),
        }
        ExprRet::Single((ctx, member_idx))
    }
}
