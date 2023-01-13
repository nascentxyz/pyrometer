use crate::AnalyzerLike;
use crate::ExprRet;
use crate::{ContextBuilder, ContextNode, Edge, Node};
use solang_parser::pt::Identifier;

impl<T> Variable for T where T: AnalyzerLike + Sized {}

pub trait Variable: AnalyzerLike + Sized {
    fn variable(&mut self, ident: &Identifier, ctx: ContextNode) -> ExprRet {
        if let Some(cvar) = ctx.latest_var_by_name(self, &ident.name) {
            ExprRet::Single((ctx, self.advance_var_in_ctx(cvar, ident.loc, ctx).0.into()))
        } else {
            if let Some(parent_ctx) = ctx.underlying(self).parent_ctx {
                // check if we can inherit it
                let (_pctx, cvar) = self.variable(ident, parent_ctx).expect_single();
                // let cvar_node = ContextVarNode::from(cvar);
                // let cvar_node = if fork {
                //     let copy_var = cvar_node.underlying(self).clone();
                //     ContextVarNode::from(self.add_node(Node::ContextVar(copy_var)))
                // } else {
                //     cvar_node
                // };

                // println!("var ctx: {}", ctx.underlying(self).path);

                // self.add_edge(
                //     cvar_node,
                //     ctx,
                //     Edge::Context(ContextEdge::Variable),
                // );
                ExprRet::Single((ctx, cvar))
            } else {
                if let Some(idx) = self.user_types().get(&ident.name) {
                    ExprRet::Single((ctx, *idx))
                } else {
                    if let Some(func) = self.builtin_fns().get(&ident.name) {
                        let (inputs, outputs) = self
                            .builtin_fn_inputs()
                            .get(&ident.name)
                            .expect("builtin func but no inputs")
                            .clone();
                        let func_node = self.add_node(Node::Function(func.clone()));
                        inputs.into_iter().for_each(|input| {
                            let input_node = self.add_node(input);
                            self.add_edge(input_node, func_node, Edge::FunctionParam);
                        });
                        outputs.into_iter().for_each(|output| {
                            let output_node = self.add_node(output);
                            self.add_edge(output_node, func_node, Edge::FunctionReturn);
                        });
                        ExprRet::Single((ctx, func_node))
                    } else {
                        let node = self.add_node(Node::Unresolved(ident.clone()));
                        self.user_types_mut().insert(ident.name.clone(), node);
                        ExprRet::Single((ctx, node))
                    }
                }
            }
        }
    }
}
