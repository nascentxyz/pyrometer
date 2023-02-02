use crate::context::ContextBuilder;
use crate::ExprRet;
use shared::analyzer::AnalyzerLike;
use shared::context::*;
use shared::{Edge, Node};
use solang_parser::pt::Identifier;

impl<T> Variable for T where T: AnalyzerLike + Sized {}

pub trait Variable: AnalyzerLike + Sized {
    fn variable(&mut self, ident: &Identifier, ctx: ContextNode) -> ExprRet {
        if let Some(cvar) = ctx.latest_var_by_name(self, &ident.name) {
            let var = self.advance_var_in_ctx(cvar, ident.loc, ctx);
            ExprRet::Single((ctx, var.0.into()))
        } else {
            if let Some(parent_ctx) = ctx.underlying(self).parent_ctx {
                // check if we can inherit it
                let (_pctx, cvar) = self.variable(ident, parent_ctx).expect_single();
                match self.node(cvar) {
                    Node::ContextVar(_) => {
                        let mut ctx_cvar = self.advance_var_in_ctx(cvar.into(), ident.loc, ctx);
                        ctx_cvar.update_deps(ctx, self);
                        ExprRet::Single((ctx, ctx_cvar.0.into()))
                    }
                    _ => ExprRet::Single((ctx, cvar)),
                }
            } else {
                if let Some(idx) = self.user_types().get(&ident.name) {
                    let var = ContextVar::maybe_from_user_ty(self, ident.loc, *idx)
                        .expect("Could not create context variable from user type");
                    let new_cvarnode = self.add_node(Node::ContextVar(var));
                    self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
                    ExprRet::Single((ctx, new_cvarnode))
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
