use crate::AnalyzerLike;
use crate::{ContextBuilder, ContextNode, Edge, Node, NodeIdx};
use solang_parser::pt::Identifier;

impl<T> Variable for T where T: AnalyzerLike + Sized {}

pub trait Variable: AnalyzerLike + Sized {
    fn variable(&mut self, ident: &Identifier, ctx: ContextNode) -> Vec<NodeIdx> {
        if let Some(cvar) = ctx.latest_var_by_name(self, &ident.name) {
            vec![self.advance_var(cvar, ident.loc).0.into()]
        } else {
            if let Some(idx) = self.user_types().get(&ident.name) {
                vec![*idx]
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
                    vec![func_node]
                } else {
                    let node = self.add_node(Node::Unresolved(ident.clone()));
                    self.user_types_mut().insert(ident.name.clone(), node);
                    vec![node]
                }
            }
        }
    }
}
