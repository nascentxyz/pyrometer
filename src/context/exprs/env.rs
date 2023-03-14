use crate::context::func::FuncCaller;
use crate::{context::ContextNode, AnalyzerLike, ExprRet};
use solang_parser::pt::Expression;

use solang_parser::pt::Identifier;

impl<T> Env for T where T: AnalyzerLike<Expr = Expression> + Sized {}
pub trait Env: AnalyzerLike<Expr = Expression> + Sized {
    fn env_variable(&mut self, ident: &Identifier, ctx: ContextNode) -> Option<ExprRet> {
        match &*ident.name {
            "msg" => Some(ExprRet::Single((ctx, self.msg().into()))),
            "block" => Some(ExprRet::Single((ctx, self.block().into()))),
            "abi" => todo!("abi"),
            "_" => {
                #[allow(clippy::manual_map)]
                if let Some(mod_state) = &ctx.underlying(self).modifier_state.clone() {
                    // println!("going back to function execution from modifier: {}", mod_state.num);
                    let res = self.resume_from_modifier(ctx, mod_state.clone());
                    // println!("back in modifier: {}", mod_state.num);

                    // TODO: inherit the input changes as well
                    // println!("inheriting back from parent into modifier");
                    self.inherit_storage_changes(ctx, mod_state.parent_ctx);

                    Some(res)
                } else {
                    None
                }
            }
            _e => None,
        }
    }

    // fn gasleft(&mut self, ctx: ContextNode) -> ExprRet {

    // }
}
