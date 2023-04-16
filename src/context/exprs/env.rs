use crate::context::exprs::IntoExprErr;
use crate::context::func_call::FuncCaller;
use crate::context::ExprErr;
use crate::{context::ContextNode, AnalyzerLike, ExprRet};
use solang_parser::pt::Expression;

use solang_parser::pt::Identifier;

impl<T> Env for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {}
pub trait Env: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn env_variable(
        &mut self,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> Result<Option<ExprRet>, ExprErr> {
        match &*ident.name {
            "msg" => Ok(Some(ExprRet::Single((ctx, self.msg().into())))),
            "block" => Ok(Some(ExprRet::Single((ctx, self.block().into())))),
            "abi" => Ok(Some(ExprRet::Multi(vec![]))),
            "_" => {
                #[allow(clippy::manual_map)]
                if let Some(mod_state) = &ctx
                    .underlying(self)
                    .into_expr_err(ident.loc)?
                    .modifier_state
                    .clone()
                {
                    // println!("going back to function execution from modifier: {}", mod_state.num);
                    let res = self.resume_from_modifier(ctx, mod_state.clone())?;
                    // println!("back in modifier: {}", mod_state.num);

                    // TODO: inherit the input changes as well
                    // println!("inheriting back from parent into modifier");
                    self.inherit_storage_changes(ctx, mod_state.parent_ctx);

                    self.modifier_inherit_return(ctx, mod_state.parent_ctx);
                    Ok(Some(res))
                } else {
                    Ok(None)
                }
            }
            _e => Ok(None),
        }
    }
}
