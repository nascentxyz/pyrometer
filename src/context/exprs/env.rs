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
            e => {
                println!("{:?}", e);
                None
            }
        }
    }

    // fn gasleft(&mut self, ctx: ContextNode) -> ExprRet {

    // }
}
