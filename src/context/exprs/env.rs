use crate::context::ContextNode;
use crate::AnalyzerLike;
use crate::ExprRet;
use solang_parser::pt::Identifier;

impl<T> Env for T where T: AnalyzerLike + Sized {}
pub trait Env: AnalyzerLike + Sized {
    fn env_variable(&mut self, ident: &Identifier, ctx: ContextNode) -> Option<ExprRet> {
        match &*ident.name {
            "msg" => Some(ExprRet::Single((ctx, self.msg().into()))),
            "block" => Some(ExprRet::Single((ctx, self.block().into()))),
            "abi" => todo!("abi"),
            e => todo!("{:?}", e),
        }
    }

    // fn gasleft(&mut self, ctx: ContextNode) -> ExprRet {

    // }
}
