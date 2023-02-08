use crate::AnalyzerLike;
use solang_parser::pt::Identifier;
use crate::context::ContextNode;
use crate::ExprRet;

impl<T> Env for T where T: AnalyzerLike + Sized {}
pub trait Env: AnalyzerLike + Sized {
	fn env_variable(&mut self, ident: &Identifier, ctx: ContextNode) -> Option<ExprRet> {
		match &*ident.name {
			"msg" => Some(ExprRet::Single((ctx, self.msg().into()))),
			"block" => Some(ExprRet::Single((ctx, self.block().into()))),
			"abi" => todo!("abi"),
			e => todo!("{:?}", e)
		}
	}

	// fn gasleft(&mut self, ctx: ContextNode) -> ExprRet {
		
	// }
}