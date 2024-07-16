use crate::func_call::helper::CallerHelper;

use graph::{
    elem::Elem,
    nodes::{Builtin, Concrete, ConcreteNode, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, Node,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use ethers_core::types::H256;
use solang_parser::pt::{Expression, Loc};

impl<T> SolidityCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerHelper
{
}

/// Trait for calling solidity's intrinsic functions, like `keccak256`
pub trait SolidityCaller:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerHelper
{
    /// Perform a solidity intrinsic function call, like `keccak256`
    fn solidity_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        func_name: &str,
        inputs: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "keccak256" => {
                let cvar = if let Ok(var) = inputs.expect_single() {
                    ContextVarNode::from(var)
                } else {
                    return Err(ExprErr::NoRhs(loc, "No input into keccak256".to_string()));
                };

                if cvar.is_const(self, arena).into_expr_err(loc)? {
                    let bytes = cvar
                        .evaled_range_min(self, arena)
                        .unwrap()
                        .unwrap()
                        .as_bytes(self, true, arena)
                        .unwrap();
                    let mut out = [0; 32];
                    keccak_hash::keccak_256(&bytes, &mut out);

                    let hash_node = ConcreteNode::from(self.add_node(Concrete::from(H256(out))));
                    let var = ContextVar::new_from_concrete(loc, ctx, hash_node, self)
                        .into_expr_err(loc)?;
                    let cvar = self.add_node(var);
                    ctx.push_expr(ExprRet::Single(cvar), self)
                        .into_expr_err(loc)?;
                } else {
                    let var = ContextVar::new_from_builtin(
                        loc,
                        self.builtin_or_add(Builtin::Bytes(32)).into(),
                        self,
                    )
                    .into_expr_err(loc)?;
                    let cvar = self.add_node(var);
                    ctx.push_expr(ExprRet::Single(cvar), self)
                        .into_expr_err(loc)?;
                }

                Ok(())
            }
            "addmod" => {
                // TODO: actually calcuate this if possible
                let var = ContextVar::new_from_builtin(
                    loc,
                    self.builtin_or_add(Builtin::Uint(256)).into(),
                    self,
                )
                .into_expr_err(loc)?;
                let cvar = self.add_node(var);
                ctx.push_expr(ExprRet::Single(cvar), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "mulmod" => {
                // TODO: actually calcuate this if possible
                let var = ContextVar::new_from_builtin(
                    loc,
                    self.builtin_or_add(Builtin::Uint(256)).into(),
                    self,
                )
                .into_expr_err(loc)?;
                let cvar = self.add_node(var);
                ctx.push_expr(ExprRet::Single(cvar), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "require" | "assert" => {
                // self.handle_require(arena, input_exprs.unnamed_args().unwrap(), ctx)
                todo!()
            }
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find builtin solidity function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }
}
