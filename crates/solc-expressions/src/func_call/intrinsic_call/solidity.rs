use crate::func_caller::NamedOrUnnamedArgs;
use crate::{
    func_call::helper::CallerHelper, require::Require, ContextBuilder, ExprErr, ExpressionParser,
    IntoExprErr,
};

use graph::{
    nodes::{Builtin, ContextNode, ContextVar, ExprRet, Concrete, ConcreteNode, ContextVarNode},
    AnalyzerBackend, Node,
};

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
        func_name: String,
        input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "keccak256" => {
                self.parse_ctx_expr(&input_exprs.unnamed_args().unwrap()[0], ctx)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(input) =
                        ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "No input into keccak256"
                                .to_string(),
                        ));
                    };

                    let cvar = if let Ok(var) = input.expect_single() {
                        ContextVarNode::from(var)
                    } else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "No input into keccak256"
                                .to_string(),
                        ));
                    };


                    if cvar.is_const(analyzer).into_expr_err(loc)? {
                        let bytes = cvar.evaled_range_min(analyzer)
                            .unwrap()
                            .unwrap()
                            .as_bytes(analyzer, true)
                            .unwrap();
                        let mut out = [0; 32];
                        keccak_hash::keccak_256(&bytes, &mut out);

                        let hash = Node::Concrete(Concrete::from(H256(out)));
                        let hash_node = ConcreteNode::from(analyzer.add_node(hash));
                        let var = ContextVar::new_from_concrete(
                            loc,
                            ctx,
                            hash_node,
                            analyzer,
                        )
                        .into_expr_err(loc)?;
                        let cvar = analyzer.add_node(Node::ContextVar(var));
                        ctx.push_expr(ExprRet::Single(cvar), analyzer)
                            .into_expr_err(loc)?;
                    } else {
                        println!("not const: [{}]", cvar.range_string(analyzer).unwrap().unwrap());
                        let var = ContextVar::new_from_builtin(
                            loc,
                            analyzer.builtin_or_add(Builtin::Bytes(32)).into(),
                            analyzer,
                        )
                        .into_expr_err(loc)?;
                        let cvar = analyzer.add_node(Node::ContextVar(var));
                        ctx.push_expr(ExprRet::Single(cvar), analyzer)
                            .into_expr_err(loc)?;
                    }
                    
                    Ok(())
                })
            }
            "addmod" => {
                // TODO: actually calcuate this if possible
                input_exprs.parse(self, ctx, loc)?;

                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?;
                    let var = ContextVar::new_from_builtin(
                        loc,
                        analyzer.builtin_or_add(Builtin::Uint(256)).into(),
                        analyzer,
                    )
                    .into_expr_err(loc)?;
                    let cvar = analyzer.add_node(Node::ContextVar(var));
                    ctx.push_expr(ExprRet::Single(cvar), analyzer)
                        .into_expr_err(loc)?;
                    Ok(())
                })
            }
            "mulmod" => {
                // TODO: actually calcuate this if possible
                input_exprs.parse(self, ctx, loc)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?;
                    let var = ContextVar::new_from_builtin(
                        loc,
                        analyzer.builtin_or_add(Builtin::Uint(256)).into(),
                        analyzer,
                    )
                    .into_expr_err(loc)?;
                    let cvar = analyzer.add_node(Node::ContextVar(var));
                    ctx.push_expr(ExprRet::Single(cvar), analyzer)
                        .into_expr_err(loc)?;
                    Ok(())
                })
            }
            "require" | "assert" => self.apply_to_edges(ctx, loc, &|analyzer, ctx, _loc| {
                analyzer.handle_require(input_exprs.unnamed_args().unwrap(), ctx)
            }),
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
