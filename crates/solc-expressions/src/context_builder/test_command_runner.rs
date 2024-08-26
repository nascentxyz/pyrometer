use graph::{
    elem::{Elem, RangeElem},
    nodes::{Concrete, ContextNode, ContextVarNode},
    AnalyzerBackend, CoverageCommand, TestCommand, VariableCommand,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Loc};

impl<T> TestCommandRunner for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
}

/// Solidity statement parser
pub trait TestCommandRunner: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn run_test_command(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        test_command: TestCommand,
        loc: Loc,
    ) -> Result<Option<()>, ExprErr> {
        match test_command {
            TestCommand::Variable(var_name, VariableCommand::RangeAssert { min, max }) => {
                if let Ok(Some(var)) = ctx.var_by_name_or_recurse(self, &var_name) {
                    return self.check_range(arena, var_name, var, min, max, loc);
                } else {
                    let split = var_name.split('.').collect::<Vec<_>>();
                    let Some(base_name) = split.first() else {
                        return Ok(None);
                    };
                    let Ok(Some(base_var)) = ctx.var_by_name_or_recurse(self, base_name) else {
                        return Err(ExprErr::TestError(
                            loc,
                            format!("No variable \"{var_name}\" found in context"),
                        ));
                    };

                    let mut curr_var = base_var;
                    for member in split.iter().skip(1) {
                        let Ok(Some(field)) = curr_var.find_field(self, member) else {
                            return Err(ExprErr::TestError(
                                loc,
                                format!("No variable \"{var_name}\" found in context"),
                            ));
                        };
                        curr_var = field;
                    }
                    return self.check_range(arena, var_name, curr_var, min, max, loc);
                }
            }
            TestCommand::Constraint(c) => {
                let Ok(deps) = ctx.ctx_deps(self) else {
                    return Ok(None);
                };
                if !deps.iter().any(|dep| dep.display_name(self).unwrap() == c) {
                    return Err(ExprErr::TestError(
                        loc,
                        format!(
                            "No dependency \"{c}\" found for context, constraints: {:#?}",
                            deps.iter()
                                .map(|i| i.display_name(self).unwrap())
                                .collect::<Vec<_>>()
                        ),
                    ));
                }
            }
            TestCommand::Coverage(CoverageCommand::OnlyPath) => {
                if let Some(parent) = ctx.underlying(self).unwrap().parent_ctx() {
                    if parent.underlying(self).unwrap().child.is_some() {
                        return Err(ExprErr::TestError(
                            loc,
                            "Expected a single path, but another was reached".to_string(),
                        ));
                    }
                }
            }
            TestCommand::Coverage(CoverageCommand::Unreachable) => {
                return Err(ExprErr::TestError(
                    loc,
                    "Hit an unreachable path".to_string(),
                ))
            }
        }

        Ok(None)
    }

    fn check_range(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        var_name: String,
        var: ContextVarNode,
        min: Concrete,
        max: Concrete,
        loc: Loc,
    ) -> Result<Option<()>, ExprErr> {
        let min = Elem::from(min);
        let max = Elem::from(max);
        let latest = var.latest_version(self);
        let Some(eval_min) = latest.evaled_range_min(self, arena).into_expr_err(loc)? else {
            return Ok(None);
        };
        let Some(eval_max) = latest.evaled_range_max(self, arena).into_expr_err(loc)? else {
            return Ok(None);
        };
        if !eval_min.range_eq(&min, arena) {
            return Err(ExprErr::TestError(
                loc,
                format!(
                    "Variable \"{var_name}\"'s minimum was {}, expected {}",
                    eval_min, min
                ),
            ));
        }
        if !eval_max.range_eq(&max, arena) {
            return Err(ExprErr::TestError(
                loc,
                format!(
                    "Variable \"{var_name}\"'s maximum was {}, expected {}",
                    eval_max, max
                ),
            ));
        }
        Ok(Some(()))
    }
}
