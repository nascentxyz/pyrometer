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
    ) -> Option<()> {
        match test_command {
            TestCommand::Variable(var_name, VariableCommand::RangeAssert { min, max }) => {
                if let Some(var) = ctx.var_by_name_or_recurse(self, &var_name).ok()? {
                    return self.check_range(arena, var_name, var, min, max, loc);
                } else {
                    let split = var_name.split('.').collect::<Vec<_>>();
                    let base_name = split.first()?;
                    let Ok(Some(base_var)) = ctx.var_by_name_or_recurse(self, base_name) else {
                        self.add_expr_err(ExprErr::TestError(
                            loc,
                            format!("No variable \"{var_name}\" found in context"),
                        ));
                        return None;
                    };

                    let mut curr_var = base_var;
                    for member in split.iter().skip(1) {
                        let Ok(Some(field)) = curr_var.find_field(self, member) else {
                            self.add_expr_err(ExprErr::TestError(
                                loc,
                                format!("No variable \"{var_name}\" found in context"),
                            ));
                            return None;
                        };
                        curr_var = field;
                    }
                    return self.check_range(arena, var_name, curr_var, min, max, loc);
                }
            }
            TestCommand::Constraint(c) => {
                let deps = ctx.ctx_deps(self).ok()?;
                if !deps.iter().any(|dep| dep.display_name(self).unwrap() == c) {
                    self.add_expr_err(ExprErr::TestError(
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
                        self.add_expr_err(ExprErr::TestError(
                            loc,
                            "Expected a single path, but another was reached".to_string(),
                        ));
                    }
                }
            }
            TestCommand::Coverage(CoverageCommand::Unreachable) => {
                self.add_expr_err(ExprErr::TestError(
                    loc,
                    "Hit an unreachable path".to_string(),
                ));
            }
        }

        None
    }

    fn check_range(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        var_name: String,
        var: ContextVarNode,
        min: Concrete,
        max: Concrete,
        loc: Loc,
    ) -> Option<()> {
        let min = Elem::from(min);
        let max = Elem::from(max);
        let latest = var.latest_version(self);
        let eval_min =
            self.add_if_err(latest.evaled_range_min(self, arena).into_expr_err(loc))??;
        let eval_max =
            self.add_if_err(latest.evaled_range_max(self, arena).into_expr_err(loc))??;
        if !eval_min.range_eq(&min, arena) {
            self.add_expr_err(ExprErr::TestError(
                loc,
                format!(
                    "Variable \"{var_name}\"'s minimum was {}, expected {}",
                    eval_min, min
                ),
            ));
        }
        if !eval_max.range_eq(&max, arena) {
            self.add_expr_err(ExprErr::TestError(
                loc,
                format!(
                    "Variable \"{var_name}\"'s maximum was {}, expected {}",
                    eval_max, max
                ),
            ));
        }
        Some(())
    }
}
