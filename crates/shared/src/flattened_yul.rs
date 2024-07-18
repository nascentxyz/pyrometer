use crate::{string_to_static, ExprErr};

use solang_parser::pt::{
    Identifier, Loc, YulExpression, YulFunctionCall, YulStatement, YulSwitchOptions,
};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum FlatYulExpr {
    YulStartBlock,
    YulVariable(Loc, &'static str),
    YulFuncCall(Loc, &'static str, usize),
    YulSuffixAccess(Loc, &'static str),
    YulAssign(Loc, usize),
    YulVarDecl(Loc, usize, bool),
    YulFuncDef(Loc, &'static str, usize),
    YulEndBlock,
}

impl std::fmt::Display for FlatYulExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use FlatYulExpr::*;
        match self {
            YulFuncCall(_c, s, n) => write!(f, "{s}({})", "_,".repeat(*n)),
            YulVariable(_, s) | YulSuffixAccess(_, s) => write!(f, "{s}"),
            _ => write!(f, ""),
        }
    }
}

impl TryFrom<&YulExpression> for FlatYulExpr {
    type Error = ();
    fn try_from(expr: &YulExpression) -> Result<Self, ()> {
        use YulExpression::*;
        let res = match expr {
            Variable(ident) => {
                FlatYulExpr::YulVariable(ident.loc, string_to_static(ident.name.clone()))
            }
            FunctionCall(yul_func_call) => FlatYulExpr::YulFuncCall(
                yul_func_call.loc,
                string_to_static(yul_func_call.id.name.clone()),
                yul_func_call.arguments.len(),
            ),
            SuffixAccess(loc, _, ident) => {
                FlatYulExpr::YulSuffixAccess(*loc, string_to_static(ident.name.clone()))
            }
            _ => return Err(()),
        };
        Ok(res)
    }
}

#[derive(Clone, Debug)]
/// A yul-based if-else chain, which represents a switch statement
pub struct IfElseChain {
    pub if_expr: YulExpression,
    pub true_stmt: YulStatement,
    pub next: Option<ElseOrDefault>,
}

#[derive(Clone, Debug)]
/// Wrapper over a switch statement that denotes either another else statement or the default case
pub enum ElseOrDefault {
    Else(Box<IfElseChain>),
    Default(YulStatement),
}

impl From<IfElseChain> for ElseOrDefault {
    fn from(iec: IfElseChain) -> Self {
        Self::Else(Box::new(iec))
    }
}

impl IfElseChain {
    pub fn from_child(ed: ElseOrDefault) -> Option<Self> {
        match ed {
            ElseOrDefault::Else(iec) => Some(*iec),
            _ => None,
        }
    }
}

impl From<YulSwitchOptions> for ElseOrDefault {
    fn from(default: YulSwitchOptions) -> Self {
        match default {
            YulSwitchOptions::Default(_loc, block) => {
                ElseOrDefault::Default(YulStatement::Block(block))
            }
            _ => unreachable!("case as default"),
        }
    }
}

pub type SwitchInfo = (
    YulExpression,
    Vec<YulSwitchOptions>,
    Option<YulSwitchOptions>,
);

impl IfElseChain {
    pub fn from(loc: Loc, (condition, cases, default): SwitchInfo) -> Result<Self, ExprErr> {
        let mut child: Option<ElseOrDefault> = default.map(|default| default.into());

        cases.into_iter().rev().for_each(|case| {
            let mut chain_part: IfElseChain = From::from((condition.clone(), case));
            if let Some(c) = child.take() {
                chain_part.next = c.into();
            }
            child = Some(chain_part.into());
        });
        let Some(child) = child else {
            return Err(ExprErr::NoRhs(
                loc,
                "No cases or default found for switch statement".to_string(),
            ));
        };

        let Some(iec) = IfElseChain::from_child(child) else {
            return Err(ExprErr::NoRhs(
                loc,
                "No cases or default found for switch statement".to_string(),
            ));
        };
        Ok(iec)
    }
}

impl From<(YulExpression, YulSwitchOptions)> for IfElseChain {
    fn from((condition, case): (YulExpression, YulSwitchOptions)) -> Self {
        match case {
            YulSwitchOptions::Case(loc, expr, stmt) => {
                let if_expr = YulExpression::FunctionCall(Box::new(YulFunctionCall {
                    loc,
                    id: Identifier {
                        loc,
                        name: "eq".to_string(),
                    },
                    arguments: vec![condition, expr],
                }));
                IfElseChain {
                    if_expr,
                    true_stmt: YulStatement::Block(stmt),
                    next: None,
                }
            }
            YulSwitchOptions::Default(_loc, _block) => {
                unreachable!("We shouldn't have a `default` case in cases - only in the `default` input parameter")
            }
        }
    }
}
