use graph::{
    elem::{Elem, RangeElem},
    nodes::{
        Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, Error, ErrorParam, ExprRet,
    },
    AnalyzerBackend, ContextEdge, Edge, SolcRange, VarType,
};
use shared::{ExprErr, GraphError, IntoExprErr, RangeArena};

use alloy_primitives::U256;
use solang_parser::pt::{Expression, Identifier, Loc};

impl<T> SolcError for T where
    T: AnalyzerBackend<ExprErr = ExprErr, ExecError = Error, ExecErrorParam = ErrorParam> + Sized
{
}

#[derive(Default, Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrType {
    Custom(ContextVarNode),
    RevertString(ContextVarNode),
    Panic(U256),
    #[default]
    Revert,
}

impl ErrType {
    pub fn assertion() -> Self {
        ErrType::Panic(U256::from(0x1))
    }

    pub fn arithmetic() -> Self {
        ErrType::Panic(U256::from(0x11))
    }

    pub fn division() -> Self {
        ErrType::Panic(U256::from(0x12))
    }

    pub fn enum_conversion() -> Self {
        ErrType::Panic(U256::from(0x21))
    }

    pub fn encode_storage() -> Self {
        ErrType::Panic(U256::from(0x22))
    }

    pub fn pop() -> Self {
        ErrType::Panic(U256::from(0x31))
    }

    pub fn index_oob() -> Self {
        ErrType::Panic(U256::from(0x32))
    }

    pub fn mem_overflow() -> Self {
        ErrType::Panic(U256::from(0x41))
    }

    pub fn zero_var() -> Self {
        ErrType::Panic(U256::from(0x51))
    }

    pub fn add_as_node(
        &self,
        analyzer: &mut impl AnalyzerBackend<
            ExprErr = ExprErr,
            ExecError = Error,
            ExecErrorParam = ErrorParam,
        >,
        ctx: ContextNode,
        loc: Loc,
    ) -> Result<ContextVarNode, ExprErr> {
        use ErrType::*;
        match self {
            Custom(inner) => Ok(*inner),
            RevertString(inner) => {
                let err = Error {
                    name: Some(Identifier {
                        loc: Loc::Builtin,
                        name: "Error".to_string(),
                    }),
                    loc: Loc::Builtin,
                };
                let params = vec![ErrorParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::String),
                    name: Some(Identifier {
                        loc: Loc::Builtin,
                        name: "reason".to_string(),
                    }),
                }];
                let err = analyzer.builtin_error_or_add(err, params);
                let var = ContextVar::maybe_from_user_ty(analyzer, loc, err).unwrap();
                let cvar = analyzer.add_node(var).into();
                analyzer.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                let tmp = inner.as_tmp(analyzer, ctx, loc).into_expr_err(loc)?;
                tmp.underlying_mut(analyzer)
                    .into_expr_err(loc)?
                    .display_name = "Error.reason".to_string();
                analyzer.add_edge(tmp, cvar, Edge::Context(ContextEdge::AttrAccess("field")));
                Ok(cvar)
            }
            Panic(i) => {
                let err = Error {
                    name: Some(Identifier {
                        loc: Loc::Builtin,
                        name: "Panic".to_string(),
                    }),
                    loc: Loc::Builtin,
                };
                let params = vec![ErrorParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Uint(8)),
                    name: Some(Identifier {
                        loc: Loc::Builtin,
                        name: "id".to_string(),
                    }),
                }];
                let err = analyzer.builtin_error_or_add(err, params);
                let var = ContextVar::maybe_from_user_ty(analyzer, loc, err).unwrap();
                let cvar = analyzer.add_node(var);
                let inner = analyzer.add_concrete_var(ctx, Concrete::from(*i), loc)?;
                inner.underlying_mut(analyzer).unwrap().display_name = "Panic.id".to_string();
                analyzer.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                analyzer.add_edge(inner, cvar, Edge::Context(ContextEdge::AttrAccess("field")));
                Ok(cvar.into())
            }
            Revert => {
                let err = Error {
                    name: Some(Identifier {
                        loc: Loc::Builtin,
                        name: "revert".to_string(),
                    }),
                    loc: Loc::Builtin,
                };
                let params = vec![];
                let err = analyzer.builtin_error_or_add(err, params);
                let var = ContextVar::maybe_from_user_ty(analyzer, loc, err).unwrap();
                let cvar = analyzer.add_node(var);
                analyzer.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                Ok(cvar.into())
            }
            _ => todo!(),
        }
    }
}

pub trait SolcError:
    AnalyzerBackend<ExprErr = ExprErr, ExecError = Error, ExecErrorParam = ErrorParam> + Sized
{
    fn add_err_node(
        &mut self,
        ctx: ContextNode,
        err: ErrType,
        loc: Loc,
    ) -> Result<ContextVarNode, ExprErr> {
        err.add_as_node(self, ctx, loc)
    }
}
