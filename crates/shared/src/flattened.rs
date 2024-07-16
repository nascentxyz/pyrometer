use crate::{AnalyzerLike, ExprErr, IntoExprErr, RangeArena, StorageLocation};
use solang_parser::pt::Identifier;
use solang_parser::pt::{Expression, Loc, Statement, Type};

#[derive(Debug, Clone, Copy)]
pub enum ExprFlag {
    FunctionName(usize),
    New,
    Negate,
}

#[derive(Debug, Clone, Copy)]
pub enum FlatExpr {
    VarDef(Loc, Option<&'static str>, Option<StorageLocation>, bool),
    If {
        loc: Loc,
        true_cond: usize,
        false_cond: usize,
        true_body: usize,
        false_body: usize,
    },

    FunctionCallName(usize),

    Continue(Loc),
    Break(Loc),
    Return(Loc, bool),

    PostIncrement(Loc),
    PostDecrement(Loc),
    New(Loc),
    ArrayTy(Loc),
    ArrayIndexAccess(Loc),
    ArraySlice(Loc),
    Parenthesis(Loc),
    MemberAccess(Loc),
    FunctionCall(Loc, usize),
    FunctionCallBlock(Loc),
    NamedFunctionCall(Loc),
    Not(Loc),
    Negate(Loc),
    Delete(Loc),
    PreIncrement(Loc),
    PreDecrement(Loc),
    UnaryPlus(Loc),
    Power(Loc),
    Multiply(Loc),
    Divide(Loc),
    Modulo(Loc),
    Add(Loc),
    Subtract(Loc),
    ShiftLeft(Loc),
    ShiftRight(Loc),
    BitwiseAnd(Loc),
    BitwiseXor(Loc),
    BitwiseOr(Loc),
    BitwiseNot(Loc),
    Less(Loc),
    More(Loc),
    LessEqual(Loc),
    MoreEqual(Loc),
    Equal(Loc),
    NotEqual(Loc),
    And(Loc),
    Or(Loc),
    ConditionalOperator(Loc),
    Assign(Loc),
    AssignOr(Loc),
    AssignAnd(Loc),
    AssignXor(Loc),
    AssignShiftLeft(Loc),
    AssignShiftRight(Loc),
    AssignAdd(Loc),
    AssignSubtract(Loc),
    AssignMultiply(Loc),
    AssignDivide(Loc),
    AssignModulo(Loc),
    Type(Loc, &'static Type),
    This(Loc),
    List(Loc, usize),

    Parameter(Loc, Option<StorageLocation>, Option<&'static str>),
    Null(Loc),

    BoolLiteral(Loc, bool),
    NumberLiteral(Loc, &'static str, &'static str, Option<&'static str>),
    RationalNumberLiteral(
        Loc,
        &'static str,
        &'static str,
        &'static str,
        Option<&'static str>,
    ),
    HexNumberLiteral(Loc, &'static str, Option<&'static str>),
    StringLiteral(Loc, &'static str),
    HexLiteral(Loc, &'static str),
    AddressLiteral(Loc, &'static str),
    Variable(Loc, &'static str),
    ArrayLiteral(Loc),
}

pub fn string_to_static(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}

impl From<&Expression> for FlatExpr {
    fn from(expr: &Expression) -> Self {
        use Expression::*;
        match expr {
            PostIncrement(loc, ..) => FlatExpr::PostIncrement(*loc),
            PostDecrement(loc, ..) => FlatExpr::PostDecrement(*loc),
            New(loc, ..) => FlatExpr::New(*loc),
            ArraySubscript(loc, _, None) => FlatExpr::ArrayTy(*loc),
            ArraySubscript(loc, _, Some(_)) => FlatExpr::ArrayIndexAccess(*loc),
            ArraySlice(loc, ..) => FlatExpr::ArraySlice(*loc),
            Parenthesis(loc, ..) => FlatExpr::Parenthesis(*loc),
            MemberAccess(loc, ..) => FlatExpr::MemberAccess(*loc),
            FunctionCall(loc, _, input_exprs) => FlatExpr::FunctionCall(*loc, input_exprs.len()),
            FunctionCallBlock(loc, _, _) => FlatExpr::FunctionCallBlock(*loc),
            NamedFunctionCall(loc, ..) => FlatExpr::NamedFunctionCall(*loc),
            Not(loc, ..) => FlatExpr::Not(*loc),
            Delete(loc, ..) => FlatExpr::Delete(*loc),
            PreIncrement(loc, ..) => FlatExpr::PreIncrement(*loc),
            PreDecrement(loc, ..) => FlatExpr::PreDecrement(*loc),
            UnaryPlus(loc, ..) => FlatExpr::UnaryPlus(*loc),
            Power(loc, ..) => FlatExpr::Power(*loc),
            Multiply(loc, ..) => FlatExpr::Multiply(*loc),
            Divide(loc, ..) => FlatExpr::Divide(*loc),
            Modulo(loc, ..) => FlatExpr::Modulo(*loc),
            Add(loc, ..) => FlatExpr::Add(*loc),
            Subtract(loc, ..) => FlatExpr::Subtract(*loc),
            ShiftLeft(loc, ..) => FlatExpr::ShiftLeft(*loc),
            ShiftRight(loc, ..) => FlatExpr::ShiftRight(*loc),
            BitwiseAnd(loc, ..) => FlatExpr::BitwiseAnd(*loc),
            BitwiseXor(loc, ..) => FlatExpr::BitwiseXor(*loc),
            BitwiseOr(loc, ..) => FlatExpr::BitwiseOr(*loc),
            BitwiseNot(loc, ..) => FlatExpr::BitwiseNot(*loc),
            Less(loc, ..) => FlatExpr::Less(*loc),
            More(loc, ..) => FlatExpr::More(*loc),
            LessEqual(loc, ..) => FlatExpr::LessEqual(*loc),
            MoreEqual(loc, ..) => FlatExpr::MoreEqual(*loc),
            Equal(loc, ..) => FlatExpr::Equal(*loc),
            NotEqual(loc, ..) => FlatExpr::NotEqual(*loc),
            And(loc, ..) => FlatExpr::And(*loc),
            Or(loc, ..) => FlatExpr::Or(*loc),
            ConditionalOperator(loc, ..) => FlatExpr::ConditionalOperator(*loc),
            Assign(loc, ..) => FlatExpr::Assign(*loc),
            AssignOr(loc, ..) => FlatExpr::AssignOr(*loc),
            AssignAnd(loc, ..) => FlatExpr::AssignAnd(*loc),
            AssignXor(loc, ..) => FlatExpr::AssignXor(*loc),
            AssignShiftLeft(loc, ..) => FlatExpr::AssignShiftLeft(*loc),
            AssignShiftRight(loc, ..) => FlatExpr::AssignShiftRight(*loc),
            AssignAdd(loc, ..) => FlatExpr::AssignAdd(*loc),
            AssignSubtract(loc, ..) => FlatExpr::AssignSubtract(*loc),
            AssignMultiply(loc, ..) => FlatExpr::AssignMultiply(*loc),
            AssignDivide(loc, ..) => FlatExpr::AssignDivide(*loc),
            AssignModulo(loc, ..) => FlatExpr::AssignModulo(*loc),
            Type(loc, ty) => {
                let ty_box = Box::new(ty.clone());
                let leaked_ty = Box::leak(ty_box);
                FlatExpr::Type(*loc, leaked_ty)
            }
            Negate(loc, ..) => FlatExpr::Negate(*loc),
            NumberLiteral(loc, int, exp, unit) => {
                if let Some(unit) = unit {
                    FlatExpr::NumberLiteral(
                        *loc,
                        Box::leak(int.clone().into_boxed_str()),
                        Box::leak(exp.clone().into_boxed_str()),
                        Some(Box::leak(unit.name.clone().into_boxed_str())),
                    )
                } else {
                    FlatExpr::NumberLiteral(
                        *loc,
                        Box::leak(int.clone().into_boxed_str()),
                        Box::leak(exp.clone().into_boxed_str()),
                        None,
                    )
                }
            }
            AddressLiteral(loc, addr) => {
                FlatExpr::AddressLiteral(*loc, Box::leak(addr.clone().into_boxed_str()))
            }
            StringLiteral(lits) => {
                let mut final_str = "".to_string();
                let mut loc = lits[0].loc;
                lits.iter().for_each(|s| {
                    loc.use_end_from(&s.loc);
                    final_str.push_str(&s.string);
                });
                FlatExpr::StringLiteral(loc, string_to_static(final_str))
            }
            BoolLiteral(loc, b) => FlatExpr::BoolLiteral(*loc, *b),
            HexNumberLiteral(loc, b, unit) => {
                if let Some(unit) = unit {
                    FlatExpr::HexNumberLiteral(
                        *loc,
                        Box::leak(b.clone().into_boxed_str()),
                        Some(Box::leak(unit.name.clone().into_boxed_str())),
                    )
                } else {
                    FlatExpr::HexNumberLiteral(*loc, Box::leak(b.clone().into_boxed_str()), None)
                }
            }
            HexLiteral(hexes) => {
                let mut final_str = "".to_string();
                let mut loc = hexes[0].loc;
                hexes.iter().for_each(|s| {
                    loc.use_end_from(&s.loc);
                    final_str.push_str(&s.hex);
                });
                FlatExpr::HexLiteral(loc, string_to_static(final_str))
            }
            RationalNumberLiteral(loc, integer, fraction, exp, unit) => {
                if let Some(unit) = unit {
                    FlatExpr::RationalNumberLiteral(
                        *loc,
                        Box::leak(integer.clone().into_boxed_str()),
                        Box::leak(fraction.clone().into_boxed_str()),
                        Box::leak(exp.clone().into_boxed_str()),
                        Some(Box::leak(unit.name.clone().into_boxed_str())),
                    )
                } else {
                    FlatExpr::RationalNumberLiteral(
                        *loc,
                        Box::leak(integer.clone().into_boxed_str()),
                        Box::leak(fraction.clone().into_boxed_str()),
                        Box::leak(exp.clone().into_boxed_str()),
                        None,
                    )
                }
            }
            ArrayLiteral(loc, ..) => FlatExpr::ArrayLiteral(*loc),
            Variable(var) => {
                FlatExpr::Variable(var.loc, Box::leak(var.name.clone().into_boxed_str()))
            }
            List(loc, params) => FlatExpr::List(*loc, params.len()),
            This(loc, ..) => FlatExpr::This(*loc),
        }
    }
}
