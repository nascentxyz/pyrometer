use crate::{FlatYulExpr, StorageLocation};
use solang_parser::pt::{Expression, Loc, NamedArgument, Type, YulExpression};

#[derive(Debug, Clone, Copy)]
pub enum ExprFlag {
    FunctionName(usize, bool, bool),
    New,
    Negate,
    Requirement,
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

    NamedArgument(Loc, &'static str),
    FunctionCallName(usize, bool, bool),
    Requirement(Loc),
    Super(Loc, &'static str),

    Continue(Loc),
    Break(Loc),
    Return(Loc, bool),

    PostIncrement(Loc),
    PostDecrement(Loc),
    New(Loc),
    ArrayTy(Loc),
    ArrayIndexAccess(Loc),
    ArraySlice(Loc),
    MemberAccess(Loc, &'static str),
    FunctionCall(Loc, usize),
    FunctionCallBlock(Loc),
    NamedFunctionCall(Loc, usize),
    Not(Loc),
    Negate(Loc),
    Delete(Loc),
    PreIncrement(Loc),
    PreDecrement(Loc),
    UnaryPlus(Loc),

    // binary ops
    Power(Loc, bool),
    Multiply(Loc, bool),
    Divide(Loc, bool),
    Modulo(Loc),
    Add(Loc, bool),
    Subtract(Loc, bool),
    AssignAdd(Loc, bool),
    AssignSubtract(Loc, bool),
    AssignMultiply(Loc, bool),
    AssignDivide(Loc, bool),
    AssignModulo(Loc),
    ShiftLeft(Loc),
    ShiftRight(Loc),
    BitwiseAnd(Loc),
    BitwiseXor(Loc),
    BitwiseOr(Loc),
    BitwiseNot(Loc),
    AssignOr(Loc),
    AssignAnd(Loc),
    AssignXor(Loc),
    AssignShiftLeft(Loc),
    AssignShiftRight(Loc),

    // cmp ops
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

    YulExpr(FlatYulExpr),
}

impl FlatExpr {
    pub fn try_inv_cmp(&self) -> Option<Self> {
        use FlatExpr::*;
        Some(match self {
            Less(loc) => MoreEqual(*loc),
            More(loc) => LessEqual(*loc),
            LessEqual(loc) => More(*loc),
            MoreEqual(loc) => Less(*loc),
            Equal(loc) => NotEqual(*loc),
            NotEqual(loc) => Equal(*loc),
            _ => Not(self.try_loc()?),
        })
    }
    pub fn try_loc(&self) -> Option<Loc> {
        use FlatExpr::*;
        match self {
            If { loc, .. }
            | VarDef(loc, ..)
            | NamedArgument(loc, ..)
            | Continue(loc, ..)
            | Break(loc, ..)
            | Return(loc, ..)
            | PostIncrement(loc, ..)
            | PostDecrement(loc, ..)
            | New(loc, ..)
            | ArrayTy(loc, ..)
            | ArrayIndexAccess(loc, ..)
            | ArraySlice(loc, ..)
            | MemberAccess(loc, ..)
            | FunctionCall(loc, ..)
            | FunctionCallBlock(loc, ..)
            | NamedFunctionCall(loc, ..)
            | Not(loc, ..)
            | Negate(loc, ..)
            | Delete(loc, ..)
            | PreIncrement(loc, ..)
            | PreDecrement(loc, ..)
            | UnaryPlus(loc, ..)
            | Power(loc, ..)
            | Multiply(loc, ..)
            | Divide(loc, ..)
            | Modulo(loc, ..)
            | Add(loc, ..)
            | Subtract(loc, ..)
            | AssignAdd(loc, ..)
            | AssignSubtract(loc, ..)
            | AssignMultiply(loc, ..)
            | AssignDivide(loc, ..)
            | AssignModulo(loc, ..)
            | ShiftLeft(loc, ..)
            | ShiftRight(loc, ..)
            | BitwiseAnd(loc, ..)
            | BitwiseXor(loc, ..)
            | BitwiseOr(loc, ..)
            | BitwiseNot(loc, ..)
            | AssignOr(loc, ..)
            | AssignAnd(loc, ..)
            | AssignXor(loc, ..)
            | AssignShiftLeft(loc, ..)
            | AssignShiftRight(loc, ..)
            | Less(loc, ..)
            | More(loc, ..)
            | LessEqual(loc, ..)
            | MoreEqual(loc, ..)
            | Equal(loc, ..)
            | NotEqual(loc, ..)
            | And(loc, ..)
            | Or(loc, ..)
            | ConditionalOperator(loc, ..)
            | Assign(loc, ..)
            | Type(loc, ..)
            | This(loc, ..)
            | List(loc, ..)
            | Parameter(loc, ..)
            | Null(loc, ..)
            | BoolLiteral(loc, ..)
            | NumberLiteral(loc, ..)
            | RationalNumberLiteral(loc, ..)
            | HexNumberLiteral(loc, ..)
            | StringLiteral(loc, ..)
            | HexLiteral(loc, ..)
            | AddressLiteral(loc, ..)
            | Variable(loc, ..)
            | Requirement(loc, ..)
            | Super(loc, ..)
            | YulExpr(FlatYulExpr::YulVariable(loc, ..))
            | YulExpr(FlatYulExpr::YulFuncCall(loc, ..))
            | YulExpr(FlatYulExpr::YulSuffixAccess(loc, ..))
            | ArrayLiteral(loc, ..) => Some(*loc),

            FunctionCallName(..)
            | YulExpr(FlatYulExpr::YulStartBlock)
            | YulExpr(FlatYulExpr::YulEndBlock)
            | YulExpr(FlatYulExpr::YulFunctionCallName(..)) => None,
        }
    }
}

pub fn string_to_static(s: impl ToString) -> &'static str {
    Box::leak(s.to_string().into_boxed_str())
}

impl From<&NamedArgument> for FlatExpr {
    fn from(arg: &NamedArgument) -> Self {
        FlatExpr::NamedArgument(arg.loc, string_to_static(arg.name.name.clone()))
    }
}

impl TryFrom<&YulExpression> for FlatExpr {
    type Error = ();
    fn try_from(expr: &YulExpression) -> Result<Self, ()> {
        use YulExpression::*;
        let res = match expr {
            BoolLiteral(loc, b, _unimpled_type) => FlatExpr::BoolLiteral(*loc, *b),
            NumberLiteral(loc, int, exp, _unimpled_type) => FlatExpr::NumberLiteral(
                *loc,
                Box::leak(int.clone().into_boxed_str()),
                Box::leak(exp.clone().into_boxed_str()),
                None,
            ),
            HexNumberLiteral(loc, b, _unimpled_type) => {
                FlatExpr::HexNumberLiteral(*loc, Box::leak(b.clone().into_boxed_str()), None)
            }
            HexStringLiteral(hexes, _unimpled_type) => {
                let final_str = hexes.hex.clone();
                let loc = hexes.loc;
                FlatExpr::HexLiteral(loc, string_to_static(final_str))
            }
            StringLiteral(lits, _unimpled_type) => {
                let final_str = lits.string.clone();
                let loc = lits.loc;
                FlatExpr::StringLiteral(loc, string_to_static(final_str))
            }
            other => FlatExpr::YulExpr(FlatYulExpr::try_from(other)?),
        };
        Ok(res)
    }
}

impl TryFrom<&Expression> for FlatExpr {
    type Error = ();
    fn try_from(expr: &Expression) -> Result<Self, ()> {
        use Expression::*;
        let res = match expr {
            PostIncrement(loc, ..) => FlatExpr::PostIncrement(*loc),
            PostDecrement(loc, ..) => FlatExpr::PostDecrement(*loc),
            New(loc, ..) => FlatExpr::New(*loc),
            ArraySubscript(loc, _, None) => FlatExpr::ArrayTy(*loc),
            ArraySubscript(loc, _, Some(_)) => FlatExpr::ArrayIndexAccess(*loc),
            ArraySlice(loc, ..) => FlatExpr::ArraySlice(*loc),
            MemberAccess(loc, _, name) => {
                FlatExpr::MemberAccess(*loc, string_to_static(name.name.clone()))
            }
            FunctionCall(loc, _, input_exprs) => FlatExpr::FunctionCall(*loc, input_exprs.len()),
            FunctionCallBlock(loc, _, _) => FlatExpr::FunctionCallBlock(*loc),
            NamedFunctionCall(loc, _, input_exprs) => {
                FlatExpr::NamedFunctionCall(*loc, input_exprs.len())
            }
            Not(loc, ..) => FlatExpr::Not(*loc),
            Delete(loc, ..) => FlatExpr::Delete(*loc),
            PreIncrement(loc, ..) => FlatExpr::PreIncrement(*loc),
            PreDecrement(loc, ..) => FlatExpr::PreDecrement(*loc),
            UnaryPlus(loc, ..) => FlatExpr::UnaryPlus(*loc),
            Parenthesis(_, expr) => FlatExpr::try_from(&**expr)?,
            Modulo(loc, _, _) => FlatExpr::Modulo(*loc),
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

            Power(_, _, _)
            | Multiply(_, _, _)
            | Divide(_, _, _)
            | Add(_, _, _)
            | Subtract(_, _, _)
            | AssignAdd(_, _, _)
            | AssignSubtract(_, _, _)
            | AssignMultiply(_, _, _)
            | AssignDivide(_, _, _) => return Err(()),
        };
        Ok(res)
    }
}
