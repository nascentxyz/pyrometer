use graph::{
    elem::*,
    nodes::{Concrete, ConcreteNode, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node, TestCommand, VariableCommand,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use ethers_core::types::{Address, H256, I256, U256};
use solang_parser::pt::{HexLiteral, Identifier, Loc};

use std::str::FromStr;

impl<T> Literal for T where T: AnalyzerBackend + Sized {}

/// Dealing with literal expression and parsing them into nodes
pub trait Literal: AnalyzerBackend + Sized {
    fn concrete_number_from_str(
        &mut self,
        loc: Loc,
        integer: &str,
        exponent: &str,
        negative: bool,
        unit: &Option<Identifier>,
    ) -> Result<Concrete, ExprErr> {
        let Ok(int) = U256::from_dec_str(integer) else {
            return Err(ExprErr::ParseError(
                loc,
                format!("{integer} is too large, it does not fit into a uint256"),
            ));
        };
        let val = if !exponent.is_empty() {
            let exp = U256::from_dec_str(exponent)
                .map_err(|e| ExprErr::ParseError(loc, e.to_string()))?;
            int * U256::from(10).pow(exp)
        } else {
            int
        };

        let val = if let Some(unit) = unit {
            val * self.unit_to_uint(unit)
        } else {
            val
        };

        let size: u16 = ((32 - (val.leading_zeros() / 8)) * 8).max(8) as u16;
        if negative {
            let val = if val == U256::from(2).pow(255.into()) {
                // no need to set upper bit
                I256::from_raw(val)
            } else {
                let raw = I256::from_raw(val);
                if raw < 0.into() {
                    return Err(ExprErr::ParseError(
                        loc,
                        "Negative value cannot fit into int256".to_string(),
                    ));
                }
                I256::from(-1i32) * raw
            };
            Ok(Concrete::Int(size, val))
        } else {
            Ok(Concrete::Uint(size, val))
        }
    }
    fn number_literal(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        integer: &str,
        exponent: &str,
        negative: bool,
        unit: &Option<Identifier>,
    ) -> Result<(), ExprErr> {
        let conc = self.concrete_number_from_str(loc, integer, exponent, negative, unit)?;
        let concrete_node = ConcreteNode::from(self.add_node(Node::Concrete(conc)));
        let ccvar = Node::ContextVar(
            ContextVar::new_from_concrete(loc, ctx, concrete_node, self).into_expr_err(loc)?,
        );
        let node = self.add_node(ccvar);
        ctx.add_var(node.into(), self).into_expr_err(loc)?;
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::SingleLiteral(node), self)
            .into_expr_err(loc)?;
        Ok(())
    }

    fn unit_to_uint(&self, unit: &Identifier) -> U256 {
        match &*unit.name {
            "gwei" => U256::from(10).pow(9.into()),
            "ether" => U256::from(10).pow(18.into()),
            "minutes" => U256::from(60),
            "hours" => U256::from(3600),
            "days" => U256::from(86400),
            "weeks" => U256::from(604800),
            _ => U256::from(1),
        }
    }

    /// 1.0001e18
    fn rational_number_literal(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        integer: &str,
        fraction: &str,
        exponent: &str,
        unit: &Option<Identifier>,
        negative: bool,
    ) -> Result<(), ExprErr> {
        let int =
            U256::from_dec_str(integer).map_err(|e| ExprErr::ParseError(loc, e.to_string()))?;
        let exp = if !exponent.is_empty() {
            U256::from_dec_str(exponent).map_err(|e| ExprErr::ParseError(loc, e.to_string()))?
        } else {
            U256::from(0)
        };
        let fraction_len = fraction.len();
        let fraction_denom = U256::from(10).pow(fraction_len.into());
        let fraction =
            U256::from_dec_str(fraction).map_err(|e| ExprErr::ParseError(loc, e.to_string()))?;

        let unit_num = if let Some(unit) = unit {
            self.unit_to_uint(unit)
        } else {
            U256::from(1)
        };

        let int_elem = Elem::max(
            Elem::from(Concrete::from(int)),
            Elem::from(Concrete::from(U256::from(1))),
        );

        // move the decimal place to the right
        let mut rational_range = int_elem * Elem::from(Concrete::from(fraction_denom));
        // add the fraction
        rational_range = rational_range + Elem::from(Concrete::from(fraction));
        let mut rhs_power_res = U256::from(10).pow(exp) * unit_num;

        if fraction > rhs_power_res {
            return Err(ExprErr::ParseError(
                loc,
                format!("Invalid rational number: fraction part ({fraction}) has more precision than exponent ({exp}) and unit provide ({unit_num})"),
            ));
        }

        // decrease the exponentiation by the number of places we moved the decimal over
        rhs_power_res /= fraction_denom;

        rational_range = rational_range * Elem::from(Concrete::from(rhs_power_res));

        let concrete_node = if negative {
            let evaled = rational_range.maximize(self, arena).into_expr_err(loc)?;
            let val = evaled.maybe_concrete().unwrap().val.uint_val().unwrap();
            if val > U256::from(2).pow(255.into()) {
                return Err(ExprErr::ParseError(
                    loc,
                    "Negative value cannot fit into int256".to_string(),
                ));
            }
            rational_range = rational_range * Elem::from(Concrete::from(I256::from(-1i32)));
            let evaled = rational_range
                .maximize(self, arena)
                .into_expr_err(loc)?
                .maybe_concrete()
                .unwrap()
                .val
                .fit_size();

            ConcreteNode::from(self.add_node(Node::Concrete(evaled)))
        } else {
            let evaled = rational_range
                .maximize(self, arena)
                .into_expr_err(loc)?
                .maybe_concrete()
                .unwrap()
                .val
                .fit_size();
            ConcreteNode::from(self.add_node(Node::Concrete(evaled)))
        };

        let ccvar = Node::ContextVar(
            ContextVar::new_from_concrete(loc, ctx, concrete_node, self).into_expr_err(loc)?,
        );

        let node = ContextVarNode::from(self.add_node(ccvar));
        ctx.add_var(node, self).into_expr_err(loc)?;
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::SingleLiteral(node.into()), self)
            .into_expr_err(loc)?;
        Ok(())
    }

    /// 0x7B
    fn hex_num_literal(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        integer: &str,
        negative: bool,
    ) -> Result<(), ExprErr> {
        let integer: String = integer.chars().filter(|c| *c != '_').collect();
        let val = U256::from_str_radix(&integer, 16)
            .map_err(|e| ExprErr::ParseError(loc, e.to_string()))?;
        let size: u16 = (((32 - (val.leading_zeros() / 8)) * 8).max(8)) as u16;
        let concrete_node = if negative {
            let raw = I256::from_raw(val);
            if raw < 0.into() {
                return Err(ExprErr::ParseError(
                    loc,
                    "Negative value cannot fit into int256".to_string(),
                ));
            }
            let val = I256::from(-1i32) * raw;
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Int(size, val))))
        } else {
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Uint(size, val))))
        };

        let ccvar = Node::ContextVar(
            ContextVar::new_from_concrete(loc, ctx, concrete_node, self).into_expr_err(loc)?,
        );
        let node = self.add_node(ccvar);
        ctx.add_var(node.into(), self).into_expr_err(loc)?;
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::SingleLiteral(node), self)
            .into_expr_err(loc)?;
        Ok(())
    }

    /// hex"123123"
    fn hex_literals(&mut self, ctx: ContextNode, hexes: &[HexLiteral]) -> Result<(), ExprErr> {
        let mut h = vec![];
        hexes.iter().for_each(|sub_hex| {
            if let Ok(hex_val) = hex::decode(&sub_hex.hex) {
                h.extend(hex_val)
            }
        });

        let mut loc = hexes[0].loc;
        loc.use_end_from(&hexes[hexes.len() - 1].loc);

        let concrete_node = if h.len() <= 32 {
            let mut target = H256::default();
            let mut max = 1;
            h.iter().enumerate().for_each(|(i, hex_byte)| {
                if *hex_byte != 0x00u8 {
                    max = i as u8 + 1;
                }
                target.0[i] = *hex_byte;
            });
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bytes(max, target))))
        } else {
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::DynBytes(h))))
        };

        let ccvar = Node::ContextVar(
            ContextVar::new_from_concrete(loc, ctx, concrete_node, self).into_expr_err(loc)?,
        );
        let node = self.add_node(ccvar);
        ctx.add_var(node.into(), self).into_expr_err(loc)?;
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::SingleLiteral(node), self)
            .into_expr_err(loc)?;
        Ok(())
    }

    fn address_literal(&mut self, ctx: ContextNode, loc: Loc, addr: &str) -> Result<(), ExprErr> {
        let addr = Address::from_str(addr).map_err(|e| ExprErr::ParseError(loc, e.to_string()))?;

        let concrete_node =
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Address(addr))));
        let ccvar = Node::ContextVar(
            ContextVar::new_from_concrete(loc, ctx, concrete_node, self).into_expr_err(loc)?,
        );
        let node = self.add_node(ccvar);
        ctx.add_var(node.into(), self).into_expr_err(loc)?;
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::SingleLiteral(node), self)
            .into_expr_err(loc)?;
        Ok(())
    }

    fn test_string_literal(&mut self, s: &str) -> Option<TestCommand> {
        let split = s.split("::").collect::<Vec<_>>();
        if split.first().copied() == Some("pyro") {
            match split.get(1).copied() {
                Some("variable") => {
                    let name = split.get(2).copied()?;
                    match split.get(3).copied() {
                        Some("range") => {
                            let range = split
                                .get(4)
                                .copied()?
                                .trim_start_matches('[')
                                .trim_end_matches(']')
                                .split(',')
                                .collect::<Vec<_>>();
                            let mut min_str = *range.first()?;
                            let mut min_neg = false;
                            if let Some(new_min) = min_str.strip_prefix('-') {
                                min_neg = true;
                                min_str = new_min;
                            }

                            let mut max_str = *range.get(1)?;
                            let mut max_neg = false;
                            if let Some(new_max) = max_str.strip_prefix('-') {
                                max_neg = true;
                                max_str = new_max;
                            }

                            let min = self
                                .concrete_number_from_str(
                                    Loc::Implicit,
                                    min_str,
                                    "",
                                    min_neg,
                                    &None,
                                )
                                .ok()?;
                            let max = self
                                .concrete_number_from_str(
                                    Loc::Implicit,
                                    max_str,
                                    "",
                                    max_neg,
                                    &None,
                                )
                                .ok()?;

                            Some(TestCommand::Variable(
                                name.to_string(),
                                VariableCommand::RangeAssert { min, max },
                            ))
                        }
                        _ => None,
                    }
                }
                Some("constraint") => {
                    let constraint = split.get(2).copied()?;
                    Some(TestCommand::Constraint(constraint.to_string()))
                }
                Some("coverage") => match split.get(2).copied() {
                    Some("onlyPath") => {
                        Some(TestCommand::Coverage(graph::CoverageCommand::OnlyPath))
                    }
                    Some("unreachable") => {
                        Some(TestCommand::Coverage(graph::CoverageCommand::Unreachable))
                    }
                    _ => None,
                },
                _ => None,
            }
        } else {
            None
        }
    }

    fn string_literal(&mut self, ctx: ContextNode, loc: Loc, s: &str) -> Result<(), ExprErr> {
        let concrete_node =
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::String(s.to_string()))));
        let ccvar = Node::ContextVar(
            ContextVar::new_from_concrete(loc, ctx, concrete_node, self).into_expr_err(loc)?,
        );
        let node = self.add_node(ccvar);
        ctx.add_var(node.into(), self).into_expr_err(loc)?;
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::SingleLiteral(node), self)
            .into_expr_err(loc)?;
        Ok(())
    }

    fn bool_literal(&mut self, ctx: ContextNode, loc: Loc, b: bool) -> Result<(), ExprErr> {
        let concrete_node = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(b))));
        let ccvar = Node::ContextVar(
            ContextVar::new_from_concrete(loc, ctx, concrete_node, self).into_expr_err(loc)?,
        );
        let node = self.add_node(ccvar);
        ctx.add_var(node.into(), self).into_expr_err(loc)?;
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::SingleLiteral(node), self)
            .into_expr_err(loc)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use eyre::Result;
    use graph::nodes::Context;
    use graph::nodes::Function;
    use pyrometer::Analyzer;
    use solang_parser::pt::Loc;

    fn make_context_node_for_analyzer(analyzer: &mut Analyzer) -> ContextNode {
        // need to make a function, then provide the function to the new Context
        let func = Function::default();
        let func_node = analyzer.graph.add_node(Node::Function(func)).into();

        let loc = Loc::File(0, 0, 0);
        let ctx = Context::new(func_node, "test_fn".to_string(), loc);

        ContextNode::from(analyzer.graph.add_node(Node::Context(ctx)))
    }

    fn test_number_literal(
        num_literal: &str,
        exponent: &str,
        negative: bool,
        unit: Option<Identifier>,
        expected: Concrete,
    ) -> Result<()> {
        // setup
        let mut analyzer = Analyzer {
            debug_panic: true,
            ..Default::default()
        };
        let mut arena_base = RangeArena::default();
        let arena = &mut arena_base;
        let ctx = make_context_node_for_analyzer(&mut analyzer);
        let loc = Loc::File(0, 0, 0);

        // create a number literal
        analyzer.number_literal(ctx, loc, num_literal, exponent, negative, &unit)?;

        // checks
        let stack = &ctx.underlying(&analyzer)?.expr_ret_stack;
        assert!(
            stack.len() == 1,
            "ret stack length should be 1, got {}",
            stack.len()
        );
        assert!(
            stack[0].is_single(),
            "ret stack[0] should be a single literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].has_literal(),
            "ret stack[0] should have a literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].literals_list()?.len() == 1,
            "ret stack[0] should have a single literal in the literal list"
        );
        let cvar_node = ContextVarNode::from(stack[0].expect_single()?);
        assert!(cvar_node.is_const(&analyzer, arena)?);
        let min = cvar_node.evaled_range_min(&analyzer, arena)?.unwrap();
        let conc_value = min.maybe_concrete().unwrap().val;
        assert!(
            conc_value == expected,
            "Values do not match: {:?} != {:?}",
            conc_value,
            expected
        );
        Ok(())
    }

    #[test]
    fn test_number_literal_positive() -> Result<()> {
        let num_literal = "123";
        let expected = Concrete::Uint(8, U256::from_dec_str(num_literal).unwrap());
        test_number_literal(num_literal, "", false, None, expected)
    }

    #[test]
    fn test_number_literal_positive_overflow() -> Result<()> {
        let num_literal =
            "115792089237316195423570985008687907853269984665640564039457584007913129639936";
        let expected = Concrete::Uint(8, U256::default()); // we aren't using `expected`
        let result = test_number_literal(num_literal, "", false, None, expected);
        assert!(result.is_err(), "expected an error, got {:?}", result);
        Ok(())
    }

    #[test]
    fn test_number_literal_positive_with_exponent() -> Result<()> {
        // 123e18
        let num_literal = "123";
        let exponent = "10";
        let expected = Concrete::Uint(48, U256::from_dec_str("1230000000000").unwrap());
        test_number_literal(num_literal, exponent, false, None, expected)
    }

    #[test]
    fn test_number_literal_positive_with_zero_exponent() -> Result<()> {
        let num_literal = "123";
        let exponent = "0";
        let expected = Concrete::Uint(8, U256::from_dec_str("123").unwrap());
        test_number_literal(num_literal, exponent, false, None, expected)
    }

    #[test]
    fn test_number_literal_positive_with_zero_exponent_and_unit() -> Result<()> {
        let num_literal = "123";
        let exponent = "0";
        let unit = Some(Identifier {
            name: "ether".into(),
            loc: Loc::File(0, 0, 0),
        });
        let expected = Concrete::Uint(72, U256::from_dec_str("123000000000000000000").unwrap());
        test_number_literal(num_literal, exponent, false, unit, expected)
    }

    #[test]
    fn test_number_literal_positive_with_unit() -> Result<()> {
        let num_literal = "123";
        let exponent = "";
        let unit = Some(Identifier {
            name: "ether".into(),
            loc: Loc::File(0, 0, 0),
        });
        let expected = Concrete::Uint(72, U256::from_dec_str("123000000000000000000").unwrap());
        test_number_literal(num_literal, exponent, false, unit, expected)
    }

    #[test]
    fn test_number_literal_negative() -> Result<()> {
        let num_literal = "123";
        let expected = Concrete::Int(8, I256::from_dec_str("-123").unwrap());
        test_number_literal(num_literal, "", true, None, expected)
    }

    #[test]
    fn test_number_literal_negative_zero() -> Result<()> {
        let num_literal = "0";
        let expected = Concrete::Int(8, I256::from_dec_str("0").unwrap());
        test_number_literal(num_literal, "", true, None, expected)
    }

    #[test]
    fn test_number_literal_max() -> Result<()> {
        let num_literal =
            "57896044618658097711785492504343953926634992332820282019728792003956564819968";
        let expected = Concrete::Int(
            256,
            I256::from_dec_str(
                "-57896044618658097711785492504343953926634992332820282019728792003956564819968",
            )
            .unwrap(),
        );
        test_number_literal(num_literal, "", true, None, expected)
    }

    #[test]
    fn test_number_literal_negative_too_large() -> Result<()> {
        let num_literal =
            "57896044618658097711785492504343953926634992332820282019728792003956564819969";
        let expected = Concrete::Int(8, I256::default()); // this doesn't matter since we arent using `expected`
        let result = test_number_literal(num_literal, "", true, None, expected);
        assert!(result.is_err(), "expected an error, got {:?}", result);
        Ok(())
    }

    fn test_rational_number_literal(
        integer: &str,
        fraction: &str,
        exponent: &str,
        negative: bool,
        unit: Option<Identifier>,
        expected: Concrete,
    ) -> Result<()> {
        // setup
        let mut analyzer = Analyzer {
            debug_panic: true,
            ..Default::default()
        };
        let mut arena_base = RangeArena::default();
        let arena = &mut arena_base;
        let ctx = make_context_node_for_analyzer(&mut analyzer);
        let loc = Loc::File(0, 0, 0);

        // create a rational number literal
        analyzer.rational_number_literal(
            arena, ctx, loc, integer, fraction, exponent, &unit, negative,
        )?;

        // checks
        let stack = &ctx.underlying(&analyzer)?.expr_ret_stack;
        assert!(
            stack.len() == 1,
            "ret stack length should be 1, got {}",
            stack.len()
        );
        assert!(
            stack[0].is_single(),
            "ret stack[0] should be a single literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].has_literal(),
            "ret stack[0] should have a literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].literals_list()?.len() == 1,
            "ret stack[0] should have a single literal in the literal list"
        );
        let cvar_node = ContextVarNode::from(stack[0].expect_single()?);
        assert!(cvar_node.is_const(&analyzer, arena)?);
        let min = cvar_node.evaled_range_min(&analyzer, arena)?.unwrap();
        let conc_value = min.maybe_concrete().unwrap().val;
        assert!(
            conc_value == expected,
            "Values do not match: {:?} != {:?}",
            conc_value,
            expected
        );
        Ok(())
    }

    #[test]
    fn test_rational_number_literal_positive() -> Result<()> {
        let integer = "1";
        let fraction = "00001";
        let exponent = "18";
        let expected = Concrete::Uint(64, U256::from_dec_str("1000010000000000000").unwrap());
        test_rational_number_literal(integer, fraction, exponent, false, None, expected)
    }

    #[test]
    fn test_rational_number_literal_positive_fraction() -> Result<()> {
        let integer = "23";
        let fraction = "5";
        let exponent = "5";
        let expected = Concrete::Uint(24, U256::from_dec_str("2350000").unwrap());
        test_rational_number_literal(integer, fraction, exponent, false, None, expected)
    }

    #[test]
    fn test_rational_number_literal_negative() -> Result<()> {
        let integer = "23";
        let fraction = "5";
        let exponent = "5";
        let expected = Concrete::Int(24, I256::from_dec_str("-2350000").unwrap());
        test_rational_number_literal(integer, fraction, exponent, true, None, expected)
    }

    #[test]
    fn test_rational_number_literal_with_unit() -> Result<()> {
        let integer = "1";
        let fraction = "5";
        let exponent = "0";
        let unit = Some(Identifier {
            name: "ether".into(),
            loc: Loc::File(0, 0, 0),
        });
        let expected = Concrete::Uint(64, U256::from_dec_str("1500000000000000000").unwrap());
        test_rational_number_literal(integer, fraction, exponent, false, unit, expected)
    }

    fn test_hex_num_literal(hex_literal: &str, negative: bool, expected: Concrete) -> Result<()> {
        // setup
        let mut analyzer = Analyzer {
            debug_panic: true,
            ..Default::default()
        };
        let mut arena_base = RangeArena::default();
        let arena = &mut arena_base;
        let ctx = make_context_node_for_analyzer(&mut analyzer);
        let loc = Loc::File(0, 0, 0);

        // create a hex number literal
        analyzer.hex_num_literal(ctx, loc, hex_literal, negative)?;

        // checks
        let stack = &ctx.underlying(&analyzer)?.expr_ret_stack;
        assert!(
            stack.len() == 1,
            "ret stack length should be 1, got {}",
            stack.len()
        );
        assert!(
            stack[0].is_single(),
            "ret stack[0] should be a single literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].has_literal(),
            "ret stack[0] should have a literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].literals_list()?.len() == 1,
            "ret stack[0] should have a single literal in the literal list"
        );
        let cvar_node = ContextVarNode::from(stack[0].expect_single()?);
        assert!(cvar_node.is_const(&analyzer, arena)?);
        let min = cvar_node.evaled_range_min(&analyzer, arena)?.unwrap();
        let conc_value = min.maybe_concrete().unwrap().val;
        assert!(
            conc_value == expected,
            "Values do not match: {:?} != {:?}",
            conc_value,
            expected
        );
        Ok(())
    }

    #[test]
    fn test_hex_num_literal_positive() -> Result<()> {
        let hex_literal = "7B"; // 123 in decimal
        let expected = Concrete::Uint(8, U256::from_dec_str("123").unwrap());
        test_hex_num_literal(hex_literal, false, expected)
    }

    #[test]
    fn test_hex_num_literal_negative() -> Result<()> {
        let hex_literal = "7B"; // 123 in decimal
        let expected = Concrete::Int(8, I256::from_dec_str("-123").unwrap());
        test_hex_num_literal(hex_literal, true, expected)
    }

    #[test]
    fn test_hex_num_literal_large_positive() -> Result<()> {
        let hex_literal = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"; // max U256
        let expected = Concrete::Uint(
            256,
            U256::from_dec_str(
                "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            )
            .unwrap(),
        );
        test_hex_num_literal(hex_literal, false, expected)
    }

    #[test]
    fn test_hex_num_literal_large_negative() -> Result<()> {
        let hex_literal = "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"; // -1
        let expected = Concrete::Int(
            256,
            I256::from_dec_str(
                "-57896044618658097711785492504343953926634992332820282019728792003956564819967",
            )
            .unwrap(),
        );
        test_hex_num_literal(hex_literal, true, expected)
    }

    #[test]
    fn test_hex_num_literal_too_large_negative() -> Result<()> {
        let hex_literal = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"; // max U256
        let expected = Concrete::Int(256, I256::default()); // doesn't matter since it's out of range
        assert!(test_hex_num_literal(hex_literal, true, expected).is_err());
        Ok(())
    }

    #[test]
    fn test_hex_num_literal_zero() -> Result<()> {
        let hex_literal = "0"; // zero
        let expected = Concrete::Uint(8, U256::from_dec_str("0").unwrap());
        test_hex_num_literal(hex_literal, false, expected)
    }

    #[test]
    fn test_hex_num_literal_min_positive() -> Result<()> {
        let hex_literal = "1"; // smallest positive value
        let expected = Concrete::Uint(8, U256::from_dec_str("1").unwrap());
        test_hex_num_literal(hex_literal, false, expected)
    }

    #[test]
    fn test_hex_num_literal_min_negative() -> Result<()> {
        let hex_literal = "1"; // smallest negative value
        let expected = Concrete::Int(8, I256::from_dec_str("-1").unwrap());
        test_hex_num_literal(hex_literal, true, expected)
    }

    #[test]
    fn test_hex_num_literal_just_below_max_positive() -> Result<()> {
        let hex_literal = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE"; // just below max U256
        let expected = Concrete::Uint(
            256,
            U256::from_dec_str(
                "115792089237316195423570985008687907853269984665640564039457584007913129639934",
            )
            .unwrap(),
        );
        test_hex_num_literal(hex_literal, false, expected)
    }

    #[test]
    fn test_hex_num_literal_negative_just_above_min_negative() -> Result<()> {
        let hex_literal = "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE"; // just above min I256
        let expected = Concrete::Int(
            256,
            I256::from_dec_str(
                "-57896044618658097711785492504343953926634992332820282019728792003956564819966",
            )
            .unwrap(),
        );
        test_hex_num_literal(hex_literal, true, expected)
    }

    fn test_hex_literals(hex_literals: &[HexLiteral], expected: Concrete) -> Result<()> {
        // setup
        let mut analyzer = Analyzer {
            debug_panic: true,
            ..Default::default()
        };
        let mut arena_base = RangeArena::default();
        let arena = &mut arena_base;
        let ctx = make_context_node_for_analyzer(&mut analyzer);

        // create hex literals
        analyzer.hex_literals(ctx, hex_literals)?;

        // checks
        let stack = &ctx.underlying(&analyzer)?.expr_ret_stack;
        assert!(
            stack.len() == 1,
            "ret stack length should be 1, got {}",
            stack.len()
        );
        assert!(
            stack[0].is_single(),
            "ret stack[0] should be a single literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].has_literal(),
            "ret stack[0] should have a literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].literals_list()?.len() == 1,
            "ret stack[0] should have a single literal in the literal list"
        );
        println!(
            "{:#?}",
            analyzer.graph.node_weight(stack[0].expect_single()?)
        );
        let cvar_node = ContextVarNode::from(stack[0].expect_single()?);
        assert!(cvar_node.is_const(&analyzer, arena)?);
        let min = cvar_node.evaled_range_min(&analyzer, arena)?.unwrap();

        let conc_value = min.maybe_concrete().unwrap().val;
        assert!(
            conc_value == expected,
            "Values do not match: {:?} != {:?}",
            conc_value,
            expected
        );
        Ok(())
    }

    #[test]
    fn test_hex_literals_single() -> Result<()> {
        let hex_literal = HexLiteral {
            hex: "7B".to_string(), // 123 in decimal
            loc: Loc::File(0, 0, 0),
        };
        let mut bytes = [0u8; 32];
        bytes[0] = 0x7B; // Set the first byte to 0x7B as solidity does
        let expected = Concrete::Bytes(1, H256::from_slice(&bytes));
        test_hex_literals(&[hex_literal], expected)
    }

    #[test]
    fn test_hex_literals_multiple() -> Result<()> {
        let hex_literals = vec![
            HexLiteral {
                hex: "7B".to_string(), // 123 in decimal
                loc: Loc::File(0, 0, 0),
            },
            HexLiteral {
                hex: "FF".to_string(), // 255 in decimal
                loc: Loc::File(0, 0, 0),
            },
        ];

        let mut bytes = [0u8; 32];
        bytes[0] = 0x7B;
        bytes[1] = 0xFF;
        let expected = Concrete::Bytes(2, H256::from_slice(&bytes));
        test_hex_literals(&hex_literals, expected)
    }

    #[test]
    fn test_hex_literals_empty() -> Result<()> {
        let hex_literal = HexLiteral {
            hex: "".to_string(),
            loc: Loc::File(0, 0, 0),
        };
        let expected = Concrete::Bytes(1, H256::default());
        test_hex_literals(&[hex_literal], expected)
    }

    #[test]
    fn test_hex_literals_large() -> Result<()> {
        let hex_literal = HexLiteral {
            hex: "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF".to_string(), // max H256
            loc: Loc::File(0, 0, 0),
        };
        let expected = Concrete::Bytes(32, H256::from_slice(&[0xFF; 32]));
        test_hex_literals(&[hex_literal], expected)
    }

    fn test_address_literal(address: &str, expected: Concrete) -> Result<()> {
        // setup
        let mut analyzer = Analyzer {
            debug_panic: true,
            ..Default::default()
        };
        let mut arena_base = RangeArena::default();
        let arena = &mut arena_base;
        let ctx = make_context_node_for_analyzer(&mut analyzer);
        let loc = Loc::File(0, 0, 0);

        // create an address literal
        analyzer.address_literal(ctx, loc, address)?;

        // checks
        let stack = &ctx.underlying(&analyzer)?.expr_ret_stack;
        assert!(
            stack.len() == 1,
            "ret stack length should be 1, got {}",
            stack.len()
        );
        assert!(
            stack[0].is_single(),
            "ret stack[0] should be a single literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].has_literal(),
            "ret stack[0] should have a literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].literals_list()?.len() == 1,
            "ret stack[0] should have a single literal in the literal list"
        );
        let cvar_node = ContextVarNode::from(stack[0].expect_single()?);
        assert!(cvar_node.is_const(&analyzer, arena)?);
        let min = cvar_node.evaled_range_min(&analyzer, arena)?.unwrap();
        let conc_value = min.maybe_concrete().unwrap().val;
        assert!(
            conc_value == expected,
            "Values do not match: {:?} != {:?}",
            conc_value,
            expected
        );
        Ok(())
    }

    #[test]
    fn test_address_literal_valid() -> Result<()> {
        let address = "0x0000000000000000000000000000000000000001";
        let expected = Concrete::Address(Address::from_str(address).unwrap());
        test_address_literal(address, expected)
    }

    #[test]
    fn test_address_literal_zero() -> Result<()> {
        let address = "0x0000000000000000000000000000000000000000";
        let expected = Concrete::Address(Address::from_str(address).unwrap());
        test_address_literal(address, expected)
    }

    #[test]
    fn test_address_literal_max() -> Result<()> {
        let address = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF";
        let expected = Concrete::Address(Address::from_str(address).unwrap());
        test_address_literal(address, expected)
    }

    #[test]
    fn test_address_literal_too_large() -> Result<()> {
        let address = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"; // 168 bits
        let expected = Concrete::Address(Address::default()); // doesn't matter since we aren't using `expected`
        assert!(test_address_literal(address, expected).is_err());
        Ok(())
    }

    fn test_string_literal(string_value: &str, expected: Concrete) -> Result<()> {
        // setup
        let mut analyzer = Analyzer {
            debug_panic: true,
            ..Default::default()
        };
        let mut arena_base = RangeArena::default();
        let arena = &mut arena_base;
        let ctx = make_context_node_for_analyzer(&mut analyzer);
        let loc = Loc::File(0, 0, 0);

        // create a string literal
        analyzer.string_literal(ctx, loc, string_value)?;

        // checks
        let stack = &ctx.underlying(&analyzer)?.expr_ret_stack;
        assert!(
            stack.len() == 1,
            "ret stack length should be 1, got {}",
            stack.len()
        );
        assert!(
            stack[0].is_single(),
            "ret stack[0] should be a single literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].has_literal(),
            "ret stack[0] should have a literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].literals_list()?.len() == 1,
            "ret stack[0] should have a single literal in the literal list"
        );
        let cvar_node = ContextVarNode::from(stack[0].expect_single()?);
        assert!(cvar_node.is_const(&analyzer, arena)?);
        let min = cvar_node.evaled_range_min(&analyzer, arena)?.unwrap();
        println!("{min}");
        let conc_value = min.maybe_concrete().unwrap().val;
        assert!(
            conc_value == expected,
            "Values do not match: {:?} != {:?}",
            conc_value,
            expected
        );
        Ok(())
    }

    #[test]
    fn test_string_literal_empty() -> Result<()> {
        let string_value = "";
        let expected = Concrete::String(string_value.to_string());
        test_string_literal(string_value, expected)
    }

    #[test]
    fn test_string_literal_short() -> Result<()> {
        let string_value = "hello";
        let expected = Concrete::String(string_value.to_string());
        test_string_literal(string_value, expected)
    }

    #[test]
    fn test_string_literal_long() -> Result<()> {
        let string_value = "a".repeat(256); // 256 characters long
        let expected = Concrete::String(string_value.clone());
        test_string_literal(&string_value, expected)
    }

    #[test]
    fn test_string_literal_special_chars() -> Result<()> {
        let string_value = r#"!@#$%^&*()_+-=[]{}|;':,.<>/?"#;
        let expected = Concrete::String(string_value.to_string());
        test_string_literal(string_value, expected)
    }

    #[test]
    fn test_string_literal_unicode() -> Result<()> {
        let string_value = r#"🔥🔫"#;
        // Chisel -> unicode"🔥🔫" returns:
        // ├ Hex (Memory):
        // ├─ Length ([0x00:0x20]): 0x0000000000000000000000000000000000000000000000000000000000000008
        // ├─ Contents ([0x20:..]): 0xf09f94a5f09f94ab000000000000000000000000000000000000000000000000

        /* pyrometer analysis cuts off the contents
         21 │ │           string memory s = unicode"🔥🔫";
            │ │           ─────────────────┬───────────────────
            │ │                            ╰───────────────────── Memory var "s" == {len: 8, indices: {0: 0xf0, 1: 0xf0}}
            │ │                            │
            │ │                            ╰───────────────────── Memory var "s" ∈ [ {len: 0, indices: {0: 0xf0, 1: 0xf0}}, {len: 2**256 - 1, indices: {0: 0xf0, 1: 0xf0}} ]
            │ │                            │
            │ │                            ╰───────────────────── Memory var "s" == {len: 8, indices: {0: 0xf0, 1: 0xf0}}
        22 │ │           return s;
            │ │           ────┬───
            │ │               ╰───── returns: "s" == {len: 8, indices: {0: 0xf0, 1: 0xf0}}
         */
        let expected = Concrete::String(string_value.to_string());
        test_string_literal(string_value, expected)
    }

    fn test_bool_literal(bool_value: bool, expected: Concrete) -> Result<()> {
        // setup
        let mut analyzer = Analyzer {
            debug_panic: true,
            ..Default::default()
        };
        let mut arena_base = RangeArena::default();
        let arena = &mut arena_base;
        let ctx = make_context_node_for_analyzer(&mut analyzer);
        let loc = Loc::File(0, 0, 0);

        // create a boolean literal
        analyzer.bool_literal(ctx, loc, bool_value)?;

        // checks
        let stack = &ctx.underlying(&analyzer)?.expr_ret_stack;
        assert!(
            stack.len() == 1,
            "ret stack length should be 1, got {}",
            stack.len()
        );
        assert!(
            stack[0].is_single(),
            "ret stack[0] should be a single literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].has_literal(),
            "ret stack[0] should have a literal, got {:?}",
            stack[0]
        );
        assert!(
            stack[0].literals_list()?.len() == 1,
            "ret stack[0] should have a single literal in the literal list"
        );
        let cvar_node = ContextVarNode::from(stack[0].expect_single()?);
        assert!(cvar_node.is_const(&analyzer, arena)?);
        let min = cvar_node.evaled_range_min(&analyzer, arena)?.unwrap();
        let conc_value = min.maybe_concrete().unwrap().val;
        assert!(
            conc_value == expected,
            "Values do not match: {:?} != {:?}",
            conc_value,
            expected
        );
        Ok(())
    }

    #[test]
    fn test_bool_literal_true() -> Result<()> {
        let bool_value = true;
        let expected = Concrete::Bool(true);
        test_bool_literal(bool_value, expected)
    }

    #[test]
    fn test_bool_literal_false() -> Result<()> {
        let bool_value = false;
        let expected = Concrete::Bool(false);
        test_bool_literal(bool_value, expected)
    }
}
