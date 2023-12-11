use crate::{ExprErr, IntoExprErr};

use graph::{
    elem::*,
    nodes::{Builtin, Concrete, ConcreteNode, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node,
};

use ethers_core::types::{Address, H256, I256, U256};
use solang_parser::pt::{HexLiteral, Identifier, Loc};

use std::str::FromStr;

impl<T> Literal for T where T: AnalyzerBackend + Sized {}

/// Dealing with literal expression and parsing them into nodes
pub trait Literal: AnalyzerBackend + Sized {
    fn number_literal(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        integer: &str,
        exponent: &str,
        negative: bool,
    ) -> Result<(), ExprErr> {
        let int = U256::from_dec_str(integer).unwrap();
        let val = if !exponent.is_empty() {
            let exp = U256::from_dec_str(exponent).unwrap();
            int * U256::from(10).pow(exp)
        } else {
            int
        };

        let size: u16 = ((32 - (val.leading_zeros() / 8)) * 8) as u16;
        let concrete_node = if negative {
            let val = if val == U256::from(2).pow(255.into()) {
                // no need to set upper bit
                I256::from_raw(val)
            } else {
                I256::from(-1i32) * I256::from_raw(val)
            };
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

    fn rational_number_literal(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        integer: &str,
        fraction: &str,
        exponent: &str,
        _unit: &Option<Identifier>,
    ) -> Result<(), ExprErr> {
        let int = U256::from_dec_str(integer).unwrap();
        let exp = if !exponent.is_empty() {
            U256::from_dec_str(exponent).unwrap()
        } else {
            U256::from(0)
        };
        let fraction_len = fraction.len();
        let fraction_denom = U256::from(10).pow(fraction_len.into());
        let fraction = U256::from_dec_str(fraction).unwrap();

        let int_elem = Elem::min(
            Elem::from(Concrete::from(int)),
            Elem::from(Concrete::from(U256::from(1))),
        );
        let exp_elem = Elem::from(Concrete::from(exp));
        let rational_range = (Elem::from(Concrete::from(fraction))
            + int_elem * Elem::from(Concrete::from(fraction_denom)))
            * Elem::from(Concrete::from(U256::from(10))).pow(exp_elem);
        let cvar =
            ContextVar::new_from_builtin(loc, self.builtin_or_add(Builtin::Uint(256)).into(), self)
                .into_expr_err(loc)?;
        let node = ContextVarNode::from(self.add_node(Node::ContextVar(cvar)));
        node.set_range_max(self, rational_range.clone())
            .into_expr_err(loc)?;
        node.set_range_min(self, rational_range)
            .into_expr_err(loc)?;

        ctx.add_var(node, self).into_expr_err(loc)?;
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::SingleLiteral(node.into()), self)
            .into_expr_err(loc)?;
        Ok(())
    }

    fn hex_num_literal(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        integer: &str,
        negative: bool,
    ) -> Result<(), ExprErr> {
        let integer: String = integer.chars().filter(|c| *c != '_').collect();
        let val = U256::from_str_radix(&integer, 16).unwrap();
        let size: u16 = ((32 - (val.leading_zeros() / 8)) * 8) as u16;
        let concrete_node = if negative {
            let val = I256::from(-1i32) * I256::from_raw(val);
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

    fn hex_literals(&mut self, ctx: ContextNode, hexes: &[HexLiteral]) -> Result<(), ExprErr> {
        if hexes.len() == 1 {
            let mut h = H256::default();
            let mut max = 0;
            if let Ok(hex_val) = hex::decode(&hexes[0].hex) {
                hex_val.iter().enumerate().for_each(|(i, hex_byte)| {
                    if *hex_byte != 0x00u8 {
                        max = i as u8;
                    }
                    h.0[i] = *hex_byte;
                });
            }

            let concrete_node =
                ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bytes(max + 1, h))));
            let ccvar = Node::ContextVar(
                ContextVar::new_from_concrete(hexes[0].loc, ctx, concrete_node, self)
                    .into_expr_err(hexes[0].loc)?,
            );
            let node = self.add_node(ccvar);
            ctx.add_var(node.into(), self).into_expr_err(hexes[0].loc)?;
            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
            ctx.push_expr(ExprRet::SingleLiteral(node), self)
                .into_expr_err(hexes[0].loc)?;
            Ok(())
        } else {
            let mut h = vec![];
            hexes.iter().for_each(|sub_hex| {
                if let Ok(hex_val) = hex::decode(&sub_hex.hex) {
                    h.extend(hex_val)
                }
            });

            let mut loc = hexes[0].loc;
            loc.use_end_from(&hexes[hexes.len() - 1].loc);
            let concrete_node =
                ConcreteNode::from(self.add_node(Node::Concrete(Concrete::DynBytes(h))));
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

    fn address_literal(&mut self, ctx: ContextNode, loc: Loc, addr: &str) -> Result<(), ExprErr> {
        let addr = Address::from_str(addr).unwrap();

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
