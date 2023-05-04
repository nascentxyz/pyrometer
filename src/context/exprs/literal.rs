use crate::context::exprs::IntoExprErr;
use crate::ExprErr;
use ethers_core::types::H256;
use ethers_core::types::I256;
use shared::context::ExprRet;
use shared::{
    analyzer::AnalyzerLike,
    context::*,
    nodes::{Concrete, ConcreteNode},
    Edge, Node,
};
use solang_parser::pt::HexLiteral;

use ethers_core::types::{Address, U256};
use solang_parser::pt::Loc;
use std::str::FromStr;

impl<T> Literal for T where T: AnalyzerLike + Sized {}

pub trait Literal: AnalyzerLike + Sized {
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
            int.pow(exp)
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
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::SingleLiteral(node), self)
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
        let val = U256::from_str_radix(integer, 16).unwrap();
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
            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
            ctx.push_expr(ExprRet::SingleLiteral(node), self)
                .into_expr_err(hexes[0].loc)?;
            Ok(())
        } else {
            todo!("hexes: {:?}", hexes);
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
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::Single(node), self)
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
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::Single(node), self)
            .into_expr_err(loc)?;
        Ok(())
    }

    fn bool_literal(&mut self, ctx: ContextNode, loc: Loc, b: bool) -> Result<(), ExprErr> {
        let concrete_node = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(b))));
        let ccvar = Node::ContextVar(
            ContextVar::new_from_concrete(loc, ctx, concrete_node, self).into_expr_err(loc)?,
        );
        let node = self.add_node(ccvar);
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::Single(node), self)
            .into_expr_err(loc)?;
        Ok(())
    }
}
