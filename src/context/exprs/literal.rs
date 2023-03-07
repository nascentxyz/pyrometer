use ethers_core::types::I256;
use ethers_core::types::H256;
use solang_parser::pt::HexLiteral;
use crate::ExprRet;
use shared::{
    analyzer::AnalyzerLike,
    context::*,
    nodes::{Concrete, ConcreteNode},
    Edge, Node,
};

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
    ) -> ExprRet {
        let int = U256::from_dec_str(integer).unwrap();
        let val = if !exponent.is_empty() {
            let exp = U256::from_dec_str(exponent).unwrap();
            int.pow(exp)
        } else {
            int
        };

        let concrete_node = if negative {
            let val = I256::from(-1i32) * I256::from_raw(val);
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Int(256, val))))
        } else {
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Uint(256, val))))
        };

        let ccvar = Node::ContextVar(ContextVar::new_from_concrete(loc, concrete_node, self));
        let node = self.add_node(ccvar);
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ExprRet::Single((ctx, node))
    }

    fn hex_num_literal(&mut self, ctx: ContextNode, loc: Loc, integer: &str, negative: bool,) -> ExprRet {
        let val = U256::from_str_radix(integer, 16).unwrap();
        let concrete_node = if negative {
            let val = I256::from(-1i32) * I256::from_raw(val);
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Int(256, val))))
        } else {
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Uint(256, val))))
        };

        let ccvar = Node::ContextVar(ContextVar::new_from_concrete(loc, concrete_node, self));
        let node = self.add_node(ccvar);
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ExprRet::Single((ctx, node))
    }

    fn hex_literals(&mut self, ctx: ContextNode, hexes: &[HexLiteral]) -> ExprRet {
        if hexes.len() == 1 {
            let mut h = H256::default();
            if let Ok(hex_val) = hex::decode(&hexes[0].hex) {
                hex_val.iter().enumerate().for_each(|(i, hex_byte)| {
                    h.0[i] = *hex_byte;
                });
            }

            let concrete_node =
                ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bytes(32, h))));
            let ccvar = Node::ContextVar(ContextVar::new_from_concrete(hexes[0].loc, concrete_node, self));
            let node = self.add_node(ccvar);
            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
            ExprRet::Single((ctx, node))
        } else {
            todo!("hexes: {:?}", hexes);
        }
    }

    fn address_literal(&mut self, ctx: ContextNode, loc: Loc, addr: &str) -> ExprRet {
        let addr = Address::from_str(addr).unwrap();

        let concrete_node =
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Address(addr))));
        let ccvar = Node::ContextVar(ContextVar::new_from_concrete(loc, concrete_node, self));
        let node = self.add_node(ccvar);
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ExprRet::Single((ctx, node))
    }

    fn string_literal(&mut self, ctx: ContextNode, loc: Loc, s: &str) -> ExprRet {
        let concrete_node =
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::String(s.to_string()))));
        let ccvar = Node::ContextVar(ContextVar::new_from_concrete(loc, concrete_node, self));
        let node = self.add_node(ccvar);
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ExprRet::Single((ctx, node))
    }

    fn bool_literal(&mut self, ctx: ContextNode, loc: Loc, b: bool) -> ExprRet {
        let concrete_node = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(b))));
        let ccvar = Node::ContextVar(ContextVar::new_from_concrete(loc, concrete_node, self));
        let node = self.add_node(ccvar);
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ExprRet::Single((ctx, node))
    }
}
