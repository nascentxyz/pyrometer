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
    ) -> ExprRet {
        let int = U256::from_dec_str(integer).unwrap();
        let val = if !exponent.is_empty() {
            let exp = U256::from_dec_str(exponent).unwrap();
            int.pow(exp)
        } else {
            int
        };

        let concrete_node =
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Uint(256, val))));
        let ccvar = Node::ContextVar(ContextVar::new_from_concrete(loc, concrete_node, self));
        let node = self.add_node(ccvar);
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ExprRet::Single((ctx, node))
    }

    fn hex_num_literal(&mut self, ctx: ContextNode, loc: Loc, integer: &str) -> ExprRet {
        let val = U256::from_str_radix(integer, 16).unwrap();

        let concrete_node =
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Uint(256, val))));
        let ccvar = Node::ContextVar(ContextVar::new_from_concrete(loc, concrete_node, self));
        let node = self.add_node(ccvar);
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ExprRet::Single((ctx, node))
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
