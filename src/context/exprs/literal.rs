use shared::context::*;
use crate::ExprRet;
use shared::{analyzer::AnalyzerLike, nodes::{Concrete, ConcreteNode}, Node};
use ethers_core::types::{Address, U256};
use solang_parser::pt::Loc;
use std::str::FromStr;

impl<T> Literal for T where T: AnalyzerLike + Sized {}

pub trait Literal: AnalyzerLike + Sized {
    fn number_literal(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        integer: &String,
        exponent: &String,
    ) -> ExprRet {
        let int = U256::from_dec_str(&integer).unwrap();
        let val = if !exponent.is_empty() {
            let exp = U256::from_dec_str(&exponent).unwrap();
            int.pow(exp)
        } else {
            int
        };

        let concrete_node =
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Uint(256, val))));
        let ccvar = Node::ContextVar(ContextVar::new_from_concrete(loc, concrete_node, self));
        ExprRet::Single((ctx, self.add_node(ccvar)))
    }

    fn address_literal(&mut self, ctx: ContextNode, loc: Loc, addr: &String) -> ExprRet {
        let addr = Address::from_str(&addr).unwrap();

        let concrete_node =
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Address(addr))));
        let ccvar = Node::ContextVar(ContextVar::new_from_concrete(loc, concrete_node, self));
        ExprRet::Single((ctx, self.add_node(ccvar)))
    }

    fn string_literal(&mut self, ctx: ContextNode, loc: Loc, s: &String) -> ExprRet {
        let concrete_node =
            ConcreteNode::from(self.add_node(Node::Concrete(Concrete::String(s.to_string()))));
        let ccvar = Node::ContextVar(ContextVar::new_from_concrete(loc, concrete_node, self));
        ExprRet::Single((ctx, self.add_node(ccvar)))
    }

    fn bool_literal(&mut self, ctx: ContextNode, loc: Loc, b: bool) -> ExprRet {
        let concrete_node = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(b))));
        let ccvar = Node::ContextVar(ContextVar::new_from_concrete(loc, concrete_node, self));
        ExprRet::Single((ctx, self.add_node(ccvar)))
    }
}
