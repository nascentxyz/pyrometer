use crate::{
    nodes::{Builtin, Concrete, ContextNode, ContextVarNode, StructNode},
    range::elem::Elem,
    ContextEdge, Edge, GraphBackend, Node, RepresentationInvariant, TypeNode, VarType,
};
use shared::{GraphError, NodeIdx, RangeArena, RepresentationErr, VarReprErr};

use petgraph::{visit::EdgeRef, Direction};

impl ContextVarNode {
    fn ty_check(
        &self,
        g: &impl GraphBackend,
        arena: &RangeArena<Elem<Concrete>>,
    ) -> Result<Option<RepresentationErr>, GraphError> {
        match self.ty(g)? {
            // we should have all types resolved by now
            VarType::User(TypeNode::Unresolved(u), range) => {
                Ok(Some(VarReprErr::Unresolved(self.0.into()).into()))
            }
            VarType::User(TypeNode::Contract(con), range) => Ok(None),
            VarType::User(TypeNode::Struct(strt), range) => self.struct_has_all_fields(*strt, g),
            VarType::User(TypeNode::Enum(enu), range) => Ok(None),
            VarType::User(TypeNode::Ty(ty), range) => Ok(None),
            VarType::User(TypeNode::Func(func), range) => Ok(None),
            VarType::BuiltIn(bn, range) => {
                let Node::Builtin(b) = g.node(*bn) else {
                    panic!("here")
                };
                match b {
                    Builtin::Address | Builtin::Payable | Builtin::AddressPayable => Ok(None),
                    Builtin::Bool => Ok(None),
                    Builtin::String => Ok(None),
                    Builtin::Bytes(size) => Ok(None),
                    Builtin::DynamicBytes => Ok(None),
                    Builtin::Int(size) => Ok(None),
                    Builtin::Uint(size) => Ok(None),
                    Builtin::Array(inner_ty) => Ok(None),
                    Builtin::SizedArray(size, inner_ty) => Ok(None),
                    Builtin::Mapping(key_ty, v_ty) => Ok(None),
                    Builtin::Rational => Ok(None),
                    Builtin::Func(inputs, rets) => Ok(None),
                }
            }
            VarType::Concrete(cn) => Ok(None),
        }
    }

    fn struct_has_all_fields(
        &self,
        strukt_node: StructNode,
        g: &impl GraphBackend,
    ) -> Result<Option<RepresentationErr>, GraphError> {
        let fields: Vec<_> = g
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|e| *e.weight() == Edge::Context(ContextEdge::AttrAccess("field")))
            .map(|e| ContextVarNode::from(e.source()))
            .collect();

        let struct_fields = strukt_node.fields(g);

        let mut real_field_names: Vec<String> = fields
            .iter()
            .map(|field| field.name(g).unwrap())
            .map(|name| {
                name.split('.')
                    .collect::<Vec<_>>()
                    .last()
                    .unwrap()
                    .to_string()
            })
            .collect();
        let mut target_field_names: Vec<_> = struct_fields
            .iter()
            .map(|field| field.name(g).unwrap())
            .collect();

        real_field_names.sort();
        target_field_names.sort();
        if real_field_names != target_field_names {
            Ok(Some(
                VarReprErr::StructErr(self.0.into(), "Missing fields").into(),
            ))
        } else {
            Ok(None)
        }
    }
}

impl RepresentationInvariant for ContextVarNode {
    fn is_representation_ok(
        &self,
        g: &impl GraphBackend,
        arena: &RangeArena<Elem<Concrete>>,
    ) -> Result<Option<RepresentationErr>, GraphError> {
        if let Some(ty_bad) = self.ty_check(g, arena)? {
            return Ok(Some(ty_bad));
        }
        Ok(None)
    }
}
