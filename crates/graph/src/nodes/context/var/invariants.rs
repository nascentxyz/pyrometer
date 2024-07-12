use crate::{
    nodes::{Builtin, Concrete, ContextVarNode, StructNode},
    range::elem::Elem,
    ContextEdge, Edge, GraphBackend, Node, RepresentationInvariant, TypeNode, VarType,
};
use shared::{GraphError, RangeArena, RepresentationErr, VarReprErr};

use petgraph::{visit::EdgeRef, Direction};

impl ContextVarNode {
    fn ty_check(
        &self,
        g: &impl GraphBackend,
        _arena: &RangeArena<Elem<Concrete>>,
    ) -> Result<Option<RepresentationErr>, GraphError> {
        match self.ty(g)? {
            // we should have all types resolved by now
            VarType::User(TypeNode::Unresolved(_u), _range) => {
                Ok(Some(VarReprErr::Unresolved(self.0.into()).into()))
            }
            VarType::User(TypeNode::Contract(_con), _range) => Ok(None),
            VarType::User(TypeNode::Struct(strt), _range) => self.struct_invariants(*strt, g),
            VarType::User(TypeNode::Enum(_enu), _range) => Ok(None),
            VarType::User(TypeNode::Ty(_ty), _range) => Ok(None),
            VarType::User(TypeNode::Func(_func), _range) => Ok(None),
            VarType::User(TypeNode::Error(_err), _) => Ok(None),
            VarType::BuiltIn(bn, _range) => {
                let Node::Builtin(b) = g.node(*bn) else {
                    panic!("here")
                };
                match b {
                    Builtin::Address | Builtin::Payable | Builtin::AddressPayable => Ok(None),
                    Builtin::Bool => Ok(None),
                    Builtin::String => Ok(None),
                    Builtin::Bytes(_size) => Ok(None),
                    Builtin::DynamicBytes => Ok(None),
                    Builtin::Int(_size) => Ok(None),
                    Builtin::Uint(_size) => Ok(None),
                    Builtin::Array(_inner_ty) => Ok(None),
                    Builtin::SizedArray(_size, _inner_ty) => Ok(None),
                    Builtin::Mapping(_key_ty, _v_ty) => Ok(None),
                    Builtin::Rational => Ok(None),
                    Builtin::Func(_inputs, _rets) => Ok(None),
                }
            }
            VarType::Concrete(_cn) => Ok(None),
        }
    }

    fn struct_invariants(
        &self,
        strukt_node: StructNode,
        g: &impl GraphBackend,
    ) -> Result<Option<RepresentationErr>, GraphError> {
        if let Some(err) = self
            .first_version(g)
            .struct_has_all_fields(strukt_node, g)?
        {
            return Ok(Some(err));
        }
        Ok(None)
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
        if real_field_names.len() < target_field_names.len() {
            Ok(Some(
                VarReprErr::StructErr(
                    self.0.into(),
                    Box::leak(
                        format!("{} has missing fields", self.display_name(g).unwrap())
                            .into_boxed_str(),
                    ),
                )
                .into(),
            ))
        } else if real_field_names.len() > target_field_names.len() {
            Ok(Some(
                VarReprErr::StructErr(
                    self.0.into(),
                    Box::leak(
                        format!("{} has extra fields", self.display_name(g).unwrap())
                            .into_boxed_str(),
                    ),
                )
                .into(),
            ))
        } else if real_field_names != target_field_names {
            Ok(Some(
                VarReprErr::StructErr(
                    self.0.into(),
                    Box::leak(
                        format!("{} has misnamed fields", self.display_name(g).unwrap())
                            .into_boxed_str(),
                    ),
                )
                .into(),
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
