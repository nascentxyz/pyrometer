use crate::{nodes::ContextVarNode, GraphBackend};

use shared::GraphError;

use solang_parser::pt::Loc;

pub trait Fielded {
    type Field;
    fn find_field(&self, analyzer: &impl GraphBackend, field_name: &str) -> Option<Self::Field>;
    fn fields(&self, analyzer: &impl GraphBackend) -> Vec<Self::Field>;
    fn add_fields_to_cvar(
        &self,
        analyzer: &mut impl GraphBackend,
        cvar: ContextVarNode,
        loc: Loc,
    ) -> Result<(), GraphError>;
}
