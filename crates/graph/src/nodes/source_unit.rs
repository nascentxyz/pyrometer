use crate::{
    nodes::{Concrete, ContractNode, FunctionNode, SourceUnitPartNode, StructNode, VarNode},
    range::elem::Elem,
    AsDotStr, GraphBackend, GraphError, Node,
};

use shared::{NodeIdx, RangeArena};

#[derive(Default, Clone, Debug, PartialOrd, PartialEq, Ord, Eq)]
pub struct SourceUnit {
    pub file: usize,
    pub parts: Vec<SourceUnitPartNode>,
}

impl SourceUnit {
    pub fn new(file: usize) -> Self {
        Self {
            file,
            ..Default::default()
        }
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct SourceUnitNode(pub usize);

impl From<SourceUnitNode> for NodeIdx {
    fn from(val: SourceUnitNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for SourceUnitNode {
    fn from(idx: NodeIdx) -> Self {
        SourceUnitNode(idx.index())
    }
}

impl AsDotStr for SourceUnitNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        let underlying = self.underlying(analyzer).unwrap();
        format!("SourceUnit({})", underlying.file)
    }
}

impl SourceUnitNode {
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a SourceUnit, GraphError> {
        match analyzer.node(*self) {
            Node::SourceUnit(c) => Ok(c),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find source unit part: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be SourceUnit but it was: {e:?}"
            ))),
        }
    }

    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut impl GraphBackend,
    ) -> Result<&'a mut SourceUnit, GraphError> {
        match analyzer.node_mut(*self) {
            Node::SourceUnit(c) => Ok(c),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find source unit: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be SourceUnit but it was: {e:?}"
            ))),
        }
    }

    pub fn parts<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a Vec<SourceUnitPartNode>, GraphError> {
        Ok(&self.underlying(analyzer)?.parts)
    }

    pub fn visible_funcs(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<FunctionNode>, GraphError> {
        let mut nodes = vec![];
        self.parts(analyzer)?.iter().try_for_each(|part| {
            nodes.extend(part.visible_funcs(analyzer)?);
            Ok(())
        })?;
        Ok(nodes)
    }

    pub fn visible_structs(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<StructNode>, GraphError> {
        let mut nodes = vec![];
        self.parts(analyzer)?.iter().try_for_each(|part| {
            nodes.extend(part.visible_structs(analyzer)?);
            Ok(())
        })?;
        Ok(nodes)
    }

    pub fn visible_constants(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<VarNode>, GraphError> {
        let mut nodes = vec![];
        self.parts(analyzer)?.iter().try_for_each(|part| {
            nodes.extend(part.visible_constants(analyzer)?);
            Ok(())
        })?;
        Ok(nodes)
    }

    pub fn visible_contracts(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<ContractNode>, GraphError> {
        let mut nodes = vec![];
        self.parts(analyzer)?.iter().try_for_each(|part| {
            nodes.extend(part.visible_contracts(analyzer)?);
            Ok(())
        })?;
        Ok(nodes)
    }

    pub fn add_part(
        &self,
        part: SourceUnitPartNode,
        analyzer: &mut impl GraphBackend,
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.parts.push(part);
        Ok(())
    }
}
