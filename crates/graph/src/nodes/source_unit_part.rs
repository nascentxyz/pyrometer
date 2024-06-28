use crate::{
    nodes::{Concrete, ContractNode, FunctionNode, StructNode, VarNode},
    range::elem::Elem,
    AsDotStr, GraphBackend, Node,
};

use shared::{GraphError, NodeIdx, RangeArena};

#[derive(Default, Clone, Debug, PartialOrd, PartialEq, Ord, Eq)]
pub struct SourceUnitPart {
    pub file: usize,
    pub part: usize,
    pub funcs: Vec<FunctionNode>,
    pub structs: Vec<StructNode>,
    pub constants: Vec<VarNode>,
    pub contracts: Vec<ContractNode>,
}

impl SourceUnitPart {
    pub fn new(file: usize, part: usize) -> Self {
        Self {
            file,
            part,
            ..Default::default()
        }
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct SourceUnitPartNode(pub usize);

impl From<SourceUnitPartNode> for NodeIdx {
    fn from(val: SourceUnitPartNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for SourceUnitPartNode {
    fn from(idx: NodeIdx) -> Self {
        SourceUnitPartNode(idx.index())
    }
}

impl AsDotStr for SourceUnitPartNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        let underlying = self.underlying(analyzer).unwrap();
        format!("SourceUnitPart({}, {})", underlying.file, underlying.part)
    }
}

impl SourceUnitPartNode {
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a SourceUnitPart, GraphError> {
        match analyzer.node(*self) {
            Node::SourceUnitPart(c) => Ok(c),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find source unit part: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be SourceUnitPart but it was: {e:?}"
            ))),
        }
    }

    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut impl GraphBackend,
    ) -> Result<&'a mut SourceUnitPart, GraphError> {
        match analyzer.node_mut(*self) {
            Node::SourceUnitPart(c) => Ok(c),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find source unit part: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be SourceUnitPart but it was: {e:?}"
            ))),
        }
    }

    pub fn visible_funcs<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a Vec<FunctionNode>, GraphError> {
        Ok(&self.underlying(analyzer)?.funcs)
    }

    pub fn visible_structs<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a Vec<StructNode>, GraphError> {
        Ok(&self.underlying(analyzer)?.structs)
    }

    pub fn visible_constants<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a Vec<VarNode>, GraphError> {
        Ok(&self.underlying(analyzer)?.constants)
    }

    pub fn visible_contracts<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a Vec<ContractNode>, GraphError> {
        Ok(&self.underlying(analyzer)?.contracts)
    }

    pub fn add_func(
        &self,
        func: FunctionNode,
        analyzer: &mut impl GraphBackend,
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.funcs.push(func);
        Ok(())
    }

    pub fn add_struct(
        &self,
        strukt: StructNode,
        analyzer: &mut impl GraphBackend,
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.structs.push(strukt);
        Ok(())
    }

    pub fn add_contract(
        &self,
        contract: ContractNode,
        analyzer: &mut impl GraphBackend,
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.contracts.push(contract);
        Ok(())
    }

    pub fn add_constant(
        &self,
        constant: VarNode,
        analyzer: &mut impl GraphBackend,
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.constants.push(constant);
        Ok(())
    }
}
