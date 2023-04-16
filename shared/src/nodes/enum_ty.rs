use crate::analyzer::GraphError;
use crate::analyzer::{GraphLike, GraphAnalyzer};
use crate::range::SolcRange;
use crate::AsDotStr;
use crate::Concrete;
use crate::Node;
use crate::NodeIdx;
use solang_parser::pt::{EnumDefinition, Identifier, Loc};

/// An index in the graph that references a [`Enum`] node
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct EnumNode(pub usize);

impl AsDotStr for EnumNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let underlying = self.underlying(analyzer).unwrap();
        format!(
            "enum {} {{ {} }}",
            if let Some(name) = &underlying.name {
                name.name.clone()
            } else {
                "".to_string()
            },
            "..."
        )
    }
}

impl EnumNode {
    /// Gets the underlying node data for the [`Enum`]
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> Result<&'a Enum, GraphError> {
        match analyzer.node(*self) {
            Node::Enum(e) => Ok(e),
            e => Err(GraphError::NodeConfusion(format!("Node type confusion: expected node to be Contract but it was: {e:?}"))),
        }
    }

    /// Gets the name of the enum from the underlying node data for the [`Enum`]
    pub fn name(&self, analyzer: &impl GraphLike) -> Result<String, GraphError> {
        Ok(self.underlying(analyzer)?
            .name
            .clone()
            .expect("Unnamed contract")
            .name)
    }

    pub fn variants(&self, analyzer: &impl GraphLike) -> Result<Vec<String>, GraphError> {
        Ok(self.underlying(analyzer)?.variants())
    }

    pub fn maybe_default_range(&self, analyzer: &impl GraphLike) -> Result<Option<SolcRange>, GraphError> {
        let variants = self.variants(analyzer)?;
        if !variants.is_empty() {
            let min = Concrete::from(variants.first().unwrap().clone()).into();
            let max = Concrete::from(variants.last().unwrap().clone()).into();
            Ok(Some(SolcRange::new(min, max, vec![])))
        } else {
            Ok(None)
        }
    }

    pub fn range_from_variant(&self, variant: String, analyzer: &impl GraphLike) -> Result<SolcRange, GraphError> {
        let variants = self.variants(analyzer)?;
        assert!(variants.contains(&variant));
        let min = Concrete::from(variant.clone()).into();
        let max = Concrete::from(variant).into();
        Ok(SolcRange::new(min, max, vec![]))
    }
}

impl From<EnumNode> for NodeIdx {
    fn from(val: EnumNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for EnumNode {
    fn from(idx: NodeIdx) -> Self {
        EnumNode(idx.index())
    }
}

/// A solidity enum representation
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Enum {
    pub loc: Loc,
    pub name: Option<Identifier>,
    pub values: Vec<Option<Identifier>>,
}

impl Enum {
    pub fn variants(&self) -> Vec<String> {
        self.values
            .iter()
            .map(|ident| ident.clone().unwrap().name)
            .collect()
    }
}

impl From<Enum> for Node {
    fn from(val: Enum) -> Self {
        Node::Enum(val)
    }
}

impl From<EnumDefinition> for Enum {
    fn from(enu: EnumDefinition) -> Enum {
        Enum {
            loc: enu.loc,
            name: enu.name,
            values: enu.values,
        }
    }
}
