mod analyzer_like;
mod graph_like;
mod search;

pub use analyzer_like::*;
pub use graph_like::*;
pub use search::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum StorageLocation {
    Memory(solang_parser::pt::Loc),
    Storage(solang_parser::pt::Loc),
    Calldata(solang_parser::pt::Loc),
    Block(solang_parser::pt::Loc),
    Msg(solang_parser::pt::Loc),
}

impl std::fmt::Display for StorageLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Memory(_) => write!(f, "memory"),
            Self::Storage(_) => write!(f, "storage"),
            Self::Calldata(_) => write!(f, "calldata"),
            Self::Block(_) => write!(f, "block"),
            Self::Msg(_) => write!(f, "msg"),
        }
    }
}

impl From<solang_parser::pt::StorageLocation> for StorageLocation {
    fn from(sl: solang_parser::pt::StorageLocation) -> Self {
        match sl {
            solang_parser::pt::StorageLocation::Memory(m) => StorageLocation::Memory(m),
            solang_parser::pt::StorageLocation::Storage(m) => StorageLocation::Storage(m),
            solang_parser::pt::StorageLocation::Calldata(m) => StorageLocation::Calldata(m),
        }
    }
}
