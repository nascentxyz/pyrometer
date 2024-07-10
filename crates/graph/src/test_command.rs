use crate::nodes::Concrete;

#[derive(Debug, Clone)]
pub enum TestCommand {
    Variable(String, VariableCommand),
    Constraint(String),
    Coverage(CoverageCommand),
}

#[derive(Debug, Clone)]
pub enum VariableCommand {
    RangeAssert { min: Concrete, max: Concrete },
}

#[derive(Debug, Clone)]
pub enum CoverageCommand {
    OnlyPath,
    Unreachable,
}
