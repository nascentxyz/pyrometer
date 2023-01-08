use ethers_core::types::{U256, H256, Address};
use solang_parser::pt::Identifier;
use std::collections::HashMap;
use solang_parser::pt::{
    ContractPart,
    TypeDefinition,
    VariableDefinition,
    FunctionDefinition,
    ErrorDefinition,
    StructDefinition,
    EnumDefinition,
    ContractDefinition,
    SourceUnitPart,
    SourceUnit,
    Expression,
    Statement,
};

use petgraph::dot::Dot;
use petgraph::visit::EdgeRef;
use petgraph::{Direction, Directed, graph::*};
use petgraph::graph::Edges;

mod builtin_fns;

pub mod queries;
pub mod types;
pub mod context;
use types::*;
use context::*;

pub type NodeIdx = NodeIndex<usize>;
pub type EdgeIdx = EdgeIndex<usize>;



#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Node {
    Context(Context),
    ContextVar(ContextVar),
    Builtin(Builtin),
    DynBuiltin(DynBuiltin),
    VarType(VarType),
    SourceUnit(usize),
    SourceUnitPart(usize, usize),
    Contract(Contract),
    Function(Function),
    FunctionParam(FunctionParam),
    FunctionReturn(FunctionReturn),
    Struct(Struct),
    Enum(Enum),
    Error(Error),
    ErrorParam(ErrorParam),
    Field(Field),
    Var(Var),
    Ty(Ty),
    Unresolved(Identifier),
    Concrete(Concrete),
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ConcreteNode(pub usize);

impl ConcreteNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Concrete {
        match analyzer.node(*self) {
            Node::Concrete(c) => c,
            e => panic!("Node type confusion: expected node to be Concrete but it was: {:?}", e)
        }
    }
}


impl From<NodeIdx> for ConcreteNode {
    fn from(idx: NodeIdx) -> Self {
        ConcreteNode(idx.index())
    }
}

impl Into<NodeIdx> for ConcreteNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Concrete {
    Uint(u16, U256),
    Int(u16, U256),
    Bytes(u8, H256),
    Address(Address),
    DynBytes(Vec<u8>),
    Array(Vec<Concrete>),
}
impl Concrete {
    pub fn uint_val(&self) -> Option<U256> {
        match self {
            Concrete::Uint(_, val) => Some(*val),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Edge {
    Part,
    Context(ContextEdge),
    Contract,
    Field,
    Enum,
    Struct,
    Error,
    ErrorParam,
    Event,
    Var,
    Ty,
    Func,
    FunctionParam,
    FunctionReturn,
}

#[derive(Debug, Clone)]
pub struct Analyzer {
    pub graph: Graph::<Node, Edge, Directed, usize>,
    pub builtins: HashMap<Builtin, NodeIdx>,
    pub dyn_builtins: HashMap<DynBuiltin, NodeIdx>,
    pub user_types: HashMap<String, NodeIdx>,
    pub builtin_fns: HashMap<String, Function>,
    pub builtin_fn_inputs: HashMap<String, (Vec<FunctionParam>, Vec<FunctionReturn>)>,
}

impl Default for Analyzer {
    fn default() -> Self {
        let mut a = Self {
            graph: Default::default(),
            builtins: Default::default(),
            dyn_builtins: Default::default(),
            user_types: Default::default(),
            builtin_fns: builtin_fns::builtin_fns(),
            builtin_fn_inputs: Default::default(),
        };
        a.builtin_fn_inputs = builtin_fns::builtin_fns_inputs(&mut a);
        a
    }
}

impl ArrayAccessAnalyzer for Analyzer {}
impl Search for Analyzer {}
impl ContextAnalyzer for Analyzer {}

pub trait AnalyzerLike: GraphLike {
    fn builtin_fns(&self) -> &HashMap<String, Function>;
    fn builtin_fn_inputs(&self) -> &HashMap<String, (Vec<FunctionParam>, Vec<FunctionReturn>)>;
    fn builtins(&self) -> &HashMap<Builtin, NodeIdx>;
    fn builtins_mut(&mut self) -> &mut HashMap<Builtin, NodeIdx>;
    fn builtin_or_add(&mut self, builtin: Builtin) -> NodeIdx {
        if let Some(idx) = self.builtins().get(&builtin) {
            *idx
        } else {
            let idx = self.add_node(Node::Builtin(builtin.clone()));
            self.builtins_mut().insert(builtin, idx);
            idx
        }
    }
    fn dyn_builtins(&self) -> &HashMap<DynBuiltin, NodeIdx>;
    fn dyn_builtins_mut(&mut self) -> &mut HashMap<DynBuiltin, NodeIdx>;
    fn user_types(&self) -> &HashMap<String, NodeIdx>;
    fn user_types_mut(&mut self) -> &mut HashMap<String, NodeIdx>;
    fn parse_expr(&mut self, expr: &Expression) -> NodeIdx;
}

pub trait GraphLike {
    fn graph_mut(&mut self) -> &mut Graph::<Node, Edge, Directed, usize>;
    fn graph(&self) -> &Graph::<Node, Edge, Directed, usize>;

    fn add_node(&mut self, node: impl Into<Node>) -> NodeIdx {
        self.graph_mut().add_node(node.into())
    }

    fn node(&self, node: impl Into<NodeIdx>) -> &Node {
        self.graph().node_weight(node.into()).expect("Index not in graph")
    }

    fn node_mut(&mut self, node: impl Into<NodeIdx>) -> &mut Node {
        self.graph_mut().node_weight_mut(node.into()).expect("Index not in graph")
    }

    fn add_edge(&mut self, from_node: impl Into<NodeIdx>, to_node: impl Into<NodeIdx>, edge: impl Into<Edge>) {
        self.graph_mut().add_edge(from_node.into(), to_node.into(), edge.into());
    }

    fn dot_str(&self) -> String {
        format!("{:?}", Dot::new(self.graph()))
    }
}

impl GraphLike for Analyzer {
    fn graph_mut(&mut self) -> &mut Graph::<Node, Edge, Directed, usize> {
        &mut self.graph
    }

    fn graph(&self) -> &Graph::<Node, Edge, Directed, usize> {
        &self.graph
    }
}

impl AnalyzerLike for Analyzer {
    fn builtin_fns(&self) -> &HashMap<String, Function> {
        &self.builtin_fns
    }

    fn builtin_fn_inputs(&self) -> &HashMap<String, (Vec<FunctionParam>, Vec<FunctionReturn>)> {
        &self.builtin_fn_inputs
    }

    fn builtins(&self) -> &HashMap<Builtin, NodeIdx> {
        &self.builtins
    }
    fn builtins_mut(&mut self) -> &mut HashMap<Builtin, NodeIdx> {
        &mut self.builtins
    }
    fn dyn_builtins(&self) -> &HashMap<DynBuiltin, NodeIdx> {
        &self.dyn_builtins
    }
    fn dyn_builtins_mut(&mut self) -> &mut HashMap<DynBuiltin, NodeIdx> {
        &mut self.dyn_builtins
    }
    fn user_types(&self) -> &HashMap<String, NodeIdx> {
        &self.user_types
    }
    fn user_types_mut(&mut self) -> &mut HashMap<String, NodeIdx> {
        &mut self.user_types
    }

    fn parse_expr(&mut self, expr: &Expression) -> NodeIdx {
        use Expression::*;
        // println!("{:?}", expr);
        match expr {
            Type(_loc, ty) => {
                if let Some(builtin) = Builtin::try_from_ty(ty.clone()) {
                    if let Some(idx) = self.builtins.get(&builtin) {
                        *idx
                    } else {
                        let idx = self.add_node(Node::Builtin(builtin.clone()));
                        self.builtins.insert(builtin, idx);
                        idx
                    }
                } else {
                    0.into()
                }
            }
            Variable(ident) => {
                if let Some(idx) = self.user_types.get(&ident.name) {
                    *idx
                } else {
                    let node = self.add_node(Node::Unresolved(ident.clone()));
                    self.user_types.insert(ident.name.clone(), node);
                    node
                }
            }
            ArraySubscript(_loc, ty_expr, None) => {
                let inner_ty = self.parse_expr(ty_expr);
                if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
                    let dyn_b = DynBuiltin::Array(var_type);
                    if let Some(idx) = self.dyn_builtins.get(&dyn_b) {
                        *idx
                    } else {
                        let idx = self.add_node(Node::DynBuiltin(dyn_b.clone()));
                        self.dyn_builtins.insert(dyn_b, idx);
                        idx
                    }
                } else {
                    todo!("???")
                }
            }
            ArraySubscript(_loc, ty_expr, Some(index_expr)) => {
                let inner_ty = self.parse_expr(ty_expr);
                let index_ty = self.parse_expr(index_expr);
                // println!("here: {:?}", index_expr);
                // if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
                //     let dyn_b = DynBuiltin::Array(var_type);
                //     if let Some(idx) = self.dyn_builtins.get(&dyn_b) {
                //         *idx
                //     } else {
                //         let idx = self.add_node(Node::DynBuiltin(dyn_b.clone()));
                //         self.dyn_builtins.insert(dyn_b, idx);
                //         idx
                //     }
                // } else {
                //     todo!("???")
                // }
                0.into()
            }
            NumberLiteral(loc, int, exp) => {
                let int = U256::from_dec_str(int).unwrap();
                let val = if !exp.is_empty() {
                    let exp = U256::from_dec_str(exp).unwrap();
                    int.pow(exp)
                } else {
                    int
                };
                self.add_node(Node::Concrete(Concrete::Uint(256, val)))
            }
            _ => 0.into()
        }
    }
}

impl ContextBuilder for Analyzer {}

impl Analyzer {
    pub fn parse(&mut self, src: &str, file_no: usize) -> Option<NodeIdx> {
        match solang_parser::parse(src, file_no) {
            Ok((source_unit, _comments)) => {
                let parent = self.add_node(Node::SourceUnit(file_no));
                self.parse_source_unit(source_unit, file_no, parent);
                Some(parent)
            },
            Err(e) => panic!("FAIL to parse, {:?}", e),
        }
    }

    pub fn parse_source_unit(&mut self, source_unit: SourceUnit, file_no: usize, parent: NodeIdx) {
        source_unit.0.iter().enumerate().for_each(|(unit_part, source_unit_part)| {
            self.parse_source_unit_part(source_unit_part, file_no, unit_part, parent);
        })
    }

    pub fn parse_source_unit_part(&mut self, sup: &SourceUnitPart, file_no: usize, unit_part: usize, parent: NodeIdx) -> NodeIdx {
        use SourceUnitPart::*;

        let sup_node = self.add_node(Node::SourceUnitPart(file_no, unit_part));
        self.add_edge(sup_node, parent, Edge::Part);
        match sup {
            ContractDefinition(def) => {
                let node = self.parse_contract_def(&*def);
                self.add_edge(node, sup_node, Edge::Contract);
            },
            StructDefinition(def) => {
                let node = self.parse_struct_def(&*def);
                self.add_edge(node, sup_node, Edge::Struct);
            },
            EnumDefinition(def) => {
                let node = self.parse_enum_def(&*def);
                self.add_edge(node, sup_node, Edge::Enum);
            },
            ErrorDefinition(def) => {
                let node = self.parse_err_def(&*def);
                self.add_edge(node, sup_node, Edge::Error);
            },
            VariableDefinition(def) => {
                let node = self.parse_var_def(&*def);
                self.add_edge(node, sup_node, Edge::Var);
            },
            FunctionDefinition(def) => {
                let node = self.parse_func_def(&*def);
                self.add_edge(node, sup_node, Edge::Func);  
            },
            TypeDefinition(def) => {
                let node = self.parse_ty_def(&*def);
                self.add_edge(node, sup_node, Edge::Ty);
            },
            EventDefinition(_def) => todo!(),
            Annotation(_anno) => todo!(),
            Using(_using) => todo!(),
            StraySemicolon(_loc) => todo!(),
            PragmaDirective(_, _, _) => todo!(),
            ImportDirective(_) => todo!(),
        }
        sup_node
    }

    pub fn parse_contract_def(&mut self, contract_def: &ContractDefinition) -> ContractNode {
        use ContractPart::*;

        let con_node = ContractNode(self.add_node(Contract::from(contract_def.clone())).index());

        contract_def.parts.iter().for_each(|cpart| {
            match cpart {
                StructDefinition(def) => {
                    let node = self.parse_struct_def(&*def);
                    self.add_edge(node, con_node, Edge::Struct);
                },
                EnumDefinition(def) => {
                    let node = self.parse_enum_def(&*def);
                    self.add_edge(node, con_node, Edge::Enum);
                },
                ErrorDefinition(def) => {
                    let node = self.parse_err_def(&*def);
                    self.add_edge(node, con_node, Edge::Error);
                },
                VariableDefinition(def) => {
                    let node = self.parse_var_def(&*def);
                    self.add_edge(node, con_node, Edge::Var);
                },
                FunctionDefinition(def) => {
                    let node = self.parse_func_def(&*def);
                    self.add_edge(node, con_node, Edge::Func);  
                },
                TypeDefinition(def) => {
                    let node = self.parse_ty_def(&*def);
                    self.add_edge(node, con_node, Edge::Ty);
                },
                EventDefinition(_def) => todo!(),
                Annotation(_anno) => todo!(),
                Using(_using) => todo!(),
                StraySemicolon(_loc) => todo!(),
            }
        });
        con_node
    }

    pub fn parse_enum_def(&mut self, enum_def: &EnumDefinition) -> EnumNode {
        let enu = Enum::from(enum_def.clone());
        let name = enu.name.clone().expect("Struct was not named").name;

        // check if we have an unresolved type by the same name
        let enu_node: EnumNode = if let Some(user_ty_node) = self.user_types.get(&name).cloned() {
            let unresolved = self.node_mut(user_ty_node);
            *unresolved = Node::Enum(enu);
            user_ty_node.into()
        } else {
            let node = self.add_node(enu);
            self.user_types.insert(name, node);
            node.into()
        };

        enu_node
    }

    pub fn parse_struct_def(&mut self, struct_def: &StructDefinition) -> StructNode {
        let strukt = Struct::from(struct_def.clone());
        let name = strukt.name.clone().expect("Struct was not named").name;

        // check if we have an unresolved type by the same name
        let strukt_node: StructNode = if let Some(user_ty_node) = self.user_types.get(&name).cloned() {
            let unresolved = self.node_mut(user_ty_node);
            *unresolved = Node::Struct(strukt);
            user_ty_node.into()
        } else {
            let node = self.add_node(strukt);
            self.user_types.insert(name, node);
            node.into()
        };

        struct_def.fields.iter().for_each(|field| {
            let f = Field::new(self, field.clone());
            let field_node = self.add_node(f);
            self.add_edge(field_node, strukt_node, Edge::Field);
        });
        strukt_node
    }


    pub fn parse_err_def(&mut self, err_def: &ErrorDefinition) -> ErrorNode {
        let err_node = ErrorNode(self.add_node(Error::from(err_def.clone())).index());
        err_def.fields.iter().for_each(|field| {
            let param = ErrorParam::new(self, field.clone());
            let field_node = self.add_node(param);
            self.add_edge(field_node, err_node, Edge::ErrorParam);
        });
        err_node
    }

    pub fn parse_func_def(&mut self, func_def: &FunctionDefinition) -> FunctionNode {
        let func = Function::from(func_def.clone());
        let name = func.name.clone().expect("Struct was not named").name;
        // TODO: check if we have an unresolved type by the same name

        let func_node: FunctionNode = if let Some(user_ty_node) = self.user_types.get(&name).cloned() {
            let unresolved = self.node_mut(user_ty_node);
            *unresolved = Node::Function(func);
            user_ty_node.into()
        } else {
            let node = self.add_node(func);
            self.user_types.insert(name, node);
            node.into()
        };

        func_def.params.iter().for_each(|(_loc, input)| {
            if let Some(input) = input {
                let param = FunctionParam::new(self, input.clone());
                let input_node = self.add_node(param);
                self.add_edge(input_node, func_node, Edge::FunctionParam);
            }
        });
        func_def.returns.iter().for_each(|(_loc, output)| {
            if let Some(output) = output {
                let ret = FunctionReturn::new(self, output.clone());
                let output_node = self.add_node(ret);
                self.add_edge(output_node, func_node, Edge::FunctionReturn);
            }
        });

        if let Some(body) = &func_def.body {
            self.parse_ctx_statement(body, false, Some(func_node));
        }

        func_node
    }

    pub fn parse_var_def(&mut self, var_def: &VariableDefinition) -> VarNode {
        let var = Var::new(self, var_def.clone());
        VarNode(self.add_node(var).index())
    }

    pub fn parse_ty_def(&mut self, ty_def: &TypeDefinition) -> TyNode {
        let ty = Ty::new(self, ty_def.clone());
        TyNode(self.add_node(ty).index())
    }

    pub fn parse_statement(&mut self, stmt: &Statement, unchecked: bool, parent_ctx: Option<impl Into<NodeIdx>>) {
        use Statement::*;
        // println!("stmt: {:?}", stmt);
        match stmt {
            Block{loc, unchecked, statements} => {
                let ctx = Context::new(*loc);
                let ctx_node = self.add_node(Node::Context(ctx));
                
                if let Some(parent) = parent_ctx {
                    self.add_edge(ctx_node, parent, Edge::Context(ContextEdge::Context));
                }

                statements.iter().for_each(|stmt| { self.parse_statement(stmt, *unchecked, Some(ctx_node)) });
            },
            VariableDefinition(loc, var_decl, maybe_expr) => {

            }
            Assembly {
                loc,
                dialect,
                flags,
                block: yul_block,
            } => {},
            Args(loc, args) => {},
            If(loc, cond, true_body, maybe_false_body) => {},
            While(loc, cond, body) => {},
            Expression(loc, expr) => {},
            VariableDefinition(loc, var_decl, maybe_expr) => {},
            For(loc, maybe_for_start, maybe_for_middle, maybe_for_end, maybe_for_body) => {},
            DoWhile(loc, while_stmt, while_expr) => {},
            Continue(loc) => {},
            Break(loc) => {},
            Return(loc, maybe_ret_expr) => {
                if let Some(ret_expr) = maybe_ret_expr {
                    let expr_node = self.parse_expr(ret_expr);
                    if let Some(parent) = parent_ctx {
                        self.add_edge(expr_node, parent, Edge::Context(ContextEdge::Return));
                    }
                }
            },
            Revert(loc, maybe_err_path, exprs) => {},
            RevertNamedArgs(loc,maybe_err_path, named_args) => {},
            Emit(loc, emit_expr) => {},
            Try(loc, try_expr, maybe_returns, clauses) => {},
            Error(loc) => {},
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let sol = r###"
contract Storage {
    struct A {
        uint256[] a;
    }

    function b(A memory k) public returns (uint256) {
        return k.a[0];
    }

    function b2(A memory k, uint256 s) public returns (uint256) {
        return k.a[s];
    }

    function b3(A memory k, uint256 s) public returns (uint256) {
        require(s < 10);
        return k.a[s];
    }
}"###;
        let mut analyzer = Analyzer::default();
        let entry = analyzer.parse(&sol, 0).unwrap();
        println!("{}", analyzer.dot_str());
        let contexts = analyzer.search_children(entry, &crate::Edge::Context(ContextEdge::Context));
        println!("contexts: {:?}", contexts);
        for context in contexts.into_iter() {
            let mins = analyzer.min_size_to_prevent_access_revert(ContextNode::from(context));
            mins[0].print_report((0, &sol), &analyzer);
        }
        
        
    }
}
