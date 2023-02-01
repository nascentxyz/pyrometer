use ethers_core::types::U256;
use shared::analyzer::*;
use shared::nodes::*;
use shared::{Edge, Node, NodeIdx};

use solang_parser::pt::{
    ContractDefinition, ContractPart, EnumDefinition, ErrorDefinition, Expression,
    FunctionDefinition, SourceUnit, SourceUnitPart, StructDefinition, TypeDefinition,
    VariableDefinition,
};
use std::collections::HashMap;

use petgraph::{graph::*, Directed};

mod builtin_fns;

pub mod context;
// pub mod range;
use context::*;

#[derive(Debug, Clone)]
pub struct Analyzer {
    pub graph: Graph<Node, Edge, Directed, usize>,
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

impl GraphLike for Analyzer {
    fn graph_mut(&mut self) -> &mut Graph<Node, Edge, Directed, usize> {
        &mut self.graph
    }

    fn graph(&self) -> &Graph<Node, Edge, Directed, usize> {
        &self.graph
    }
}

impl AnalyzerLike for Analyzer {
    type Expr = Expression;
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
                let _inner_ty = self.parse_expr(ty_expr);
                let _index_ty = self.parse_expr(index_expr);
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
            NumberLiteral(_loc, int, exp) => {
                let int = U256::from_dec_str(int).unwrap();
                let val = if !exp.is_empty() {
                    let exp = U256::from_dec_str(exp).unwrap();
                    int.pow(exp)
                } else {
                    int
                };
                self.add_node(Node::Concrete(Concrete::Uint(256, val)))
            }
            _ => 0.into(),
        }
    }
}

impl Analyzer {
    pub fn parse(&mut self, src: &str, file_no: usize) -> Option<NodeIdx> {
        match solang_parser::parse(src, file_no) {
            Ok((source_unit, _comments)) => {
                let parent = self.add_node(Node::SourceUnit(file_no));
                self.parse_source_unit(source_unit, file_no, parent);
                Some(parent)
            }
            Err(e) => panic!("FAIL to parse, {:?}", e),
        }
    }

    pub fn parse_source_unit(&mut self, source_unit: SourceUnit, file_no: usize, parent: NodeIdx) {
        source_unit
            .0
            .iter()
            .enumerate()
            .for_each(|(unit_part, source_unit_part)| {
                self.parse_source_unit_part(source_unit_part, file_no, unit_part, parent);
            })
    }

    pub fn parse_source_unit_part(
        &mut self,
        sup: &SourceUnitPart,
        file_no: usize,
        unit_part: usize,
        parent: NodeIdx,
    ) -> NodeIdx {
        use SourceUnitPart::*;

        let sup_node = self.add_node(Node::SourceUnitPart(file_no, unit_part));
        self.add_edge(sup_node, parent, Edge::Part);
        match sup {
            ContractDefinition(def) => {
                let node = self.parse_contract_def(&*def);
                self.add_edge(node, sup_node, Edge::Contract);
            }
            StructDefinition(def) => {
                let node = self.parse_struct_def(&*def);
                self.add_edge(node, sup_node, Edge::Struct);
            }
            EnumDefinition(def) => {
                let node = self.parse_enum_def(&*def);
                self.add_edge(node, sup_node, Edge::Enum);
            }
            ErrorDefinition(def) => {
                let node = self.parse_err_def(&*def);
                self.add_edge(node, sup_node, Edge::Error);
            }
            VariableDefinition(def) => {
                let node = self.parse_var_def(&*def, false);
                self.add_edge(node, sup_node, Edge::Var);
            }
            FunctionDefinition(def) => {
                let node = self.parse_func_def(&*def);
                self.add_edge(node, sup_node, Edge::Func);
            }
            TypeDefinition(def) => {
                let node = self.parse_ty_def(&*def);
                self.add_edge(node, sup_node, Edge::Ty);
            }
            EventDefinition(_def) => todo!(),
            Annotation(_anno) => todo!(),
            Using(_using) => todo!(),
            StraySemicolon(_loc) => todo!(),
            PragmaDirective(_, _, _) => {}
            ImportDirective(_) => todo!(),
        }
        sup_node
    }

    pub fn parse_contract_def(&mut self, contract_def: &ContractDefinition) -> ContractNode {
        use ContractPart::*;

        let con_node = ContractNode(self.add_node(Contract::from(contract_def.clone())).index());

        contract_def.parts.iter().for_each(|cpart| match cpart {
            StructDefinition(def) => {
                let node = self.parse_struct_def(&*def);
                self.add_edge(node, con_node, Edge::Struct);
            }
            EnumDefinition(def) => {
                let node = self.parse_enum_def(&*def);
                self.add_edge(node, con_node, Edge::Enum);
            }
            ErrorDefinition(def) => {
                let node = self.parse_err_def(&*def);
                self.add_edge(node, con_node, Edge::Error);
            }
            VariableDefinition(def) => {
                let node = self.parse_var_def(&*def, true);
                self.add_edge(node, con_node, Edge::Var);
            }
            FunctionDefinition(def) => {
                let node = self.parse_func_def(&*def);
                self.add_edge(node, con_node, Edge::Func);
            }
            TypeDefinition(def) => {
                let node = self.parse_ty_def(&*def);
                self.add_edge(node, con_node, Edge::Ty);
            }
            EventDefinition(_def) => todo!(),
            Annotation(_anno) => todo!(),
            Using(_using) => todo!(),
            StraySemicolon(_loc) => todo!(),
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
        let strukt_node: StructNode =
            if let Some(user_ty_node) = self.user_types.get(&name).cloned() {
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

        let func_node: FunctionNode =
            if let Some(user_ty_node) = self.user_types.get(&name).cloned() {
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

        // we delay the function body parsing to the end after parsing all sources
        if let Some(body) = &func_def.body {
            self.parse_ctx_statement(body, false, Some(func_node));
        }

        func_node
    }

    pub fn parse_var_def(&mut self, var_def: &VariableDefinition, in_contract: bool) -> VarNode {
        let var = Var::new(self, var_def.clone(), in_contract);
        let var_node = VarNode::from(self.add_node(var));
        self.user_types.insert(var_node.name(self), var_node.into());
        var_node
    }

    pub fn parse_ty_def(&mut self, ty_def: &TypeDefinition) -> TyNode {
        let ty = Ty::new(self, ty_def.clone());
        TyNode(self.add_node(ty).index())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shared::context::{ContextEdge, ContextNode};

    #[test]
    fn it_works() {
        let sol = r###"
contract Storage {
    uint256 c;

    function b5(uint64 x) public  {
        // if (x % 2 == 0) {
        //     x = x / 2;
        // } else {
        //     x = x * 3 + 1;
        //     require( x % 2 == 0);
        // }
        c += x;
        (uint256 a, uint256 b) = x < 5 ? (1 + 2, 5) : (3 + 4, 6);
        // a += 1;
        // require(a < 10);
        // require(b < 8);
        if (x < 7) {
            c += 1;
        } else {
            if (x < 10) {
                c += 2;    
            } else {
                c += 3;
            }
        }

        x += 10;

        c += x*0;
    }
}"###;
        let mut analyzer = Analyzer::default();
        let t0 = std::time::Instant::now();
        let entry = analyzer.parse(&sol, 0).unwrap();
        println!("parse time: {:?}", t0.elapsed().as_nanos());
        println!("{}", analyzer.dot_str_no_tmps_for_ctx("b5".to_string()));
        let contexts = analyzer.search_children(entry, &crate::Edge::Context(ContextEdge::Context));
        for context in contexts.into_iter() {
            let config = ReportConfig {
                eval_bounds: true,
                simplify_bounds: true,
                show_tmps: false,
                show_consts: true,
                show_subctxs: true,
                show_initial_bounds: true,
            };
            let ctx = ContextNode::from(context);

            let analysis = analyzer.bounds_for_all(ctx, config);
            analysis.print_reports((0, &sol), &analyzer);
        }
        println!("total analyze time: {:?}", t0.elapsed().as_nanos());
    }
}
