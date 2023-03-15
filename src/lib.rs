use ethers_core::types::U256;
use shared::analyzer::*;
use shared::nodes::*;
use shared::{Edge, Node, NodeIdx};
use solang_parser::pt::Import;

use solang_parser::pt::{
    ContractDefinition, ContractPart, EnumDefinition, ErrorDefinition, Expression,
    FunctionDefinition, FunctionTy, SourceUnit, SourceUnitPart, StructDefinition, TypeDefinition,
    VariableDefinition,
};
use std::{collections::HashMap, fs};

use petgraph::{graph::*, Directed};

mod builtin_fns;

pub mod context;
// pub mod range;
use context::*;

#[derive(Debug, Clone)]
pub struct Analyzer {
    pub remappings: HashMap<String, String>,
    pub file_no: usize,
    pub msg: MsgNode,
    pub block: BlockNode,
    pub graph: Graph<Node, Edge, Directed, usize>,
    pub builtins: HashMap<Builtin, NodeIdx>,
    pub user_types: HashMap<String, NodeIdx>,
    pub builtin_fns: HashMap<String, Function>,
    pub builtin_fn_inputs: HashMap<String, (Vec<FunctionParam>, Vec<FunctionReturn>)>,
}

impl Default for Analyzer {
    fn default() -> Self {
        let mut a = Self {
            remappings: Default::default(),
            file_no: 0,
            msg: MsgNode(0),
            block: BlockNode(0),
            graph: Default::default(),
            builtins: Default::default(),
            user_types: Default::default(),
            builtin_fns: builtin_fns::builtin_fns(),
            builtin_fn_inputs: Default::default(),
        };
        a.builtin_fn_inputs = builtin_fns::builtin_fns_inputs(&mut a);

        let msg = Msg::default();
        // msg.sender = Some(Address::random());
        let block = Block::default();
        let msg = a.graph.add_node(Node::Msg(msg)).into();
        let block = a.graph.add_node(Node::Block(block)).into();
        a.msg = msg;
        a.block = block;
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
    fn msg(&mut self) -> MsgNode {
        self.msg
    }

    fn block(&mut self) -> BlockNode {
        self.block
    }

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
    fn user_types(&self) -> &HashMap<String, NodeIdx> {
        &self.user_types
    }
    fn user_types_mut(&mut self) -> &mut HashMap<String, NodeIdx> {
        &mut self.user_types
    }

    fn parse_expr(&mut self, expr: &Expression) -> NodeIdx {
        use Expression::*;
        // println!("top level expr: {:?}", expr);
        match expr {
            Type(_loc, ty) => {
                if let Some(builtin) = Builtin::try_from_ty(ty.clone(), self) {
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
                    let dyn_b = Builtin::Array(var_type);
                    if let Some(idx) = self.builtins.get(&dyn_b) {
                        *idx
                    } else {
                        let idx = self.add_node(Node::Builtin(dyn_b.clone()));
                        self.builtins.insert(dyn_b, idx);
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
    pub fn parse(
        &mut self,
        src: &str,
    ) -> (
        Option<NodeIdx>,
        Vec<(Option<NodeIdx>, String, String, usize)>,
    ) {
        let file_no = self.file_no;
        let mut imported = vec![];
        match solang_parser::parse(src, file_no) {
            Ok((source_unit, _comments)) => {
                let parent = self.add_node(Node::SourceUnit(file_no));
                let funcs = self.parse_source_unit(source_unit, file_no, parent, &mut imported);
                funcs.iter().for_each(|func| {
                    // add params now that parsing is done
                    func.set_params_and_ret(self);
                    func.set_modifiers(self);
                    let name = func.name(self);
                    if let Some(user_ty_node) = self.user_types.get(&name).cloned() {
                        let underlying = func.underlying(self).clone();
                        let unresolved = self.node_mut(user_ty_node);
                        *unresolved = Node::Function(underlying);
                    } else {
                        self.user_types
                            .insert(name.to_string(), NodeIdx::from(*func));
                    }
                });

                funcs.into_iter().for_each(|func| {
                    if let Some(body) = &func.underlying(self).body.clone() {
                        self.parse_ctx_statement(body, false, Some(func));
                    }
                });

                (Some(parent), imported)
            }
            Err(e) => panic!("FAIL to parse, {e:?}"),
        }
    }

    pub fn parse_source_unit(
        &mut self,
        source_unit: SourceUnit,
        file_no: usize,
        parent: NodeIdx,
        imported: &mut Vec<(Option<NodeIdx>, String, String, usize)>,
    ) -> Vec<FunctionNode> {
        let mut all_funcs = vec![];
        source_unit
            .0
            .iter()
            .enumerate()
            .for_each(|(unit_part, source_unit_part)| {
                let (_sup, funcs) = self.parse_source_unit_part(
                    source_unit_part,
                    file_no,
                    unit_part,
                    parent,
                    imported,
                );
                all_funcs.extend(funcs);
            });
        all_funcs
    }

    pub fn parse_source_unit_part(
        &mut self,
        sup: &SourceUnitPart,
        file_no: usize,
        unit_part: usize,
        parent: NodeIdx,
        imported: &mut Vec<(Option<NodeIdx>, String, String, usize)>,
    ) -> (NodeIdx, Vec<FunctionNode>) {
        use SourceUnitPart::*;

        let sup_node = self.add_node(Node::SourceUnitPart(file_no, unit_part));
        self.add_edge(sup_node, parent, Edge::Part);

        let mut func_nodes = vec![];

        match sup {
            ContractDefinition(def) => {
                let (node, funcs) = self.parse_contract_def(def, imported);
                self.add_edge(node, sup_node, Edge::Contract);
                func_nodes.extend(funcs);
            }
            StructDefinition(def) => {
                let node = self.parse_struct_def(def);
                self.add_edge(node, sup_node, Edge::Struct);
            }
            EnumDefinition(def) => {
                let node = self.parse_enum_def(def);
                self.add_edge(node, sup_node, Edge::Enum);
            }
            ErrorDefinition(def) => {
                let node = self.parse_err_def(def);
                self.add_edge(node, sup_node, Edge::Error);
            }
            VariableDefinition(def) => {
                let (node, maybe_func) = self.parse_var_def(def, false);
                if let Some(func) = maybe_func {
                    func_nodes.push(self.handle_func(func, None));
                }
                self.add_edge(node, sup_node, Edge::Var);
            }
            FunctionDefinition(def) => {
                let node = self.parse_func_def(def, None);
                func_nodes.push(node);
                self.add_edge(node, sup_node, Edge::Func);
            }
            TypeDefinition(def) => {
                let node = self.parse_ty_def(def);
                self.add_edge(node, sup_node, Edge::Ty);
            }
            EventDefinition(_def) => todo!(),
            Annotation(_anno) => todo!(),
            Using(_using) => todo!(),
            StraySemicolon(_loc) => todo!(),
            PragmaDirective(_, _, _) => {}
            ImportDirective(import) => imported.extend(self.parse_import(import)),
        }
        (sup_node, func_nodes)
    }

    pub fn parse_import(
        &mut self,
        import: &Import,
    ) -> Vec<(Option<NodeIdx>, String, String, usize)> {
        match import {
            Import::Plain(path, _) => {
                // println!("path: {:?}", path);
                let sol = fs::read_to_string(path.string.clone()).unwrap_or_else(|_| {
                    panic!("Could not find file for dependency: {:?}", path.string)
                });
                self.file_no += 1;
                let file_no = self.file_no;
                let (maybe_entry, mut inner_sources) = self.parse(&sol);
                inner_sources.push((maybe_entry, path.string.clone(), sol.to_string(), file_no));
                inner_sources
            }
            Import::Rename(path, elems, _) => {
                println!(
                    "path: {:?}, elems: {:?}, curr: {:?}",
                    path,
                    elems,
                    std::env::current_dir()
                );
                let sol = fs::read_to_string(path.string.clone()).unwrap_or_else(|_| {
                    panic!("Could not find file for dependency: {:?}", path.string)
                });
                self.file_no += 1;
                let file_no = self.file_no;
                let (maybe_entry, mut inner_sources) = self.parse(&sol);
                inner_sources.push((maybe_entry, path.string.clone(), sol.to_string(), file_no));
                inner_sources
            }
            e => todo!("import {:?}", e),
        }
    }

    pub fn parse_contract_def(
        &mut self,
        contract_def: &ContractDefinition,
        imports: &[(Option<NodeIdx>, String, String, usize)],
    ) -> (ContractNode, Vec<FunctionNode>) {
        use ContractPart::*;

        let contract = Contract::from_w_imports(contract_def.clone(), imports, self);
        let inherits = contract.inherits.clone();
        let con_node = ContractNode(self.add_node(contract).index());
        inherits.iter().for_each(|contract_node| {
            self.add_edge(*contract_node, con_node, Edge::InheritedContract);
        });

        let mut func_nodes = vec![];
        contract_def.parts.iter().for_each(|cpart| match cpart {
            StructDefinition(def) => {
                let node = self.parse_struct_def(def);
                self.add_edge(node, con_node, Edge::Struct);
            }
            EnumDefinition(def) => {
                let node = self.parse_enum_def(def);
                self.add_edge(node, con_node, Edge::Enum);
            }
            ErrorDefinition(def) => {
                let node = self.parse_err_def(def);
                self.add_edge(node, con_node, Edge::Error);
            }
            VariableDefinition(def) => {
                let (node, maybe_func) = self.parse_var_def(def, true);
                if let Some(func) = maybe_func {
                    func_nodes.push(self.handle_func(func, Some(con_node)));
                }
                self.add_edge(node, con_node, Edge::Var);
            }
            FunctionDefinition(def) => {
                let node = self.parse_func_def(def, Some(con_node));
                func_nodes.push(node);
            }
            TypeDefinition(def) => {
                let node = self.parse_ty_def(def);
                self.add_edge(node, con_node, Edge::Ty);
            }
            EventDefinition(_def) => {}
            Annotation(_anno) => todo!(),
            Using(_using) => todo!(),
            StraySemicolon(_loc) => todo!(),
        });
        self.user_types
            .insert(con_node.name(self), con_node.0.into());
        (con_node, func_nodes)
    }

    pub fn parse_enum_def(&mut self, enum_def: &EnumDefinition) -> EnumNode {
        let enu = Enum::from(enum_def.clone());
        let name = enu.name.clone().expect("Enum was not named").name;

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

    pub fn parse_func_def(
        &mut self,
        func_def: &FunctionDefinition,
        con_node: Option<ContractNode>,
    ) -> FunctionNode {
        let func = Function::from(func_def.clone());
        self.handle_func(func, con_node)
    }

    pub fn handle_func(&mut self, func: Function, con_node: Option<ContractNode>) -> FunctionNode {
        match func.ty {
            FunctionTy::Constructor => {
                let node = self.add_node(func);
                let func_node = node.into();

                if let Some(con_node) = con_node {
                    self.add_edge(node, con_node, Edge::Constructor);
                }
                func_node
            }
            FunctionTy::Fallback => {
                let node = self.add_node(func);
                let func_node = node.into();

                if let Some(con_node) = con_node {
                    self.add_edge(node, con_node, Edge::FallbackFunc);
                }

                func_node
            }
            FunctionTy::Receive => {
                // receive function cannot have input/output
                let node = self.add_node(func);
                if let Some(con_node) = con_node {
                    self.add_edge(node, con_node, Edge::ReceiveFunc);
                }
                FunctionNode::from(node)
            }
            FunctionTy::Function => {
                let fn_node = self.add_node(func);
                if let Some(con_node) = con_node {
                    self.add_edge(fn_node, con_node, Edge::Func);
                }
                fn_node.into()
            }
            FunctionTy::Modifier => {
                let fn_node = self.add_node(func);
                if let Some(con_node) = con_node {
                    self.add_edge(fn_node, con_node, Edge::Modifier);
                }
                fn_node.into()
            }
        }
    }

    // fn named_fn_internal(&mut self, func: Function, func_def: &FunctionDefinition) -> FunctionNode {
    // let name = func
    //     .name
    //     .as_ref()
    //     .expect("Function was not named")
    //     .name
    //     .clone();
    // let func_node: FunctionNode =
    //     if let Some(user_ty_node) = self.user_types.get(&name).cloned() {
    //         let unresolved = self.node_mut(user_ty_node);
    //         *unresolved = Node::Function(func);
    //         user_ty_node.into()
    //     } else {
    //         let node = self.add_node(func);
    //         self.user_types.insert(name.to_string(), node);
    //         node.into()
    //     };

    // func_def.params.iter().for_each(|(_loc, input)| {
    //     if let Some(input) = input {
    //         let param = FunctionParam::new(self, input.clone());
    //         let input_node = self.add_node(param);
    //         self.add_edge(input_node, func_node, Edge::FunctionParam);
    //     }
    // });
    // func_def.returns.iter().for_each(|(_loc, output)| {
    //     if let Some(output) = output {
    //         let ret = FunctionReturn::new(self, output.clone());
    //         let output_node = self.add_node(ret);
    //         self.add_edge(output_node, func_node, Edge::FunctionReturn);
    //     }
    // });

    // func_node
    // }

    pub fn parse_var_def(
        &mut self,
        var_def: &VariableDefinition,
        in_contract: bool,
    ) -> (VarNode, Option<Function>) {
        let var = Var::new(self, var_def.clone(), in_contract);
        let mut func = None;
        if var.is_public() {
            func = Some(Function::from(var_def.clone()));
        }
        let var_node = VarNode::from(self.add_node(var));
        self.user_types.insert(var_node.name(self), var_node.into());
        (var_node, func)
    }

    pub fn parse_ty_def(&mut self, ty_def: &TypeDefinition) -> TyNode {
        let ty = Ty::new(self, ty_def.clone());
        TyNode(self.add_node(ty).index())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyzers::ReportConfig;
    use crate::context::analyzers::bounds::BoundAnalyzer;
    use shared::context::{ContextEdge, ContextNode};

    #[test]
    fn it_works() {
        let sol = r###"
contract Storage {
    uint256 c;

    function b5(uint64 x) public  {
        address a = address(uint160(1));

        int256 b = int256(1);
        b -= 10000;

        c = uint256(int256(uint256(x)) - b);
        c += 10 + 20;

    }
}"###;
        let mut analyzer = Analyzer::default();
        let t0 = std::time::Instant::now();
        let (maybe_entry, _sources) = analyzer.parse(sol);
        let entry = maybe_entry.unwrap();
        let file_mapping = vec![(0usize, "test.sol".to_string())].into_iter().collect();
        println!("parse time: {:?}", t0.elapsed().as_nanos());
        println!("{}", analyzer.dot_str_no_tmps_for_ctx("b5".to_string()));
        let contexts = analyzer.search_children(entry, &crate::Edge::Context(ContextEdge::Context));
        for context in contexts.into_iter() {
            let config = ReportConfig {
                eval_bounds: true,
                simplify_bounds: false,
                show_tmps: false,
                show_consts: true,
                show_subctxs: true,
                show_initial_bounds: true,
                show_all_lines: true,
            };
            let ctx = ContextNode::from(context);

            let analysis =
                analyzer.bounds_for_var(None, &file_mapping, ctx, "a".to_string(), config, false);
            println!("{analysis:#?}");
            // analysis.print_reports(("test.sol".to_string(), &sol), &analyzer);
        }
        println!("total analyze time: {:?}", t0.elapsed().as_nanos());
    }
}
