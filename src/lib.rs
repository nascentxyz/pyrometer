use crate::analyzers::LocStrSpan;
use crate::context::exprs::IntoExprErr;
use crate::exprs::ExprErr;
use ariadne::Source;
use ethers_core::types::U256;
use shared::analyzer::*;
use shared::context::ContextNode;
use shared::context::ExprRet;
use shared::context::{Context, ContextEdge};
use shared::nodes::*;
use shared::{Edge, Node, NodeIdx};
use solang_parser::diagnostics::Diagnostic;
use solang_parser::helpers::CodeLocation;
use solang_parser::pt::Identifier;
use solang_parser::pt::Import;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::ffi::OsString;
use std::path::Path;

use solang_parser::pt::{
    ContractDefinition, ContractPart, EnumDefinition, ErrorDefinition, Expression,
    FunctionDefinition, FunctionTy, SourceUnit, SourceUnitPart, StructDefinition, TypeDefinition,
    Using, UsingList, VariableDefinition,
};
use std::path::PathBuf;
use std::{collections::HashMap, fs};

use ariadne::{Cache, Color, Config, Fmt, Label, Report, ReportKind, Span};
use petgraph::{graph::*, Directed};

mod builtin_fns;

pub mod context;
pub mod tracer;
// pub mod range;
use context::*;
pub use shared;

#[derive(Debug, Clone)]
pub struct Analyzer {
    pub root: PathBuf,
    pub remappings: Vec<(String, String)>,
    pub imported_srcs: BTreeMap<OsString, Option<NodeIdx>>,
    pub final_pass_items: Vec<(
        Vec<FunctionNode>,
        Vec<(Using, NodeIdx)>,
        Vec<(ContractNode, Vec<String>)>,
    )>,
    pub file_no: usize,
    pub msg: MsgNode,
    pub block: BlockNode,
    pub graph: Graph<Node, Edge, Directed, usize>,
    pub entry: NodeIdx,
    pub builtins: HashMap<Builtin, NodeIdx>,
    pub user_types: HashMap<String, NodeIdx>,
    pub builtin_fns: HashMap<String, Function>,
    pub builtin_fn_nodes: HashMap<String, NodeIdx>,
    pub builtin_fn_inputs: HashMap<String, (Vec<FunctionParam>, Vec<FunctionReturn>)>,
    pub expr_errs: Vec<ExprErr>,
    pub max_depth: usize,
    /// The maximum number of forks throughout the lifetime of the analysis.
    pub max_width: usize,
    pub parse_fn: FunctionNode,
}

impl Default for Analyzer {
    fn default() -> Self {
        let mut a = Self {
            root: Default::default(),
            remappings: Default::default(),
            imported_srcs: Default::default(),
            final_pass_items: Default::default(),
            file_no: 0,
            msg: MsgNode(0),
            block: BlockNode(0),
            graph: Default::default(),
            entry: NodeIndex::from(0),
            builtins: Default::default(),
            user_types: Default::default(),
            builtin_fns: builtin_fns::builtin_fns(),
            builtin_fn_nodes: Default::default(),
            builtin_fn_inputs: Default::default(),
            expr_errs: Default::default(),
            max_depth: 1024,
            max_width: 2_i32.pow(14) as usize,
            parse_fn: NodeIdx::from(0).into(),
        };
        a.builtin_fn_inputs = builtin_fns::builtin_fns_inputs(&mut a);

        let msg = Msg::default();
        let block = Block::default();
        let msg = a.graph.add_node(Node::Msg(msg)).into();
        let block = a.graph.add_node(Node::Block(block)).into();
        a.msg = msg;
        a.block = block;
        a.entry = a.add_node(Node::Entry);
        let pf = Function {
            name: Some(Identifier {
                loc: solang_parser::pt::Loc::Implicit,
                name: "__parser_fn__".into(),
            }),
            ..Default::default()
        };
        let parser_fn = FunctionNode::from(a.add_node(pf));
        a.add_edge(parser_fn, a.entry, Edge::Func);
        a.parse_fn = parser_fn;
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
    type ExprErr = ExprErr;

    fn builtin_fn_nodes(&self) -> &HashMap<String, NodeIdx> {
        &self.builtin_fn_nodes
    }

    fn builtin_fn_nodes_mut(&mut self) -> &mut HashMap<String, NodeIdx> {
        &mut self.builtin_fn_nodes
    }

    fn max_depth(&self) -> usize {
        self.max_depth
    }

    fn max_width(&self) -> usize {
        self.max_width
    }

    fn add_expr_err(&mut self, err: ExprErr) {
        if !self.expr_errs.contains(&err) {
            self.expr_errs.push(err);
        }
    }

    fn expr_errs(&self) -> Vec<ExprErr> {
        self.expr_errs.clone()
    }

    fn entry(&self) -> NodeIdx {
        self.entry
    }

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
        println!("top level expr: {:?}", expr);

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
                } else if let Some(idx) = self.complicated_parse(expr) {
                    self.add_if_err(idx.expect_single().into_expr_err(expr.loc()))
                        .unwrap_or(0.into())
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
                    inner_ty
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
            NumberLiteral(_loc, int, exp, _unit) => {
                let int = U256::from_dec_str(int).unwrap();
                let val = if !exp.is_empty() {
                    let exp = U256::from_dec_str(exp).unwrap();
                    int.pow(exp)
                } else {
                    int
                };
                self.add_node(Node::Concrete(Concrete::Uint(256, val)))
            }
            _ => {
                if let Some(idx) = self.complicated_parse(expr) {
                    self.add_if_err(idx.expect_single().into_expr_err(expr.loc()))
                        .unwrap_or(0.into())
                } else {
                    0.into()
                }
            }
        }
    }
}

impl Analyzer {
    pub fn complicated_parse(&mut self, expr: &Expression) -> Option<ExprRet> {
        let dummy_ctx = Context::new(
            self.parse_fn,
            "__parser_fn__".to_string(),
            solang_parser::pt::Loc::Implicit,
        );
        let ctx = ContextNode::from(self.add_node(Node::Context(dummy_ctx)));
        self.add_edge(ctx, self.entry(), Edge::Context(ContextEdge::Context));
        let res = self.parse_ctx_expr(expr, ctx);
        self.add_if_err(res);
        let res = ctx
            .pop_expr_latest(expr.loc(), self)
            .into_expr_err(expr.loc());
        let res = self.add_if_err(res);
        res?
    }
    pub fn set_remappings_and_root(&mut self, remappings_path: String) {
        self.root = PathBuf::from(&remappings_path)
            .parent()
            .unwrap()
            .to_path_buf();
        let remappings_file = fs::read_to_string(remappings_path)
            .map_err(|err| err.to_string())
            .expect("Remappings file not found");

        self.remappings = remappings_file
            .lines()
            .map(|x| x.trim())
            .filter(|x| !x.is_empty())
            .map(|x| x.split_once('=').expect("Invalid remapping"))
            .map(|(name, path)| (name.to_owned(), path.to_owned()))
            .collect();
    }

    pub fn print_errors(
        &self,
        file_mapping: &'_ BTreeMap<usize, String>,
        mut src: &mut impl Cache<String>,
    ) {
        if self.expr_errs.is_empty() {
        } else {
            self.expr_errs.iter().for_each(|error| {
                let str_span = LocStrSpan::new(file_mapping, error.loc());
                let report = Report::build(ReportKind::Error, str_span.source(), str_span.start())
                    .with_message(error.report_msg())
                    .with_config(
                        Config::default()
                            .with_cross_gap(false)
                            .with_underlines(true)
                            .with_tab_width(4),
                    )
                    .with_label(
                        Label::new(str_span)
                            .with_color(Color::Red)
                            .with_message(format!("{}", error.msg().fg(Color::Red))),
                    );
                report.finish().print(&mut src).unwrap();
            });
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse(
        &mut self,
        src: &str,
        current_path: &Path,
        entry: bool,
    ) -> (
        Option<NodeIdx>,
        Vec<(Option<NodeIdx>, String, String, usize)>,
    ) {
        // tracing::trace!("parsing: {:?}", current_path);
        let file_no = self.file_no;
        let mut imported = vec![];
        match solang_parser::parse(src, file_no) {
            Ok((source_unit, _comments)) => {
                let parent = self.add_node(Node::SourceUnit(file_no));
                self.add_edge(parent, self.entry, Edge::Source);
                let final_pass_part = self.parse_source_unit(
                    source_unit,
                    file_no,
                    parent,
                    &mut imported,
                    current_path,
                );
                self.final_pass_items.push(final_pass_part);
                if entry {
                    self.final_pass();
                }

                (Some(parent), imported)
            }
            Err(diagnostics) => {
                print_diagnostics_report(src, current_path, diagnostics).unwrap();
                panic!("Failed to parse Solidity code for {current_path:?}.");
            }
        }
    }

    pub fn final_pass(&mut self) {
        let elems = self.final_pass_items.clone();
        elems.iter().for_each(|(funcs, usings, inherits)| {
            inherits.iter().for_each(|(contract, inherits)| {
                contract.inherit(inherits.to_vec(), self);
            });
            usings.iter().for_each(|(using, scope_node)| {
                self.parse_using(using, *scope_node);
            });
            funcs.iter().for_each(|func| {
                // add params now that parsing is done
                func.set_params_and_ret(self).unwrap();
            });
        });

        elems.into_iter().for_each(|(funcs, _usings, _inherits)| {
            funcs.into_iter().for_each(|func| {
                if let Some(body) = &func.underlying(self).unwrap().body.clone() {
                    self.parse_ctx_statement(body, false, Some(func));
                }
            });
        });
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_source_unit(
        &mut self,
        source_unit: SourceUnit,
        file_no: usize,
        parent: NodeIdx,
        imported: &mut Vec<(Option<NodeIdx>, String, String, usize)>,
        current_path: &Path,
    ) -> (
        Vec<FunctionNode>,
        Vec<(Using, NodeIdx)>,
        Vec<(ContractNode, Vec<String>)>,
    ) {
        let mut all_funcs = vec![];
        let mut all_usings = vec![];
        let mut all_inherits = vec![];
        source_unit
            .0
            .iter()
            .enumerate()
            .for_each(|(unit_part, source_unit_part)| {
                let (_sup, funcs, usings, inherits) = self.parse_source_unit_part(
                    source_unit_part,
                    file_no,
                    unit_part,
                    parent,
                    imported,
                    current_path,
                );
                all_funcs.extend(funcs);
                all_usings.extend(usings);
                all_inherits.extend(inherits);
            });
        (all_funcs, all_usings, all_inherits)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_source_unit_part(
        &mut self,
        sup: &SourceUnitPart,
        file_no: usize,
        unit_part: usize,
        parent: NodeIdx,
        imported: &mut Vec<(Option<NodeIdx>, String, String, usize)>,
        current_path: &Path,
    ) -> (
        NodeIdx,
        Vec<FunctionNode>,
        Vec<(Using, NodeIdx)>,
        Vec<(ContractNode, Vec<String>)>,
    ) {
        use SourceUnitPart::*;

        let sup_node = self.add_node(Node::SourceUnitPart(file_no, unit_part));
        self.add_edge(sup_node, parent, Edge::Part);

        let mut func_nodes = vec![];
        let mut usings = vec![];
        let mut inherits = vec![];

        match sup {
            ContractDefinition(def) => {
                let (node, funcs, con_usings, unhandled_inherits) =
                    self.parse_contract_def(def, parent, imported);
                self.add_edge(node, sup_node, Edge::Contract);
                func_nodes.extend(funcs);
                usings.extend(con_usings);
                inherits.push((node, unhandled_inherits));
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
            Using(using) => usings.push((*using.clone(), parent)),
            StraySemicolon(_loc) => todo!(),
            PragmaDirective(_, _, _) => {}
            ImportDirective(import) => {
                imported.extend(self.parse_import(import, current_path, parent))
            }
        }
        (sup_node, func_nodes, usings, inherits)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_import(
        &mut self,
        import: &Import,
        current_path: &Path,
        parent: NodeIdx,
    ) -> Vec<(Option<NodeIdx>, String, String, usize)> {
        match import {
            Import::Plain(import_path, _) => {
                tracing::trace!("parse_import, path: {:?}", import_path);
                let remapping = self
                    .remappings
                    .iter()
                    .find(|x| import_path.string.starts_with(&x.0));

                let remapped = if let Some((name, path)) = remapping {
                    self.root.join(path).join(
                        import_path
                            .string
                            .replacen(name, "", 1)
                            .trim_start_matches('/'),
                    )
                } else {
                    current_path
                        .parent()
                        .unwrap()
                        .join(import_path.string.clone())
                };

                let canonical = fs::canonicalize(&remapped)
                    .unwrap_or_else(|_| panic!(
                            "Could not find file: {remapped:?}{}",
                            if self.remappings.is_empty() {
                                ". It looks like you didn't pass in any remappings. Try adding the `--remappings ./path/to/remappings.txt` to the command line input"
                            } else { "" }
                        )
                    );
                let canonical_str_path = canonical.as_os_str();
                if let Some(other_entry) = self.imported_srcs.get(canonical_str_path) {
                    if let Some(o_e) = other_entry {
                        self.add_edge(*o_e, parent, Edge::Import);
                    }
                    return vec![];
                }

                let sol = fs::read_to_string(&canonical).unwrap_or_else(|_| {
                    panic!(
                        "Could not find file for dependency: {canonical:?}{}",
                        if self.remappings.is_empty() {
                            ". It looks like you didn't pass in any remappings. Try adding the `--remappings ./path/to/remappings.txt` to the command line input (where `remappings.txt` is the output of `forge remappings > remappings.txt`)"
                        } else { "" }
                    )
                });
                self.file_no += 1;
                let file_no = self.file_no;
                // breaks recursion issues
                self.imported_srcs.insert(canonical_str_path.into(), None);
                let (maybe_entry, mut inner_sources) = self.parse(&sol, &remapped, false);
                self.imported_srcs
                    .insert(canonical_str_path.into(), maybe_entry);
                if let Some(other_entry) = maybe_entry {
                    self.add_edge(other_entry, parent, Edge::Import);
                }

                inner_sources.push((
                    maybe_entry,
                    remapped.to_str().unwrap().to_owned(),
                    sol.to_string(),
                    file_no,
                ));
                inner_sources
            }
            Import::Rename(import_path, _elems, _) => {
                tracing::trace!("parse_import, path: {:?}, Rename", import_path);
                let remapping = self
                    .remappings
                    .iter()
                    .find(|x| import_path.string.starts_with(&x.0));

                let remapped = if let Some((name, path)) = remapping {
                    self.root.join(path).join(
                        import_path
                            .string
                            .replacen(name, "", 1)
                            .trim_start_matches('/'),
                    )
                } else {
                    current_path
                        .parent()
                        .unwrap()
                        .join(import_path.string.clone())
                };

                let canonical = fs::canonicalize(&remapped).unwrap_or_else(|_| panic!(
                        "Could not find file: {remapped:?}{}",
                        if self.remappings.is_empty() {
                            ". It looks like you didn't pass in any remappings. Try adding the `--remappings ./path/to/remappings.txt` to the command line input"
                        } else { "" }
                    )
                );
                let canonical_str_path = canonical.as_os_str();
                if let Some(other_entry) = self.imported_srcs.get(canonical_str_path) {
                    if let Some(o_e) = other_entry {
                        self.add_edge(*o_e, parent, Edge::Import);
                    }
                    return vec![];
                }

                let sol = fs::read_to_string(&canonical).unwrap_or_else(|_| {
                    panic!(
                        "Could not find file for dependency: {canonical:?}{}",
                        if self.remappings.is_empty() {
                            ". It looks like you didn't pass in any remappings. Try adding the `--remappings ./path/to/remappings.txt` to the command line input"
                        } else { "" }
                    )
                });
                self.file_no += 1;
                let file_no = self.file_no;

                // breaks recursion issues
                self.imported_srcs.insert(canonical_str_path.into(), None);
                let (maybe_entry, mut inner_sources) = self.parse(&sol, &remapped, false);
                self.imported_srcs
                    .insert(canonical_str_path.into(), maybe_entry);
                if let Some(other_entry) = maybe_entry {
                    self.add_edge(other_entry, parent, Edge::Import);
                }

                inner_sources.push((
                    maybe_entry,
                    remapped.to_str().unwrap().to_owned(),
                    sol.to_string(),
                    file_no,
                ));
                inner_sources
            }
            e => todo!("import {:?}", e),
        }
    }

    // #[tracing::instrument(name = "parse_contract_def", skip_all, fields(name = format!("{:?}", contract_def.name)))]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_contract_def(
        &mut self,
        contract_def: &ContractDefinition,
        source: NodeIdx,
        imports: &[(Option<NodeIdx>, String, String, usize)],
    ) -> (
        ContractNode,
        Vec<FunctionNode>,
        Vec<(Using, NodeIdx)>,
        Vec<String>,
    ) {
        tracing::trace!(
            "Parsing contract {}",
            if let Some(ident) = &contract_def.name {
                ident.name.clone()
            } else {
                "interface".to_string()
            }
        );
        use ContractPart::*;

        let (contract, unhandled_inherits) =
            Contract::from_w_imports(contract_def.clone(), source, imports, self);
        let inherits = contract.inherits.clone();
        let con_node = ContractNode(self.add_node(contract).index());
        inherits.iter().for_each(|contract_node| {
            self.add_edge(*contract_node, con_node, Edge::InheritedContract);
        });
        let mut usings = vec![];

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
            Using(using) => usings.push((*using.clone(), con_node.0.into())),
            StraySemicolon(_loc) => todo!(),
        });
        self.user_types
            .insert(con_node.name(self).unwrap(), con_node.0.into());
        (con_node, func_nodes, usings, unhandled_inherits)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_using(&mut self, using_def: &Using, scope_node: NodeIdx) {
        tracing::trace!("Parsing \"using\" {:?}", using_def);
        let ty_idx = self.parse_expr(
            &using_def
                .ty
                .clone()
                .expect("No type defined for using statement"),
        );
        match &using_def.list {
            UsingList::Library(ident_paths) => {
                ident_paths.identifiers.iter().for_each(|ident| {
                    if let Some(hopefully_contract) = self.user_types.get(&ident.name) {
                        self.add_edge(
                            *hopefully_contract,
                            ty_idx,
                            Edge::LibraryContract(scope_node),
                        );
                    } else {
                        panic!("Cannot find library contract {}", ident.name);
                    }
                });
            }
            UsingList::Functions(vec_ident_paths) => {
                vec_ident_paths.iter().for_each(|ident_paths| {
                    if ident_paths.path.identifiers.len() == 2 {
                        if let Some(hopefully_contract) =
                            self.user_types.get(&ident_paths.path.identifiers[0].name)
                        {
                            if let Some(func) = ContractNode::from(*hopefully_contract)
                                .funcs(self)
                                .iter()
                                .find(|func| {
                                    func.name(self)
                                        .unwrap()
                                        .starts_with(&ident_paths.path.identifiers[1].name)
                                })
                            {
                                self.add_edge(*func, ty_idx, Edge::LibraryFunction(scope_node));
                            } else {
                                panic!(
                                    "Cannot find library function {}.{}",
                                    ident_paths.path.identifiers[0].name,
                                    ident_paths.path.identifiers[1].name
                                );
                            }
                        } else {
                            panic!(
                                "Cannot find library contract {}",
                                ident_paths.path.identifiers[0].name
                            );
                        }
                    } else {
                        // looking for free floating function
                        let funcs = match self.node(scope_node) {
                            Node::Contract(_) => self.search_children(
                                ContractNode::from(scope_node).associated_source(self),
                                &Edge::Func,
                            ),
                            Node::SourceUnit(..) => self.search_children(scope_node, &Edge::Func),
                            _ => unreachable!(),
                        };
                        if let Some(func) = funcs.iter().find(|func| {
                            FunctionNode::from(**func)
                                .name(self)
                                .unwrap()
                                .starts_with(&ident_paths.path.identifiers[0].name)
                        }) {
                            self.add_edge(*func, ty_idx, Edge::LibraryFunction(scope_node));
                        } else {
                            panic!(
                                "Cannot find library function {}",
                                ident_paths.path.identifiers[0].name
                            );
                        }
                    }
                });
            }
            UsingList::Error => todo!(),
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_enum_def(&mut self, enum_def: &EnumDefinition) -> EnumNode {
        tracing::trace!("Parsing enum {:?}", enum_def);
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

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_struct_def(&mut self, struct_def: &StructDefinition) -> StructNode {
        let strukt = Struct::from(struct_def.clone());

        let name = strukt.name.clone().expect("Struct was not named").name;
        tracing::trace!("Parsing struct {}", name);

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

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_err_def(&mut self, err_def: &ErrorDefinition) -> ErrorNode {
        tracing::trace!("Parsing error {:?}", err_def);
        let err_node = ErrorNode(self.add_node(Error::from(err_def.clone())).index());
        err_def.fields.iter().for_each(|field| {
            let param = ErrorParam::new(self, field.clone());
            let field_node = self.add_node(param);
            self.add_edge(field_node, err_node, Edge::ErrorParam);
        });
        err_node
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_func_def(
        &mut self,
        func_def: &FunctionDefinition,
        con_node: Option<ContractNode>,
    ) -> FunctionNode {
        let func = Function::from(func_def.clone());
        tracing::trace!(
            "Parsing function {:?}",
            func.name
                .clone()
                .unwrap_or_else(|| solang_parser::pt::Identifier {
                    loc: solang_parser::pt::Loc::Implicit,
                    name: "".to_string()
                })
                .name
        );
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
        self.user_types
            .insert(var_node.name(self).unwrap(), var_node.into());
        (var_node, func)
    }

    pub fn parse_ty_def(&mut self, ty_def: &TypeDefinition) -> TyNode {
        let ty = Ty::new(self, ty_def.clone());
        TyNode(self.add_node(ty).index())
    }
}

/// Print the report of parser's diagnostics
pub fn print_diagnostics_report(
    content: &str,
    path: &Path,
    diagnostics: Vec<Diagnostic>,
) -> std::io::Result<()> {
    let filename = path.file_name().unwrap().to_string_lossy().to_string();
    for diag in diagnostics {
        let (start, end) = (diag.loc.start(), diag.loc.end());
        let mut report = Report::build(ReportKind::Error, &filename, start)
            .with_message(format!("{:?}", diag.ty))
            .with_label(
                Label::new((&filename, start..end))
                    .with_color(Color::Red)
                    .with_message(format!("{}", diag.message.fg(Color::Red))),
            );

        for note in diag.notes {
            report = report.with_note(note.message);
        }

        report.finish().print((&filename, Source::from(content)))?;
    }
    Ok(())
}
