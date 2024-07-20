use crate::builtin_fns;
use analyzers::LocStrSpan;
use graph::elem::Elem;
use graph::{nodes::*, ContextEdge, Edge, Node, VarType};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use shared::{AnalyzerLike, ApplyStats, GraphLike, NodeIdx, Search};
use shared::{ExprErr, ExprFlag, FlatExpr, IntoExprErr, RangeArena, USE_DEBUG_SITE};
use solc_expressions::Flatten;
use tokio::runtime::Runtime;
use tracing::{error, trace, warn};

use ahash::AHashMap;
use ariadne::{Cache, Color, Config, Fmt, Label, Report, ReportKind, Source, Span};
use petgraph::{graph::*, Directed};
use serde_json::Value;
use solang_parser::{
    diagnostics::Diagnostic,
    helpers::CodeLocation,
    pt::{
        ContractDefinition, ContractPart, EnumDefinition, ErrorDefinition, Expression,
        FunctionDefinition, FunctionTy, Identifier, Import, SourceUnit, SourceUnitPart,
        StructDefinition, TypeDefinition, Using, UsingList, VariableDefinition,
    },
};

use std::collections::BTreeSet;
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

/// A path to either a single solidity file or a Solc Standard JSON file
#[derive(Debug, Clone)]
pub enum Root {
    /// A path to a single solidity file
    SolidityFile(PathBuf),
    /// A path to a Solc Standard JSON file
    SolcJSON(PathBuf),
    /// A path to a directory containing a remappings file
    RemappingsDirectory(PathBuf),
}

impl Default for Root {
    fn default() -> Self {
        Root::SolidityFile(PathBuf::new())
    }
}

/// An intermediate representation of a path to a solidity source
///
/// This is done so that any source can be fetched from the filesystem again if needed
#[derive(Debug, Clone, Ord, PartialEq, PartialOrd, Eq)]
pub enum SourcePath {
    /// A path to a solidity file
    SolidityFile(PathBuf),
    /// A path to a Solc JSON file and the path within pointing to the solidity source
    SolcJSON(PathBuf, String),
}

impl SourcePath {
    pub fn path_to_solidity_source(&self) -> PathBuf {
        match self {
            SourcePath::SolidityFile(path) => path.clone(),
            SourcePath::SolcJSON(_path_to_json, path) => path.clone().into(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct FinalPassItem {
    pub funcs: Vec<FunctionNode>,
    pub usings: Vec<(Using, NodeIdx)>,
    pub inherits: Vec<(ContractNode, Vec<String>)>,
    pub vars: Vec<(VarNode, NodeIdx)>,
}
impl FinalPassItem {
    pub fn new(
        funcs: Vec<FunctionNode>,
        usings: Vec<(Using, NodeIdx)>,
        inherits: Vec<(ContractNode, Vec<String>)>,
        vars: Vec<(VarNode, NodeIdx)>,
    ) -> Self {
        Self {
            funcs,
            usings,
            inherits,
            vars,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Analyzer {
    /// The root of the path to either the contract or solc json file to be analyzed
    pub root: Root,
    /// Solidity remappings - as would be passed into the solidity compiler
    pub remappings: Vec<(String, String)>,
    /// Solidity sources - tuple of SourcePath, solidity string, file number (None until parsed), and entry node (None until parsed)
    pub sources: Vec<(SourcePath, String, Option<usize>, Option<NodeIdx>)>,
    /// Since we use a staged approach to analysis, we analyze all user types first then go through and patch up any missing or unresolved
    /// parts of a contract (i.e. we parsed a struct which is used as an input to a function signature, we have to know about the struct)
    pub final_pass_items: Vec<FinalPassItem>,
    /// The next file number to use when parsing a new file
    pub file_no: usize,
    /// The index of the current `msg` node
    pub msg: MsgNode,
    /// The index of the current `msg` node
    pub tmp_msg: Option<Msg>,
    /// The index of the current `block` node
    pub block: BlockNode,
    /// The underlying graph holding all of the elements of the contracts
    pub graph: Graph<Node, Edge, Directed, usize>,
    /// Nodes that may have been mutated in some way
    pub dirty_nodes: BTreeSet<NodeIdx>,
    /// The entry node - this is the root of the dag, all relevant things should eventually point back to this (otherwise can be discarded)
    pub entry: NodeIdx,
    /// A mapping of a solidity builtin to the index in the graph
    pub builtins: AHashMap<Builtin, NodeIdx>,
    /// A mapping of a user type's name to the index in the graph (i.e. `struct A` would mapped `A` -> index)
    pub user_types: AHashMap<String, Vec<NodeIdx>>,
    /// A mapping of solidity builtin function to a [Function] struct, i.e. `ecrecover` -> `Function { name: "ecrecover", ..}`
    pub builtin_fns: AHashMap<String, Function>,
    /// A mapping of solidity builtin functions to their indices in the graph
    pub builtin_fn_nodes: AHashMap<String, NodeIdx>,
    /// A mapping of solidity builtin function names to their parameters and returns, i.e. `ecrecover` -> `([hash, r, s, v], [signer])`
    pub builtin_fn_inputs: AHashMap<String, (Vec<FunctionParam>, Vec<FunctionReturn>)>,
    /// Accumulated errors that happened while analyzing
    pub expr_errs: Vec<ExprErr>,
    /// The maximum depth to analyze to (i.e. call depth)
    pub max_depth: usize,
    /// The maximum number of forks throughout the lifetime of the analysis.
    pub max_width: usize,
    /// Dummy function used during parsing to attach contexts to for more complex first-pass parsing (i.e. before `final_pass`)
    pub parse_fn: FunctionNode,
    /// Whether to force a panic on first error encountered
    pub debug_panic: bool,
    /// Per function, a list of functions that are called
    pub fn_calls_fns: BTreeMap<FunctionNode, Vec<FunctionNode>>,

    pub apply_stats: ApplyStats,
    /// An arena of ranges
    pub range_arena: RangeArena<Elem<Concrete>>,
    /// Parsed functions
    pub handled_funcs: Vec<FunctionNode>,
    /// Target Context to debug
    pub minimize_debug: Option<String>,

    pub flattened: Vec<FlatExpr>,
    pub expr_flag: Option<ExprFlag>,
    pub current_asm_block: usize,
    pub debug_stack: bool,
}

impl Default for Analyzer {
    fn default() -> Self {
        let mut a = Self {
            root: Default::default(),
            remappings: Default::default(),
            sources: Default::default(),
            final_pass_items: Default::default(),
            file_no: 0,
            msg: MsgNode(0),
            tmp_msg: None,
            block: BlockNode(0),
            graph: Default::default(),
            dirty_nodes: Default::default(),
            entry: NodeIndex::from(0),
            builtins: Default::default(),
            user_types: Default::default(),
            builtin_fns: builtin_fns::builtin_fns(),
            builtin_fn_nodes: Default::default(),
            builtin_fn_inputs: Default::default(),
            expr_errs: Default::default(),
            max_depth: 200,
            max_width: 2_i32.pow(14) as usize, // 14 splits == 16384 contexts
            parse_fn: NodeIdx::from(0).into(),
            debug_panic: false,
            fn_calls_fns: Default::default(),
            apply_stats: ApplyStats::default(),
            range_arena: RangeArena {
                ranges: vec![Elem::Null],
                map: {
                    let mut map: AHashMap<Elem<Concrete>, usize> = Default::default();
                    map.insert(Elem::Null, 0);
                    map
                },
            },
            handled_funcs: Vec::default(),
            minimize_debug: None,
            flattened: vec![],
            expr_flag: None,
            current_asm_block: 0,
            debug_stack: false,
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
                name: "<parser_fn>".into(),
            }),
            ..Default::default()
        };
        let parser_fn = FunctionNode::from(a.add_node(pf));
        a.add_edge(parser_fn, a.entry, Edge::Func);
        a.parse_fn = parser_fn;
        a
    }
}

impl Analyzer {
    pub fn stats(
        &self,
        duration: std::time::Duration,
        arena: &RangeArena<Elem<Concrete>>,
    ) -> String {
        let num_nodes = self.graph.node_count();
        let num_contracts = self.number_of_contracts();
        let num_funcs = self.number_of_functions();
        let num_vars = self.number_of_variables();
        let num_contexts = self.number_of_contexts();

        vec![
            format!(""),
            format!("          Analyzer stats"),
            format!("====================================="),
            format!(""),
            format!(
                "   Number of nodes: {}, {} nodes/ms",
                num_nodes,
                num_nodes as f64 / duration.as_millis() as f64
            ),
            format!(
                "     Number of Contracts: {}, {} contracts/ms",
                num_contracts,
                num_contracts as f64 / duration.as_millis() as f64
            ),
            format!(
                "     Number of Functions: {}, {} functions/ms",
                num_funcs,
                num_funcs as f64 / duration.as_millis() as f64
            ),
            format!(
                "     Number of Variables: {}, {} variables/ms",
                num_vars,
                num_vars as f64 / duration.as_millis() as f64
            ),
            format!(""),
            format!(
                "   Unique Range Elements: {}",
                arena.ranges.len()
            ),
            format!(""),
            format!(
                "   Number of Contexts: {}, {} contexts/ms",
                num_contexts,
                num_contexts as f64 / duration.as_millis() as f64
            ),
            format!("     Max depth of Contexts: {}", self.max_context_depth()),
            format!("     Max width of Contexts: {}", self.max_context_width()),
            format!(""),
            format!("   Number of applies: {}, {} completed, {} variables reduced", self.apply_stats.total_applies(), self.apply_stats.completed_applies(), self.apply_stats.reduced_vars()),
            format!("      Number of pure applies: {}, {} completed, {} variables reduced", self.apply_stats.total_pure_applies(), self.apply_stats.completed_pure_applies(), self.apply_stats.pure_reduced_vars()),
            format!("           Number of simple pure applies: {}, {} completed, {} variables reduced", self.apply_stats.pure_no_children_applies.num_applies, self.apply_stats.pure_no_children_applies.completed_applies, self.apply_stats.pure_no_children_applies.vars_reduced),
            format!("           Number of children pure applies: {}, {} completed, {} variables reduced", self.apply_stats.pure_children_no_forks_applies.num_applies, self.apply_stats.pure_children_no_forks_applies.completed_applies, self.apply_stats.pure_children_no_forks_applies.vars_reduced),
            format!("           Number of fork children pure applies: {}, {} completed, {} variables reduced", self.apply_stats.pure_children_forks_applies.num_applies, self.apply_stats.pure_children_forks_applies.completed_applies, self.apply_stats.pure_children_forks_applies.vars_reduced),
            format!("      Number of view applies: {}, {} completed, {} variables reduced", self.apply_stats.total_view_applies(), self.apply_stats.completed_view_applies(), self.apply_stats.view_reduced_vars()),
            format!("           Number of simple view applies: {}, {} completed, {} variables reduced", self.apply_stats.view_no_children_applies.num_applies, self.apply_stats.view_no_children_applies.completed_applies, self.apply_stats.view_no_children_applies.vars_reduced),
            format!("           Number of children view applies: {}, {} completed, {} variables reduced", self.apply_stats.view_children_no_forks_applies.num_applies, self.apply_stats.view_children_no_forks_applies.completed_applies, self.apply_stats.view_children_no_forks_applies.vars_reduced),
            format!("           Number of fork children view applies: {}, {} completed, {} variables reduced", self.apply_stats.view_children_forks_applies.num_applies, self.apply_stats.view_children_forks_applies.completed_applies, self.apply_stats.view_children_forks_applies.vars_reduced),
            format!("      Number of mut applies: {}, {} completed, {} variables reduced", self.apply_stats.total_mut_applies(), self.apply_stats.completed_mut_applies(), self.apply_stats.mut_reduced_vars()),
            format!("           Number of simple mut applies: {}, {} completed, {} variables reduced", self.apply_stats.mut_no_children_applies.num_applies, self.apply_stats.mut_no_children_applies.completed_applies, self.apply_stats.mut_no_children_applies.vars_reduced),
            format!("           Number of children mut applies: {}, {} completed, {} variables reduced", self.apply_stats.mut_children_no_forks_applies.num_applies, self.apply_stats.mut_children_no_forks_applies.completed_applies, self.apply_stats.mut_children_no_forks_applies.vars_reduced),
            format!("           Number of fork children mut applies: {}, {} completed, {} variables reduced", self.apply_stats.mut_children_forks_applies.num_applies, self.apply_stats.mut_children_forks_applies.completed_applies, self.apply_stats.mut_children_forks_applies.vars_reduced),
            format!(""),
            format!("====================================="),
        ]
        .join("\n")
    }

    pub fn number_of_contexts(&self) -> usize {
        self.graph
            .node_weights()
            .filter(|n| matches!(n, Node::Context(_)))
            .count()
    }

    pub fn number_of_forks(&self) -> usize {
        self.graph
            .node_weights()
            .filter(|n| matches!(n, Node::ContextFork))
            .count()
    }

    pub fn number_of_variables(&self) -> usize {
        self.graph
            .node_weights()
            .filter(|n| matches!(n, Node::ContextVar(_)))
            .count()
    }

    pub fn number_of_functions(&self) -> usize {
        self.graph
            .node_weights()
            .filter(|n| matches!(n, Node::Function(_)))
            .count()
    }

    pub fn number_of_contracts(&self) -> usize {
        self.graph
            .node_weights()
            .filter(|n| matches!(n, Node::Contract(_)))
            .count()
    }

    pub fn max_context_depth(&self) -> usize {
        self.graph
            .node_weights()
            .filter_map(|n| {
                if let Node::Context(c) = n {
                    Some(c)
                } else {
                    None
                }
            })
            .fold(0, |mut acc, c| {
                if c.depth > acc {
                    acc = c.depth;
                    acc
                } else {
                    acc
                }
            })
    }

    pub fn max_context_width(&self) -> usize {
        self.graph
            .node_weights()
            .filter_map(|n| {
                if let Node::Context(c) = n {
                    Some(c)
                } else {
                    None
                }
            })
            .fold(0, |mut acc, c| {
                if c.width > acc {
                    acc = c.width;
                    acc
                } else {
                    acc
                }
            })
    }

    pub fn complicated_parse(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        expr: &Expression,
        parent: Option<NodeIdx>,
    ) -> Option<ExprRet> {
        tracing::trace!("Parsing required compile-time evaluation: {expr:?}, {parent:?}");

        let ctx = if let Some(parent) = parent {
            let pf = Function {
                name: Some(Identifier {
                    loc: solang_parser::pt::Loc::Implicit,
                    name: "<parser_fn>".into(),
                }),
                ..Default::default()
            };
            let parser_fn = FunctionNode::from(self.add_node(pf));
            self.add_edge(parser_fn, parent, Edge::Func);

            let dummy_ctx = Context::new(parser_fn, "<parser_fn>".to_string(), expr.loc());
            let ctx = ContextNode::from(self.add_node(Node::Context(dummy_ctx)));
            self.add_edge(ctx, parser_fn, Edge::Context(ContextEdge::Context));
            ctx
        } else {
            let dummy_ctx = Context::new(self.parse_fn, "<parser_fn>".to_string(), expr.loc());
            let ctx = ContextNode::from(self.add_node(Node::Context(dummy_ctx)));
            self.add_edge(ctx, self.entry(), Edge::Context(ContextEdge::Context));
            ctx
        };

        let full_stmt = solang_parser::pt::Statement::Return(expr.loc(), Some(expr.clone()));
        self.traverse_statement(&full_stmt, None);
        self.interpret(ctx, full_stmt.loc(), arena);
        let edges = self.add_if_err(ctx.successful_edges(self).into_expr_err(expr.loc()))?;
        if edges.len() == 1 {
            let res = edges[0].return_nodes(self).into_expr_err(expr.loc());

            let res = self.add_if_err(res);

            if let Some(res) = res {
                res.last().map(|last| ExprRet::Single(last.1.into()))
            } else {
                None
            }
        } else if edges.is_empty() {
            let res = ctx.return_nodes(self).into_expr_err(expr.loc());

            let res = self.add_if_err(res);

            if let Some(res) = res {
                res.last().map(|last| ExprRet::Single(last.1.into()))
            } else {
                None
            }
        } else {
            self.add_expr_err(ExprErr::ParseError(expr.loc(), "Expected this to be compile-time evaluatable, but it was nondeterministic likely due to an external call via an interface".to_string()));
            None
        }
    }

    pub fn set_remappings_and_root(&mut self, remappings_path: String) {
        let parent_path_buf = PathBuf::from(&remappings_path)
            .parent()
            .unwrap()
            .to_path_buf();
        self.root = Root::RemappingsDirectory(parent_path_buf);

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

    pub fn update_with_solc_json(&mut self, path_to_json: &PathBuf) {
        self.root = Root::SolcJSON(path_to_json.clone());

        // iterate over the Solc JSON and add all the sources
        let json_file = fs::read_to_string(path_to_json)
            .unwrap_or_else(|_| panic!("Solc JSON file not found: {}", path_to_json.display()));
        let solc_json: Value = serde_json::from_str(&json_file).unwrap();
        let sources = solc_json["sources"].as_object().unwrap();
        for (name, value_obj) in sources {
            // value_obj is a Value with a `content` field -> save the `content` field's solidity string
            let sol_source = value_obj.as_object().unwrap()["content"].as_str().unwrap();
            // create SourcePath with the path to the JSON and the name of the source
            let source_path = SourcePath::SolcJSON(path_to_json.clone(), name.to_owned());
            // Don't know the solang file no yet, so set it to None
            let source = (source_path.clone(), sol_source.to_owned(), None, None);
            self.sources.push(source);
        }

        // also iterate over the Solc JSON and add all the remappings
        // settings (optional) -> remappings (optional) -> iterate over all remappings
        let remappings = solc_json["settings"]["remappings"].as_array();
        if let Some(remappings) = remappings {
            // vec of strings
            for remapping in remappings {
                // split the remapping string into two parts
                let remapping = remapping.as_str().unwrap();
                let remapping = remapping.split_once('=').expect("Invalid remapping");
                // remapping.0 is the name of the remapping
                // remapping.1 is the path of the remapping
                self.remappings.push((
                    remapping.0.to_owned().to_string(),
                    remapping.1.to_owned().to_string(),
                ));
            }
        }
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
                            .with_tab_width(4)
                            .with_index_type(ariadne::IndexType::Byte),
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
        arena: &mut RangeArena<Elem<Concrete>>,
        src: &str,
        current_path: &SourcePath,
        entry: bool,
    ) -> Option<NodeIdx> {
        let file_no = self.file_no;
        self.sources
            .push((current_path.clone(), src.to_string(), Some(file_no), None));
        if unsafe { USE_DEBUG_SITE } {
            Self::post_source_to_site(file_no, &current_path.path_to_solidity_source(), src);
        }
        match solang_parser::parse(src, file_no) {
            Ok((source_unit, _comments)) => {
                let parent =
                    self.add_node(Node::SourceUnit(graph::nodes::SourceUnit::new(file_no)));
                self.add_edge(parent, self.entry, Edge::Source);
                let final_pass_part = self.parse_source_unit(
                    arena,
                    source_unit,
                    file_no,
                    parent.into(),
                    current_path,
                );
                self.final_pass_items.push(final_pass_part);
                if entry {
                    self.final_pass(arena);
                }

                Some(parent)
            }
            Err(diagnostics) => {
                print_diagnostics_report(src, &current_path.path_to_solidity_source(), diagnostics)
                    .unwrap();
                panic!("Failed to parse Solidity code for {current_path:?}.");
            }
        }
    }

    pub fn final_pass(&mut self, arena: &mut RangeArena<Elem<Concrete>>) {
        let elems = self.final_pass_items.clone();
        elems.iter().for_each(|final_pass_item| {
            final_pass_item.funcs.iter().for_each(|func| {
                func.set_params_and_ret(self, arena).unwrap();
            });
        });
        elems.iter().for_each(|final_pass_item| {
            final_pass_item
                .inherits
                .iter()
                .for_each(|(contract, inherits)| {
                    contract.inherit(inherits.to_vec(), self);
                });
            // final_pass_item.funcs.iter().for_each(|func| {
            //     // add params now that parsing is done
            //     func.set_params_and_ret(self, arena).unwrap();
            // });

            final_pass_item
                .usings
                .iter()
                .for_each(|(using, scope_node)| {
                    self.parse_using(arena, using, *scope_node);
                });
            final_pass_item.vars.iter().for_each(|(var, parent)| {
                let loc = var.underlying(self).unwrap().loc;
                let res = var
                    .parse_initializer(self, arena, *parent)
                    .into_expr_err(loc);
                let _ = self.add_if_err(res);
            });
        });

        elems.into_iter().for_each(|final_pass_item| {
            final_pass_item.funcs.into_iter().for_each(|func| {
                if !self.handled_funcs.contains(&func) {
                    if let Some(body) = &func.underlying(self).unwrap().body {
                        let body = body.clone();
                        self.traverse_statement(&body, None);
                        self.interpret(func, body.loc(), arena)
                    }
                }
            });
        });
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_source_unit(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        source_unit: SourceUnit,
        file_no: usize,
        parent: SourceUnitNode,
        current_path: &SourcePath,
    ) -> FinalPassItem {
        let mut all_funcs = vec![];
        let mut all_usings = vec![];
        let mut all_inherits = vec![];
        let mut all_vars = vec![];
        source_unit
            .0
            .iter()
            .enumerate()
            .for_each(|(unit_part, source_unit_part)| {
                let (sup, funcs, usings, inherits, vars) = self.parse_source_unit_part(
                    arena,
                    source_unit_part,
                    file_no,
                    unit_part,
                    parent,
                    current_path,
                );
                parent.add_part(sup, self).unwrap();
                all_funcs.extend(funcs);
                all_usings.extend(usings);
                all_inherits.extend(inherits);
                all_vars.extend(vars);
            });
        FinalPassItem::new(all_funcs, all_usings, all_inherits, all_vars)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_source_unit_part(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        sup: &SourceUnitPart,
        file_no: usize,
        unit_part: usize,
        parent: SourceUnitNode,
        // imported: &mut Vec<(Option<NodeIdx>, String, String, usize)>,
        current_path: &SourcePath,
    ) -> (
        SourceUnitPartNode,
        Vec<FunctionNode>,
        Vec<(Using, NodeIdx)>,
        Vec<(ContractNode, Vec<String>)>,
        Vec<(VarNode, NodeIdx)>,
    ) {
        use SourceUnitPart::*;

        let sup_node = self.add_node(Node::SourceUnitPart(graph::nodes::SourceUnitPart::new(
            file_no, unit_part,
        )));
        let s_node = SourceUnitPartNode::from(sup_node);
        self.add_edge(sup_node, parent, Edge::Part);

        let mut func_nodes = vec![];
        let mut usings = vec![];
        let mut inherits = vec![];
        let mut vars = vec![];

        match sup {
            ContractDefinition(def) => {
                let (node, funcs, con_usings, unhandled_inherits, unhandled_vars) =
                    self.parse_contract_def(arena, def, parent);
                s_node.add_contract(node, self).unwrap();
                self.add_edge(node, sup_node, Edge::Contract);
                func_nodes.extend(funcs);
                usings.extend(con_usings);
                inherits.push((node, unhandled_inherits));
                vars.extend(unhandled_vars);
            }
            StructDefinition(def) => {
                let node = self.parse_struct_def(arena, def);
                s_node.add_struct(node, self).unwrap();
                self.add_edge(node, sup_node, Edge::Struct);
            }
            EnumDefinition(def) => {
                let node = self.parse_enum_def(def);
                s_node.add_enum(node, self).unwrap();
                self.add_edge(node, sup_node, Edge::Enum);
            }
            ErrorDefinition(def) => {
                let node = self.parse_err_def(arena, def);
                s_node.add_error(node, self).unwrap();
                self.add_edge(node, sup_node, Edge::Error);
            }
            VariableDefinition(def) => {
                let (node, maybe_func, needs_final_pass) = self.parse_var_def(arena, def, false);
                s_node.add_constant(node, self).unwrap();
                if let Some(func) = maybe_func {
                    let func = self.handle_func(func, None);
                    func_nodes.push(func);
                    s_node.add_func(func, self).unwrap();
                }

                if needs_final_pass {
                    vars.push((node, parent.into()));
                }

                self.add_edge(node, sup_node, Edge::Var);
            }
            FunctionDefinition(def) => {
                let node = self.parse_func_def(def, None);
                s_node.add_func(node, self).unwrap();
                func_nodes.push(node);

                self.add_edge(node, sup_node, Edge::Func);
            }
            TypeDefinition(def) => {
                let node = self.parse_ty_def(arena, def);
                s_node.add_ty(node, self).unwrap();
                self.add_edge(node, sup_node, Edge::Ty);
            }
            EventDefinition(_def) => todo!(),
            Annotation(_anno) => todo!(),
            Using(using) => usings.push((*using.clone(), parent.into())),
            StraySemicolon(_loc) => todo!(),
            PragmaDirective(_, _, _) => {}
            ImportDirective(import) => {
                self.parse_import(arena, import, current_path, parent);
            }
        }

        (s_node, func_nodes, usings, inherits, vars)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_import(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        import: &Import,
        current_path: &SourcePath,
        parent: SourceUnitNode,
    ) {
        let (import_path, remapping) = match import {
            Import::Plain(import_path, _) => {
                tracing::trace!("parse_import, path: {:?}", import_path);
                // find the longest remapping that the import_path starts with
                let remapping = self
                    .remappings
                    .iter()
                    .filter_map(|(name, target)| {
                        let str_lit = &import_path.string;
                        if str_lit.starts_with(name) {
                            Some((name, target))
                        } else {
                            None
                        }
                    })
                    .max_by(|(name1, _), (name2, _)| name1.len().cmp(&name2.len()));
                (import_path, remapping)
            }
            Import::Rename(import_path, _elems, _) => {
                tracing::trace!("parse_import, path: {:?}, Rename", import_path);
                // find the longest remapping that the import_path starts with
                let remapping = self
                    .remappings
                    .iter()
                    .filter_map(|(name, target)| {
                        let str_lit = &import_path.string;
                        if str_lit.starts_with(name) {
                            Some((name, target))
                        } else {
                            None
                        }
                    })
                    .max_by(|(name1, _), (name2, _)| name1.len().cmp(&name2.len()));
                (import_path, remapping)
            }
            e => todo!("import {:?}", e),
        };
        /*
        Cases to handle:
        current path SolidityFile, remapping found
        - Root is RemappingsDirectory
        current path SolidityFile, no remapping found
        - Root is SolidityFile
        - Root is RemappingsDirectory
        current path SolcJSON, remapping found
        - Root is SolcJSON
        current path SolcJSON, no remapping found
        - Root is SolcJSON
        */
        let (remapped, sol) = match current_path {
            SourcePath::SolidityFile(sol_file_path) => {
                // check for remappings found
                let remapped = if let Some((name, target)) = remapping {
                    // Found matching remapping name and target, check for remapping within the root path
                    match &self.root {
                        Root::RemappingsDirectory(root_path) => {
                            let remapped_path = root_path.join(target).join(
                                import_path
                                    .string
                                    .replacen(name, "", 1)
                                    .trim_start_matches('/'),
                            );
                            SourcePath::SolidityFile(remapped_path)
                        }
                        Root::SolcJSON(_) => {
                            panic!("Please report this as a bug, root is SolcJSON but current path is a SolidityFile w/ remapping found")
                        }
                        Root::SolidityFile(_) => {
                            panic!("Please report this as a bug, root is SolidityFile but remappings are available")
                        }
                    }
                } else {
                    // no remapping found, check for import within the root path
                    match &self.root {
                        Root::RemappingsDirectory(_) | Root::SolidityFile(_) => {
                            // _root_path is not used, should be equal to sol_file_path for first level imports, but different for chains of imports
                            // should be a relative import from sol_file_path
                            let remapped_path = sol_file_path
                                .parent()
                                .unwrap()
                                .join(import_path.string.trim_start_matches('/'));
                            SourcePath::SolidityFile(remapped_path)
                        }
                        Root::SolcJSON(_) => {
                            panic!("Please report this as a bug, root is SolcJSON but current path is a SolidityFile w/ no remapping found")
                        }
                    }
                };

                let canonical = fs::canonicalize(remapped.path_to_solidity_source())
                    .unwrap_or_else(|_| panic!(
                            "Could not find file: {remapped:?}{}",
                            if self.remappings.is_empty() {
                                ". It looks like you didn't pass in any remappings. Try adding the `--remappings ./path/to/remappings.txt` to the command line input"
                            } else { "" }
                        )
                    );
                let sol = fs::read_to_string(&canonical).unwrap_or_else(|_| {
                    panic!(
                        "Could not find file for dependency: {canonical:?}{}",
                        if self.remappings.is_empty() {
                            ". It looks like you didn't pass in any remappings. Try adding the `--remappings ./path/to/remappings.txt` to the command line input (where `remappings.txt` is the output of `forge remappings > remappings.txt`)"
                        } else { "" }
                    )
                });
                let canonical_source = SourcePath::SolidityFile(canonical);
                (canonical_source, sol)
            }
            SourcePath::SolcJSON(_json_path, current_name) => {
                // can use the import_path and remappings to find the import amongst self.sources
                let (remapped, sol) = match &self.root {
                    Root::SolcJSON(_solc_path) => {
                        // check for remappings found
                        if let Some((name, target)) = remapping {
                            // First, take the import_path and remove the remapping name
                            let import_path_str = import_path.string.replacen(name, "", 1);
                            let remapped_path = import_path_str.trim_start_matches('/');
                            // the source that matches should be "{target}/{remapped_path}". Create PathBuf for this
                            let remapped_path_buf =
                                PathBuf::from(format!("{}/{}", target, remapped_path));
                            // look for this path in self.sources
                            let normalized_remapped_path_buf = normalize_path(&remapped_path_buf);
                            if let Some((confirmed_source_path, sol, _file_no, _entry)) =
                                self.sources.iter().find(|(path, _sol, _file_no, _entry)| {
                                    normalize_path(path.path_to_solidity_source())
                                        == normalized_remapped_path_buf
                                })
                            {
                                // found the path, return the source_path
                                (confirmed_source_path.clone(), sol.clone())
                            } else {
                                // didn't find the path, panic
                                panic!("Could not find file: {:#?}", remapped_path_buf);
                            }
                        } else {
                            // need to find name of the file in self.sources
                            // import will be relative to the current_name
                            let current_path_buf = PathBuf::from(current_name);
                            let current_name_parent = current_path_buf
                                .parent()
                                .expect("no parent found for current file");

                            let import_path_str = import_path.string.as_str();
                            // convert to a PathBuf
                            let import_path_buf = PathBuf::from(import_path_str);
                            // check if the import_path begins with an '@'
                            if import_path_str.starts_with('@') {
                                // if lib, look for this path in self.sources
                                let normalized_import = normalize_path(&import_path_buf);
                                if let Some((confirmed_source_path, sol, _file_no, _entry)) =
                                    self.sources.iter().find(|(path, _sol, _file_no, _entry)| {
                                        normalize_path(path.path_to_solidity_source())
                                            == normalized_import
                                    })
                                {
                                    // found the path, return the source_path
                                    (confirmed_source_path.clone(), sol.clone())
                                } else {
                                    // didn't find the path, panic
                                    panic!("Could not find file: {:#?}", normalized_import);
                                }
                            } else {
                                tracing::debug!("import_path_buf is relative");

                                // if relative, join to the current_name_parent
                                let joined = current_name_parent.join(import_path_buf);
                                // look for this path in self.sources
                                let normalized_joined = normalize_path(joined);

                                if let Some((confirmed_source_path, sol, _file_no, _entry)) =
                                    self.sources.iter().find(|(path, _sol, _file_no, _entry)| {
                                        normalize_path(path.path_to_solidity_source())
                                            == normalized_joined
                                    })
                                {
                                    // found the path, return the source_path
                                    (confirmed_source_path.clone(), sol.clone())
                                } else {
                                    // didn't find the path, panic
                                    panic!("Could not find file: {:#?}", normalized_joined);
                                }
                            }
                        }
                    }
                    Root::SolidityFile(_) | Root::RemappingsDirectory(_) => {
                        panic!("Please report this as a bug, root is SolidityFile or RemappingsDirectory but current path is a SolcJSON")
                    }
                };

                (remapped, sol)
            }
        };

        // check for entry in self.sources that has a matching SourcePath
        let normalized_remapped = normalize_path(remapped.path_to_solidity_source());
        if let Some((_, _, _, optional_entry)) = self.sources.iter().find(|(path, _, _, _)| {
            normalize_path(path.path_to_solidity_source()) == normalized_remapped
        }) {
            // if found, add an edge from the parent to the entry
            if let Some(o_e) = optional_entry {
                self.add_edge(*o_e, parent, Edge::Import);
            }
        } else {
            // if not found, add it
            self.sources
                .push((remapped.clone(), sol.clone(), None, None));
        }

        let normalized_remapped = normalize_path(remapped.path_to_solidity_source());
        // take self.sources entry with the same path as remapped and update the file_no
        if let Some((source_path, source, optional_file_no, _)) =
            self.sources.iter_mut().find(|(path, _, _, _)| {
                normalize_path(path.path_to_solidity_source()) == normalized_remapped
            })
        {
            if optional_file_no.is_some() {
                // if the file_no is already set, don't recurse, just return
                return;
            }
            self.file_no += 1;
            let file_no = self.file_no;
            *optional_file_no = Some(file_no);
            if unsafe { USE_DEBUG_SITE } {
                // send the source to the site
                Self::post_source_to_site(file_no, &source_path.path_to_solidity_source(), source);
            }
        }

        let maybe_entry = self.parse(arena, &sol, &remapped, false);

        // take self.sources entry with the same path as remapped and update the entry node
        if let Some((_, _, _, optional_entry)) = self.sources.iter_mut().find(|(path, _, _, _)| {
            normalize_path(path.path_to_solidity_source()) == normalized_remapped
        }) {
            *optional_entry = maybe_entry;
        }

        if let Some(other_entry) = maybe_entry {
            self.add_edge(other_entry, parent, Edge::Import);
        };
    }

    // #[tracing::instrument(name = "parse_contract_def", skip_all, fields(name = format!("{:?}", contract_def.name)))]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_contract_def(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        contract_def: &ContractDefinition,
        source: SourceUnitNode,
    ) -> (
        ContractNode,
        Vec<FunctionNode>,
        Vec<(Using, NodeIdx)>,
        Vec<String>,
        Vec<(VarNode, NodeIdx)>,
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

        let import_nodes = self
            .sources
            .iter()
            .map(|(_, _, _, maybe_node)| *maybe_node)
            .collect::<Vec<_>>();
        // convert vec to slice
        let import_nodes = import_nodes.as_slice();

        let (contract, unhandled_inherits) =
            Contract::from_w_imports(contract_def.clone(), source.into(), import_nodes, self);

        let inherits = contract.inherits.clone();
        let con_name = contract.name.clone().unwrap().name;
        let con_node: ContractNode =
            if let Some(user_ty_nodes) = self.user_types.get(&con_name).cloned() {
                // assert we only have at most one unknown at a time for a given name
                assert!(
                    user_ty_nodes.iter().fold(0, |mut acc, idx| {
                        if matches!(self.node(*idx), Node::Unresolved(_)) {
                            acc += 1;
                        }
                        acc
                    }) <= 1
                );
                let mut ret = None;
                // see if we can fill the unknown with this contract
                for user_ty_node in user_ty_nodes.iter() {
                    if matches!(self.node(*user_ty_node), Node::Unresolved(_)) {
                        let unresolved = self.node_mut(*user_ty_node);
                        *unresolved = Node::Contract(contract.clone());
                        ret = Some(ContractNode::from(*user_ty_node));
                        break;
                    }
                }
                match ret {
                    Some(ret) => ret,
                    None => {
                        // no unresolved to fill
                        let node = self.add_node(Node::Contract(contract));
                        let entry = self.user_types.entry(con_name).or_default();
                        entry.push(node);
                        node.into()
                    }
                }
            } else {
                let node = self.add_node(Node::Contract(contract));
                let entry = self.user_types.entry(con_name).or_default();
                entry.push(node);
                node.into()
            };

        inherits.iter().for_each(|contract_node| {
            self.add_edge(*contract_node, con_node, Edge::InheritedContract);
        });

        let mut usings = vec![];
        let mut func_nodes = vec![];
        let mut vars = vec![];
        contract_def.parts.iter().for_each(|cpart| match cpart {
            StructDefinition(def) => {
                let node = self.parse_struct_def(arena, def);
                self.add_edge(node, con_node, Edge::Struct);
            }
            EnumDefinition(def) => {
                let node = self.parse_enum_def(def);
                self.add_edge(node, con_node, Edge::Enum);
            }
            ErrorDefinition(def) => {
                let node = self.parse_err_def(arena, def);
                self.add_edge(node, con_node, Edge::Error);
            }
            VariableDefinition(def) => {
                let (node, maybe_func, needs_final_pass) = self.parse_var_def(arena, def, true);
                if let Some(func) = maybe_func {
                    func_nodes.push(self.handle_func(func, Some(con_node)));
                }

                if needs_final_pass {
                    vars.push((node, con_node.into()));
                }

                self.add_edge(node, con_node, Edge::Var);
            }
            FunctionDefinition(def) => {
                let node = self.parse_func_def(def, Some(con_node));
                func_nodes.push(node);
            }
            TypeDefinition(def) => {
                let node = self.parse_ty_def(arena, def);
                self.add_edge(node, con_node, Edge::Ty);
            }
            EventDefinition(_def) => {}
            Annotation(_anno) => todo!(),
            Using(using) => usings.push((*using.clone(), con_node.0.into())),
            StraySemicolon(_loc) => {}
        });
        (con_node, func_nodes, usings, unhandled_inherits, vars)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_using(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        using_def: &Using,
        scope_node: NodeIdx,
    ) {
        tracing::trace!("Parsing \"using\" {:?}", using_def);
        let Some(ref using_def_ty) = using_def.ty else {
            self.add_expr_err(ExprErr::Todo(
                using_def.loc(),
                "Using statements with wildcards currently unsupported".to_string(),
            ));
            return;
        };
        let maybe_cvar_idx = self.parse_expr(arena, using_def_ty, None);
        let ty_idx = match VarType::try_from_idx(self, maybe_cvar_idx) {
            Some(v_ty) => v_ty.ty_idx(),
            None => {
                self.add_expr_err(ExprErr::Unresolved(
                    using_def.loc(),
                    "Unable to deduce the type for which to apply the `using` statement to"
                        .to_string(),
                ));
                return;
            }
        };

        match &using_def.list {
            UsingList::Library(ident_paths) => {
                ident_paths.identifiers.iter().for_each(|ident| {
                    if let Some(idxs) = self.user_types.get(&ident.name).cloned() {
                        let mut found = false;
                        for idx in idxs.iter() {
                            if let Node::Contract(_) = self.node(*idx) {
                                found = true;
                                let funcs = ContractNode::from(*idx).funcs(self);
                                let relevant_funcs: Vec<_> = funcs
                                    .iter()
                                    .filter_map(|func| {
                                        let first_param: FunctionParamNode =
                                            *func.params(self).iter().take(1).next()?;
                                        let param_ty = first_param.ty(self).unwrap();
                                        if param_ty == ty_idx {
                                            Some(func)
                                        } else {
                                            None
                                        }
                                    })
                                    .copied()
                                    .collect();
                                println!("relevant_funcs: {relevant_funcs:#?}");
                                if matches!(self.node(scope_node), Node::Contract(_)) {
                                    self.add_edge(
                                        scope_node,
                                        *idx,
                                        Edge::UsingContract(using_def.loc),
                                    );
                                }

                                relevant_funcs.iter().for_each(|func| {
                                    println!("connecting: {:#?}, {:#?}", self.node(ty_idx), func);
                                    self.add_edge(ty_idx, *func, Edge::LibraryFunction(scope_node));
                                });
                                break;
                            }
                        }
                        if !found && !idxs.is_empty() {
                            self.add_expr_err(ExprErr::ParseError(
                                using_def.loc(),
                                "Tried to use a non-contract as a contract in a `using` statement"
                                    .to_string(),
                            ))
                        }
                    } else {
                        panic!("Cannot find library contract {}", ident.name);
                    }
                });
            }
            UsingList::Functions(vec_ident_paths) => {
                vec_ident_paths.iter().for_each(|ident_paths| {
                    if ident_paths.path.identifiers.len() == 2 {
                        if let Some(idxs) =
                            self.user_types.get(&ident_paths.path.identifiers[0].name)
                        {
                            for idx in idxs {
                                if let Node::Contract(_) = self.node(*idx) {
                                    if let Some(func) =
                                        ContractNode::from(*idx).funcs(self).iter().find(|func| {
                                            func.name(self)
                                                .unwrap()
                                                .starts_with(&ident_paths.path.identifiers[1].name)
                                        })
                                    {
                                        self.add_edge(
                                            ty_idx,
                                            *func,
                                            Edge::LibraryFunction(scope_node),
                                        );
                                    } else {
                                        panic!(
                                            "Cannot find library function {}.{}",
                                            ident_paths.path.identifiers[0].name,
                                            ident_paths.path.identifiers[1].name
                                        );
                                    }
                                    break;
                                }
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
                                ContractNode::from(scope_node)
                                    .associated_source(self)
                                    .into(),
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
                            self.add_edge(ty_idx, *func, Edge::LibraryFunction(scope_node));
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
        let enu_node: EnumNode = if let Some(user_ty_nodes) = self.user_types.get(&name).cloned() {
            // assert we only have at most one unknown at a time for a given name
            assert!(
                user_ty_nodes.iter().fold(0, |mut acc, idx| {
                    if matches!(self.node(*idx), Node::Unresolved(_)) {
                        acc += 1;
                    }
                    acc
                }) <= 1
            );
            let mut ret = None;
            // see if we can fill the unknown with this contract
            for user_ty_node in user_ty_nodes.iter() {
                if matches!(self.node(*user_ty_node), Node::Unresolved(_)) {
                    let unresolved = self.node_mut(*user_ty_node);
                    *unresolved = Node::Enum(enu.clone());
                    ret = Some(EnumNode::from(*user_ty_node));
                    break;
                }
            }
            match ret {
                Some(ret) => ret,
                None => {
                    // no unresolved to fill
                    let node = self.add_node(enu);
                    let entry = self.user_types.entry(name).or_default();
                    entry.push(node);
                    node.into()
                }
            }
        } else {
            let node = self.add_node(enu);
            let entry = self.user_types.entry(name).or_default();
            entry.push(node);
            node.into()
        };

        enu_node
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_struct_def(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        struct_def: &StructDefinition,
    ) -> StructNode {
        tracing::trace!("Parsing struct {:?}", struct_def.name);
        let strukt = Struct::from(struct_def.clone());

        let name = strukt.name.clone().expect("Struct was not named").name;

        // check if we have an unresolved type by the same name
        let strukt_node: StructNode =
            if let Some(user_ty_nodes) = self.user_types.get(&name).cloned() {
                // assert we only have at most one unknown at a time for a given name
                assert!(
                    user_ty_nodes.iter().fold(0, |mut acc, idx| {
                        if matches!(self.node(*idx), Node::Unresolved(_)) {
                            acc += 1;
                        }
                        acc
                    }) <= 1
                );
                let mut ret = None;
                // see if we can fill the unknown with this contract
                for user_ty_node in user_ty_nodes.iter() {
                    if matches!(self.node(*user_ty_node), Node::Unresolved(_)) {
                        let unresolved = self.node_mut(*user_ty_node);
                        *unresolved = Node::Struct(strukt.clone());
                        ret = Some(StructNode::from(*user_ty_node));
                        break;
                    }
                }
                match ret {
                    Some(ret) => ret,
                    None => {
                        // no unresolved to fill
                        let node = self.add_node(Node::Struct(strukt));
                        let entry = self.user_types.entry(name).or_default();
                        entry.push(node);
                        node.into()
                    }
                }
            } else {
                let node = self.add_node(strukt);
                let entry = self.user_types.entry(name).or_default();
                entry.push(node);
                node.into()
            };

        struct_def.fields.iter().for_each(|field| {
            let f = Field::new(self, arena, field.clone());
            let field_node = self.add_node(f);
            self.add_edge(field_node, strukt_node, Edge::Field);
        });
        strukt_node
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn parse_err_def(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        err_def: &ErrorDefinition,
    ) -> ErrorNode {
        tracing::trace!("Parsing error {:?}", err_def);
        let err_node = ErrorNode(self.add_node(Error::from(err_def.clone())).index());
        err_def.fields.iter().for_each(|field| {
            let param = ErrorParam::new(self, arena, field.clone());
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
                let fn_node = self.add_node(func.clone());
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
        arena: &mut RangeArena<Elem<Concrete>>,
        var_def: &VariableDefinition,
        in_contract: bool,
    ) -> (VarNode, Option<Function>, bool) {
        tracing::trace!("Parsing variable definition: {:?}", var_def.name);
        let var = Var::new(self, arena, var_def.clone(), in_contract);
        let mut func = None;
        if var.is_public() {
            func = Some(Function::from(var_def.clone()));
        }
        let needs_final_pass = var.initializer_expr.is_some();
        let var_node = VarNode::from(self.add_node(var));
        let name = var_node.name(self).unwrap();
        let entry = self.user_types.entry(name).or_default();
        entry.push(var_node.into());
        (var_node, func, needs_final_pass)
    }

    pub fn parse_ty_def(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ty_def: &TypeDefinition,
    ) -> TyNode {
        tracing::trace!("Parsing type definition");
        let ty = Ty::new(self, arena, ty_def.clone());
        let name = ty.name.name.clone();
        let ty_node: TyNode = if let Some(user_ty_nodes) = self.user_types.get(&name).cloned() {
            // assert we only have at most one unknown at a time for a given name
            assert!(
                user_ty_nodes.iter().fold(0, |mut acc, idx| {
                    if matches!(self.node(*idx), Node::Unresolved(_)) {
                        acc += 1;
                    }
                    acc
                }) <= 1
            );
            let mut ret = None;
            // see if we can fill the unknown with this contract
            for user_ty_node in user_ty_nodes.iter() {
                if matches!(self.node(*user_ty_node), Node::Unresolved(_)) {
                    let unresolved = self.node_mut(*user_ty_node);
                    *unresolved = Node::Ty(ty.clone());
                    ret = Some(TyNode::from(*user_ty_node));
                    break;
                }
            }
            match ret {
                Some(ret) => ret,
                None => {
                    // no unresolved to fill
                    let node = self.add_node(Node::Ty(ty));
                    let entry = self.user_types.entry(name).or_default();
                    entry.push(node);
                    node.into()
                }
            }
        } else {
            let node = self.add_node(Node::Ty(ty));
            let entry = self.user_types.entry(name).or_default();
            entry.push(node);
            node.into()
        };
        ty_node
    }

    fn post_source_to_site(file_no: usize, path: &Path, source: &str)
    where
        Self: std::marker::Sized,
        Self: AnalyzerLike,
    {
        let rt = Runtime::new().unwrap();
        rt.block_on(async {
            Self::post_source_to_site_async(file_no, path, source).await;
        });
    }

    async fn post_source_to_site_async(file_no: usize, path: &Path, source: &str)
    where
        Self: std::marker::Sized,
        Self: AnalyzerLike,
    {
        let client = Client::new();
        let source_msg = SourceMessage {
            file_number: file_no,
            path: path.to_path_buf(),
            source: source.to_string(),
        };
        let res = client
            .post("http://127.0.0.1:8545/addsource")
            .json(&source_msg)
            .send()
            .await
            .expect("Failed to send request");

        if res.status().is_success() {
            trace!("Successfully posted source to site");
        } else {
            error!("Failed to post source to site: {:?}", res.status());
        }
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

/// Normalize the path by resolving the `.` and `..` components in order to do path comparison.
///
/// This is used instead of `std::fs::canonicalize()` in cases where the path is not present on the filesystem (e.g. in the case of a Solc Standard JSON)
///
/// ## Examples
///
/// ```
/// use std::path::{Path, PathBuf};
/// use pyrometer::normalize_path;
///
/// let path = Path::new("/src/contracts/./Main.sol");
/// assert_eq!(normalize_path(path), PathBuf::from("/src/contracts/Main.sol"));
///
/// let path = Path::new("/src/contracts/../Main.sol");
/// assert_eq!(normalize_path(path), PathBuf::from("/src/Main.sol"));
/// ```
pub fn normalize_path<P: AsRef<Path>>(path: P) -> PathBuf {
    let mut normalized_path = PathBuf::new();

    for component in path.as_ref().components() {
        match component {
            std::path::Component::CurDir => {} // Ignore current dir component
            std::path::Component::ParentDir => {
                // Handle parent dir component
                normalized_path.pop();
            }
            _ => normalized_path.push(component),
        }
    }

    normalized_path
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Hash)]
struct SourceMessage {
    file_number: usize,
    path: PathBuf,
    source: String,
}
