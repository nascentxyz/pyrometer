use crate::{GraphError, GraphLike, NodeIdx, RangeArena, RepresentationErr};

use ahash::AHashMap;

use solang_parser::pt::Loc;
use std::{collections::BTreeMap, fmt};

#[derive(Debug, Clone, Copy, Default)]
pub struct ApplyStats {
    pub pure_no_children_applies: ApplyStat,
    pub pure_children_no_forks_applies: ApplyStat,
    pub pure_children_forks_applies: ApplyStat,

    pub view_no_children_applies: ApplyStat,
    pub view_children_no_forks_applies: ApplyStat,
    pub view_children_forks_applies: ApplyStat,

    pub mut_no_children_applies: ApplyStat,
    pub mut_children_no_forks_applies: ApplyStat,
    pub mut_children_forks_applies: ApplyStat,
}

#[derive(Debug, Clone, Default)]
pub struct InterpStats {
    pub nanos: u128,
    pub funcs: BTreeMap<String, FuncStat>,
}

impl fmt::Display for InterpStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "total time: {}", milli_str(self.nanos))?;
        writeln!(f, "number of functions: {}", self.funcs.len())?;
        writeln!(f, "functions:")?;
        let mut funcs = self.funcs.iter().collect::<Vec<_>>();
        funcs.sort_by(|(_, v), (_, v2)| v2.nanos.cmp(&v.nanos));
        funcs.iter().try_for_each(|(func_name, func_stat)| {
            let n = 2;
            writeln!(
                f,
                "{}{} -- {func_name}: {} ctxs, {} exprs",
                " ".repeat(n),
                milli_str(func_stat.nanos),
                func_stat.ctxs.len(),
                func_stat.ctxs.iter().fold(0, |mut acc, (_, ctx)| {
                    acc += ctx.exprs_ran;
                    acc
                })
            )
            // write!(f, "{func_stat}")
        })
    }
}

#[derive(Debug, Clone, Default)]
pub struct FuncStat {
    pub nanos: u128,
    pub ctxs: BTreeMap<String, CtxStat>,
}

impl fmt::Display for FuncStat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = 4;
        writeln!(f, "{}total time: {}", " ".repeat(n), milli_str(self.nanos))?;
        writeln!(
            f,
            "{}number of contexts: {}",
            " ".repeat(n),
            self.ctxs.len()
        )
        // writeln!(f, "{}contexts:", " ".repeat(n))?;
        // self.ctxs.iter().try_for_each(|(ctx_key, ctx_stat)| {
        //     let n = 6;
        //     writeln!(f, "{}{ctx_key}:", " ".repeat(n))?;
        //     write!(f, "{ctx_stat}")
        // })
    }
}

#[derive(Debug, Clone, Default)]
pub struct CtxStat {
    pub nanos: u128,
    pub exprs_ran: usize,
    pub exprs: BTreeMap<&'static str, ExprStat>,
}

impl fmt::Display for CtxStat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = 8;
        writeln!(f, "{}total time: {}", " ".repeat(n), milli_str(self.nanos))?;
        writeln!(
            f,
            "{}number of expressions: {}",
            " ".repeat(n),
            self.exprs_ran
        )
        // writeln!(f, "{}expressions:", " ".repeat(n))?;
        // self.exprs.iter().try_for_each(|(expr_key, expr_stat)| {
        //     let n = 10;
        //     writeln!(f, "{}{expr_key}:", " ".repeat(n))?;
        //     write!(f, "{expr_stat}")
        // })
    }
}

#[derive(Debug, Clone, Default)]
pub struct ExprStat {
    pub longest: LocStat,
    pub total: u128,
    pub n: usize,
}

impl fmt::Display for ExprStat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = 12;
        writeln!(f, "{}total time: {}", " ".repeat(n), milli_str(self.total))?;
        writeln!(f, "{}number of times ran: {}", " ".repeat(n), self.n)?;
        writeln!(f, "{}longest: {}", " ".repeat(n), self.longest)
    }
}

#[derive(Debug, Clone, Default)]
pub struct LocStat {
    pub loc: Loc,
    pub nanos: u128,
}

pub fn milli_str(nanos: u128) -> String {
    let millis = nanos / 1000000;
    let rem_nanos = nanos % 1000000;
    format!("{millis}.{rem_nanos}ms")
}

impl fmt::Display for LocStat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", milli_str(self.nanos))
    }
}

impl ApplyStats {
    pub fn total_applies(&self) -> usize {
        self.total_pure_applies() + self.total_view_applies() + self.total_mut_applies()
    }

    pub fn completed_applies(&self) -> usize {
        self.completed_pure_applies() + self.completed_view_applies() + self.completed_mut_applies()
    }

    pub fn reduced_vars(&self) -> usize {
        self.pure_reduced_vars() + self.view_reduced_vars() + self.mut_reduced_vars()
    }

    pub fn total_pure_applies(&self) -> usize {
        self.pure_no_children_applies.num_applies
            + self.pure_children_no_forks_applies.num_applies
            + self.pure_children_forks_applies.num_applies
    }

    pub fn completed_pure_applies(&self) -> usize {
        self.pure_no_children_applies.completed_applies
            + self.pure_children_no_forks_applies.completed_applies
            + self.pure_children_forks_applies.completed_applies
    }

    pub fn pure_reduced_vars(&self) -> usize {
        self.pure_no_children_applies.vars_reduced
            + self.pure_children_no_forks_applies.vars_reduced
            + self.pure_children_forks_applies.vars_reduced
    }

    pub fn total_view_applies(&self) -> usize {
        self.view_no_children_applies.num_applies
            + self.view_children_no_forks_applies.num_applies
            + self.view_children_forks_applies.num_applies
    }

    pub fn completed_view_applies(&self) -> usize {
        self.view_no_children_applies.completed_applies
            + self.view_children_no_forks_applies.completed_applies
            + self.view_children_forks_applies.completed_applies
    }

    pub fn view_reduced_vars(&self) -> usize {
        self.view_no_children_applies.vars_reduced
            + self.view_children_no_forks_applies.vars_reduced
            + self.view_children_forks_applies.vars_reduced
    }

    pub fn total_mut_applies(&self) -> usize {
        self.mut_no_children_applies.num_applies
            + self.mut_children_no_forks_applies.num_applies
            + self.mut_children_forks_applies.num_applies
    }

    pub fn completed_mut_applies(&self) -> usize {
        self.mut_no_children_applies.completed_applies
            + self.mut_children_no_forks_applies.completed_applies
            + self.mut_children_forks_applies.completed_applies
    }

    pub fn mut_reduced_vars(&self) -> usize {
        self.mut_no_children_applies.vars_reduced
            + self.mut_children_no_forks_applies.vars_reduced
            + self.mut_children_forks_applies.vars_reduced
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct ApplyStat {
    pub num_applies: usize,
    pub completed_applies: usize,
    pub vars_reduced: usize,
}

pub trait AnalyzerLike: GraphLike {
    /// The expression type
    type Expr;
    /// An error when parsing an expression
    type ExprErr;

    /// Type of the `msg` node
    type MsgNode;
    /// Type of the `block` node
    type BlockNode;

    /// Type of execution error node
    type ExecError;
    type ExecErrorParam;
    /// Type of a function
    type Function;
    /// Node of a function type
    type FunctionNode;
    /// Type of a function input parameter
    type FunctionParam;
    /// Type of a function return paramter
    type FunctionReturn;
    /// Type of a context node
    type ContextNode;

    /// Type of a builtin
    type Builtin;

    /// Gets the builtin functions map
    fn builtin_fns(&self) -> &AHashMap<String, Self::Function>;
    /// Mutably gets the builtin functions map
    fn builtin_fn_nodes_mut(&mut self) -> &mut AHashMap<String, NodeIdx>;
    /// Gets the builtin function nodes mapping
    fn builtin_fn_nodes(&self) -> &AHashMap<String, NodeIdx>;
    /// Returns the configured max call depth
    fn max_depth(&self) -> usize;
    /// Returns the configured max fork width
    fn max_width(&self) -> usize;
    fn user_types(&self) -> &AHashMap<String, Vec<NodeIdx>>;
    fn user_types_mut(&mut self) -> &mut AHashMap<String, Vec<NodeIdx>>;
    fn parse_expr(
        &mut self,
        arena: &mut RangeArena<Self::RangeElem>,
        expr: &Self::Expr,
        parent: Option<NodeIdx>,
    ) -> NodeIdx;
    fn msg(&mut self) -> Self::MsgNode;
    fn block(&mut self) -> Self::BlockNode;
    fn entry(&self) -> NodeIdx;
    fn parse_fn(&self) -> Self::FunctionNode;
    fn add_expr_err(&mut self, err: Self::ExprErr);
    fn expr_errs(&self) -> Vec<Self::ExprErr>;

    #[allow(clippy::type_complexity)]
    fn builtin_fn_inputs(
        &self,
    ) -> &AHashMap<String, (Vec<Self::FunctionParam>, Vec<Self::FunctionReturn>)>;
    fn builtins(&self) -> &AHashMap<Self::Builtin, NodeIdx>;
    fn builtins_mut(&mut self) -> &mut AHashMap<Self::Builtin, NodeIdx>;
    fn builtin_or_add(&mut self, builtin: Self::Builtin) -> NodeIdx;
    fn builtin_fn_or_maybe_add(&mut self, builtin_name: &str) -> Option<NodeIdx>
    where
        Self: std::marker::Sized;

    fn builtin_error_or_add(
        &mut self,
        err: Self::ExecError,
        params: Vec<Self::ExecErrorParam>,
    ) -> NodeIdx;

    fn debug_panic(&self) -> bool;

    fn fn_calls_fns(&self) -> &BTreeMap<Self::FunctionNode, Vec<Self::FunctionNode>>;
    fn fn_calls_fns_mut(&mut self) -> &mut BTreeMap<Self::FunctionNode, Vec<Self::FunctionNode>>;
    fn add_fn_call(&mut self, caller: Self::FunctionNode, callee: Self::FunctionNode)
    where
        Self::FunctionNode: Ord,
    {
        let calls = self.fn_calls_fns_mut();
        let entry = calls.entry(caller).or_default();
        if !entry.contains(&callee) {
            entry.push(callee)
        }
    }

    fn add_if_err<T>(&mut self, err: Result<T, Self::ExprErr>) -> Option<T>
    where
        Self::ExprErr: std::fmt::Debug,
    {
        match err {
            Ok(t) => Some(t),
            Err(e) => {
                self.add_expr_err(e);
                None
            }
        }
    }

    fn apply_stats_mut(&mut self) -> &mut ApplyStats;
    fn handled_funcs(&self) -> &[Self::FunctionNode];
    fn handled_funcs_mut(&mut self) -> &mut Vec<Self::FunctionNode>;
    fn file_mapping(&self) -> BTreeMap<usize, &str>;
    fn minimize_debug(&self) -> &Option<String>;
    fn minimize_err(&mut self, ctx: Self::ContextNode) -> String;
    fn is_representation_ok(
        &mut self,
        arena: &RangeArena<<Self as GraphLike>::RangeElem>,
    ) -> Result<Vec<RepresentationErr>, GraphError>;

    type FlatExpr;
    fn push_expr(&mut self, flat: Self::FlatExpr);
    fn increment_asm_block(&mut self);
    fn decrement_asm_block(&mut self);
    fn current_asm_block(&self) -> usize;
    fn expr_stack(&self) -> &[Self::FlatExpr];
    fn expr_stack_mut(&mut self) -> &mut Vec<Self::FlatExpr>;
    fn debug_stack(&self) -> bool;

    fn increment_contract_id(&mut self) -> usize;

    fn interp_stats_mut(&mut self) -> &mut InterpStats;
}
