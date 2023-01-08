use crate::Range;
use crate::FunctionNode;
use crate::BuiltInNode;
use crate::RangeElem;
use crate::ConcreteNode;
use crate::FieldNode;
use crate::FunctionReturnNode;
use crate::FunctionParamNode;
use crate::Edge;
use crate::AnalyzerLike;
use ethers_core::types::U256;
use crate::Concrete;
use crate::DynBuiltin;
use crate::VarType;
use crate::TypeNode;
use crate::Node;
use crate::Builtin;
use crate::NodeIdx;
use solang_parser::pt::{Loc, Expression, Statement};

use petgraph::visit::EdgeRef;
use petgraph::{Direction, Directed, graph::*};
use petgraph::graph::Edges;

pub mod var;
pub use var::*;
pub mod analyzer;
pub use analyzer::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum ContextEdge {
	// Control flow
	Context,
	Subcontext,
	Call,

	// Context Variables
	Variable,
	InheritedVariable,

	AttrAccess,
    Index,
	IndexAccess,

	// Variable incoming edges
	Assign,
	StorageAssign,
	MemoryAssign,
	Next,

	// Control flow
	Return,


	// Range analysis
	Range
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ContextNode(pub usize);
impl ContextNode {
    pub fn underlying_mut<'a>(&self, analyzer: &'a mut impl AnalyzerLike) -> &'a mut Context {
        match analyzer.node_mut(*self) {
            Node::Context(c) => c,
            e => panic!("Node type confusion: expected node to be Context but it was: {:?}", e)
        }
    }

    pub fn var_by_name(&self, analyzer: &impl AnalyzerLike, name: &str) -> Option<ContextVarNode> {
        analyzer.graph().edges_directed((*self).into(), Direction::Incoming)
            .filter(|edge| *edge.weight() == Edge::Context(ContextEdge::Variable))
            .map(|edge| ContextVarNode::from(edge.source()))
            .filter_map(|cvar_node| {
                let cvar = cvar_node.underlying(analyzer);
                if cvar.name == name {
                    Some(cvar_node)
                } else {
                    None
                }
            })
            .take(1)
            .next()
    }

    pub fn new_tmp(&self, analyzer: &mut impl AnalyzerLike) -> usize {
        let context = self.underlying_mut(analyzer);
        let ret = context.tmp_var_ctr;
        context.tmp_var_ctr += 1;
        ret
    }
}
impl Into<NodeIdx> for ContextNode {
	fn into(self) -> NodeIdx {
		self.0.into()
	}
}

impl From<NodeIdx> for ContextNode {
	fn from(idx: NodeIdx) -> Self {
		ContextNode(idx.index())
	}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Context {
	pub tmp_var_ctr: usize,
	pub loc: Loc
}

impl Context {
	pub fn new(loc: Loc) -> Self {
		Context {
			tmp_var_ctr: 0,
			loc,
		}
	}
}

pub trait ContextBuilder: AnalyzerLike + Sized {
	fn parse_ctx_statement(&mut self, stmt: &Statement, unchecked: bool, parent_ctx: Option<impl Into<NodeIdx> + Clone + Copy>) where Self: Sized {
        use Statement::*;
        // println!("stmt: {:?}", stmt);
        match stmt {
            Block{loc, unchecked, statements} => {
                let ctx = Context::new(*loc);
                let ctx_node = self.add_node(Node::Context(ctx));
                
                if let Some(parent) = parent_ctx {
                    self.add_edge(ctx_node, parent, Edge::Context(ContextEdge::Context));
                }

                // optionally add named input and named outputs into context
		        if let Some(parent) = parent_ctx.clone() {
		        	self.graph().edges_directed(parent.into(), Direction::Incoming)
		        		.filter(|edge| *edge.weight() == Edge::FunctionParam)
		        		.map(|edge| FunctionParamNode::from(edge.source()))
		        		.collect::<Vec<FunctionParamNode>>()
		        		.iter()
		        		.for_each(|param_node| {
		        			let func_param = param_node.underlying(self);
		        			if let Some(cvar) = ContextVar::maybe_new_from_func_param(self, func_param.clone()) {
		        				let cvar_node = self.add_node(Node::ContextVar(cvar));
			        			self.add_edge(cvar_node, ctx_node, Edge::Context(ContextEdge::Variable));	
		        			}
		        		});

		        	self.graph().edges_directed(parent.into(), Direction::Incoming)
		        		.filter(|edge| *edge.weight() == Edge::FunctionReturn)
		        		.map(|edge| FunctionReturnNode::from(edge.source()))
		        		.collect::<Vec<FunctionReturnNode>>()
		        		.iter()
		        		.for_each(|ret_node| {
		        			let func_ret = ret_node.underlying(self);
		        			if let Some(cvar) = ContextVar::maybe_new_from_func_ret(self, func_ret.clone()) {
		        				let cvar_node = self.add_node(Node::ContextVar(cvar));
			        			self.add_edge(cvar_node, ctx_node, Edge::Context(ContextEdge::Variable));	
		        			}
		        		});
		        }

                statements.iter().for_each(|stmt| { self.parse_ctx_statement(stmt, *unchecked, Some(ctx_node)) });
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
            Expression(loc, expr) => {
                if let Some(parent) = parent_ctx {
                    let expr_nodes = self.parse_ctx_expr(expr, ContextNode::from(parent.into()));
                    if expr_nodes.is_empty() {

                    } else {
                        self.add_edge(expr_nodes[0], parent, Edge::Context(ContextEdge::Call));
                    }
                }
            },
            VariableDefinition(loc, var_decl, maybe_expr) => {},
            For(loc, maybe_for_start, maybe_for_middle, maybe_for_end, maybe_for_body) => {},
            DoWhile(loc, while_stmt, while_expr) => {},
            Continue(loc) => {},
            Break(loc) => {},
            Return(loc, maybe_ret_expr) => {
                if let Some(ret_expr) = maybe_ret_expr {
                    if let Some(parent) = parent_ctx {
                        let expr_node = self.parse_ctx_expr(ret_expr, ContextNode::from(parent.into()))[0];
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

	fn parse_ctx_expr(&mut self, expr: &Expression, ctx: ContextNode) -> Vec<NodeIdx> {
        use Expression::*;
        println!("ctx_expr: {:?}", expr);
        match expr {
            Type(_loc, ty) => {
                if let Some(builtin) = Builtin::try_from_ty(ty.clone()) {
                    if let Some(idx) = self.builtins().get(&builtin) {
                        vec![*idx]
                    } else {
                        let idx = self.add_node(Node::Builtin(builtin.clone()));
                        self.builtins_mut().insert(builtin, idx);
                        vec![idx]
                    }
                } else {
                    todo!("??")
                }
            }
            Variable(ident) => {
                if let Some(cvar) = ctx.var_by_name(self, &ident.name) {
                    vec![cvar.into()]
                } else {
                    if let Some(idx) = self.user_types().get(&ident.name) {
                        vec![*idx]
                    } else {
                        if let Some(func) = self.builtin_fns().get(&ident.name) {
                            let (inputs, outputs) = self.builtin_fn_inputs().get(&ident.name).expect("builtin func but no inputs").clone();
                            let func_node = self.add_node(Node::Function(func.clone()));
                            inputs.into_iter().for_each(|input| {
                                let input_node = self.add_node(input);
                                self.add_edge(input_node, func_node, Edge::FunctionParam);
                            });
                            outputs.into_iter().for_each(|output| {
                                let output_node = self.add_node(output);
                                self.add_edge(output_node, func_node, Edge::FunctionReturn);
                            });
                            vec![func_node]
                        } else {
                            let node = self.add_node(Node::Unresolved(ident.clone()));
                            self.user_types_mut().insert(ident.name.clone(), node);
                            vec![node]
                        }    
                    }
                }
            }
            ArraySubscript(_loc, ty_expr, None) => {
                let inner_ty = self.parse_ctx_expr(&ty_expr, ctx)[0];
                if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
                    let dyn_b = DynBuiltin::Array(var_type);
                    if let Some(idx) = self.dyn_builtins().get(&dyn_b) {
                        vec![*idx]
                    } else {
                        let idx = self.add_node(Node::DynBuiltin(dyn_b.clone()));
                        self.dyn_builtins_mut().insert(dyn_b, idx);
                        vec![idx]
                    }
                } else {
                    todo!("???")
                }
            }
            ArraySubscript(loc, ty_expr, Some(index_expr)) => {
                let inner_ty = self.parse_ctx_expr(&ty_expr, ctx)[0];
                let index_ty = self.parse_ctx_expr(&index_expr, ctx)[0];

                let index_var = ContextVar {
                    loc: Some(*loc),
                    name: ContextVarNode::from(index_ty).name(self),
                    storage: ContextVarNode::from(inner_ty).storage(self).clone(),
                    ty: ContextVarNode::from(inner_ty).ty(self).array_underlying_ty(self),
                };

                let cvar_idx = self.add_node(Node::ContextVar(index_var));
                self.add_edge(cvar_idx, inner_ty, Edge::Context(ContextEdge::IndexAccess));

                self.add_edge(index_ty, cvar_idx, Edge::Context(ContextEdge::Index));

                vec![cvar_idx]
            }
            NumberLiteral(loc, int, exp) => {
                // TODO: improve this to actually work

                let int = U256::from_dec_str(&int).unwrap();
                let val = if !exp.is_empty() {
                    let exp = U256::from_dec_str(&exp).unwrap();
                    int.pow(exp)
                } else {
                    int
                };
                let concrete_node = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Uint(256, val))));
                let ccvar = Node::ContextVar(ContextVar::new_from_concrete(*loc, ctx.new_tmp(self), concrete_node));
                vec![self.add_node(ccvar)]
            }
            MemberAccess(loc, member_expr, ident) => {
                let member_idx = self.parse_ctx_expr(member_expr, ctx)[0];
                match self.node(member_idx) {
                    Node::ContextVar(cvar) => {
                        match cvar.ty {
                            VarType::User(TypeNode::Struct(struct_node)) => {
                                let field = self.graph().edges_directed(struct_node.into(), Direction::Incoming)
                                    .filter(|edge| *edge.weight() == Edge::Field)
                                    .map(|edge| FieldNode::from(edge.source()))
                                    .collect::<Vec<FieldNode>>()
                                    .iter()
                                    .filter_map(|field_node| {
                                        let field = field_node.underlying(self);
                                        if field.name.as_ref().expect("field wasnt named").name == ident.name {
                                            Some(field)
                                        } else {
                                            None
                                        }
                                    })
                                    .take(1)
                                    .next()
                                    .expect(&format!("No field with name {:?} in struct: {:?}", ident.name, struct_node.name(self)));
                                if let Some(field_cvar) = ContextVar::maybe_new_from_field(self, *loc, cvar, field.clone()) {
                                    let fc_node = self.add_node(Node::ContextVar(field_cvar));
                                    self.add_edge(fc_node, member_idx, Edge::Context(ContextEdge::AttrAccess));
                                    return vec![fc_node]
                                }
                                

                            }
                            _ => todo!(),
                        }
                    }
                    // Struct(strukt) => {
                    //     let field_idx = self.graph().edges_directed(member_idx, Direction::Incoming)
                    //         .filter(|edge| *edge.weight() == Edge::Field)
                    //         .map(|edge| FieldNode::from(edge.source()))
                    //         .collect::<Vec<FieldNode>>()
                    //         .iter()
                    //         .filter_map(|field_node| {
                    //             let field = field_node.underlying(self);
                    //             if field.name == ident.name {
                    //                 Some(field_node)
                    //             } else {
                    //                 None
                    //             }
                    //         })
                    //         .take(1)
                    //         .next()
                    //         .expect(format!("No field with name {:?} in struct: {:?}", ident.name, strukt.name);
                    //     let cvar = ContextVar::maybe_new_from_field(self, loc, ContextVarNode::from(member_idx))
                    // }
                    _ => todo!()
                }
                vec![member_idx]
            }
            Less(loc, lhs, rhs) => {
                let lhs_cvar = ContextVarNode::from(self.parse_ctx_expr(lhs, ctx)[0]);
                let rhs_idx = self.parse_ctx_expr(lhs, ctx)[0];

                let out_var = ContextVar {
                    loc: Some(*loc),
                    name: "$tmp_var".to_string() + &ctx.new_tmp(self).to_string(),
                    storage: None,
                    ty: VarType::BuiltIn(BuiltInNode::from(self.builtin_or_add(Builtin::Bool)), None),
                };

                vec![self.add_node(Node::ContextVar(out_var))]

            }
            FunctionCall(loc, func_expr, input_exprs) => {
                let func_idx = self.parse_ctx_expr(func_expr, ctx)[0];

                if let Some(func_name) = &FunctionNode::from(func_idx).underlying(self).name {
                    if func_name.name == "require" {
                        self.handle_require(input_exprs, ctx);
                        return vec![];
                    }
                }

                let inputs: Vec<_> = input_exprs.into_iter().map(|expr| self.parse_ctx_expr(expr, ctx)).collect();    


                // todo!("func call")
                vec![func_idx]
            },
            e => todo!("{:?}", e)
        }
	}

    fn handle_require(&mut self, inputs: &Vec<Expression>, ctx: ContextNode) {
        println!("handling require");
        match inputs.get(0) {
            Some(Expression::Less(loc, lhs, rhs)) => {
                let lhs_cvar = ContextVarNode::from(self.parse_ctx_expr(lhs, ctx)[0]);
                let rhs_cvar = ContextVarNode::from(self.parse_ctx_expr(rhs, ctx)[0]);
                let new_upper_bound = match rhs_cvar.underlying(self).ty {
                    VarType::Concrete(c) => {
                        let val = c.underlying(self).uint_val().expect("Not uint bound");
                        RangeElem::Concrete(val)
                    }
                    _ => RangeElem::Dynamic(rhs_cvar.into())
                };

                let lhs_underlying = lhs_cvar.underlying_mut(self);
                match lhs_underlying.ty {
                    VarType::BuiltIn(_bn, ref mut maybe_lhs_range) => {
                        if let Some(lhs_range) = maybe_lhs_range {
                            lhs_range.max = new_upper_bound;
                        } else {
                            *maybe_lhs_range = Some(Range { min: RangeElem::Concrete(U256::zero()), max: new_upper_bound})
                        }
                    },
                    e => {println!("wasnt builting: {:?}", e)}
                }
                println!("require lhs {:?}", lhs_underlying);
            }
            None => panic!("Empty require"),
            _ => todo!()
        }
    }
}

