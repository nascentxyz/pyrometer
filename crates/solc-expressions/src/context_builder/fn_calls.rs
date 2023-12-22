use solang_parser::helpers::CodeLocation;
use crate::{
    ExprErr, ExpressionParser, StatementParser
};

use graph::{
    nodes::{
        Context, ContextNode, FunctionNode,
    },
    AnalyzerBackend, ContextEdge, Edge, Node,
};

use solang_parser::{
    pt::{Expression, Statement},
};


impl<T> FnCallBuilder for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + StatementParser + ExpressionParser
{
}

/// Dispatcher for building up a context of a function
pub trait FnCallBuilder:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + StatementParser + ExpressionParser
{
    fn analyze_fn_calls(&mut self, caller: FunctionNode) {
    	self.fn_calls_fns_mut().entry(caller).or_default();
        if let Some(body) = caller.underlying(self).unwrap().body.clone() {
        	self.analyze_fn_calls_stmt(caller, body);
        }
    }

    fn analyze_fn_calls_stmt(&mut self, caller: FunctionNode, stmt: Statement) {
    	use Statement::*;
    	match stmt {
            Block {statements, ..} => {
            	statements.iter().for_each(|stmt| {
            		self.analyze_fn_calls_stmt(caller, stmt.clone());
            	});
            },
		    Assembly {..} => {},
		    Args(_, args) => {
		    	args.iter().for_each(|arg| {
		    		self.analyze_fn_calls_expr(caller, arg.expr.clone());
		    	});
		    },
		    If(_, expr, stmt_true, maybe_stmt_false) => {
		    	self.analyze_fn_calls_expr(caller, expr);
		    	self.analyze_fn_calls_stmt(caller, *stmt_true);
		    	if let Some(stmt_false) = maybe_stmt_false {
		    		self.analyze_fn_calls_stmt(caller, *stmt_false);
		    	}
		    },
		    While(_, expr, stmt) => {
		    	self.analyze_fn_calls_expr(caller, expr);
		    	self.analyze_fn_calls_stmt(caller, *stmt);
		    },
		    Expression(_, expr) => self.analyze_fn_calls_expr(caller, expr),
		    VariableDefinition(_, var_decl, maybe_expr) => {
		    	self.analyze_fn_calls_expr(caller, var_decl.ty);
		    	if let Some(expr) = maybe_expr {
		    		self.analyze_fn_calls_expr(caller, expr);
		    	}
		    },
		    For(_, maybe_stmt, maybe_expr, maybe_stmt_1, maybe_stmt_2) => {
		    	if let Some(stmt) = maybe_stmt {
		    		self.analyze_fn_calls_stmt(caller, *stmt);
		    	}
		    	
		    	if let Some(expr) = maybe_expr {
		    		self.analyze_fn_calls_expr(caller, *expr);
		    	}

		    	if let Some(stmt1) = maybe_stmt_1 {
		    		self.analyze_fn_calls_stmt(caller, *stmt1);
		    	}
		    	
		    	if let Some(stmt2) = maybe_stmt_2 {
		    		self.analyze_fn_calls_stmt(caller, *stmt2);
		    	}
		    },
		    DoWhile(_, stmt, expr) => {
		    	self.analyze_fn_calls_stmt(caller, *stmt);
				self.analyze_fn_calls_expr(caller, expr);
		    },
		    Continue(_) => {},
		    Break(_) => {},
		    Return(_, maybe_expr) => {
		    	if let Some(expr) = maybe_expr {
		    		self.analyze_fn_calls_expr(caller, expr);
		    	}
		    },
		    Revert(_, _, exprs) => {
		    	exprs.iter().for_each(|expr| {
		    		self.analyze_fn_calls_expr(caller, expr.clone());
		    	});
		    },
		    RevertNamedArgs(_, _, args) => {
		    	args.iter().for_each(|arg| {
		    		self.analyze_fn_calls_expr(caller, arg.expr.clone());
		    	});
		    },
		    Emit(_, expr) => {
		    	self.analyze_fn_calls_expr(caller, expr);
		    },
		    Try(_, expr, maybe_tuple, catch_clauses) => {
		    	self.analyze_fn_calls_expr(caller, expr);
		    	// Option<(ParameterList, Box<Statement>)>
		    	if let Some((param_list, stmt)) = maybe_tuple {
		    		param_list.iter().for_each(|(_, maybe_param)| {
		    			if let Some(param) = maybe_param {
		    				self.analyze_fn_calls_expr(caller, param.ty.clone());
		    			}
		    		});
		    		self.analyze_fn_calls_stmt(caller, *stmt);
		    	}

		    	catch_clauses.iter().for_each(|catch_clause| {
		    		match catch_clause {
	    			    solang_parser::pt::CatchClause::Simple(_, maybe_param, stmt) => {
	    			    	if let Some(param) = maybe_param {
			    				self.analyze_fn_calls_expr(caller, param.ty.clone());
			    			}
			    			self.analyze_fn_calls_stmt(caller, stmt.clone());
	    			    },
					    solang_parser::pt::CatchClause::Named(_, _, param, stmt) => {
					    	self.analyze_fn_calls_expr(caller, param.ty.clone());
					    	self.analyze_fn_calls_stmt(caller, stmt.clone());
					    },
		    		}
		    	})
		    },
		    Error(_) => {},
		}
    }

    fn analyze_fn_calls_expr(&mut self, caller: FunctionNode, expr: Expression) {
    	use Expression::*;
        match expr {
        	BoolLiteral(_, _)
		    | NumberLiteral(_, _, _, _)
		    | RationalNumberLiteral(_, _, _, _, _)
		    | HexNumberLiteral(_, _, _)
		    | StringLiteral(_)
		    | HexLiteral(_)
		    | AddressLiteral(_, _)
		    | Variable(_)
		    | This(_) => {}

        	PostIncrement(_, expr)
		    | PostDecrement(_, expr)
		    | New(_, expr)
		    | Parenthesis(_, expr)
		    | MemberAccess(_, expr, _)
		    | Not(_, expr)
		    | Delete(_, expr)
		    | PreIncrement(_, expr)
		    | PreDecrement(_, expr)
		    | BitwiseNot(_, expr)
		    | Negate(_, expr)
		    | UnaryPlus(_, expr) => {
		    	self.analyze_fn_calls_expr(caller, *expr);
		    }

		    Power(_, expr, expr1)
		    | Multiply(_, expr, expr1)
		    | Divide(_, expr, expr1)
		    | Modulo(_, expr, expr1)
		    | Add(_, expr, expr1)
		    | Subtract(_, expr, expr1)
		    | ShiftLeft(_, expr, expr1)
		    | ShiftRight(_, expr, expr1)
		    | BitwiseAnd(_, expr, expr1)
		    | BitwiseXor(_, expr, expr1)
		    | BitwiseOr(_, expr, expr1)
		    | Less(_, expr, expr1)
		    | More(_, expr, expr1)
		    | LessEqual(_, expr, expr1)
		    | MoreEqual(_, expr, expr1)
		    | Equal(_, expr, expr1)
		    | NotEqual(_, expr, expr1)
		    | And(_, expr, expr1)
		    | Or(_, expr, expr1)
		    | Assign(_, expr, expr1)
		    | AssignOr(_, expr, expr1)
		    | AssignAnd(_, expr, expr1)
		    | AssignXor(_, expr, expr1)
		    | AssignShiftLeft(_, expr, expr1)
		    | AssignShiftRight(_, expr, expr1)
		    | AssignAdd(_, expr, expr1)
		    | AssignSubtract(_, expr, expr1)
		    | AssignMultiply(_, expr, expr1)
		    | AssignDivide(_, expr, expr1)
		    | AssignModulo(_, expr, expr1) => {
		    	self.analyze_fn_calls_expr(caller, *expr);
		    	self.analyze_fn_calls_expr(caller, *expr1);
		    }

		    ArraySubscript(_, expr, maybe_expr) => {
		    	self.analyze_fn_calls_expr(caller, *expr);
		    	if let Some(expr1) = maybe_expr {
		    		self.analyze_fn_calls_expr(caller, *expr1);
		    	}
		    },
		    ArraySlice(_, expr, maybe_expr, maybe_expr1) => {
		    	self.analyze_fn_calls_expr(caller, *expr);
		    	if let Some(expr1) = maybe_expr {
		    		self.analyze_fn_calls_expr(caller, *expr1);
		    	}

		    	if let Some(expr2) = maybe_expr1 {
		    		self.analyze_fn_calls_expr(caller, *expr2);
		    	}
		    },
		    ConditionalOperator(_, expr, expr1, expr2) => {
		    	self.analyze_fn_calls_expr(caller, *expr);
		    	self.analyze_fn_calls_expr(caller, *expr1);
		    	self.analyze_fn_calls_expr(caller, *expr2);
		    },
		    List(_, param_list) => {
		    	param_list.iter().for_each(|(_, maybe_param)| {
	    			if let Some(param) = maybe_param {
	    				self.analyze_fn_calls_expr(caller, param.ty.clone());
	    			}
	    		});
		    },
		    ArrayLiteral(_, exprs) => {
		    	exprs.into_iter().for_each(|expr| {
    				self.analyze_fn_calls_expr(caller, expr);
	    		});
		    },
		    
		    Type(_, ty) => {
		    	match ty {
		    		solang_parser::pt::Type::Mapping {
				        key,
				        value,
				        ..
				    } => {
		    			self.analyze_fn_calls_expr(caller, *key);
				    	self.analyze_fn_calls_expr(caller, *value);
		    		},
				    solang_parser::pt::Type::Function {
				        params,
				        returns,
				        ..
				    } => {
				    	params.iter().for_each(|(_, maybe_param)| {
			    			if let Some(param) = maybe_param {
			    				self.analyze_fn_calls_expr(caller, param.ty.clone());
			    			}
			    		});
			    		if let Some((param_list, _)) = returns {
			    			param_list.iter().for_each(|(_, maybe_param)| {
				    			if let Some(param) = maybe_param {
				    				self.analyze_fn_calls_expr(caller, param.ty.clone());
				    			}
				    		});
			    		}
				    },
				    _ => {}
		    	}
		    },

            FunctionCallBlock(_, func_expr, _input_exprs) => {
            	match *func_expr {
		            Variable(ref ident) => {
		            	let loc = func_expr.loc();
			            let ctx = Context::new(caller, format!("<{}_parser_fn>", caller.name(self).unwrap()), loc);
			            let ctx = ContextNode::from(self.add_node(Node::Context(ctx)));
				        let visible_funcs = ctx
				            .visible_funcs(self)
				            .unwrap();
				        let possible_funcs: Vec<_> = visible_funcs.into_iter().filter(|f| f.name(self).unwrap().starts_with(&ident.name)).collect();
				        if possible_funcs.len() == 1 {
				        	let func = possible_funcs[0];
				        	self.add_fn_call(caller, func);
				        }
		            },
		            _ => {}
		        }
            }
            NamedFunctionCall(_, func_expr, _input_args) => {
                match *func_expr {
		            Variable(ref ident) => {
		            	let loc = func_expr.loc();
			            let ctx = Context::new(caller, format!("<{}_parser_fn>", caller.name(self).unwrap()), loc);
			            let ctx = ContextNode::from(self.add_node(Node::Context(ctx)));
				        let visible_funcs = ctx
				            .visible_funcs(self)
				            .unwrap();
				        let possible_funcs: Vec<_> = visible_funcs.into_iter().filter(|f| f.name(self).unwrap().starts_with(&ident.name)).collect();
				        if possible_funcs.len() == 1 {
				        	let func = possible_funcs[0];
				        	self.add_fn_call(caller, func);
				        }
		            },
		            _ => {}
		        }
            }
            FunctionCall(_, func_expr, input_exprs) => {
            	match *func_expr {
		            Variable(ref ident) => {
		            	let loc = func_expr.loc();
			            let ctx = Context::new(caller, format!("<{}_parser_fn>", caller.name(self).unwrap()), loc);
			            let ctx = ContextNode::from(self.add_node(Node::Context(ctx)));
				        let visible_funcs = ctx
				            .visible_funcs(self)
				            .unwrap();
				        let possible_funcs: Vec<_> = visible_funcs.into_iter().filter(|f| f.name(self).unwrap().starts_with(&ident.name)).collect();
				        if possible_funcs.len() == 1 {
				        	let func = possible_funcs[0];
				        	self.add_fn_call(caller, func);
				        }
		            },
		            _ => {}
		        }

		        input_exprs.iter().for_each(|expr| {
		        	self.analyze_fn_calls_expr(caller, expr.clone());
		        })
            },
        }
    }
}