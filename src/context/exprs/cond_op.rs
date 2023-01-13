use crate::ExprRet;
use crate::Context;


use crate::AnalyzerLike;
use crate::{
    exprs::Require,
    ContextBuilder, ContextEdge, ContextNode, ContextVarNode, Edge, Node, NodeIdx,
};

use solang_parser::pt::{Expression, Loc};

impl<T> CondOp for T where T: AnalyzerLike + Require + Sized {}
pub trait CondOp: AnalyzerLike + Require + Sized {
	/// When we have a conditional operator, we create a fork in the context. One side of the fork is
    /// if the expression is true, the other is if it is false.
    fn cond_op_expr(
        &mut self,
        loc: Loc,
        if_expr: &Expression,
        true_expr: &Expression,
        false_expr: &Expression,
        ctx: ContextNode,
    ) -> ExprRet {
    	let true_subctx = ContextNode::from(self.add_node(Node::Context(Context::new_subctx(ctx, loc, true, self))));
    	ctx.add_fork(true_subctx, self);
    	let false_subctx = ContextNode::from(self.add_node(Node::Context(Context::new_subctx(ctx, loc, true, self))));
    	ctx.add_fork(false_subctx, self);
    	let ctx_fork = self.add_node(Node::ContextFork);
    	self.add_edge(ctx_fork, ctx, Edge::Context(ContextEdge::ContextFork));
    	self.add_edge(NodeIdx::from(true_subctx.0), ctx_fork, Edge::Context(ContextEdge::Subcontext));
    	self.add_edge(NodeIdx::from(false_subctx.0), ctx_fork, Edge::Context(ContextEdge::Subcontext));

    	let true_cvars = self.parse_ctx_expr(true_expr, true_subctx);
    	self.match_true(loc, &true_cvars, if_expr);

        let false_cvars = self.parse_ctx_expr(false_expr, false_subctx);
    	self.match_false(loc, &false_cvars, if_expr);

        ExprRet::Fork(Box::new(true_cvars), Box::new(false_cvars))
    }

    fn match_true(&mut self, loc: Loc, true_cvars: &ExprRet, if_expr: &Expression) {
    	match true_cvars {
    		ExprRet::CtxKilled => {},
    		ExprRet::Single((fork_ctx, true_cvar)) => {
    			self.true_fork_if_cvar(ContextVarNode::from(*true_cvar).underlying(self).loc.unwrap_or(loc), if_expr.clone(), *fork_ctx);
    		}
    		ExprRet::Multi(ref true_paths) => {
    			true_paths.iter().for_each(|expr_ret| {
		    		let (fork_ctx, true_cvar) = expr_ret.expect_single();
		    		self.true_fork_if_cvar(ContextVarNode::from(true_cvar).underlying(self).loc.unwrap_or(loc), if_expr.clone(), fork_ctx);
		    	});
    		}
    		ExprRet::Fork(true_paths, other_true_paths) => {
    			self.match_true(loc, true_paths, if_expr);
    			self.match_true(loc, other_true_paths, if_expr);
    		}
    	}
    }

    fn match_false(&mut self, loc: Loc, false_cvars: &ExprRet, if_expr: &Expression) {
    	match false_cvars {
    		ExprRet::CtxKilled => {},
    		ExprRet::Single((fork_ctx, false_cvar)) => {
    			self.false_fork_if_cvar(ContextVarNode::from(*false_cvar).underlying(self).loc.unwrap_or(loc), if_expr.clone(), *fork_ctx);
    		}
    		ExprRet::Multi(ref false_paths) => {
    			false_paths.iter().for_each(|expr_ret| {
		        	let (fork_ctx, false_cvar) = expr_ret.expect_single();
		    		self.false_fork_if_cvar(ContextVarNode::from(false_cvar).underlying(self).loc.unwrap_or(loc), if_expr.clone(), fork_ctx);
		    	});
    		}
    		ExprRet::Fork(false_paths, other_false_paths) => {
    			self.match_false(loc, false_paths, if_expr);
    			self.match_false(loc, other_false_paths, if_expr);
    		}
    	}
    }

    /// Creates the true_fork cvar (updates bounds assuming its true)
    fn true_fork_if_cvar(&mut self, loc: Loc, if_expr: Expression, true_fork_ctx: ContextNode) {
    	let if_expr = match if_expr {
    		Expression::Less(_loc, lhs, rhs) => {
                Expression::Less(loc, lhs, rhs)
            }
            Expression::More(_loc, lhs, rhs) => {
                Expression::More(loc, lhs, rhs)
            }
            Expression::MoreEqual(_loc, lhs, rhs) => {
                Expression::MoreEqual(loc, lhs, rhs)
            }
            Expression::LessEqual(_loc, lhs, rhs) => {
                Expression::LessEqual(loc, lhs, rhs)
            }
            Expression::Variable(ref ident) => {
            	let mut c = ident.clone();
            	c.loc = loc;
            	Expression::Variable(c)
            }
            e => todo!("Wasnt comparator: {:?}", e)
    	};
    	self.handle_require(&vec![if_expr], true_fork_ctx)
    }

    /// Creates the false_fork cvar (inverts the expression and sets the bounds assuming its false)
    fn false_fork_if_cvar(&mut self, loc: Loc, if_expr: Expression, false_fork_ctx: ContextNode) {
    	let inv_if_expr = match if_expr {
    		Expression::Less(_loc, lhs, rhs) => {
                Expression::MoreEqual(loc, lhs, rhs)
            }
            Expression::More(_loc, lhs, rhs) => {
                Expression::LessEqual(loc, lhs, rhs)
            }
            Expression::MoreEqual(_loc, lhs, rhs) => {
                Expression::Less(loc, lhs, rhs)
            }
            Expression::LessEqual(_loc, lhs, rhs) => {
                Expression::More(loc, lhs, rhs)
            }
            Expression::Variable(ref _ident) => {
            	Expression::Not(loc, Box::new(if_expr))
            }
            e => todo!("Wasnt comparator: {:?}", e)
    	};
    	self.handle_require(&vec![inv_if_expr], false_fork_ctx)
    }
}