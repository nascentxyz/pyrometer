use crate::GraphLike;
use crate::Node;
use petgraph::graph::Graph;
use petgraph::Directed;
use shared::context::ContextNode;

use shared::range::elem::RangeOp;

pub struct SolverEdge {
    pub op: RangeOp,
    pub index: usize,
}

pub enum SolverNode {
    Var(String),
}

type SG = Graph<Node, SolverEdge, Directed, usize>;

pub struct SolverGraph {
    pub ctx: ContextNode,
    pub solver_graph: SG,
}

impl SolverGraph {
    pub fn new(ctx: ContextNode, analyzer: &impl GraphLike) -> Self {
        let deps = ctx.ctx_deps(analyzer).unwrap();
        let _sg = SG::default();
        deps.iter().for_each(|(_k, _v)| {});

        todo!()
    }

    //     pub fn recurse_node(idx: NodeIdx, graph: &mut SG, analyzer: &impl GraphLike) -> NodeIdx {

    //     	match elem {
    //     		Elem::Concrete(RangeConcrete { val, ..}) => {

    //     		}
    //     		Elem::Dynamic(Dynamic { idx }) => {
    //     			match analyzer.node(idx) {
    //     				Node::ContextVar(_) => {
    //     					ContextVarNode::from(idx).range(analyzer)
    //     				}
    //     			}
    //     		}
    //     		Elem::Expr(RangeExpr { lhs, op, rhs }) => {
    //     			let lhs = Self::recurse_node(lhs, graph, analyzer);
    //     			let rhs = Self::recurse_node(rhs, graph, analyzer);

    //     		}
    //     		Elem::ConcreteDyn(RangeDyn { len, val, .. }) => {

    //     		}
    //     		Elem::Null => {

    //     		}
    //     	}
    //         if tmp.lhs.is_tmp(analyzer).unwrap() {
    //             println!("lhs is tmp");
    //         }
    //         let _lhs = analyzer.node(tmp.lhs.0);
    //         let _rhs = match tmp.rhs {
    //             Some(rhs) => {
    //                 if rhs.is_tmp(analyzer).unwrap() {
    //                     println!("rhs is tmp");
    //                 }
    //                 Some(analyzer.node(rhs.0).clone())
    //             }
    //             None => None,
    //         };
    //         // println!("{lhs:#?} {rhs:#?}");
    //     }

    //     pub fn independent_nodes(&self) -> Vec<NodeIdx> {
    //         todo!()
    //     }
}
