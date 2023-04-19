use shared::context::TmpConstruction;
use crate::GraphLike;
use shared::NodeIdx;
use petgraph::Directed;
use shared::context::ContextNode;
use crate::Node;
use petgraph::graph::Graph;


pub enum SolverEdge {
	DependsOn,
}

type SG = Graph<Node, SolverEdge, Directed, usize>;

pub struct SolverGraph {
	pub ctx: ContextNode,
	pub solver_graph: SG,
}

impl SolverGraph {
	pub fn new(ctx: ContextNode, analyzer: &impl GraphLike) -> Self {
		let deps = ctx.ctx_deps(analyzer).unwrap();
		let mut sg = SG::default();
		deps.iter().for_each(|(k, v)| {
			
			let underlying = v.underlying(analyzer).unwrap();
			if let Some(tmp) = underlying.tmp_of {
				Self::recurse_node(&mut sg, analyzer, tmp);	
			}
			
			println!("here: {:#?}", underlying.tmp_of);
		});
		
		todo!()
	}

	pub fn recurse_node(graph: &mut SG, analyzer: &impl GraphLike, tmp: TmpConstruction) {
		if tmp.lhs.is_tmp(analyzer).unwrap() {
			println!("lhs is tmp");
		}
		let lhs = analyzer.node(tmp.lhs.0);
		let rhs = match tmp.rhs {
			Some(rhs) => {
				if rhs.is_tmp(analyzer).unwrap() {
					println!("rhs is tmp");
				}
				Some(analyzer.node(rhs.0).clone())
			},
			None => None,
		};
		// println!("{lhs:#?} {rhs:#?}");
	}

	pub fn independent_nodes(&self) -> Vec<NodeIdx> {
		todo!()
	}
}