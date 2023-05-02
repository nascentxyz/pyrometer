// use shared::range::range_string::ToRangeString;
// use std::fmt::Write;
// use crate::GraphError;
// use crate::Analyzer;
// use shared::context::CallFork;
// use crate::shared::context::ContextNode;

// const PIPE: &str = "  │ ";
// const EDGE: &str = "  └─ ";
// const BRANCH: &str = "  ├─ ";
// const CALL: &str = "→ ";
// const RETURN: &str = "← ";

// impl Analyzer {
//     pub fn call_trace(&self, ctx: ContextNode) -> Result<Vec<String>, GraphError> {
//         self.inner(ctx, "".to_string(), "  ", "  ")
//     }

//     fn inner(
//         &self,
//         ctx: ContextNode,
//         mut curr: String,
//         left: &str,
//         child: &str,
//     ) -> Result<Vec<String>, GraphError> {
//     	let mut ret = vec![];
//         let left_prefix = format!("{child}{BRANCH}");
//         let right_prefix = format!("{child}{PIPE}");
//         let mut is_ret = false;
//         match ctx.underlying(self)?.child {
//         	Some(CallFork::Call(c)) => {
//         		println!("call");
//         		if c.underlying(self)?.depth >= ctx.underlying(self)?.depth {
//         			writeln!(curr, "{left}{}", ctx.associated_fn_name(self)?).unwrap();
//         		}
//     			ret.extend(self.inner(
//                     c,
//                     curr.clone(),
//                     &left_prefix,
//                     &right_prefix,
//                 )?);
//         	}
//         	Some(CallFork::Fork(w1, w2)) => {
//         		if w1.underlying(self)?.depth >= ctx.underlying(self)?.depth {
//         			writeln!(curr, "{left}{}", ctx.associated_fn_name(self)?).unwrap();
//         		}
//         		println!("fork");
//         		ret.extend(self.inner(
//                     w1,
//                     curr.clone(),
//                     &left_prefix,
//                     &right_prefix,
//                 )?);
//                 ret.extend(self.inner(
//                     w2,
//                     curr.clone(),
//                     &left_prefix,
//                     &right_prefix,
//                 )?);
//         	}
//         	None => {}
//         };

//         write!(curr, "{EDGE}{RETURN}({})", ctx.return_nodes(self).unwrap().iter().map(|(_, ret)| {
// 			let min = ret.evaled_range_min(self).unwrap().unwrap();
// 			let max = ret.evaled_range_max(self).unwrap().unwrap();
// 			format!("[ {}, {} ]",
// 				min.to_range_string(false, self).s,
// 				max.to_range_string(false, self).s
// 			)
// 		}).collect::<Vec<_>>().join(", ")).unwrap();

//         // Display trace return data
//         // let color = trace_color(&node.trace);

//         // writeln!(curr, "{}", node.trace.output)?;
//         // write!(curr, "{}").unwrap();
//         // if node.trace.created() {
//         //     if let RawOrDecodedReturnData::Raw(bytes) = &node.trace.output {
//         //         writeln!(writer, "{} bytes of code", bytes.len())?;
//         //     } else {
//         //         unreachable!("We should never have decoded calldata for contract creations");
//         //     }
//         // } else {
//         //     writeln!(writer, "{}", node.trace.output)?;
//         // }

//         ret.push(curr);
//         Ok(ret)
//     }
// }
