use crate::{
    AnalyzerBackend, GraphBackend, GraphError, VarType, Node, SolcRange, TypeNode,
    range::Range,
    nodes::{ContextVarNode, ContextNode, Concrete, Builtin, ContractNode, FunctionNode, FunctionParam, FunctionReturn, BuiltInNode, EnumNode, Field, TyNode, StructNode, ConcreteNode},
};

use crate::range::elem::*;
use shared::NodeIdx;

use solang_parser::pt::{StorageLocation, Loc};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextVar {
    pub loc: Option<Loc>,
    pub name: String,
    pub display_name: String,
    pub storage: Option<StorageLocation>,
    pub is_tmp: bool,
    pub tmp_of: Option<TmpConstruction>,
    pub is_symbolic: bool,
    pub is_return: bool,
    pub ty: VarType,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct TmpConstruction {
    pub lhs: ContextVarNode,
    pub op: RangeOp,
    pub rhs: Option<ContextVarNode>,
}

impl TmpConstruction {
    pub fn new(lhs: ContextVarNode, op: RangeOp, rhs: Option<ContextVarNode>) -> Self {
        Self { lhs, op, rhs }
    }
}

impl ContextVar {
    pub fn eq_ignore_loc(&self, other: &Self) -> bool {
        self.name == other.name
            && self.display_name == other.display_name
            && self.storage == other.storage
            && self.is_tmp == other.is_tmp
            && self.tmp_of == other.tmp_of
            && self.is_symbolic == other.is_symbolic
            && self.is_return == other.is_return
            && self.ty == other.ty
    }

    pub fn is_tmp(&self) -> bool {
        self.is_tmp || self.tmp_of.is_some()
    }

    pub fn tmp_of(&self) -> Option<TmpConstruction> {
        self.tmp_of
    }

    pub fn new_from_concrete(
        loc: Loc,
        ctx: ContextNode,
        concrete_node: ConcreteNode,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<Self, GraphError> {
        let name = format!(
            "tmp_{}({})",
            ctx.new_tmp(analyzer)?,
            concrete_node.underlying(analyzer)?.as_string()
        );
        Ok(ContextVar {
            loc: Some(loc),
            name,
            display_name: concrete_node.underlying(analyzer)?.as_human_string(),
            storage: None,
            is_tmp: true,
            tmp_of: None,
            is_symbolic: false,
            is_return: false,
            ty: VarType::Concrete(concrete_node),
        })
    }

    pub fn as_cast_tmp(
        &self,
        loc: Loc,
        ctx: ContextNode,
        cast_ty: Builtin,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<Self, GraphError> {
        let mut new_tmp = self.clone();
        new_tmp.loc = Some(loc);
        new_tmp.is_tmp = true;
        new_tmp.name = format!(
            "tmp_{}({}({}))",
            ctx.new_tmp(analyzer)?,
            cast_ty.as_string(analyzer)?,
            self.name
        );
        new_tmp.display_name = format!("{}({})", cast_ty.as_string(analyzer)?, self.display_name);
        Ok(new_tmp)
    }

    pub fn as_tmp(
        &self,
        loc: Loc,
        ctx: ContextNode,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<Self, GraphError> {
        let mut new_tmp = self.clone();
        new_tmp.loc = Some(loc);
        new_tmp.is_tmp = true;
        new_tmp.name = format!("tmp{}({})", ctx.new_tmp(analyzer)?, self.name);
        new_tmp.display_name = format!("tmp_{}", self.display_name);
        Ok(new_tmp)
    }

    pub fn new_from_contract(
        loc: Loc,
        contract_node: ContractNode,
        analyzer: &impl GraphBackend,
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(loc),
            name: contract_node.name(analyzer)?,
            display_name: contract_node.name(analyzer)?,
            storage: None,
            is_tmp: false,
            tmp_of: None,
            is_symbolic: true,
            is_return: false,
            ty: VarType::User(
                TypeNode::Contract(contract_node),
                SolcRange::try_from_builtin(&Builtin::Address),
            ),
        })
    }

    pub fn new_from_struct(
        loc: Loc,
        struct_node: StructNode,
        ctx: ContextNode,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(loc),
            name: format!(
                "tmp_struct_{}_{}",
                ctx.new_tmp(analyzer)?,
                struct_node.name(analyzer)?
            ),
            display_name: struct_node.name(analyzer)?,
            storage: Some(StorageLocation::Memory(Loc::Implicit)),
            is_tmp: false,
            tmp_of: None,
            is_symbolic: true,
            is_return: false,
            ty: VarType::User(TypeNode::Struct(struct_node), None),
        })
    }

    pub fn new_from_ty(
        loc: Loc,
        ty_node: TyNode,
        ctx: ContextNode,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(loc),
            name: format!(
                "tmp_ty_{}_{}",
                ctx.new_tmp(analyzer)?,
                ty_node.name(analyzer)?
            ),
            display_name: ty_node.name(analyzer)?,
            storage: Some(StorageLocation::Memory(Loc::Implicit)),
            is_tmp: false,
            tmp_of: None,
            is_symbolic: true,
            is_return: false,
            ty: VarType::try_from_idx(analyzer, ty_node.0.into()).unwrap(),
        })
    }

    pub fn new_from_builtin(
        loc: Loc,
        bn_node: BuiltInNode,
        analyzer: &impl GraphBackend,
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(loc),
            name: format!("tmp_{}", bn_node.underlying(analyzer)?.as_string(analyzer)?),
            display_name: format!("tmp_{}", bn_node.underlying(analyzer)?.as_string(analyzer)?),
            storage: None,
            is_tmp: true,
            tmp_of: None,
            is_symbolic: false,
            is_return: false,
            ty: VarType::try_from_idx(analyzer, bn_node.into()).unwrap(),
        })
    }

    pub fn fallback_range(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<SolcRange>, GraphError> {
        match &self.ty {
            VarType::User(TypeNode::Contract(_), ref maybe_range) => {
                if let Some(range) = maybe_range {
                    Ok(Some(range.clone()))
                } else {
                    Ok(SolcRange::try_from_builtin(&Builtin::Address))
                }
            }
            VarType::User(TypeNode::Enum(enum_node), ref maybe_range) => {
                if let Some(range) = maybe_range {
                    Ok(Some(range.clone()))
                } else {
                    Ok(enum_node.maybe_default_range(analyzer)?)
                }
            }
            VarType::User(TypeNode::Ty(ty_node), ref maybe_range) => {
                if let Some(range) = maybe_range {
                    Ok(Some(range.clone()))
                } else {
                    let underlying =
                        BuiltInNode::from(ty_node.underlying(analyzer)?.ty).underlying(analyzer)?;
                    Ok(SolcRange::try_from_builtin(underlying))
                }
            }
            VarType::BuiltIn(bn, ref maybe_range) => {
                if let Some(range) = maybe_range {
                    Ok(Some(range.clone()))
                } else {
                    let underlying = bn.underlying(analyzer)?;
                    Ok(SolcRange::try_from_builtin(underlying))
                }
            }
            VarType::Concrete(cn) => Ok(SolcRange::from(cn.underlying(analyzer)?.clone())),
            _ => Ok(None),
        }
    }

    pub fn set_range(&mut self, new_range: SolcRange) {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                *maybe_range = Some(new_range);
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin: {e:?}"),
        }
    }

    pub fn needs_fallback(&self) -> bool {
        match &self.ty {
            VarType::User(TypeNode::Contract(_), ref maybe_range)
            | VarType::User(TypeNode::Enum(_), ref maybe_range)
            | VarType::User(TypeNode::Ty(_), ref maybe_range)
            | VarType::BuiltIn(_, ref maybe_range) => maybe_range.is_some(),
            _ => false,
        }
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    pub fn set_range_min(&mut self, new_min: Elem<Concrete>, fallback_range: Option<SolcRange>) {
        // tracing::trace!("Setting range min in underlying: {:?}", self.ty);
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_min(new_min);
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_min(new_min);
                    *maybe_range = Some(fr);
                }
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin: {e:?}"),
        }
    }

    pub fn try_set_range_min(
        &mut self,
        new_min: Elem<Concrete>,
        fallback_range: Option<SolcRange>,
    ) -> bool {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_min(new_min);
                    true
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_min(new_min);
                    *maybe_range = Some(fr);
                    true
                }
            }
            VarType::Concrete(_) => true,
            _ => false,
        }
    }

    pub fn set_range_max(&mut self, new_max: Elem<Concrete>, fallback_range: Option<SolcRange>) {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_max(new_max);
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_max(new_max);
                    *maybe_range = Some(fr);
                }
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin or concrete: {e:?}"),
        }
    }

    pub fn set_range_exclusions(
        &mut self,
        new_exclusions: Vec<Elem<Concrete>>,
        fallback_range: Option<SolcRange>,
    ) {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_exclusions(new_exclusions);
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_exclusions(new_exclusions);
                    *maybe_range = Some(fr);
                }
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin or concrete: {e:?}"),
        }
    }

    pub fn try_set_range_max(
        &mut self,
        new_max: Elem<Concrete>,
        fallback_range: Option<SolcRange>,
    ) -> bool {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_max(new_max);
                    true
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_max(new_max);
                    *maybe_range = Some(fr);
                    true
                }
            }
            VarType::Concrete(_) => true,
            _ => false,
        }
    }

    pub fn try_set_range_exclusions(
        &mut self,
        new_exclusions: Vec<Elem<Concrete>>,
        fallback_range: Option<SolcRange>,
    ) -> bool {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_exclusions(new_exclusions);
                    true
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_exclusions(new_exclusions);
                    *maybe_range = Some(fr);
                    true
                }
            }
            VarType::Concrete(_) => true,
            _ => false,
        }
    }

    pub fn maybe_from_user_ty(
        analyzer: &impl GraphBackend,
        loc: Loc,
        node_idx: NodeIdx,
    ) -> Option<Self> {
        if let Some(ty) = VarType::try_from_idx(analyzer, node_idx) {
            let (name, storage) = match analyzer.node(node_idx) {
                Node::Contract(c) => {
                    let name = c.name.clone().expect("Contract had no name").name;
                    (name, None)
                }
                Node::Function(f) => {
                    let name = f.name.clone().expect("Function had no name").name;
                    (name, None)
                }
                Node::Struct(s) => {
                    let name = s.name.clone().expect("Struct had no name").name;
                    (name, None)
                }
                Node::Enum(e) => {
                    let name = e.name.clone().expect("Enum had no name").name;
                    (name, None)
                }
                Node::Var(var) => {
                    let name = var.name.clone().expect("Variable had no name").name;
                    let storage = if var.in_contract {
                        if !var.attrs.iter().any(|attr| {
                            matches!(attr, solang_parser::pt::VariableAttribute::Constant(_))
                        }) {
                            Some(StorageLocation::Storage(var.loc))
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    (name, storage)
                }
                Node::Ty(ty) => {
                    let name = &ty.name.name;
                    (name.clone(), None)
                }
                _ => return None,
            };

            Some(ContextVar {
                loc: Some(loc),
                name: name.clone(),
                display_name: name,
                storage,
                is_tmp: false,
                tmp_of: None,
                is_symbolic: true,
                is_return: false,
                ty,
            })
        } else {
            None
        }
    }

    pub fn maybe_new_from_field(
        analyzer: &impl GraphBackend,
        loc: Loc,
        parent_var: &ContextVar,
        field: Field,
    ) -> Option<Self> {
        if let Some(ty) = VarType::try_from_idx(analyzer, field.ty) {
            Some(ContextVar {
                loc: Some(loc),
                name: parent_var.name.clone()
                    + "."
                    + &field.name.clone().expect("Field had no name").name,
                display_name: parent_var.name.clone()
                    + "."
                    + &field.name.expect("Field had no name").name,
                storage: parent_var.storage.clone(),
                is_tmp: false,
                tmp_of: None,
                is_symbolic: true,
                is_return: false,
                ty,
            })
        } else {
            None
        }
    }

    pub fn new_from_enum_variant(
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
        ctx: ContextNode,
        loc: Loc,
        enum_node: EnumNode,
        variant: String,
    ) -> Result<Self, GraphError> {
        let enum_name = enum_node.name(analyzer)?;
        Ok(ContextVar {
            loc: Some(loc),
            name: format!("{}.{}_{}", enum_name, variant, ctx.new_tmp(analyzer)?),
            display_name: format!("{}.{}", enum_name, variant),
            storage: None,
            is_tmp: false,
            tmp_of: None,
            is_symbolic: true,
            is_return: false,
            ty: VarType::User(
                TypeNode::Enum(enum_node),
                Some(enum_node.range_from_variant(variant, analyzer)?),
            ),
        })
    }

    pub fn new_from_index(
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
        loc: Loc,
        parent_name: String,
        parent_display_name: String,
        parent_storage: StorageLocation,
        parent_var: &BuiltInNode,
        index: ContextVarNode,
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(loc),
            name: parent_name + "[" + &index.name(analyzer)? + "]",
            display_name: parent_display_name + "[" + &index.display_name(analyzer)? + "]",
            storage: Some(parent_storage),
            is_tmp: false,
            tmp_of: None,
            is_symbolic: index.underlying(analyzer)?.is_symbolic,
            is_return: false,
            ty: parent_var.dynamic_underlying_ty(analyzer)?,
        })
    }

    pub fn new_from_func(
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
        func: FunctionNode,
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(func.underlying(analyzer)?.loc),
            name: func.name(analyzer)?,
            display_name: func.name(analyzer)?,
            storage: None,
            is_tmp: false,
            tmp_of: None,
            is_symbolic: false,
            is_return: false,
            ty: VarType::User(TypeNode::Func(func), None),
        })
    }

    pub fn maybe_new_from_func_param(
        analyzer: &impl GraphBackend,
        param: FunctionParam,
    ) -> Option<Self> {
        if let Some(name) = param.name {
            if let Some(ty) = VarType::try_from_idx(analyzer, param.ty) {
                Some(ContextVar {
                    loc: Some(param.loc),
                    name: name.name.clone(),
                    display_name: name.name,
                    storage: param.storage,
                    is_tmp: false,
                    tmp_of: None,
                    is_symbolic: true,
                    is_return: false,
                    ty,
                })
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn maybe_new_from_func_ret(analyzer: &impl GraphBackend, ret: FunctionReturn) -> Option<Self> {
        if let Some(name) = ret.name {
            if let Some(ty) = VarType::try_from_idx(analyzer, ret.ty) {
                Some(ContextVar {
                    loc: Some(ret.loc),
                    name: name.name.clone(),
                    display_name: name.name,
                    storage: ret.storage,
                    is_tmp: false,
                    tmp_of: None,
                    is_symbolic: true,
                    is_return: true,
                    ty,
                })
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn new_from_func_ret(
        ctx: ContextNode,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
        ret: FunctionReturn,
    ) -> Result<Option<Self>, GraphError> {
        let (is_tmp, name) = if let Some(name) = ret.name {
            (false, name.name)
        } else {
            (true, format!("tmp_func_ret_{}", ctx.new_tmp(analyzer)?))
        };

        if let Some(ty) = VarType::try_from_idx(analyzer, ret.ty) {
            Ok(Some(ContextVar {
                loc: Some(ret.loc),
                name: name.clone(),
                display_name: name,
                storage: ret.storage,
                is_tmp,
                tmp_of: None,
                is_symbolic: true,
                is_return: true,
                ty,
            }))
        } else {
            Ok(None)
        }
    }
}