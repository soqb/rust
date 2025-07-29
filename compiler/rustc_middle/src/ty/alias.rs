use std::marker::PhantomData;

use rustc_hir::def_id::DefId;
use rustc_macros::{HashStable, TyDecodable, TyEncodable, extension};
use rustc_span::{Span, Symbol};

use crate::ty::{self, TyCtxt};

/// A slimmer `GenericParamDef` which generalises to all aliases.
#[derive(Clone, Debug, TyEncodable, TyDecodable, HashStable)]
pub struct GenericAliasParamDef {
    pub name: Option<Symbol>,
    pub def_id: Option<DefId>,
    pub index: u32,
    pub kind: ty::GenericParamDefKind,
}

impl<'a> From<&'a ty::GenericParamDef> for GenericAliasParamDef {
    fn from(param: &'a ty::GenericParamDef) -> GenericAliasParamDef {
        GenericAliasParamDef {
            name: Some(param.name),
            def_id: Some(param.def_id),
            index: param.index,
            kind: param.kind.clone(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, HashStable, TyEncodable, TyDecodable)]
pub enum AliasCtor<'tcx> {
    /// The `DefId` of the `TraitItem` or `ImplItem` for the associated type `N` depending on whether
    /// this is a projection or an inherent projection or the `DefId` of the `OpaqueType` item if
    /// this is an opaque.
    ///
    /// During codegen, `interner.type_of(def_id)` can be used to get the type of the
    /// underlying type if the type is an opaque.
    ///
    /// Note that if this is an associated type, this is not the `DefId` of the
    /// `TraitRef` containing this associated type, which is in `interner.associated_item(def_id).container`,
    /// aka. `interner.parent(def_id)`.
    Def(DefId),
    _No(!, PhantomData<&'tcx ()>),
}

impl<'tcx> AliasCtor<'tcx> {
    pub fn expect_def(self) -> DefId {
        let AliasCtor::Def(def_id) = self;
        def_id
    }

    pub fn def(self) -> Option<DefId> {
        let AliasCtor::Def(def_id) = self;
        Some(def_id)
    }

    pub fn is_local_def(self) -> bool {
        matches!(self, AliasCtor::Def(def_id) if def_id.is_local())
    }

    pub fn span(self, cx: TyCtxt<'tcx>) -> Span {
        match self {
            AliasCtor::Def(def_id) => cx.def_span(def_id),
        }
    }

    pub fn bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Clause<'tcx>>> {
        match self {
            AliasCtor::Def(def_id) => cx.item_bounds(def_id).map_bound(IntoIterator::into_iter),
        }
    }

    pub fn self_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Clause<'tcx>>> {
        match self {
            AliasCtor::Def(def_id) => {
                cx.item_self_bounds(def_id).map_bound(IntoIterator::into_iter)
            }
        }
    }

    pub fn non_self_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Clause<'tcx>>> {
        match self {
            AliasCtor::Def(def_id) => {
                cx.item_non_self_bounds(def_id).map_bound(IntoIterator::into_iter)
            }
        }
    }

    pub fn const_conditions(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Binder<'tcx, ty::TraitRef<'tcx>>>> {
        match self {
            AliasCtor::Def(def_id) => ty::EarlyBinder::bind(
                cx.const_conditions(def_id).instantiate_identity(cx).into_iter().map(|(c, _)| c),
            ),
        }
    }

    pub fn explicit_implied_const_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Binder<'tcx, ty::TraitRef<'tcx>>>> {
        match self {
            AliasCtor::Def(def_id) => ty::EarlyBinder::bind(
                cx.explicit_implied_const_bounds(def_id).iter_identity_copied().map(|(c, _)| c),
            ),
        }
    }

    pub fn predicates(self, cx: TyCtxt<'tcx>) -> ty::GenericPredicates<'tcx> {
        match self {
            AliasCtor::Def(def_id) => cx.predicates_of(def_id),
        }
    }

    pub fn explicit_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, &'tcx [(ty::Clause<'tcx>, Span)]> {
        match self {
            AliasCtor::Def(def_id) => cx.explicit_item_bounds(def_id),
        }
    }

    pub fn explicit_self_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, &'tcx [(ty::Clause<'tcx>, Span)]> {
        match self {
            AliasCtor::Def(def_id) => cx.explicit_item_self_bounds(def_id),
        }
    }

    pub fn variances(self, cx: TyCtxt<'tcx>) -> &'tcx [ty::Variance] {
        match self {
            AliasCtor::Def(def_id) => cx.variances_of(def_id),
        }
    }

    pub fn generics(self, cx: TyCtxt<'tcx>) -> impl ExactSizeIterator<Item = GenericAliasParamDef> {
        match self {
            AliasCtor::Def(def_id) => cx.generics_of(def_id).own_params.iter().map(From::from),
        }
    }
}

impl<'tcx> rustc_type_ir::inherent::AliasCtor<TyCtxt<'tcx>> for AliasCtor<'tcx> {
    fn expect_def(self) -> DefId {
        self.expect_def()
    }

    fn span(self, cx: TyCtxt<'tcx>) -> Span {
        self.span(cx)
    }

    fn bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Clause<'tcx>>> {
        self.bounds(cx)
    }

    fn self_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Clause<'tcx>>> {
        self.self_bounds(cx)
    }

    fn non_self_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Clause<'tcx>>> {
        self.non_self_bounds(cx)
    }

    fn def(self) -> Option<DefId> {
        self.def()
    }

    fn const_conditions(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Binder<'tcx, ty::TraitRef<'tcx>>>> {
        self.const_conditions(cx)
    }

    fn explicit_implied_const_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Binder<'tcx, ty::TraitRef<'tcx>>>> {
        self.explicit_implied_const_bounds(cx)
    }
}

impl<'tcx> From<DefId> for AliasCtor<'tcx> {
    fn from(def_id: DefId) -> AliasCtor<'tcx> {
        AliasCtor::Def(def_id)
    }
}

#[extension(pub trait AliasTyInstExt<'tcx>)]
impl<'tcx> ty::AliasTy<'tcx> {
    fn predicates_instantiated(
        self,
        cx: TyCtxt<'tcx>,
    ) -> impl Iterator<Item = (ty::Clause<'tcx>, Span)> + DoubleEndedIterator + ExactSizeIterator
    {
        self.ctor.predicates(cx).instantiate_own(cx, self.args)
    }

    fn args_with_variances(
        self,
        cx: TyCtxt<'tcx>,
    ) -> impl Iterator<Item = (ty::GenericArg<'tcx>, ty::Variance)> {
        self.args.iter().zip(self.ctor.variances(cx).iter().copied())
    }
}
