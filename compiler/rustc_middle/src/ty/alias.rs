use std::hash::{Hash, Hasher};
use std::hint::unreachable_unchecked;
use std::marker::PhantomData;
use std::{fmt, ptr};

use rustc_data_structures::intern::Interned;
use rustc_data_structures::stable_hasher::{HashStable, StableHasher};
use rustc_data_structures::sync::{DynSend, DynSync};
use rustc_hir::LangItem;
use rustc_hir::def_id::{CrateNum, DefId, DefIndex};
use rustc_macros::{HashStable, TyDecodable, TyEncodable, extension};
use rustc_query_system::ich::StableHashingContext;
use rustc_serialize::{Decodable, Encodable};
use rustc_span::{Span, Symbol, sym};
use rustc_type_ir::UpcastFrom;
use rustc_type_ir::lift::Lift;
use smallvec::SmallVec;

use crate::ty::codec::{TyDecoder, TyEncoder};
use crate::ty::{self, Ty, TyCtxt};

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

#[derive(Debug, Clone, PartialEq, Eq, Hash, HashStable, TyEncodable, TyDecodable)]
pub struct VariadicAliasCtorStorage<'tcx> {
    span: Span,
    variadic_spans: Vec<Span>,
    // FIXME(soqb): Vec<bool> is inefficient; use some kind of bitvec.
    inner: SmallVec<[bool; 16]>,
    explicit_bounds: ty::EarlyBinder<'tcx, ty::Clauses<'tcx>>,
}

impl<'tcx> VariadicAliasCtor<'tcx> {
    pub fn len(self) -> usize {
        self.0.inner.len()
    }

    pub fn params(self) -> impl Iterator<Item = GenericAliasParamDef> + ExactSizeIterator {
        (0..self.len()).map(|index| GenericAliasParamDef {
            name: None,
            def_id: None,
            index: index as u32,
            kind: ty::GenericParamDefKind::Type { has_default: false, synthetic: false },
        })
    }

    pub fn tuple_params(
        self,
    ) -> impl Iterator<Item = ty::TupleParam<'tcx>> + ExactSizeIterator + DoubleEndedIterator {
        let mut spans = self.0.0.variadic_spans.iter();
        self.0.0.inner.iter().map(move |is_variadic| {
            if *is_variadic {
                ty::TupleParam::Unpacked(*spans.next().unwrap())
            } else {
                ty::TupleParam::Inline
            }
        })
    }

    pub fn span(self) -> Span {
        self.0.span
    }

    pub fn new(
        cx: TyCtxt<'tcx>,
        span: Span,
        params: impl IntoIterator<Item = ty::TupleParam<'tcx>>,
    ) -> VariadicAliasCtor<'tcx> {
        let params = params.into_iter();
        let mut spans = Vec::with_capacity(params.size_hint().0);
        let inner: SmallVec<_> = params
            .map(|param| match param {
                ty::TupleParam::Inline => false,
                ty::TupleParam::Unpacked(span) => {
                    spans.push(span);
                    true
                }
            })
            .collect();

        if inner.is_empty() {
            span_bug!(span, "created a variadic alias with zero arguments");
        } else if spans.is_empty() {
            span_bug!(span, "created a variadic alias with zero unpacked parameters");
        }

        let sized = cx.require_lang_item(LangItem::Sized, span);
        let tuple = cx.require_lang_item(LangItem::Tuple, span);

        let sized = (0..inner.len() - 1).map(|i| {
            ty::Clause::upcast_from(
                ty::ClauseKind::Trait(ty::TraitPredicate {
                    trait_ref: ty::TraitRef::new_from_args(
                        cx,
                        sized,
                        cx.mk_args(std::slice::from_ref(
                            &Ty::new_param(cx, i as u32, sym::T).into(),
                        )),
                    ),
                    polarity: ty::PredicatePolarity::Positive,
                }),
                cx,
            )
        });

        let tuple = inner.iter().enumerate().filter(|&(_, &b)| b).map(|(i, _)| {
            ty::Clause::upcast_from(
                ty::ClauseKind::Trait(ty::TraitPredicate {
                    trait_ref: ty::TraitRef::new_from_args(
                        cx,
                        tuple,
                        cx.mk_args(std::slice::from_ref(
                            &Ty::new_param(cx, i as u32, sym::T).into(),
                        )),
                    ),
                    polarity: ty::PredicatePolarity::Positive,
                }),
                cx,
            )
        });

        let explicit_bounds = cx.mk_clauses_from_iter(sized.chain(tuple));

        if explicit_bounds.is_empty() {
            span_bug!(span, "created a variadic alias without specifying any unpacked arguments.");
        }
        cx.intern_variadic_alias_ctor(VariadicAliasCtorStorage {
            span,
            variadic_spans: spans,
            inner,
            explicit_bounds: ty::EarlyBinder::bind(explicit_bounds),
        })
    }
}

impl<'tcx> rustc_type_ir::inherent::VariadicAliasCtor<TyCtxt<'tcx>> for VariadicAliasCtor<'tcx> {
    fn len(self) -> usize {
        self.len()
    }

    fn tuple_params(
        self,
    ) -> impl Iterator<Item = ty::TupleParam<'tcx>> + ExactSizeIterator + DoubleEndedIterator {
        self.tuple_params()
    }

    fn new(
        cx: TyCtxt<'tcx>,
        span: Span,
        params: impl IntoIterator<Item = ty::TupleParam<'tcx>>,
    ) -> VariadicAliasCtor<'tcx> {
        VariadicAliasCtor::new(cx, span, params)
    }
}

#[derive(Clone, Copy, Eq)]
pub struct VariadicAliasCtor<'tcx>(pub Interned<'tcx, VariadicAliasCtorStorage<'tcx>>);

impl<'tcx> PartialEq for VariadicAliasCtor<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.0.0.inner == other.0.0.inner
    }
}

impl<'tcx> Hash for VariadicAliasCtor<'tcx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.0.inner.hash(state);
    }
}

impl<'a, 'tcx> HashStable<StableHashingContext<'a>> for VariadicAliasCtor<'tcx> {
    fn hash_stable(&self, hcx: &mut StableHashingContext<'a>, hasher: &mut StableHasher) {
        self.0.0.hash_stable(hcx, hasher);
    }
}

impl<'tcx, E: TyEncoder<'tcx>> Encodable<E> for VariadicAliasCtor<'tcx> {
    fn encode(&self, e: &mut E) {
        self.0.0.encode(e);
    }
}

impl<'tcx, D: TyDecoder<'tcx>> Decodable<D> for VariadicAliasCtor<'tcx> {
    fn decode(decoder: &mut D) -> Self {
        decoder.interner().intern_variadic_alias_ctor(VariadicAliasCtorStorage::decode(decoder))
    }
}

impl<'tcx> fmt::Debug for VariadicAliasCtor<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("[")?;
        for param in self.tuple_params() {
            let str = match param {
                ty::TupleParam::Inline => "i",
                ty::TupleParam::Unpacked(_) => "u",
            };
            f.write_str(str)?;
        }
        f.write_str("]")
    }
}

#[derive(Copy, Clone, Eq)]
pub struct AliasCtor<'tcx> {
    ptr: *const (),
    marker: PhantomData<(DefId, VariadicAliasCtor<'tcx>)>,
}

impl<'tcx> PartialEq for AliasCtor<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.kind() == other.kind()
    }
}

impl<'tcx> Hash for AliasCtor<'tcx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind().hash(state);
    }
}

unsafe impl<'tcx> Send for AliasCtor<'tcx> {}
unsafe impl<'tcx> Sync for AliasCtor<'tcx> {}
unsafe impl<'tcx> DynSend for AliasCtor<'tcx> {}
unsafe impl<'tcx> DynSync for AliasCtor<'tcx> {}

impl<'tcx, E: TyEncoder<'tcx>> Encodable<E> for AliasCtor<'tcx> {
    fn encode(&self, e: &mut E) {
        self.kind().encode(e)
    }
}

impl<'tcx, D: TyDecoder<'tcx>> Decodable<D> for AliasCtor<'tcx> {
    fn decode(d: &mut D) -> AliasCtor<'tcx> {
        AliasCtor::pack(ty::AliasCtorKind::decode(d))
    }
}

impl<'a, 'tcx> HashStable<StableHashingContext<'a>> for AliasCtor<'tcx> {
    fn hash_stable(&self, hcx: &mut StableHashingContext<'a>, hasher: &mut StableHasher) {
        self.kind().hash_stable(hcx, hasher);
    }
}

impl<'tcx> fmt::Debug for AliasCtor<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.kind(), f)
    }
}

impl<'a, 'tcx> Lift<TyCtxt<'tcx>> for ty::AliasCtor<'a> {
    type Lifted = ty::AliasCtor<'tcx>;
    fn lift_to_interner(self, tcx: TyCtxt<'tcx>) -> Option<Self::Lifted> {
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => Some(ty::AliasCtor::from(def_id)),
            ty::AliasCtorKind::Variadic(ctor) => {
                tcx.lift(ctor).map(|ctor| ty::AliasCtor::pack(ty::AliasCtorKind::Variadic(ctor)))
            }
        }
    }
}

impl<'tcx> From<VariadicAliasCtor<'tcx>> for AliasCtor<'tcx> {
    fn from(ctor: VariadicAliasCtor<'tcx>) -> Self {
        AliasCtor::pack(ty::AliasCtorKind::Variadic(ctor))
    }
}

const _: () = assert!(std::mem::align_of::<DefId>() >= 4);
const TAG_MASK: usize = 0b1;

impl<'tcx> AliasCtor<'tcx> {
    pub fn kind(self) -> ty::AliasCtorKind<'tcx> {
        const { assert!(cfg!(target_pointer_width = "64")) }
        let ptr = self.ptr.map_addr(|addr| addr & !TAG_MASK);
        match self.ptr.addr() & TAG_MASK {
            0b0 => {
                let n = ptr.addr();
                ty::AliasCtorKind::Def(DefId {
                    krate: CrateNum::from_u32((n >> 33) as u32),
                    index: DefIndex::from_u32(((n & ((1 << 33) - 1)) >> 1) as u32),
                })
            }
            0b1 => ty::AliasCtorKind::Variadic(VariadicAliasCtor(unsafe {
                Interned::new_unchecked(&*ptr.cast::<VariadicAliasCtorStorage<'tcx>>())
            })),
            _ => unsafe { unreachable_unchecked() },
        }
    }

    fn pack(kind: ty::AliasCtorKind<'tcx>) -> AliasCtor<'tcx> {
        const { assert!(cfg!(target_pointer_width = "64")) }

        let (ptr, tag): (*const (), _) = match kind {
            ty::AliasCtorKind::Def(def_id) => {
                if def_id.krate.as_usize() >= (1 << 33) {
                    panic!("too large krate");
                }
                let addr = def_id.krate.as_usize() << 33 | def_id.index.as_usize() << 1;
                (ptr::without_provenance(addr), 0b0)
            }
            ty::AliasCtorKind::Variadic(ctor) => (ptr::from_ref(ctor.0.0).cast(), 0b1),
        };

        AliasCtor { ptr: ptr.map_addr(|addr| addr | tag), marker: PhantomData }
    }

    pub fn expect_def(self) -> DefId {
        self.def().unwrap_or_else(|| bug!("called `expect_def` on a variadic alias"))
    }

    pub fn expect_variadic(self) -> VariadicAliasCtor<'tcx> {
        let ty::AliasCtorKind::Variadic(ctor) = self.kind() else {
            bug!("called `expect_variadic` on a def-backed alias")
        };
        ctor
    }

    pub fn def(self) -> Option<DefId> {
        let ty::AliasCtorKind::Def(def_id) = self.kind() else {
            return None;
        };
        Some(def_id)
    }

    pub fn is_local_def(self) -> bool {
        matches!(self.kind(), ty::AliasCtorKind::Def(def_id) if def_id.is_local())
    }

    pub fn span(self, cx: TyCtxt<'tcx>) -> Span {
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => cx.def_span(def_id),
            ty::AliasCtorKind::Variadic(ctor) => ctor.span(),
        }
    }

    pub fn predicates(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<
        'tcx,
        impl Iterator<Item = (ty::Clause<'tcx>, Span)> + DoubleEndedIterator + ExactSizeIterator + Clone,
    > {
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => ty::EarlyBinder::bind(BoundsIterator::Def(
                cx.predicates_of(def_id).predicates.iter().copied(),
            )),
            ty::AliasCtorKind::Variadic(ctor) => {
                // FIXME(soqb): not the individual spans, since we don't keep those around (yet!).
                let span = ctor.0.0.span;

                ctor.0.0.explicit_bounds.map_bound(|bounds| {
                    BoundsIterator::Variadic(bounds.iter().map(move |clause| (clause, span)))
                })
            }
        }
    }

    pub fn instantiate_predicates(
        self,
        cx: TyCtxt<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> ty::InstantiatedPredicates<'tcx> {
        let mut instantiated = ty::InstantiatedPredicates::empty();
        if let Some(def_id) = self.parent(cx) {
            cx.predicates_of(def_id).instantiate_into(cx, &mut instantiated, args);
        }
        let predicates = self.predicates(cx).skip_binder();
        instantiated.predicates.extend(
            predicates.clone().map(|(p, _)| ty::EarlyBinder::bind(p).instantiate(cx, args)),
        );
        instantiated.spans.extend(predicates.map(|(_, sp)| sp));
        instantiated
    }

    pub fn bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Clause<'tcx>>> {
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => {
                cx.item_bounds(def_id).map_bound(IntoIterator::into_iter)
            }
            ty::AliasCtorKind::Variadic(ctor) => {
                ctor.0.explicit_bounds.map_bound(IntoIterator::into_iter)
            }
        }
    }

    pub fn self_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Clause<'tcx>>> {
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => {
                cx.item_self_bounds(def_id).map_bound(IntoIterator::into_iter)
            }
            ty::AliasCtorKind::Variadic(_ctor) => ty::EarlyBinder::bind(Default::default()),
        }
    }

    pub fn non_self_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Clause<'tcx>>> {
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => {
                cx.item_non_self_bounds(def_id).map_bound(IntoIterator::into_iter)
            }
            ty::AliasCtorKind::Variadic(ctor) => {
                ctor.0.explicit_bounds.map_bound(IntoIterator::into_iter)
            }
        }
    }

    pub fn const_conditions(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Binder<'tcx, ty::TraitRef<'tcx>>>> {
        let f = |(c, _)| c;
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => ty::EarlyBinder::bind(
                cx.const_conditions(def_id).instantiate_identity(cx).into_iter().map(f),
            ),
            ty::AliasCtorKind::Variadic(_ctor) => {
                ty::EarlyBinder::bind(Iterator::map(Default::default(), f))
            }
        }
    }

    pub fn explicit_implied_const_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, impl Iterator<Item = ty::Binder<'tcx, ty::TraitRef<'tcx>>>> {
        let f = |(c, _)| c;
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => ty::EarlyBinder::bind(
                cx.explicit_implied_const_bounds(def_id).iter_identity_copied().map(f),
            ),
            ty::AliasCtorKind::Variadic(_ctor) => {
                ty::EarlyBinder::bind(Iterator::map(Default::default(), f))
            }
        }
    }

    pub fn explicit_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, &'tcx [(ty::Clause<'tcx>, Span)]> {
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => cx.explicit_item_bounds(def_id),
            ty::AliasCtorKind::Variadic(_ctor) => ty::EarlyBinder::bind(&[][..]),
        }
    }

    pub fn explicit_self_bounds(
        self,
        cx: TyCtxt<'tcx>,
    ) -> ty::EarlyBinder<'tcx, &'tcx [(ty::Clause<'tcx>, Span)]> {
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => cx.explicit_item_self_bounds(def_id),
            ty::AliasCtorKind::Variadic(_ctor) => ty::EarlyBinder::bind(&[][..]),
        }
    }

    pub fn variances(self, cx: TyCtxt<'tcx>) -> impl Iterator<Item = ty::Variance> + Clone {
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => {
                BoundsIterator::Def(cx.variances_of(def_id).iter().copied())
            }
            ty::AliasCtorKind::Variadic(ctor) => {
                BoundsIterator::Variadic(std::iter::repeat_n(ty::Covariant, ctor.len()))
            }
        }
    }

    pub fn parent(self, cx: TyCtxt<'tcx>) -> Option<DefId> {
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => cx.generics_of(def_id).parent,
            ty::AliasCtorKind::Variadic(_) => None,
        }
    }

    pub fn generics(
        self,
        cx: TyCtxt<'tcx>,
    ) -> impl ExactSizeIterator<Item = GenericAliasParamDef> + ExactSizeIterator {
        match self.kind() {
            ty::AliasCtorKind::Def(def_id) => {
                BoundsIterator::Def(cx.generics_of(def_id).own_params.iter().map(From::from))
            }
            ty::AliasCtorKind::Variadic(ctor) => {
                BoundsIterator::Variadic((0..ctor.len()).map(|i| ty::GenericAliasParamDef {
                    name: None,
                    def_id: None,
                    index: i as u32,
                    kind: ty::GenericParamDefKind::Type { has_default: false, synthetic: false },
                }))
            }
        }
    }
}

#[derive(Clone)]
enum BoundsIterator<A, B> {
    Def(A),
    Variadic(B),
}

impl<T, A, B> Iterator for BoundsIterator<A, B>
where
    A: Iterator<Item = T>,
    B: Iterator<Item = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        match self {
            BoundsIterator::Def(a) => a.next(),
            BoundsIterator::Variadic(b) => b.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            BoundsIterator::Def(a) => a.size_hint(),
            BoundsIterator::Variadic(b) => b.size_hint(),
        }
    }
}

impl<T, A, B> ExactSizeIterator for BoundsIterator<A, B>
where
    A: ExactSizeIterator<Item = T>,
    B: ExactSizeIterator<Item = T>,
{
}

impl<T, A, B> DoubleEndedIterator for BoundsIterator<A, B>
where
    A: DoubleEndedIterator<Item = T>,
    B: DoubleEndedIterator<Item = T>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            BoundsIterator::Def(a) => a.next_back(),
            BoundsIterator::Variadic(b) => b.next_back(),
        }
    }
}

impl<'tcx> rustc_type_ir::inherent::IntoKind for AliasCtor<'tcx> {
    type Kind = ty::AliasCtorKind<'tcx>;

    fn kind(self) -> ty::AliasCtorKind<'tcx> {
        self.kind()
    }
}

impl<'tcx> rustc_type_ir::inherent::AliasCtor<TyCtxt<'tcx>> for AliasCtor<'tcx> {
    fn expect_def(self) -> DefId {
        self.expect_def()
    }

    fn expect_variadic(self) -> VariadicAliasCtor<'tcx> {
        self.expect_variadic()
    }

    fn span(self, cx: TyCtxt<'tcx>) -> Span {
        self.span(cx)
    }

    fn variances(self, cx: TyCtxt<'tcx>) -> impl Iterator<Item = ty::Variance> {
        self.variances(cx)
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
        AliasCtor::pack(ty::AliasCtorKind::Def(def_id))
    }
}

#[extension(pub trait AliasTyInstExt<'tcx>)]
impl<'tcx> ty::AliasTy<'tcx> {
    fn instantiate_own_predicates(
        self,
        cx: TyCtxt<'tcx>,
    ) -> impl Iterator<Item = (ty::Clause<'tcx>, Span)> + DoubleEndedIterator + ExactSizeIterator
    {
        ty::AliasTerm::from(self).instantiate_own_predicates(cx)
    }

    fn args_with_variances(
        self,
        cx: TyCtxt<'tcx>,
    ) -> impl Iterator<Item = (ty::GenericArg<'tcx>, ty::Variance)> {
        self.args.iter().zip(self.ctor.variances(cx))
    }
}
#[extension(pub trait AliasTermInstExt<'tcx>)]
impl<'tcx> ty::AliasTerm<'tcx> {
    fn instantiate_own_predicates(
        self,
        cx: TyCtxt<'tcx>,
    ) -> impl Iterator<Item = (ty::Clause<'tcx>, Span)> + DoubleEndedIterator + ExactSizeIterator
    {
        self.ctor.predicates(cx).iter_instantiated(cx, self.args)
    }
}
