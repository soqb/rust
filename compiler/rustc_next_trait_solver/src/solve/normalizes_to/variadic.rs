use rustc_type_ir::inherent::*;
use rustc_type_ir::{self as ty, Interner};

use crate::delegate::SolverDelegate;
use crate::solve::{Certainty, EvalCtxt, Goal, QueryResult};

impl<D, I> EvalCtxt<'_, D>
where
    D: SolverDelegate<Interner = I>,
    I: Interner,
{
    pub(super) fn normalize_variadic_ty(
        &mut self,
        goal: Goal<I, ty::NormalizesTo<I>>,
    ) -> QueryResult<I> {
        let cx = self.cx();

        if let &[arg] = goal.predicate.alias.args.as_slice() {
            // If there's only one argument, then since this is a variadic alias (and not just a tuple),
            // that argument must be unpacked, so return it:
            self.instantiate_normalizes_to_term(goal, arg.expect_ty().into());
            return self.evaluate_added_goals_and_make_canonical_response(Certainty::Yes);
        }

        let variadic = std::cell::Cell::new(goal.predicate.alias);
        let ctor = variadic.get().ctor.expect_variadic();
        let zip_args =
            || variadic.get().args.iter().map(|arg| arg.expect_ty()).zip(ctor.tuple_params());

        // We first scan the unpacked arguments to decide how to proceed.
        // This is merely an optimisation, it would be correct to always normalize below.
        let mut has_alias = false;
        let mut is_directly_inlinable = true;
        for ty in zip_args().filter(|&(_, param)| param.is_unpacked()).map(|(ty, _)| ty) {
            match ty.kind() {
                ty::Tuple(_) => continue,
                ty::Alias(_, _) => {
                    has_alias = true;
                }
                _ => {}
            }
            is_directly_inlinable = false;
        }

        if has_alias {
            // If there are aliases in the unpacked arguments,
            // normalizing may be fruitful so we normalize each and then flatten.
            let params = zip_args().flat_map(|(ty, param)| {
                let mut fixed = None;
                let mut tuple = None;
                let mut alias = None;

                if param.is_inline() {
                    fixed = Some(ty::TupleParam::Inline);
                } else if let ty::Tuple(tys) = ty.kind() {
                    tuple = Some(std::iter::repeat_n(ty::TupleParam::Inline, tys.len()));
                } else if let ty::Alias(ty::Variadic, data) = ty.kind() {
                    alias = Some(data.ctor.expect_variadic().tuple_params());
                } else {
                    fixed = Some(param);
                }

                fixed
                    .into_iter()
                    .chain(tuple.into_iter().flatten())
                    .chain(alias.into_iter().flatten())
            });
            let ctor = I::VariadicAliasCtor::new(cx, I::Span::dummy(), params);
            is_directly_inlinable = true;
            let args = cx.mk_args_from_iter(
                zip_args()
                    .flat_map(|(ty, arity)| {
                        let mut single = None;
                        let mut tuple = None;
                        let mut alias = None;
                        if arity == ty::TupleParam::Inline {
                            single = Some(Ok(ty));
                        } else {
                            match self.structurally_normalize_ty(goal.param_env, ty) {
                                Ok(ty) => {
                                    let mut inline = false;
                                    if let ty::Tuple(tys) = ty.kind() {
                                        tuple = Some(tys.iter());
                                        inline = true;
                                    } else if let ty::Alias(ty::Variadic, data) = ty.kind() {
                                        alias = Some(data.args.iter());
                                    } else {
                                        single = Some(Ok(ty));
                                    }

                                    if !inline {
                                        is_directly_inlinable = false;
                                    }
                                }
                                res => single = Some(res),
                            }
                        }
                        single
                            .into_iter()
                            .chain(tuple.into_iter().flatten().map(Ok))
                            .chain(alias.into_iter().flatten().map(|arg| Ok(arg.expect_ty())))
                    })
                    .map(|res| res.map(I::GenericArg::from)),
            )?;

            let term: I::Term = ty::AliasTy::new_from_args(cx, ctor.into(), args).to_ty(cx).into();
            variadic.set(term.to_alias_term().unwrap());
        }

        if is_directly_inlinable {
            // Every unpacked argument of the alias is also trivially a tuple,
            // so we bring those elements together:
            let folddown = |(ty, arity): (I::Ty, ty::TupleParam<I>)| {
                let tys = if arity == ty::TupleParam::Inline {
                    // FIXME(soqb): inefficient
                    cx.mk_type_list_from_iter(std::iter::once(ty))
                } else if let ty::Tuple(tys) = ty.kind() {
                    tys
                } else {
                    panic!("expected all variadic alias arguments to be either inline, or a tuple")
                };

                tys.iter()
            };
            let ty = Ty::new_tup_from_iter(cx, zip_args().flat_map(folddown));
            self.instantiate_normalizes_to_term(goal, ty.into());
            return self.evaluate_added_goals_and_make_canonical_response(Certainty::Yes);
        }

        // If the above branch did not return (even after normalizing), the alias is certainly rigid:
        self.structurally_instantiate_normalizes_to_term(goal, variadic.get());
        self.evaluate_added_goals_and_make_canonical_response(Certainty::Yes)
    }
}
