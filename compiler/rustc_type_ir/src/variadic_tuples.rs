use std::cell::Cell;
use std::fmt::Debug;
use std::iter::repeat_n;

use tracing::instrument;

use crate::inherent::*;
use crate::{self as ty, Interner};

/// Shallowly flattens a variadic aliases to it's constituent types under some normalization scheme.
///
/// `normalizer` is not called on any non-alias type.
#[instrument(level = "trace", skip(cx, normalizer), ret)]
pub fn flatten_variadic_alias<I: Interner, E: Debug>(
    cx: I,
    alias: ty::AliasTy<I>,
    mut normalizer: impl FnMut(I::Ty) -> Result<I::Ty, E>,
) -> Result<I::Ty, E> {
    if let &[arg] = alias.args.as_slice() {
        // If there's only one argument, then since this is a variadic alias (and not just a tuple),
        // that argument must be unpacked, so return it:
        return Ok(arg.expect_ty());
    }

    // Cell is a little heavy-handed but works reasonably well.
    let ctor = Cell::new(alias.ctor.expect_variadic());
    let args = Cell::new(alias.args);
    let zip_args = || args.get().iter().map(|arg| arg.expect_ty()).zip(ctor.get().tuple_params());

    // We first scan the unpacked arguments to decide how to proceed.
    // This is merely an optimisation, it would be correct to always normalize below.
    // NB: Don't use the flag for the alias check because we only care about shallow, unpacked aliases.
    let mut some_inlinable = false;
    let mut all_inlinable = true;
    for ty in zip_args().filter(|&(_, param)| param.is_unpacked()).map(|(ty, _)| ty) {
        let (certainly, maybe) = match ty.kind() {
            ty::Tuple(..) => (true, true),
            ty::Alias(..) => (false, true),
            _ => (false, false),
        };
        all_inlinable &= certainly;
        some_inlinable |= maybe;
    }

    if all_inlinable {
        // Every unpacked argument of the alias is also trivially a tuple,
        // so we bring those elements together:
        let folddown = |(ty, param): (I::Ty, ty::TupleParam<I>)| {
            let tys = if param == ty::TupleParam::Inline {
                // FIXME(soqb): inefficient
                cx.mk_type_list_from_iter(std::iter::once(ty))
            } else if let ty::Tuple(tys) = ty.kind() {
                tys
            } else {
                panic!("expected all variadic alias arguments to be either inline, or a tuple")
            };

            tys.iter()
        };
        Ok(Ty::new_tup_from_iter(cx, zip_args().flat_map(folddown)))
    } else if some_inlinable {
        // If there are aliases in the unpacked arguments,
        // normalizing may be fruitful so we normalize each and then flatten.

        // FIXME(soqb): allocation is annoying but very difficult to untangle here.
        // to cut it down (a little), we don't allocate until we know for sure we'll need these params.
        let mut needed_inline = 0;
        let mut params = Vec::new();
        // We need to rerun this check because in this loop we're normalizing.
        args.set(
            cx.mk_args_from_iter(
                zip_args()
                    .flat_map(|(ty, param)| {
                        let mut single = None;
                        let mut tuple = None;
                        let mut alias = None;
                        'a: {
                            if param.is_inline() {
                                single = Some(Ok(ty));
                                needed_inline += 1;
                            } else {
                                let ty = if let ty::Alias(_, _) = ty.kind() {
                                    match normalizer(ty) {
                                        Ok(ty) => ty,
                                        Err(e) => {
                                            break 'a single = Some(Err(e));
                                        }
                                    }
                                } else {
                                    ty
                                };

                                if let ty::Tuple(tys) = ty.kind() {
                                    tuple = Some(tys.iter());
                                    needed_inline += tys.len();
                                } else if let ty::Alias(ty::Variadic, data) = ty.kind() {
                                    alias = Some(data.args.iter());
                                    params.extend(repeat_n(ty::TupleParam::Inline, needed_inline));
                                    params.extend(data.ctor.expect_variadic().tuple_params());
                                    needed_inline = 0;
                                } else {
                                    single = Some(Ok(ty));
                                    needed_inline += 1;
                                }
                            }
                        }
                        single
                            .into_iter()
                            .chain(tuple.into_iter().flatten().map(Ok))
                            .chain(alias.into_iter().flatten().map(|arg| Ok(arg.expect_ty())))
                    })
                    .map(|res| res.map(I::GenericArg::from)),
            )?,
        );

        if params.len() == 0 {
            // No params means the extension branch in the loop above was never reached
            // and therefore all would-be params are inline.
            // Thus, every new argument is trivially a tuple:
            Ok(Ty::new_tup_from_iter(cx, args.get().iter().map(|ty| ty.expect_ty())))
        } else {
            // If all else fails, the alias is rigid (up to the particular `normalizer`):
            params.extend(repeat_n(ty::TupleParam::Inline, needed_inline));
            ctor.set(I::VariadicAliasCtor::new(cx, I::Span::dummy(), params));
            Ok(ty::AliasTy::new_from_args(cx, ctor.get().into(), args.get()).to_ty(cx))
        }
    } else {
        // If nothing inlinable, uhh, we'd just have what we started with:
        Ok(alias.to_ty(cx))
    }
}
