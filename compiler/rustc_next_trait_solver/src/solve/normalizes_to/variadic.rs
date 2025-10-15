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
        let ty = rustc_type_ir::flatten_variadic_alias(
            self.cx(),
            goal.predicate.alias.expect_ty(self.cx()),
            |ty| self.structurally_normalize_ty(goal.param_env, ty),
        )?;

        if let ty::Alias(ty::Variadic, data) = ty.kind() {
            // The alias is certainly rigid:
            self.structurally_instantiate_normalizes_to_term(goal, data.into());
        } else {
            self.instantiate_normalizes_to_term(goal, ty.into());
        }

        self.evaluate_added_goals_and_make_canonical_response(Certainty::Yes)
    }
}
