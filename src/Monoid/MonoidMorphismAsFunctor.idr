module Monoid.MonoidMorphismAsFunctor

import Category
import Functor
import Monoid.MonoidAsCategory
import Monoid.MonoidMorphisms

-- contrib
import Interfaces.Verified

%access public export
%default total

funRespectId : (VerifiedMonoid monoid1, VerifiedMonoid monoid2)
  => (fun : monoid1 -> monoid2)
  -> FunctionRespectsIdentity fun
  -> FunctorRespectsIdentity ()
      (monoidAsCategory {monoid = monoid1})
      (monoidAsCategory {monoid = monoid2})
      (MkCFunctor Basics.id (\_, _ => fun))

funRespectComp : (VerifiedMonoid monoid1, VerifiedMonoid monoid2)
  => (f, g : monoid1)
  -> (fun : monoid1 -> monoid2)
  -> FunctionRespectsOperation fun
  -> FunctorRespectsComposition {a = ()} {b = ()} {c = ()} f g
      (monoidAsCategory {monoid = monoid1})
      (monoidAsCategory {monoid = monoid2})
      (MkCFunctor Basics.id (\_, _ => fun))

morphismOfMonoidsToFunctor : (VerifiedMonoid monoid1, VerifiedMonoid monoid2)
  => MorphismOfMonoids monoid1 monoid2
  -> VerifiedCFunctor (monoidAsCategory {monoid = monoid1}) (monoidAsCategory {monoid = monoid2})
morphismOfMonoidsToFunctor {monoid1} {monoid2} (MkMorphismOfMonoids fun frOp frId) =
  MkVerifiedCFunctor
    (MkCFunctor id (\_, _ => fun))
    (\_ => funRespectId {monoid1} {monoid2} fun frId)
    (\_, _, _, f, g => funRespectComp {monoid1} {monoid2} f g fun frOp)
