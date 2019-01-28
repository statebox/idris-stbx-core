module MonoidMorphismAsFunctor

import Category
import Functor
import MonoidAsCategory
import MonoidMorphisms

-- contrib
import Interfaces.Verified

%access public export
%default total

fip : (VerifiedMonoid monoid1, VerifiedMonoid monoid2)
  => (fun : monoid1 -> monoid2)
  -> FunctionRespectsIdentity fun
  -> FunctorRespectsIdentity ()
      (monoidAsCategory {monoid = monoid1})
      (monoidAsCategory {monoid = monoid2})
      (MkCFunctor Basics.id fun)

fcp : (VerifiedMonoid monoid1, VerifiedMonoid monoid2)
  => (f, g : monoid1)
  -> (fun : monoid1 -> monoid2)
  -> FunctionRespectsOperation fun
  -> FunctorRespectsComposition {a = ()} {b = ()} {c = ()} f g
      (monoidAsCategory {monoid = monoid1})
      (monoidAsCategory {monoid = monoid2})
      (MkCFunctor Basics.id fun)

morphismOfMonoidsToFunctor : (VerifiedMonoid monoid1, VerifiedMonoid monoid2)
  => MorphismOfMonoids monoid1 monoid2
  -> VerifiedCFunctor (monoidAsCategory {monoid = monoid1}) (monoidAsCategory {monoid = monoid2})
morphismOfMonoidsToFunctor {monoid1} {monoid2} (MkMorphismOfMonoids fun fro fri) =
  MkVerifiedCFunctor
    (MkCFunctor id fun)
    (\_ => fip {monoid1} {monoid2} fun fri)
    (\_, _, _, f, g => fcp {monoid1} {monoid2} f g fun fro)
