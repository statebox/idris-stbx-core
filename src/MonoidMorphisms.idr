module MonoidMorphism

import MonoidAsCategory

-- contrib
import Interfaces.Verified

%access public export
%default total

FunctionRespectsOperation : (VerifiedSemigroup s1, VerifiedSemigroup s2)
  => {a, b : s1}
  -> (f : s1 -> s2)
  -> Type
FunctionRespectsOperation {a} {b} f = f (a <+> b) = f a <+> f b

FunctionRespectsIdentity : (VerifiedMonoid monoid1, VerifiedMonoid monoid2)
  => (f : monoid1 -> monoid2)
  -> Type
FunctionRespectsIdentity f = f (Algebra.neutral) = Algebra.neutral

data MorphismOfMonoids : Type -> Type -> Type where
  MkMorphismOfMonoids : (VerifiedMonoid monoid1, VerifiedMonoid monoid2)
    => {a, b : monoid1}
    -> (f : monoid1 -> monoid2)
    -> FunctionRespectsOperation {a} {b} f
    -> FunctionRespectsIdentity f
    -> MorphismOfMonoids monoid1 monoid2
