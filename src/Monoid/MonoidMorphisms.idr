module Monoid.MonoidMorphism

-- contrib
import Interfaces.Verified

%access public export
%default total

FunctionRespectsOperation : (VerifiedSemigroup s1, VerifiedSemigroup s2)
  => (a, b : s1)
  -> (f : s1 -> s2)
  -> Type
FunctionRespectsOperation a b f = f (a <+> b) = f a <+> f b

FunctionRespectsIdentity : (VerifiedMonoid monoid1, VerifiedMonoid monoid2)
  => (f : monoid1 -> monoid2)
  -> Type
FunctionRespectsIdentity f = f (Algebra.neutral) = Algebra.neutral

record MorphismOfMonoids domain codomain where
  constructor MkMorphismOfMonoids
  func : domain -> codomain
  funcRespOp : (VerifiedSemigroup domain, VerifiedSemigroup codomain) => (a, b : domain) -> FunctionRespectsOperation a b func
  funcRespId : (VerifiedMonoid domain, VerifiedMonoid codomain) => FunctionRespectsIdentity func
