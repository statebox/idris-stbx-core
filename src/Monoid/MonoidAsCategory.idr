module Monoid.MonoidAsCategory

import Category

-- contrib
import Interfaces.Verified

%access public export
%default total

MonoidMorphism : (monoid : Type) -> Unit -> Unit -> Type
MonoidMorphism monoid _ _ = monoid

identity : (VerifiedMonoid monoid) => (a : Unit) -> MonoidMorphism monoid a a
identity _ = Algebra.neutral

compose : (VerifiedMonoid monoid)
  => (a, b, c : Unit)
  -> (f : MonoidMorphism monoid a b)
  -> (g : MonoidMorphism monoid b c)
  -> MonoidMorphism monoid a c
compose a b c f g = f <+> g

leftIdentity : (VerifiedMonoid monoid)
  => (f : monoid)
  -> Algebra.neutral <+> f = f
leftIdentity f = monoidNeutralIsNeutralR f

rightIdentity : (VerifiedMonoid monoid)
  => (f : monoid)
  -> f <+> Algebra.neutral = f
rightIdentity f = monoidNeutralIsNeutralL f

associativity : (VerifiedMonoid monoid)
  => (f, g, h : monoid)
  -> f <+> (g <+> h) = (f <+> g) <+> h
associativity f g h = semigroupOpIsAssociative f g h

monoidAsCategory : VerifiedMonoid monoid => VerifiedCategory () (MonoidMorphism monoid)
monoidAsCategory {monoid} =
  MkVerifiedCategory
    (MkCategory
      {obj = ()}
      {mor = MonoidMorphism monoid}
      (identity {monoid})
      (compose {monoid})
    )
    (\_, _, f => leftIdentity f)
    (\_, _, f => rightIdentity f)
    (\_, _, _, _, f, g, h => associativity f g h)
