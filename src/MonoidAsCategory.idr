module MonoidAsCategory

import Category

-- contrib
import Interfaces.Verified

data MonoidMorphism : (monoid : Type) -> (x, y: Unit) -> Type where
  MkMonoidMorphism : (x, y : Unit) -> monoid -> MonoidMorphism monoid x y

identity : VerifiedMonoid monoid => (x : Unit) -> MonoidMorphism monoid x x
identity x = MkMonoidMorphism x x Algebra.neutral

compose : VerifiedMonoid monoid => MonoidMorphism monoid x y -> MonoidMorphism monoid y z -> MonoidMorphism monoid x z
compose (MkMonoidMorphism _ _ a) (MkMonoidMorphism _ _ b) = (MkMonoidMorphism _ _ (a <+> b))

identityLeft : VerifiedMonoid monoid => (f : MonoidMorphism monoid x y) -> compose (identity x) f = f
identityLeft (MkMonoidMorphism _ _ a) = cong {f = MkMonoidMorphism _ _} (monoidNeutralIsNeutralR a)

identityRight : VerifiedMonoid monoid => (f : MonoidMorphism monoid x y) -> compose f (identity y) = f
identityRight (MkMonoidMorphism _ _ a) = cong {f = MkMonoidMorphism _ _} (monoidNeutralIsNeutralL a)

associativity : VerifiedMonoid monoid => (f : MonoidMorphism monoid x y) -> (g : MonoidMorphism monoid y z) -> (h : MonoidMorphism monoid z w) -> compose f (compose g h) = compose (compose f g) h
associativity (MkMonoidMorphism _ _ a) (MkMonoidMorphism _ _ b) (MkMonoidMorphism _ _ c) = cong {f = MkMonoidMorphism _ _} (semigroupOpIsAssociative a b c)

VerifiedMonoid monoid => Category Unit (MonoidMorphism monoid) where
  identity = MonoidAsCategory.identity
  compose = compose
  identityLeft = identityLeft
  identityRight = identityRight
  associativity = associativity
