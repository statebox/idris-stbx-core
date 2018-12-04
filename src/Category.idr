module Category

export
interface Category object (morphism : object -> object -> Type) where
  identity : (a : object) -> morphism a a
  compose : morphism a b -> morphism b c -> morphism a c
  identityLeft : (f : morphism a b) -> compose (identity a) f = f
  identityRight :  (f : morphism a b) -> compose f (identity b) = f
  associativity : (f: morphism a b) -> (g : morphism b c) -> (h : morphism c d) -> compose f (compose g h) = compose (compose f g) h

interface MonoidLawful element where
  mIdentity : element
  mCompose : element -> element -> element
  mIdentityLeft : (a : element) -> mCompose mIdentity a = a
  mIdentityRight : (a : element) -> mCompose a mIdentity = a
  mAssociativity : (a : element) -> (b : element) -> (c : element) -> mCompose a (mCompose b c) = mCompose (mCompose a b) c

data Singleton : Type where
  Value : Singleton

data SingletonArrow : (x, y : Singleton) -> Type where
  MkSingletonArrow : (x, y : Singleton) -> SingletonArrow x y

namespace Singleton

  identity : (x : Singleton) -> SingletonArrow x x
  identity x = MkSingletonArrow x x

  compose : SingletonArrow x y -> SingletonArrow y z -> SingletonArrow x z
  compose _ _ = MkSingletonArrow x z

  identityLeft : (f : SingletonArrow x y) -> compose (identity x) f = f
  identityLeft (MkSingletonArrow x y) = Refl

  identityRight : (f : SingletonArrow x y) -> compose f (identity y) = f
  identityRight (MkSingletonArrow x y) = Refl

  associativity : (f : SingletonArrow x y) -> (g : SingletonArrow y z) -> (h : SingletonArrow z w) -> compose f (compose g h) = compose (compose f g) h
  associativity (MkSingletonArrow x y) (MkSingletonArrow y z) (MkSingletonArrow z w) = Refl

Category Singleton SingletonArrow where
  identity = Singleton.identity
  compose = Singleton.compose
  identityLeft = Singleton.identityLeft
  identityRight = Singleton.identityRight
  associativity = Singleton.associativity

data MonoidMorphism : (monoid : Type) -> (x, y: Singleton) -> Type where
  MkMonoidMorphism : (MonoidLawful monoid) => (x, y : Singleton) -> monoid -> MonoidMorphism monoid x y

namespace Monoid

  identity : MonoidLawful monoid => (x : Singleton) -> MonoidMorphism monoid x x
  identity x = MkMonoidMorphism x x mIdentity

  compose : MonoidLawful monoid => MonoidMorphism monoid x y -> MonoidMorphism monoid y z -> MonoidMorphism monoid x z
  compose (MkMonoidMorphism _ _ a) (MkMonoidMorphism _ _ b) = (MkMonoidMorphism _ _ (mCompose a b))

  liftMonoidCompose : MonoidLawful monoid => (a, b : monoid) -> compose (MkMonoidMorphism _ _ a) (MkMonoidMorphism _ _ b) = MkMonoidMorphism _ _ (mCompose a b)
  liftMonoidCompose a b = Refl

  liftMonoidIdentity : MonoidLawful monoid => {x : Singleton} -> identity x = MkMonoidMorphism x x (the monoid Category.mIdentity)
  liftMonoidIdentity = Refl

  identityLeft : MonoidLawful monoid => (f : MonoidMorphism monoid x y) -> compose (identity x) f = f
  identityLeft (MkMonoidMorphism _ _ a) = ?a --trans (liftMonoidCompose mIdentity a) (cong {f = MkMonoidMorphism _ _} (mIdentityLeft a))

  -- mIdentityLeft a : mCompose mIdentity a = a
  -- MkMonoidMorphism _ _ (mCompose mIdentity a) = (MkMonoidMorphism _ _ a)

  -- compose (identity x) f = f
  -- compose (MkMonoidMorphism x x mIdentity) (MkMonoidMorphism _ _ a) = (MkMonoidMorphism _ _ a)
  -- MkMonoidMorphism _ _ (mCompose mIdentity a) = (MkMonoidMorphism _ _ a)
  --

  identityRight : MonoidLawful monoid => (f : MonoidMorphism monoid x y) -> compose f (identity y) = f
  identityRight _ = ?a

  associativity : MonoidLawful monoid => (f : MonoidMorphism monoid x y) -> (g : MonoidMorphism monoid y z) -> (h : MonoidMorphism monoid z w) -> compose f (compose g h) = compose (compose f g) h
  associativity _ _ _ = ?a

MonoidLawful monoid => Category Singleton (MonoidMorphism monoid) where
  identity = Monoid.identity
  compose = Monoid.compose
  identityLeft = Monoid.identityLeft
  identityRight = Monoid.identityRight
  associativity = Monoid.associativity

interface PreOrder element where
  relation : element -> element -> Type
  reflexive : (a : element) -> relation a a
  transitive : relation a b -> relation b c -> relation a c

-- PreOrder element => Category element (\_, _ => Bool) where
--   identity = _
--   compose = _
--   identityLeft = _
--   identityRight = _
--   associativity = _
