module Functor

import Category

%access public export
%default total

data CFunctor : VerifiedCategory obj1 mor1 -> VerifiedCategory obj2 mor2 -> Type where
  MkCFunctor :
       {obj1 : Type}
    -> {mor1 : obj1 -> obj1 -> Type}
    -> {cat1 : VerifiedCategory obj1 mor1}
    -> {obj2 : Type}
    -> {mor2 : obj2 -> obj2 -> Type}
    -> {cat2 : VerifiedCategory obj2 mor2}
    -> (mapObj : obj1 -> obj2)
    -> (mapMor : {a, b : obj1} -> mor1 a b -> mor2 (mapObj a) (mapObj b))
    -> CFunctor cat1 cat2

FunctorRespectsIdentity :
     {obj1 : Type}
  -> {mor1 : obj1 -> obj1 -> Type}
  -> {obj2 : Type}
  -> {mor2 : obj2 -> obj2 -> Type}
  -> (a : obj1)
  -> (cat1 : VerifiedCategory obj1 mor1)
  -> (cat2 : VerifiedCategory obj2 mor2)
  -> CFunctor cat1 cat2
  -> Type
FunctorRespectsIdentity
  a
  (MkVerifiedCategory (MkCategory identity1 _) _ _ _)
  (MkVerifiedCategory (MkCategory identity2 _) _ _ _)
  (MkCFunctor mapObj mapMor)
  = mapMor (identity1 a) = identity2 (mapObj a)

FunctorRespectsComposition :
     {obj1 : Type}
  -> {mor1 : obj1 -> obj1 -> Type}
  -> {obj2 : Type}
  -> {mor2 : obj2 -> obj2 -> Type}
  -> {a, b, c : obj1}
  -> (f : mor1 a b)
  -> (g : mor1 b c)
  -> (cat1 : VerifiedCategory obj1 mor1)
  -> (cat2 : VerifiedCategory obj2 mor2)
  -> CFunctor cat1 cat2
  -> Type
FunctorRespectsComposition {a} {b} {c} f g
  (MkVerifiedCategory (MkCategory _ compose1) _ _ _)
  (MkVerifiedCategory (MkCategory _ compose2) _ _ _)
  (MkCFunctor mapObj mapMor)
  = mapMor (compose1 a b c f g) = compose2 (mapObj a) (mapObj b) (mapObj c) (mapMor f) (mapMor g)

data VerifiedCFunctor : VerifiedCategory obj1 mor1 -> VerifiedCategory obj2 mor2 -> Type where
  MkVerifiedCFunctor :
       {obj1 : Type}
    -> {mor1 : obj1 -> obj1 -> Type}
    -> {cat1 : VerifiedCategory obj1 mor1}
    -> {obj2 : Type}
    -> {mor2 : obj2 -> obj2 -> Type}
    -> {cat2 : VerifiedCategory obj2 mor2}
    -> (fun : CFunctor cat1 cat2)
    -> ((a : obj1) -> FunctorRespectsIdentity a cat1 cat2 fun)
    -> ((a, b, c : obj1) -> (f : mor1 a b) -> (g : mor1 b c) -> FunctorRespectsComposition f g cat1 cat2 fun)
    -> VerifiedCFunctor cat1 cat2
