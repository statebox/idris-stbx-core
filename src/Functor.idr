module Functor

import Category

%access public export
%default total

record CFunctor (cat1 : Category) (cat2 : Category) where
  constructor MkCFunctor
  mapObj          : obj cat1 -> obj cat2
  mapMor          : (a, b : obj cat1) -> mor cat1 a b -> mor cat2 (mapObj a) (mapObj b)
  preserveId      : (a : obj cat1) -> mapMor a a (identity cat1 a) = identity cat2 (mapObj a)
  preserveCompose : (a, b, c : obj cat1)
                 -> (f : mor cat1 a b)
                 -> (g : mor cat1 b c)
                 -> mapMor a c (compose cat1 a b c f g)
                  = compose cat2 (mapObj a) (mapObj b) (mapObj c) (mapMor a b f) (mapMor b c g)

-- data CFunctor : VerifiedCategory obj1 mor1 -> VerifiedCategory obj2 mor2 -> Type where
--   MkCFunctor :
--        {obj1 : Type}
--     -> {mor1 : obj1 -> obj1 -> Type}
--     -> {cat1 : VerifiedCategory obj1 mor1}
--     -> {obj2 : Type}
--     -> {mor2 : obj2 -> obj2 -> Type}
--     -> {cat2 : VerifiedCategory obj2 mor2}
--     -> (mapObj : obj1 -> obj2)
--     -> (mapMor : (a, b : obj1) -> mor1 a b -> mor2 (mapObj a) (mapObj b))
--     -> CFunctor cat1 cat2
--
-- mapObj :
--      {cat1 : VerifiedCategory obj1 mor1}
--   -> {cat2 : VerifiedCategory obj2 mor2}
--   -> CFunctor cat1 cat2
--   -> (obj1 -> obj2)
-- mapObj (MkCFunctor mapObj _) = mapObj
--
-- mapMor :
--      {cat1 : VerifiedCategory obj1 mor1}
--   -> {cat2 : VerifiedCategory obj2 mor2}
--   -> (fun : CFunctor cat1 cat2)
--   -> (a, b : obj1) -> mor1 a b -> mor2 (mapObj fun a) (mapObj fun b)
-- mapMor (MkCFunctor _ mapMor) = mapMor
--
-- FunctorRespectsIdentity :
--      {obj1 : Type}
--   -> {mor1 : obj1 -> obj1 -> Type}
--   -> {obj2 : Type}
--   -> {mor2 : obj2 -> obj2 -> Type}
--   -> (a : obj1)
--   -> (cat1 : VerifiedCategory obj1 mor1)
--   -> (cat2 : VerifiedCategory obj2 mor2)
--   -> CFunctor cat1 cat2
--   -> Type
-- FunctorRespectsIdentity
--   a
--   (MkVerifiedCategory (MkCategory identity1 _) _ _ _)
--   (MkVerifiedCategory (MkCategory identity2 _) _ _ _)
--   (MkCFunctor mapObj mapMor)
--   = mapMor a a (identity1 a) = identity2 (mapObj a)
--
-- FunctorRespectsComposition :
--      {obj1 : Type}
--   -> {mor1 : obj1 -> obj1 -> Type}
--   -> {obj2 : Type}
--   -> {mor2 : obj2 -> obj2 -> Type}
--   -> {a, b, c : obj1}
--   -> (f : mor1 a b)
--   -> (g : mor1 b c)
--   -> (cat1 : VerifiedCategory obj1 mor1)
--   -> (cat2 : VerifiedCategory obj2 mor2)
--   -> CFunctor cat1 cat2
--   -> Type
-- FunctorRespectsComposition {a} {b} {c} f g
--   (MkVerifiedCategory (MkCategory _ compose1) _ _ _)
--   (MkVerifiedCategory (MkCategory _ compose2) _ _ _)
--   (MkCFunctor mapObj mapMor)
--   = mapMor a c (compose1 a b c f g) = compose2 (mapObj a) (mapObj b) (mapObj c) (mapMor a b  f) (mapMor b c g)
--
-- data VerifiedCFunctor : VerifiedCategory obj1 mor1 -> VerifiedCategory obj2 mor2 -> Type where
--   MkVerifiedCFunctor :
--        {obj1 : Type}
--     -> {mor1 : obj1 -> obj1 -> Type}
--     -> {cat1 : VerifiedCategory obj1 mor1}
--     -> {obj2 : Type}
--     -> {mor2 : obj2 -> obj2 -> Type}
--     -> {cat2 : VerifiedCategory obj2 mor2}
--     -> (fun : CFunctor cat1 cat2)
--     -> ((a : obj1) -> FunctorRespectsIdentity a cat1 cat2 fun)
--     -> ((a, b, c : obj1) -> (f : mor1 a b) -> (g : mor1 b c) -> FunctorRespectsComposition f g cat1 cat2 fun)
--     -> VerifiedCFunctor cat1 cat2
