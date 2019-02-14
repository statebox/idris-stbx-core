module Functor

import Category

%access public export
%default total

record CFunctor (cat1 : Category) (cat2 : Category) where
  constructor MkCFunctor
  mapObj          : obj cat1 -> obj cat2
  mapMor          : (a, b : obj cat1) -> (<cat1> a ~> b) -> (<cat2> (mapObj a) ~> (mapObj b))
  preserveId      : (a : obj cat1) -> mapMor a a (identity cat1 a) = identity cat2 (mapObj a)
  preserveCompose : (a, b, c : obj cat1)
                 -> (f : <cat1> a ~> b)
                 -> (g : <cat1> b ~> c)
                 -> mapMor a c (<cat1 a b c> f ~> g)
                  = <cat2 (mapObj a) (mapObj b) (mapObj c)> (mapMor a b f) ~> (mapMor b c g)
