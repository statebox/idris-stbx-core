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
