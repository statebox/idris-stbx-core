module NaturalTransformation

import Category
import Functor

%access public export
%default total

record NaturalTransformation (cat1 : Category) (cat2 : Category) (func : CFunctor cat1 cat2) (gunc : CFunctor cat1 cat2) where
    constructor MkNaturalTranformation
    component : (a : obj cat1) -> <cat2> (mapObj func a) ~> (mapObj gunc a)
    commutativity : {a, b : obj cat1}
                 -> (f : <cat1> a ~> b)
                 -> (<cat2 (mapObj func a) (mapObj gunc a) (mapObj gunc b)> (component a) ~> (mapMor gunc a b f))
                  = (<cat2 (mapObj func a) (mapObj func b) (mapObj gunc b)> (mapMor func a b f) ~> (component b))
