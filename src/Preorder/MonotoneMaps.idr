module Preorder.MonotoneMaps

import Preorder.UniquePreorder

-- contrib
import Decidable.Order

%access public export
%default total

data MonotoneMap : (t1 : Type) -> (t1 -> t1 -> Type) -> (t2 : Type) -> (t2 -> t2 -> Type) -> Type where
  MkMonotoneMap : (UniquePreorder t1 po1, UniquePreorder t2 po2)
    => (f : t1 -> t2)
    -> (fRespectsOrd : (a, b : t1) -> po1 a b -> po2 (f a) (f b))
    -> MonotoneMap t1 po1 t2 po2
