module Preorder.monotoneMapAsFunctor

import Category
import Functor
import Preorder.MonotoneMaps
import Preorder.PreorderAsCategory
import Preorder.UniquePreorder

-- contrib
import Decidable.Order

monotoneMapToFunctor : (UniquePreorder t1 po1, UniquePreorder t2 po2)
  => MonotoneMap t1 po1 t2 po2
  -> VerifiedCFunctor (preorderAsCategory {t = t1} {po = po1}) (preorderAsCategory {t = t2} {po = po2})
monotoneMapToFunctor {t1} {po1} {t2} {po2} (MkMonotoneMap fun fRespectsOrd) =
  MkVerifiedCFunctor
    (MkCFunctor fun fRespectsOrd)
    (\a => unique (fun a) (fun a) (fRespectsOrd a a (reflexive a)) (reflexive (fun a)))
    (\a, b, c, f, g =>
      unique (fun a) (fun c)
        (fRespectsOrd a c (transitive a b c f g))
        (transitive (fun a) (fun b) (fun c) (fRespectsOrd a b f) (fRespectsOrd b c g))
    )
