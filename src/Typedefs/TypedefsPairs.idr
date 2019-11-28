module Typedefs.TypedefsPairs

import Basic.Category
import Basic.Functor

CompletePreorder : Type -> Category
CompletePreorder t = MkCategory
  t
  (\a, b => ())
  (\a => ())
  (\a, b, c, f, g => ())
  (\a, b, () => Refl)
  (\a, b, () => Refl)
  (\a, b, c, d, (), (), () => Refl)

completePreorderMorphism : (f : a -> b) -> CFunctor (CompletePreorder a) (CompletePreorder b)
completePreorderMorphism f = MkCFunctor
  f
  (\a, b, f => ())
  (\a => Refl)
  (\a, b, c, (), () => Refl)

collapser : (cat : Category) -> cat `CFunctor` (CompletePreorder (obj cat))
collapser cat = MkCFunctor
  id
  (\_, _, _ => ())
  (\_ => Refl)
  (\_, _, _, _, _ => Refl)
