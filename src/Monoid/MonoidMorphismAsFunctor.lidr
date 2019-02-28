> module Monoid.MonoidMorphismAsFunctor
>
> import Category
> import Functor
> import Monoid.Monoid
> import Monoid.MonoidAsCategory
> import Monoid.MonoidMorphisms
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> morphismOfMonoidsToFunctor :
>      (monoid1, monoid2 : Monoid)
>   -> MorphismOfMonoids monoid1 monoid2
>   -> CFunctor (monoidAsCategory monoid1) (monoidAsCategory monoid2)
> morphismOfMonoidsToFunctor monoid1 monoid2 (MkMorphismOfMonoids fun frOp frId) =
>   MkCFunctor
>     id
>     (\_, _ => fun)
>     (\_ => frId)
>     (\_, _, _, f, g => frOp f g)
