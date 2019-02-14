> module Monoid.MonoidMorphismAsFunctor
> 
> import Category
> import Functor
> import Monoid.MonoidAsCategory
> import Monoid.MonoidMorphisms
> 
> -- contrib
> import Interfaces.Verified
> 
> %access public export
> %default total
> 
> morphismOfMonoidsToFunctor : (VerifiedMonoid monoid1, VerifiedMonoid monoid2)
>   => MorphismOfMonoids monoid1 monoid2
>   -> CFunctor (monoidAsCategory {monoid = monoid1}) (monoidAsCategory {monoid = monoid2})
> morphismOfMonoidsToFunctor {monoid1} {monoid2} (MkMorphismOfMonoids fun frOp frId) =
>   MkCFunctor
>     id
>     (\_, _ => fun)
>     (\_ => frId)
>     (\_, _, _, f, g => frOp f g)
