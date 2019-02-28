> module Monoid.MonoidMorphisms
>
> import Monoid.Monoid
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> record MorphismOfMonoids (domain : Monoid) (codomain : Monoid) where
>   constructor MkMorphismOfMonoids
>   func       : set domain -> set codomain
>   funcRespOp : (a, b : set domain)
>             -> func ((<+>) @{verifiedMonoidToSemigroup @{axioms domain}} a b)
>              = (<+>) @{verifiedMonoidToSemigroup @{axioms codomain}} (func a) (func b)
>   funcRespId : func (Algebra.neutral @{verifiedMonoidToMonoid @{axioms domain}})
>              = Algebra.neutral @{verifiedMonoidToMonoid @{axioms codomain}}
>
> monoidIdentity : (m : Monoid) -> MorphismOfMonoids m m
> monoidIdentity m = MkMorphismOfMonoids
>   id
>   (\_, _ => Refl)
>   Refl
>
> monoidMorphismsComposition :
>      MorphismOfMonoids a b
>   -> MorphismOfMonoids b c
>   -> MorphismOfMonoids a c
> monoidMorphismsComposition
>   (MkMorphismOfMonoids func1 funcRespOp1 funcRespId1)
>   (MkMorphismOfMonoids func2 funcRespOp2 funcRespId2)
>   = MkMorphismOfMonoids
>       (func2 . func1)
>       (\a, b => trans (cong {f = func2} (funcRespOp1 a b)) (funcRespOp2 (func1 a) (func1 b)))
>       (trans (cong {f = func2} funcRespId1) funcRespId2)
