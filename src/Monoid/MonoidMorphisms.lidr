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
> morphismsOfMonoindsEq :
>      (mor1, mor2 : MorphismOfMonoids m1 m2)
>   -> ((x : set m1) -> (func mor1 x) = (func mor2 x))
>   -> mor1 = mor2
> morphismsOfMonoindsEq mor1 mor2 pointWisePrf = really_believe_me pointWisePrf
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
> monoidMorphismsComposition mor1 mor2 =
>   MkMorphismOfMonoids
>     ((func mor2) . (func mor1))
>     (\a, b => trans (cong {f = func mor2} (funcRespOp mor1 a b)) (funcRespOp mor2 (func mor1 a) (func mor1 b)))
>     (trans (cong {f = func mor2} (funcRespId mor1)) (funcRespId mor2))
