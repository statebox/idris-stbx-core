> module Monoid.MonoidsCategory
>
> import Category
> import Utils
> import Monoid.Monoid
> import Monoid.MonoidMorphisms
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> fEq : (f : a -> b) -> (\x => f x) = f
> fEq f = Refl
>
> monoidsLeftIdentity :
>      (m1, m2 : Monoid)
>   -> (mor : MorphismOfMonoids m1 m2)
>   -> monoidMorphismsComposition (monoidIdentity m1) mor = mor
> monoidsLeftIdentity m1 m2 mor = morphismsOfMonoindsEq
>   (monoidMorphismsComposition (monoidIdentity m1) mor)
>   mor
>   (\x => Refl)
>
> monoidRightIdentity :
>      (m1, m2 : Monoid)
>   -> (mor : MorphismOfMonoids m1 m2)
>   -> monoidMorphismsComposition mor (monoidIdentity m2) = mor
> monoidRightIdentity m1 m2 mor = morphismsOfMonoindsEq
>   (monoidMorphismsComposition mor (monoidIdentity m2))
>   mor
>   (\x => Refl)
>
> monoidAssociativity :
>      (m1, m2, m3, m4 : Monoid)
>   -> (mor1 : MorphismOfMonoids m1 m2)
>   -> (mor2 : MorphismOfMonoids m2 m3)
>   -> (mor3 : MorphismOfMonoids m3 m4)
>   -> monoidMorphismsComposition mor1 (monoidMorphismsComposition mor2 mor3)
>    = monoidMorphismsComposition (monoidMorphismsComposition mor1 mor2) mor3
> monoidAssociativity m1 m2 m3 m4 mor1 mor2 mor3 = morphismsOfMonoindsEq
>   (monoidMorphismsComposition mor1 (monoidMorphismsComposition mor2 mor3))
>   (monoidMorphismsComposition (monoidMorphismsComposition mor1 mor2) mor3)
>   (\x => Refl)
>
> monoidsCategory : Category
> monoidsCategory = MkCategory
>   Monoid
>   MorphismOfMonoids
>   monoidIdentity
>   (\m1, m2, m3 => monoidMorphismsComposition {a = m1} {b = m2} {c = m3})
>   monoidsLeftIdentity
>   monoidRightIdentity
>   monoidAssociativity
