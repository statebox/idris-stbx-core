> module SymmetricMonoidalCategory
>
> import Category
> import Functor
> import MonoidalCategory
> import NaturalIsomorphism
> import ProductCategory
>
> %access public export
> %default total
>
> swapMorphisms :
>      (a, b : (obj cat1, obj cat2))
>   -> mor (productCategory cat1 cat2) a b
>   -> mor (productCategory cat2 cat1) (swap a) (swap b)
> swapMorphisms (a1, a2) (b1, b2) (MkProductMorphism pi1 pi2) = MkProductMorphism pi2 pi1
>
> swapFunctor : CFunctor (productCategory cat1 cat2) (productCategory cat2 cat1)
> swapFunctor {cat1} {cat2} = MkCFunctor
>   swap
>   swapMorphisms
>   (\(a1, a2) => Refl)
>   (\(a1, a2), (b1, b2), (c1, c2), (MkProductMorphism f1 f2), (MkProductMorphism g1 g2) => Refl)
>
> data SymmetricMonoidalCategory : Type where
>   MkSymmetricMonoidalCategory :
>        (monoidalCategory : MonoidalCategory)
>     -> (symmetry : NaturalIsomorphism (productCategory (cat monoidalCategory) (cat monoidalCategory))
>                                       (cat monoidalCategory)
>                                       (tensor monoidalCategory)
>                                       (functorComposition (productCategory (cat monoidalCategory) (cat monoidalCategory))
>                                                           (productCategory (cat monoidalCategory) (cat monoidalCategory))
>                                                           (cat monoidalCategory)
>                                                           (swapFunctor {cat1 = cat monoidalCategory} {cat2 = cat monoidalCategory})
>                                                           (tensor monoidalCategory)))
>     -- TODO : symmetric monoidal category axioms
>     -> SymmetricMonoidalCategory
