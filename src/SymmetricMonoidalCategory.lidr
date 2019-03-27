> module SymmetricMonoidalCategory
>
> import Category
> import Functor
> import MonoidalCategory
> import MonoidalCategoryHelpers
> import NaturalIsomorphism
> import ProductCategory
> import SymmetricMonoidalCategoryHelpers
>
> %access public export
> %default total
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
>                                                           (swapFunctor (cat monoidalCategory) (cat monoidalCategory))
>                                                           (tensor monoidalCategory)))
>     -> ((a : obj (cat monoidalCategory)) -> UnitCoherence (cat monoidalCategory)
>                                                         (tensor monoidalCategory)
>                                                         (unit monoidalCategory)
>                                                         (leftUnitor monoidalCategory)
>                                                         (rightUnitor monoidalCategory)
>                                                         symmetry
>                                                         a)
>     -> ((a, b, c : obj (cat monoidalCategory)) -> AssociativityCoherence (cat monoidalCategory)
>                                                                          (tensor monoidalCategory)
>                                                                          ?associator --(associator monoidalCategory)
>                                                                          symmetry
>                                                                          a b c)
>     -> ((a, b : obj (cat monoidalCategory)) -> InverseLaw (cat monoidalCategory)
>                                                           (tensor monoidalCategory)
>                                                           symmetry
>                                                           a b)
>     -> SymmetricMonoidalCategory
