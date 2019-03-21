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
> flipFunctor : CFunctor (productCategory cat1 cat2) (productCategory cat2 cat1)
> flipFunctor = MkCFunctor
>   flip
>   (\a, b, f => MkProductMorphism (pi2 f) (pi1 f))
>   (\a => Refl)
>   (\a, b, c, f, g => Refl)
>
> record SymmetricMonoidalCategory where
>   constructor MkSymmetricMonoidalCategory
>   mcat : MonoidalCategory
>   symmetry : NaturalIsomorphism (productCategory cat cat) cat tensor (functorCompose flipFunctor tensor)