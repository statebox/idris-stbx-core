> module NaturalIsomorphism
>
> import Category
> import Functor
> import Isomorphism
> import NaturalTransformation
>
> %access public export
> %default total
>
> record NaturalIsomorphism
>   (cat1 : Category)
>   (cat2 : Category)
>   (func1 : CFunctor cat1 cat2)
>   (func2 : CFunctor cat1 cat2)
> where
>   constructor MkNaturalIsomorphism
>   natTrans : NaturalTransformation cat1 cat2 func1 func2
>   isIso    : (a : obj cat1) -> Isomorphism cat2 (mapObj func1 a) (mapObj func2 a) (component natTrans a)
