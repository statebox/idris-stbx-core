> module Cats.CatsAsCAtegory
>
> import Category
> import Functor
>
> %access public export
> %default total
>
> catsAsCategory : Category
> catsAsCategory = MkCategory
>   Category
>   CFunctor
>   (\cat => idFunctor {cat})
>   functorComposition
>   ?asd
>   ?adfga
>   ?qer