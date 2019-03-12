> module Isomorphism
>
> import Category
>
> %access public export
> %default total
>
> record Isomorphism (cat : Category) (a : obj cat) (b : obj cat) (morphism : mor cat a b) where
>   constructor mkIsomorphism
>   inverse: mor cat b a
>   lawleft: compose cat a b a morphism inverse = identity cat a
>   lawright: compose cat b a b inverse morphism = identity cat b
