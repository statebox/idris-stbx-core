> module Isomorphism
>
> import Category
>
> %access public export
> %default total
>
> record Isomorphism (cat : Category) (a : obj cat) (b : obj cat) (morphism : mor cat a b) where
>   constructor mkIsomorphism
>   Inverse: mor cat b a
>   lawleft: compose cat a b a morphism Inverse = identity cat a
>   lawright: compose cat b a b Inverse morphism = identity cat b
