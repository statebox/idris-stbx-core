> module PetriNet.PetriNet
>
> import PetriNet.Multiset
>
> %access public export
> %default total
>
> record PetriNet where
>   constructor MkPetriNet
>   places     : Type
>   transition : Type
>   input      : transition -> MultiSet places
>   output     : transition -> MultiSet places
