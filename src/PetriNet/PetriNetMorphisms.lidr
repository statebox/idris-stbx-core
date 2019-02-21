> module PetriNet.PetriNetMorphisms
>
> import Monoid.MonoidMorphisms
> import PetriNet.MultiSet
> import PetriNet.PetriNet
>
> %access public export
> %default total
>
> record PetriNetMorphism (pN1 : PetriNet) (pN2 : PetriNet) where
>   constructor MkPetriNetMorphism
>   transitionMor   : transitions pN1 -> transitions pN2
>   multisetMor     : MorphismOfMonoids (MultiSet (places pN1)) (MultiSet (places pN2))
>   inputCoherence  : (t : transitions pN1) -> input  pN2 (transitionMor t) = func multisetMor (input  pN1 t)
>   outputCoherence : (t : transitions pN1) -> output pN2 (transitionMor t) = func multisetMor (output pN1 t)
