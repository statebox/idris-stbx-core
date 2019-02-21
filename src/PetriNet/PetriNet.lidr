> module PetriNet.PetriNet
>
> import PetriNet.MultiSet
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
>
> Marking : PetriNet -> Type
> Marking pN = MultiSet (places pN)
>
> data TransitionIsEnabled : transition pN -> Marking pN -> Type where
>   MkTransitionIsEnabled : IsSubMultiSet (input pN t) m -> TransitionIsEnabled t m
>
> fireTransition : {pN : PetriNet} -> (t : transition pN) -> (m : Marking pN) -> TransitionIsEnabled t m -> Marking pN
> fireTransition {pN} t m (MkTransitionIsEnabled mContainsInputT) = multiSetDifference m (input pN t) mContainsInputT
