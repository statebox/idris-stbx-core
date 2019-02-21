> module PetriNet.PetriNet
>
> import PetriNet.MultiSet
>
> %access public export
> %default total
>
> record PetriNet where
>   constructor MkPetriNet
>   places      : Type
>   transitions : Type
>   input       : transitions -> MultiSet places
>   output      : transitions -> MultiSet places
>
> Marking : PetriNet -> Type
> Marking pN = MultiSet (places pN)
>
> data TransitionIsEnabled : transitions pN -> Marking pN -> Type where
>   MkTransitionIsEnabled : IsSubMultiSet (input pN t) m -> TransitionIsEnabled t m
>
> fireTransition : {pN : PetriNet} -> (t : transitions pN) -> (m : Marking pN) -> TransitionIsEnabled t m -> Marking pN
> fireTransition {pN} t m (MkTransitionIsEnabled mContainsInputT) = multiSetDifference m (input pN t) mContainsInputT
