> module PetriNet.PetriNet
>
> import Monoid.Monoid
> import PetriNet.MultiSet
>
> -- contrib
> import Interfaces.Verified
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
> placesMonoid : PetriNet -> Monoid
> placesMonoid pN = MkMonoid (Marking pN) (multiSetVerifiedMonoid)
>
> data TransitionIsEnabled : transitions pN -> Marking pN -> Type where
>   MkTransitionIsEnabled : IsSubMultiSet (input pN t) m -> TransitionIsEnabled t m
>
> fireTransition : {pN : PetriNet} -> (t : transitions pN) -> (m : Marking pN) -> TransitionIsEnabled t m -> Marking pN
> fireTransition {pN} t m (MkTransitionIsEnabled mContainsInputT) = multiSetDifference m (input pN t) mContainsInputT
