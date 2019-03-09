> module PetriNet.PetriNetMorphisms
>
> import Monoid.Monoid
> import Monoid.MonoidMorphisms
> import PetriNet.MultiSet
> import PetriNet.PetriNet
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> record PetriNetMorphism (pN1 : PetriNet) (pN2 : PetriNet) where
>   constructor MkPetriNetMorphism
>   transitionMor   : transitions pN1 -> transitions pN2
>   multisetMor     : MorphismOfMonoids (placesMonoid pN1) (placesMonoid pN2)
>   inputCoherence  : (t : transitions pN1) -> input  pN2 (transitionMor t) = func multisetMor (input  pN1 t)
>   outputCoherence : (t : transitions pN1) -> output pN2 (transitionMor t) = func multisetMor (output pN1 t)
>
> petriNetMorphismEq :
>      (mor1, mor2 : PetriNetMorphism pN1 pN2)
>   -> ((t : transitions pN1) -> transitionMor mor1 t = transitionMor mor2 t)
>   -> multisetMor mor1 = multisetMor mor2
>   -> mor1 = mor2
> petriNetMorphismEq mor1 mor2 trEqPrf msEqPrf = really_believe_me ()
>
> petriNetIdentity : (pN : PetriNet) -> PetriNetMorphism pN pN
> petriNetIdentity pN = MkPetriNetMorphism
>   id
>   (monoidIdentity (placesMonoid pN))
>   (\_ => Refl)
>   (\_ => Refl)
>
> petriNetComposition :
>      (pN1, pN2, pN3 : PetriNet)
>   -> PetriNetMorphism pN1 pN2
>   -> PetriNetMorphism pN2 pN3
>   -> PetriNetMorphism pN1 pN3
> petriNetComposition pN1 pN2 pN3
>   (MkPetriNetMorphism trMor1 mulMor1 iC1 oC1)
>   (MkPetriNetMorphism trMor2 mulMor2 iC2 oC2)
>   = MkPetriNetMorphism
>       (trMor2 . trMor1)
>       (monoidMorphismsComposition mulMor1 mulMor2)
>       (\t => trans (iC2 (trMor1 t)) (cong {f = func mulMor2} (iC1 t)))
>       (\t => trans (oC2 (trMor1 t)) (cong {f = func mulMor2} (oC1 t)))
