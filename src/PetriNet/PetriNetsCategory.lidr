> module PetriNet.PetriNetsCategory
>
> import Basic.Category
> import Monoid.Monoid
> import Monoid.MonoidMorphism
> import PetriNet.MultiSet
> import PetriNet.PetriNet
> import PetriNet.PetriNetMorphisms
> import Utils
>
> %access public export
> %default total
>
> petriNetLeftIdentity :
>      (pN1, pN2 : PetriNet)
>   -> (mor : PetriNetMorphism pN1 pN2)
>   -> petriNetComposition pN1 pN1 pN2 (petriNetIdentity pN1) mor = mor
> petriNetLeftIdentity
>   pN1
>   pN2
>   (MkPetriNetMorphism trMor mulMor iC oC)
>   = petriNetMorphismEq
>       (petriNetComposition pN1 pN1 pN2 (petriNetIdentity pN1) (MkPetriNetMorphism trMor mulMor iC oC))
>       (MkPetriNetMorphism trMor mulMor iC oC)
>       (\t => Refl)
>       (monoidMorphismEq (monoidMorphismsComposition (monoidIdentity (placesMonoid pN1)) mulMor) mulMor (\x => Refl))
>
> petriNetRightIdentity :
>      (pN1, pN2 : PetriNet)
>   -> (mor : PetriNetMorphism pN1 pN2)
>   -> petriNetComposition pN1 pN2 pN2 mor (petriNetIdentity pN2) = mor
> petriNetRightIdentity
>   pN1
>   pN2
>   (MkPetriNetMorphism trMor mulMor iC oC)
>   = petriNetMorphismEq
>       (petriNetComposition pN1 pN2 pN2 (MkPetriNetMorphism trMor mulMor iC oC) (petriNetIdentity pN2))
>       (MkPetriNetMorphism trMor mulMor iC oC)
>       (\t => Refl)
>       (monoidMorphismEq (monoidMorphismsComposition mulMor (monoidIdentity (placesMonoid pN2))) mulMor (\x => Refl))
>
> petriNetAssociativity :
>      (pN1, pN2, pN3, pN4 : PetriNet)
>   -> (mor1 : PetriNetMorphism pN1 pN2)
>   -> (mor2 : PetriNetMorphism pN2 pN3)
>   -> (mor3 : PetriNetMorphism pN3 pN4)
>   -> petriNetComposition pN1 pN2 pN4 mor1 (petriNetComposition pN2 pN3 pN4 mor2 mor3)
>    = petriNetComposition pN1 pN3 pN4 (petriNetComposition pN1 pN2 pN3 mor1 mor2) mor3
> petriNetAssociativity pN1 pN2 pN3 pN4
>   (MkPetriNetMorphism trMor1 mulMor1 iC1 oC1)
>   (MkPetriNetMorphism trMor2 mulMor2 iC2 oC2)
>   (MkPetriNetMorphism trMor3 mulMor3 iC3 oC3)
>   = petriNetMorphismEq
>       (petriNetComposition pN1 pN2 pN4 (MkPetriNetMorphism trMor1 mulMor1 iC1 oC1) (petriNetComposition pN2 pN3 pN4 (MkPetriNetMorphism trMor2 mulMor2 iC2 oC2) (MkPetriNetMorphism trMor3 mulMor3 iC3 oC3)))
>       (petriNetComposition pN1 pN3 pN4 (petriNetComposition pN1 pN2 pN3 (MkPetriNetMorphism trMor1 mulMor1 iC1 oC1) (MkPetriNetMorphism trMor2 mulMor2 iC2 oC2)) (MkPetriNetMorphism trMor3 mulMor3 iC3 oC3))
>       (\t => Refl)
>       (monoidMorphismEq
>          (monoidMorphismsComposition mulMor1 (monoidMorphismsComposition mulMor2 mulMor3))
>          (monoidMorphismsComposition (monoidMorphismsComposition mulMor1 mulMor2) mulMor3)
>          (\x => Refl)
>       )
>
> petriNetsAsCategory : Category
> petriNetsAsCategory = MkCategory
>   PetriNet
>   PetriNetMorphism
>   petriNetIdentity
>   petriNetComposition
>   petriNetLeftIdentity
>   petriNetRightIdentity
>   petriNetAssociativity
>

 implicit toOrdPetri : (Ord a) => PetriNet -> OrdPetriNet

>
> ordPetriNetsAsCategory : Category
> ordPetriNetsAsCategory = MkCategory
>   OrdPetriNet
>   (\opn1, opn2 => PetriNetMorphism (pnet opn1) (pnet opn2))
>   (\opn => petriNetIdentity (pnet opn))
>   (\opn1, opn2, opn3 => petriNetComposition (pnet opn1) (pnet opn2) (pnet opn3))
>   (\opn1, opn2 => petriNetLeftIdentity (pnet opn1) (pnet opn2))
>   (\opn1, opn2 => petriNetRightIdentity (pnet opn1) (pnet opn2))
>   (\opn1, opn2, opn3, opn4 => petriNetAssociativity (pnet opn1) (pnet opn2) (pnet opn3) (pnet opn4))
