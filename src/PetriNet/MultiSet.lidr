> module PetriNet.MultiSet
>
> -- contrib
> import Decidable.Order
> import Interfaces.Verified
>
> %access public export
> %default total
>
> -- a multiset is a function `t -> Nat`, where `t` is a type
> MultiSet : Type -> Type -- should we impose that it is non-zero only on a finite number on inputs?
> MultiSet t = t -> Nat
>
> multiSetEq : {m1, m2 : MultiSet a} -> ((x : a) -> m1 x = m2 x) -> m1 = m2
> multiSetEq eqOnElements = really_believe_me eqOnElements
>
> multiSetUnion : (m1, m2 : MultiSet a) -> MultiSet a
> multiSetUnion m1 m2 = (\x => m1 x + m2 x)
>
> data IsSubMultiSet : (m1, m2 : MultiSet a) -> Type where
>   MkIsSubMultiSet : ((x : a) -> LTE (m1 x) (m2 x)) -> IsSubMultiSet m1 m2
>
> Preorder (MultiSet a) IsSubMultiSet where
>   transitive m1 m2 m3 (MkIsSubMultiSet m1Subm2) (MkIsSubMultiSet m2Subm3) = MkIsSubMultiSet(\x => LTEIsTransitive (m1 x) (m2 x) (m3 x) (m1Subm2 x) (m2Subm3 x))
>   reflexive m = MkIsSubMultiSet (\x => LTEIsReflexive (m x))
>
> multiSetDifference : (m1, m2 : MultiSet a) -> IsSubMultiSet m2 m1 -> MultiSet a
> multiSetDifference m1 m2 (MkIsSubMultiSet isSub) = \x => (-) (m1 x) (m2 x) {smaller = isSub x}
>
> multiSetScalarMultiplication : Nat -> MultiSet a -> MultiSet a
> multiSetScalarMultiplication n m = \x => n * m x
>
> multiSetDisjointUnion : MultiSet a -> MultiSet b -> MultiSet (Either a b)
> multiSetDisjointUnion m1 m2 = \x => case x of
>                                       Left  y => m1 y
>                                       Right y => m2 y
>
> constantMultiSet : Nat -> MultiSet a
> constantMultiSet n = const n
>
> zeroMultiSet : MultiSet a
> zeroMultiSet = constantMultiSet 0
>
> Semigroup (MultiSet a) where
>   (<+>) = multiSetUnion
>
> VerifiedSemigroup (MultiSet a) where
>   semigroupOpIsAssociative m1 m2 m3 = multiSetEq (\x => plusAssociative (m1 x) (m2 x) (m3 x))
>
> Monoid (MultiSet a) where
>   neutral = zeroMultiSet
>
> [multiSetVerifiedMonoid] VerifiedMonoid (MultiSet a) where
>   monoidNeutralIsNeutralL m = multiSetEq (\x => plusZeroRightNeutral (m x))
>   monoidNeutralIsNeutralR m = multiSetEq (\x => plusZeroLeftNeutral  (m x))
