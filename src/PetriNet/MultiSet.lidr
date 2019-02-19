> module PetriNet.Multiset
>
> %access public export
> %default total
>
> -- a multiset is a function `t -> Nat`, where `t` is a type
> MultiSet : Type -> Type -- should we impose that it is non-zero only on a finite number on inputs?
> MultiSet t = t -> Nat
>
> multiSetUnion : (m1, m2 : MultiSet a) -> MultiSet a
> multiSetUnion m1 m2 = (\x => m1 x + m2 x)
>
> isSubMultiSet : {a : Type} -> (m1, m2 : MultiSet a) -> Type
> isSubMultiSet {a} m1 m2 = (x : a) -> (LTE (m1 x) (m2 x))
>
> multiSetDifference : (m1, m2 : MultiSet a) -> isSubMultiSet m2 m1 -> MultiSet a
> multiSetDifference m1 m2 isSub = \x => (-) (m1 x) (m2 x) {smaller = isSub x}
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
> Monoid (MultiSet a) where
>   neutral = zeroMultiSet
>
> -- TODO: prove verified semigroup and verified monoid
