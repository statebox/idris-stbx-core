> module PetriNet.Multiset
>
> %access public export
> %default total
>
> -- a multiset is a function `t -> Nat`, where `t` is a type
> MultiSet : Type -> Type -- should we impose that it is non-zero only on a finite number on inputs?
> MultiSet t = t -> Nat
>
> multisetUnion : (m1, m2 : MultiSet a) -> MultiSet a
> multisetUnion m1 m2 = (\x => m1 x + m2 x)
>
> isSubMultiSet : {a : Type} -> (m1, m2 : MultiSet a) -> Type
> isSubMultiSet {a} m1 m2 = (x : a) -> (LTE (m1 x) (m2 x))
>
> multiSetDifference : (m1, m2 : MultiSet a) -> isSubMultiSet m2 m1 -> MultiSet a
> multiSetDifference m1 m2 isSub = \x => (-) (m1 x) (m2 x) {smaller = isSub x}
