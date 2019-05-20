> module Permutations.Permutations
>
> import Data.Fin
> import Data.Vect
>
> -- vmchale/permutations
> import Control.Permutation.Types
>
> %access public export
> %default total
>
> countElement : DecEq a => (v : Vect n a) -> (x : a) -> Nat
> countElement [] x = 0
> countElement (y :: ys) x with (decEq x y)
>   | Yes _ = 1 + countElement ys x
>   | No _  = countElement ys x
>
> headCountIsNotZero : DecEq a => (x : a) -> (xs : Vect n a) -> LTE 1 (countElement (x :: xs) x)
> headCountIsNotZero x xs = rewrite decEqSelfIsYes {x} in LTESucc LTEZero
>
> occurrences : DecEq a => (x : a) -> (v : Vect n a) -> Vect (countElement v x) (Elem x v)
> occurrences x [] = []
> occurrences x (y :: ys) with (decEq x y)
>   occurrences x (x :: ys) | (Yes Refl) = Here :: (map There (occurrences x ys))
>   occurrences x (y :: ys) | (No _)     = map There (occurrences x ys)
>
> elemToPosition : (v : Vect n a) -> (Elem x v) -> Fin n
> elemToPosition (x :: xs) Here = 0
> elemToPosition (y :: ys) (There later) = FS $ elemToPosition ys later
>
> vectIndexer : DecEq a => (x : a) -> (v : Vect n a) -> Vect (countElement v x) (Fin n)
> vectIndexer x v = map (elemToPosition v) (occurrences x v)
>
> permutationBuilder : DecEq a => (v : Vect n a) -> ((x : a) -> Vect (countElement v x) (Fin n)) -> Permutation n
> permutationBuilder [] elementPositions = Nil
> permutationBuilder (y :: ys) elementPositions with (countElement (y :: ys) y) proof prf
>   | Z = absurd $ replace (sym prf) (headCountIsNotZero y ys)
>   | S m = ?qwer


-- > computePermutation : Eq a
-- >   => (v1, v2 : Vect n a)
-- >   -> (Elem x v1 -> countOccurrences x v1 = countOccurrences x v2)
-- >   -> Permutation n
-- > computePermutation v1 v2 countPrf = ?asdf
