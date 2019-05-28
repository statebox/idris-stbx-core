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

-- > occurrences : DecEq a => (x : a) -> (v : Vect n a) -> List (Elem x v)
-- > occurrences x [] = []
-- > occurrences x (y :: ys) with (decEq x y)
-- >   occurrences x (x :: ys) | Yes Refl = Here :: map There (occurrences x ys)
-- >   occurrences x (y :: ys) | No  _    = map There (occurrences x ys)
-- >
-- > headOccursAtLeastOnce : DecEq a => (x : a) -> (xs : Vect n a) -> NonEmpty (occurrences x (x :: xs))
-- > headOccursAtLeastOnce x xs with (decEq x x)
-- >   | No  contra = absurd $ contra Refl
-- >   | Yes Refl   = IsNonEmpty
-- >
-- > elemToPosition : (v : Vect n a) -> (Elem x v) -> Fin n
-- > elemToPosition (x :: xs)  Here         = 0
-- > elemToPosition (y :: ys) (There later) = FS $ elemToPosition ys later
-- >
-- > vectIndexer : DecEq a => (x : a) -> (v : Vect n a) -> List (Fin n)
-- > vectIndexer x v = map (elemToPosition v) (occurrences x v)
-- >
-- > permutationBuilder : DecEq a => (v : Vect n a) -> ((x : a) -> List (Fin n)) -> Permutation n
-- > permutationBuilder []        elementPositions = Nil
-- > permutationBuilder (y :: ys) elementPositions = case elementPositions y of
-- >   [] => absurd $ ?adsf (headOccursAtLeastOnce y ys)
-- >   (z :: zs) => ?qwer

> countElement : DecEq a => (v : Vect n a) -> (x : a) -> Nat
> countElement [] x = 0
> countElement (y :: ys) x with (decEq x y)
>   | Yes _ = 1 + countElement ys x
>   | No _  = countElement ys x
>
> headCountIsNotZero : DecEq a => (x : a) -> (xs : Vect n a) -> LTE 1 (countElement (x :: xs) x)
> headCountIsNotZero x xs = rewrite decEqSelfIsYes {x} in LTESucc LTEZero
>
> countElementOfEmptyVectorIsZero : DecEq a => (v : Vect 0 a) -> (x : a) -> countElement v x = 0
> countElementOfEmptyVectorIsZero [] x = Refl

-- >
-- > occurrences : DecEq a => (x : a) -> (v : Vect n a) -> Vect (countElement v x) (Elem x v)
-- > occurrences x [] = []
-- > occurrences x (y :: ys) with (decEq x y)
-- >   occurrences x (x :: ys) | Yes Refl = Here :: (map There (occurrences x ys))
-- >   occurrences x (y :: ys) | No _     = map There (occurrences x ys)
-- >
-- > elemToPosition : (v : Vect n a) -> (Elem x v) -> Fin n
-- > elemToPosition (x :: xs)  Here         = 0
-- > elemToPosition (y :: ys) (There later) = FS $ elemToPosition ys later
-- >
-- > vectIndexer : DecEq a => (x : a) -> (v : Vect n a) -> Vect (countElement v x) (Fin n)
-- > vectIndexer x v = map (elemToPosition v) (occurrences x v)

(A, B, C, C, A) and (B, C, A, A, C)
As A \= B, do (0 1), to get
(B, A, C, C, A) and (B, C, A, A, C)
Then, recurse on
(A, C, C, A) and (C, A, A, C)
 (2 1) (1 0)

(JH: I'll investigate if we can do somethign with a VPS and remote desktop sharing next time)

(JH: I'll try to write down a description of this function, plz correct if it is not right)

Given a list (`y::ys`) and a counting function `(a -> Vect ..)` and return a function that drops the first element.

(B C A A C)
elementPositions A => (2 3)

> subtractOneIfPossible : Fin (S (S n)) -> Fin (S n)
> subtractOneIfPossible FZ     = FZ
> subtractOneIfPossible (FS k) = k
>
> removeHeadFromPositions : DecEq a
>   => (y : a)
>   -> (ys : Vect n a)
>   -> ((x : a) -> Vect (countElement (y :: ys) x) (Fin (S n)))
>   -> ((x : a) -> Vect (countElement ys        x) (Fin n))
> removeHeadFromPositions {n} y ys elementPositions x with (decEq x y) proof prf
>   removeHeadFromPositions {n} y ys elementPositions y | Yes Refl = let yPositions = elementPositions y in
>     case n of
>       Z   => rewrite countElementOfEmptyVectorIsZero ys y in []
>       S k => subtractOneIfPossible <$> tail ?asdf -- yPositions

-- >  aux (elementPositions y)
-- >     where
-- >     aux : Vect (countElement (y::ys) y) (Fin (S n)) -> Vect (countElement ys y) (Fin n)
-- >     aux vs with (decEqSelfIsYes {x=y})
-- >       aux vs | pat = ?wat0

>   removeHeadFromPositions {n} y ys elementPositions x | No  _    = let xPositions = elementPositions x in
>     case n of
>       Z   => rewrite countElementOfEmptyVectorIsZero ys x in []
>       S k => subtractOneIfPossible <$> ?qwer -- xPositions
>


> permutationBuilder : DecEq a => (v : Vect n a) -> ((x : a) -> Vect (countElement v x) (Fin n)) -> Permutation n
> permutationBuilder          []     elementPositions = Nil
> permutationBuilder {n = S n} (y :: ys) elementPositions with (countElement (y :: ys) y) proof prf
>   permutationBuilder {n = S n} (y :: ys) elementPositions | Z = absurd $ replace (sym prf) (headCountIsNotZero y ys)
>   permutationBuilder {n = S n} (y :: ys) elementPositions | S m =
>     let positions = replace {P=\m => Vect m (Fin (S n))} (sym prf) (elementPositions y)
>     in  (head positions) :: permutationBuilder ys (removeHeadFromPositions y ys elementPositions)

(A, B, C, C, A) and (B, C, A, A, C)
As A \= B, do (0 1), to get
(B, A, C, C, A) and (B, C, A, A, C)
Then, recurse on
(A, C, C, A) and (C, A, A, C)

-- > computePermutation : Eq a
-- >   => (v1, v2 : Vect n a)
-- >   -> (Elem x v1 -> countOccurrences x v1 = countOccurrences x v2)
-- >   -> Permutation n
-- > computePermutation v1 v2 countPrf = ?asdf
