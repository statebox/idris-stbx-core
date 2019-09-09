module Util.Max

import Data.List
import Data.Fin

%access public export
%default total

natToFin' : (n, m : Nat) -> LTE n m -> Fin (S m)
natToFin'  Z       m   LTEZero      = FZ
natToFin' (S n) (S m) (LTESucc lte) = FS $ natToFin' n m lte

weakenMax : (a, b : Nat) -> Fin (S a) -> Fin (maximum (S a) (S b))
weakenMax  _     _     FZ    = FZ
weakenMax  Z     _    (FS f) = FS $ absurd f
weakenMax (S _)  Z    (FS f) = FS f
weakenMax (S a) (S b) (FS f) = FS $ weakenMax a b f

leftLTEMax : (a, b : Nat) -> LTE a (maximum a b)
leftLTEMax  Z     b    = LTEZero
leftLTEMax (S a)  Z    = lteRefl
leftLTEMax (S a) (S b) = LTESucc $ leftLTEMax a b

lteMaxL : LTE x z -> LTE x (maximum y z)
lteMaxL          LTEZero      = LTEZero
lteMaxL {y=Z}    lte          = lte
lteMaxL {y=S y} (LTESucc lte) = LTESucc $ lteMaxL lte

mapWithElem : (l : List a) -> (f : (x : a) -> Elem x l -> b) -> List b
mapWithElem []      _ = []
mapWithElem (x::xs) f = f x Here :: mapWithElem xs (\x => f x . There)

lengthMWE : (l : List a) -> (f : (x : a) -> Elem x l -> b) -> length l = length (mapWithElem l f)
lengthMWE []      f = Refl
lengthMWE (x::xs) f = cong $ lengthMWE xs (\x => f x . There)

---

findMax : List Nat -> Nat
findMax = foldr maximum 0

elemSmallerMax : (l : List Nat) -> (x : Nat) -> Elem x l -> LTE x (findMax l)
elemSmallerMax []      _  el        = absurd el
elemSmallerMax (y::ys) y  Here      = leftLTEMax y (findMax ys)
elemSmallerMax (y::ys) x (There el) = lteMaxL $ elemSmallerMax ys x el

maxOfSelf : (l : List Nat) -> List (Fin (S $ findMax l))
maxOfSelf l = mapWithElem l (\n, el => natToFin' n (findMax l) (elemSmallerMax l n el))

----

findMax2 : List (Nat, Nat) -> Nat
findMax2 = foldr (\(x, y), m => maximum (maximum x y) m) 0

elemSmallerMax2 : (l : List (Nat, Nat)) -> (x, y : Nat) -> Elem (x,y) l -> (LTE x (findMax2 l), LTE y (findMax2 l))
elemSmallerMax2 []         x y  el        = absurd el
elemSmallerMax2 ((x,y)::l) x y  Here      = ( rewrite sym $ maximumAssociative x y (findMax2 l) in
                                              leftLTEMax x (maximum y (findMax2 l))
                                            , rewrite maximumCommutative (maximum x y) (findMax2 l) in  -- extra step because `rewrite maximumCommutative x y` doesn't work as first step
                                              rewrite maximumAssociative (findMax2 l) x y in
                                              rewrite maximumCommutative (maximum (findMax2 l) x) y in
                                              leftLTEMax y (maximum (findMax2 l) x)
                                            )
elemSmallerMax2 ((a,b)::l) x y (There el) = let (lx, ly) = elemSmallerMax2 l x y el in
                                            (lteMaxL lx, lteMaxL ly)

maxOfSelf2 : (l : List (Nat, Nat)) -> List (Fin (S $ findMax2 l), Fin (S $ findMax2 l))
maxOfSelf2 l = mapWithElem l (\(x,y), el => let (lx, ly) = elemSmallerMax2 l x y el in
                                            ( natToFin' x (findMax2 l) lx
                                            , natToFin' y (findMax2 l) ly))
