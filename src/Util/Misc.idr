module Util

import Data.Vect

%default total

export
parseNat : String -> Maybe Nat
parseNat s = toMaybe (all isDigit (unpack s)) (cast {to=Nat} s)

export
leftMap : (a -> b) -> Either a c -> Either b c
leftMap f (Left a) = Left $ f a
leftMap f (Right c) = Right c

export
validateLength : List a -> (n : Nat) -> Maybe (Vect n a)
validateLength l n =
  case decEq (length l) n of
    Yes prf => Just $ rewrite sym prf in fromList l
    No _ => Nothing

export
validateContents : List Nat -> (n : Nat) -> Maybe (List (Fin n))
validateContents l n = traverse (\x => natToFin x n) l

export
Uninhabited (LTE (S n) n) where
  uninhabited (LTESucc x) = uninhabited x
