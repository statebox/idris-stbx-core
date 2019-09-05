module Util

import Data.Vect

%default total

export
parseNat : String -> Either String Nat
parseNat s = if all isDigit (unpack s)
                then Right $ cast {to=Nat} s
                else Left "not a number"

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