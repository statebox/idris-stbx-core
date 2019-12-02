module Util.Elem

import Data.Vect

%default total
%access public export

elem2Nat : Elem a g -> Nat
elem2Nat  Here      = Z
elem2Nat (There el) = S (elem2Nat el)

Show (Elem a g) where
  show = show . elem2Nat

indexElem : Fin n -> (g : Vect n a) -> (x ** Elem x g)
indexElem  FZ    (x::xs) = (x ** Here)
indexElem (FS k) (x::xs) = let (x ** el) = indexElem k xs in (x ** There el)

elem2Fin : Elem a g -> Fin (length g)
elem2Fin  Here      = FZ
elem2Fin (There el) = FS (elem2Fin el)
