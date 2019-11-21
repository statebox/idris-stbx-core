module Computer.IGraph

import Data.List
import Data.Vect

%access public export
%default total

record Graph vertices where
  constructor MkGraph
  edges    : Vect n (vertices, vertices)

Show v => Show (Graph v) where
  show (MkGraph edges) = "G: " ++ show edges

numEdges : Graph v -> Nat
numEdges (MkGraph {n} _) = n

Edge : (g : Graph v) -> (i, j : v) -> Type
Edge g i j = Elem (i, j) (edges g)

edgeOrigin : {g : Graph v} -> Edge g i j -> v
edgeOrigin {i} _ = i

edgeTarget : {g : Graph v} -> Edge g i j -> v
edgeTarget {j} _ = j

data Path : (g : Graph v) -> v -> v -> Type where
  Nil  : Path g i i
  (::) : (a : Edge g i j) -> Path g j k -> Path g i k

--Show (Path g s t)

edgeToPath : {g : Graph v} -> (a : Edge g i j) -> Path g (edgeOrigin a) (edgeTarget a)
edgeToPath a = [a]

joinPath : Path g i j -> Path g j k -> Path g i k
joinPath [] y = y
joinPath (x :: xs) y = x :: joinPath xs y

joinPathNil : (p : Path g i j) -> joinPath p [] = p
joinPathNil Nil       = Refl
joinPathNil (x :: xs) = cong $ joinPathNil xs

joinPathAssoc :
     (p : Path g i j)
  -> (q : Path g j k)
  -> (r : Path g k l)
  -> joinPath p (joinPath q r) = joinPath (joinPath p q) r
joinPathAssoc Nil q r = Refl
joinPathAssoc (x :: xs) q r = cong $ joinPathAssoc xs q r
