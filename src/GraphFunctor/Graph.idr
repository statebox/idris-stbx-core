module GraphFunctor.Graph

import Basic.Category

%access public export
%default total

record Graph where
  constructor MkGraph
  vertices : Type
  edges    : vertices -> vertices -> Type

data Path : (g : Graph) -> vertices g -> vertices g -> Type where
  Nil  : Path g i i
  (::) : edges g i j -> Path g j k -> Path g i k

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

pathCategory : Graph -> Category
pathCategory g = MkCategory
  (vertices g)
  (Path g)
  (\a => Nil)
  (\a, b, c, f, g => joinPath f g)
  (\a, b, f => Refl)
  (\a, b, f => joinPathNil f)
  (\a, b, c, d, f, g, h => joinPathAssoc f g h)