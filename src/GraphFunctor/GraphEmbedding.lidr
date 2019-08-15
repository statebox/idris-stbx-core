\iffalse
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
\fi

> module Free.GraphEmbedding
>
> import Data.Fin
> import Data.Vect
> import Control.Isomorphism
> import Basic.Category
> import Free.FreeFunctor
> import Free.Graph
> import Typedefs.ClosedTypedefsAsCategory
>
> %access public export
> %default total
>
>
> -- the type of morphisms
> mor' : Category -> Type
> mor' cat = (a : obj cat ** b : obj cat ** mor cat a b)


Assuming G graph fixed and target category cat fixed
Assuming vertices is enumerated and ordered:
([A,B,C,...], [f:A \to B, g:B \to C, ...])
This couple is legal if:
- Elements of the first list are objects of cat
- Elements of the second list are morphisms of cat
- The length of the first list is the same as the number of vertices in G
- The length of the second list is the same as the number of edges in G
-  For each element j of the second list:
-- make sure that MapObj(source(edge_j) ) = source element j
--- Suppose edge_j is sent to f:A -> B
--- Suppose source(edge_j) is vertex_i
--- Then I want i-th position in the first list to be (syntactically) equal to A.

-- make sure that MapObj(target(edge_j) ) = target element j

-- TODO does an Applicative suffice?

> sequenceElem : Monad f => {k : Nat} -> {xs : Vect k t}
>             -> ((x : t) -> Elem {k} x xs -> f a) -> f ({z : t} -> Elem {k} z xs -> a)
> sequenceElem               {xs=[]}    fe = pure absurd
> sequenceElem @{md} {k=S k} {xs=y::ys} fe =
>   do x1 <- fe y Here
>      x2 <- sequenceElem @{md} {k} {xs=ys} (\x => fe x . There)
>      pure $ \el => case el of
>                      Here => x1
>                      There el' => x2 el'
>
> elem2Fin : Elem a g -> Fin (length g)
> elem2Fin  Here      = FZ
> elem2Fin (There el) = FS (elem2Fin el)
>
> aux : DecEq (obj cat) => {to : gv -> Fin k}
>    -> (v : Vect k (obj cat)) -> (e : Vect (length ge) (mor' cat))
>    -> Edge (MkGraph gv _ ge) i j -> Maybe (mor cat (Vect.index (to i) v) (Vect.index (to j) v))
> aux {to} {i} {j} v e edge =
>  let (a' ** b' ** e') = index (elem2Fin edge) e in
>  case (decEq a' (Vect.index (to i) v), decEq b' (Vect.index (to j) v)) of
>    (Yes Refl, Yes Refl) => Just e'
>    _ => Nothing
>
> graphEmbedding : DecEq (obj cat) => Iso (vertices g) (Fin k) -> Vect k (obj cat) -> Vect (length $ edges g) (mor' cat) -> Maybe (GraphEmbedding g cat)
> graphEmbedding {cat} {g=MkGraph gv _ ge} (MkIso to from tf ft) v e =
>   MkGraphEmbedding (flip index v . to) <$>
>     sequenceElem {f=Maybe} {t=(gv, gv)} {xs=ge} (\(i,j) => aux {cat} {to} {i} {j} v e)
>


[v1 v2]
[e: v2 -> v1]

([B, A],[f:B->A])

f

. -e> .   ====> A -f-> B

|
v
A











{-

-- > aux' : {to : gv -> Fin k} -> Edge (MkGraph gv ne ge) i j -> (v : Vect k (obj cat)) -> (obj cat)
-- > aux' {to} {ge=(i,j)::ge} Here v e with (index (to i) v)
-- > aux' (There el) v e = ?wat6


-}
