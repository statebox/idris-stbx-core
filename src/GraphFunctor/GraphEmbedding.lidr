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

> module GraphFunctor.GraphEmbedding
>
> import Data.Fin
> import Data.Vect
> import Control.Isomorphism
> import Basic.Category
> import Free.FreeFunctor
> import Free.Graph
> import GraphFunctor.ClosedTypedefsAsCategory
>
> %access public export
> %default total
>
> -- the type of morphisms
> mor' : Category -> Type
> mor' cat = (a : obj cat ** b : obj cat ** mor cat a b)
>
> elem2Fin : Elem a g -> Fin (length g)
> elem2Fin  Here      = FZ
> elem2Fin (There el) = FS (elem2Fin el)
>
> extractMorphism : (DecEq (obj cat), Alternative f) =>
>      {to : gv -> Fin k}
>   -> (v : Vect k (obj cat))
>   -> (e : Vect (length ge) (mor' cat))
>   -> Edge (MkGraph gv ge) i j
>   -> f (mor cat (Vect.index (to i) v) (Vect.index (to j) v))
> extractMorphism {to} {i} {j} v e edge =
>  let (a' ** b' ** e') = index (elem2Fin edge) e in
>  case (decEq a' (Vect.index (to i) v), decEq b' (Vect.index (to j) v)) of
>    (Yes Refl, Yes Refl) => pure e'
>    _ => empty
>
> assembleElemM : Monad m =>
>      (ge : Vect n (gv, gv))
>   -> (to : gv -> Fin k)
>   -> (v : Vect k (obj cat))
>   -> (f : {i, j : gv} -> Elem (i, j) ge -> m (mor cat (Vect.index (to i) v) (Vect.index (to j) v)))
>   -> m ({i, j : gv} -> Elem (i, j) ge -> mor cat (Vect.index (to i) v) (Vect.index (to j) v))
> assembleElemM {cat} []        to v f = pure absurd
> assembleElemM {gv} {cat} ((i,j) :: xs) to v f =
>   do x1 <- f Here
>      x2 <- assembleElemM {cat} xs to v (f . There)
>      pure $ \el => case el of
>                      Here => x1
>                      There el' => x2 el'
>
> assembleMorphisms :
>      DecEq (obj cat)
>   => Monad m
>   => Alternative m
>   => (ge : Vect n (gv, gv))
>   -> (to : gv -> Fin k)
>   -> (v : Vect k (obj cat))
>   -> (e : Vect (length ge) (mor' cat))
>   -> m ({i, j : gv} -> Elem (i, j) ge -> mor cat (Vect.index (to i) v) (Vect.index (to j) v))
> assembleMorphisms {cat} ge to v e = assembleElemM {cat} ge to v (extractMorphism {cat} {to} v e)
>
> graphEmbedding : DecEq (obj cat) =>
>      Iso (vertices g) (Fin k)
>   -> Vect k (obj cat)
>   -> Vect (length $ edges g) (mor' cat)
>   -> Maybe (GraphEmbedding g cat)
> graphEmbedding {cat} {g=MkGraph gv ge} (MkIso to from tf ft) v e =
>   MkGraphEmbedding (flip index v . to) <$>
>     assembleMorphisms {cat} ge to v e
