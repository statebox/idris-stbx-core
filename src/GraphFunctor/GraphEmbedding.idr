-- \iffalse
-- SPDX-License-Identifier: AGPL-3.0-only

-- This file is part of `idris-ct` Category Theory in Idris library.

-- Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

-- This program is free software: you can redistribute it and/or modify
-- it under the terms of the GNU Affero General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.

-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU Affero General Public License for more details.

-- You should have received a copy of the GNU Affero General Public License
-- along with this program.  If not, see <https://www.gnu.org/licenses/>.
-- \fi

module GraphFunctor.GraphEmbedding

-- base
import Data.Fin
import Data.Vect

-- idris-ct
import Basic.Category
import Graph.Graph

import Util.Elem

%access public export
%default total

-- the type of morphisms
mor' : Category -> Type
mor' cat = (a : obj cat ** b : obj cat ** mor cat a b)

extractMorphism : (DecEq (obj cat), Alternative f) =>
     {to : gv -> Fin k}
  -> (v : Vect k (obj cat))
  -> (e : Vect (length ge) (mor' cat))
  -> Edge (MkGraph ge) i j
  -> f (mor cat (Vect.index (to i) v) (Vect.index (to j) v))
extractMorphism {to} {i} {j} v e edge =
  let (a' ** b' ** e') = Vect.index (elem2Fin edge) e in
    case (decEq a' (Vect.index (to i) v), decEq b' (Vect.index (to j) v)) of
      (Yes Refl, Yes Refl) => pure e'
      _                    => empty

assembleElemM : Applicative f =>
     (edges : Vect n (gv, gv))
  -> (to : gv -> Fin k)
  -> (vertices : Vect k (obj cat))
  -> (g : (i, j : gv) -> Elem (i, j) edges -> f (mor cat (Vect.index (to i) vertices) (Vect.index (to j) vertices)))
  -> f ((i, j : gv) -> Elem (i, j) edges -> mor cat (Vect.index (to i) vertices) (Vect.index (to j) vertices))
assembleElemM      {cat} []            to vertices g = pure (\_,_ => absurd)
assembleElemM {gv} {cat} ((i,j) :: xs) to vertices g =
  (\a', b', k, l, el => case el of
                          Here      => a'
                          There el' => b' k l el')
  <$> g i j Here
  <*> assembleElemM {cat} xs to vertices (\k, l, el => g k l (There el))
