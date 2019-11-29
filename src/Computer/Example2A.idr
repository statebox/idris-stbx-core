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

module Computer.Example2A

-- base
import Data.Vect

-- idris-ct
import Graph.Graph
import Graph.Path

import Util.Elem

%access public export
%default total

parseEdges : Vect lenV (Nat, String) -> Vect lenE (Nat, Nat, String) -> Maybe (Vect lenE (Fin lenV, Fin lenV))
parseEdges {lenV} vertices edges = traverse (\(from, to, _) => [| MkPair (rlookup from) (rlookup to) |]) edges
  where
    rlookup : Nat -> Maybe (Fin lenV)
    rlookup n = findIndex (\(m, _) => m == n) vertices

mkGraph : Vect lenE (Fin lenV, Fin lenV) -> (graph : Graph (Fin lenV) ** numEdges graph = lenE)
mkGraph edges = (MkGraph edges ** Refl)

-- TODO verify that edge labels are distinct
lookupLabels : (edges : Vect len (Nat, Nat, String)) -> List String -> Maybe (List (Fin len))
lookupLabels {len} edges = traverse rlookup
  where
    rlookup : String -> Maybe (Fin len)
    rlookup l = findIndex (\(_, _, l') => l == l') edges

firingPath : (g : Graph (Fin len)) -> List (Fin (numEdges g)) -> Maybe (s ** t ** Path g s t)
firingPath g [] = Nothing
firingPath g [e] = let ((i,j)**el) = indexElem e (edges g) in Just (i ** j ** [el])
firingPath g (e::es) = firingPath g es >>= go
  where
  go : (s ** t ** Path g s t) -> Maybe (s ** t ** Path g s t)
  go (s**t**p) =
    let ((i,j)**el) = indexElem e (edges g) in
    case decEq j s of
      Yes eq => Just (i ** t ** el :: (rewrite eq in p))
      No _ => Nothing
