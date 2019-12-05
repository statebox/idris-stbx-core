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

-- import Data.Fin
-- import Data.Vect
-- import Control.Isomorphism
-- import Basic.Category
-- import Free.FreeFunctor
-- import Free.Graph
-- import GraphFunctor.ClosedTypedefsAsCategory

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
   _ => empty

assembleElemM : -- Monad m =>
     Show gv => -- TODO: remove
     Show (obj cat) => -- TODO: remove
     (edges : Vect n (gv, gv))
  -> (to : gv -> Fin k)
  -> (vertices : Vect k (obj cat))
  -> (f : (i, j : gv) -> Elem (i, j) edges -> Maybe (mor cat (Vect.index (to i) vertices) (Vect.index (to j) vertices)))
  -> Maybe ((i, j : gv) -> Elem (i, j) edges -> mor cat (Vect.index (to i) vertices) (Vect.index (to j) vertices))
-- assembleElemM      {cat} []            to vertices f = pure (\_,_ => absurd)
-- assembleElemM {gv} {cat} ((i,j) :: xs) to vertices f =
assembleElemM {gv} {cat} edges to vertices f = do
  a <- pure $ unsafePerformIO $ do
                          putStrLn "--- assembleElemM ---"
                          printLn edges
                          printLn vertices
  case edges of
    [] => pure (\_,_ => absurd)
    ((i,j) :: xs) => do
      b <- pure $ unsafePerformIO $ do
                    putStrLn "--- assembleElemM inside"
                    printLn a
                    printLn i
                    printLn j
                    putStrLn "f i j Here"
                    printLn $ isJust (f i j Here)
                    putStrLn "any other string"
                    printLn $ isJust (assembleElemM {cat} xs to vertices (\k, l, el => f k l (There el)))
      (\a', b', k, l, el => case el of
                              Here      => a'
                              There el' => b' k l el') <$> f i j Here <*> assembleElemM {cat} xs to vertices (\k, l, el => f k l (There el))
  -- do x1 <- f i j Here
  --    x2 <- assembleElemM {cat} xs to vertices (\k,l,el => f k l (There el))
  --    pure $ \k,l,el => case el of
  --                    Here => x1
  --                    There el' => x2 k l el'

-- assembleMorphisms :
--      DecEq (obj cat)
--   => Monad m
--   => Alternative m
--   => (ge : Vect n (gv, gv))
--   -> (to : gv -> Fin k)
--   -> (v : Vect k (obj cat))
--   -> (e : Vect (length ge) (mor' cat))
--   -> m ((i, j : gv) -> Elem (i, j) ge -> mor cat (Vect.index (to i) v) (Vect.index (to j) v))
-- assembleMorphisms {m} {cat} ge to v e = assembleElemM {cat} ge to v (\k,l => extractMorphism {f=m} {cat} {to} {ge} {i=k} {j=l} v e)

-- graphEmbedding : DecEq (obj cat) =>
--      Iso (vertices g) (Fin k)
--   -> Vect k (obj cat)
--   -> Vect (length $ edges g) (mor' cat)
--   -> Maybe (GraphEmbedding g cat)
-- graphEmbedding {cat} {g} iso v e =
--   MkGraphEmbedding (flip Vect.index v . (to iso)) <$>
--     assembleMorphisms {cat} (edges g) (to iso) v e
