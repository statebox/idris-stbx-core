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

module Computer.Computer

import Basic.Category
import Basic.Functor
import Control.Isomorphism
import Data.Fin
import Data.Vect
-- import Free.FreeFunctor
import Graph.FreeFunctor
import Graph.Graph
import Graph.Path
import Graph.PathCategory
import GraphFunctor.ClosedTypedefsAsCategory
import GraphFunctor.GraphEmbedding
import Idris.TypesAsCategoryExtensional
-- import Monad.KleisliCategory
import Monad.IOMonad
import Monad.Monad
import Typedefs.Typedefs
import Typedefs.TypedefsDecEq

%access public export
%default total

-- assembleFunctor :
--   -- a graph
--      (g : Graph)
--   -- the data for building a functor to the category of closed typedefs
--   -> (iso : Iso (vertices g) (Fin k))
--   -> (v : Vect k (obj ClosedTypedefsAsCategory.closedTypedefsAsCategory))
--   -> Vect (length $ edges g) (mor' ClosedTypedefsAsCategory.closedTypedefsAsCategory)
--   -- maybe return a functor from the path category to the category of closed typedefs
--   -> Maybe (CFunctor (pathCategory g) ClosedTypedefsAsCategory.closedTypedefsAsCategory)
-- assembleFunctor g iso v e =
--   (freeFunctor g) <$> (graphEmbedding {cat = ClosedTypedefsAsCategory.closedTypedefsAsCategory} iso v e)

-- compute :
--   -- a graph
--      (g : Graph)
--   -- initial and final vertices
--   -> (initialVertex, finalVertex : Graph.vertices g)
--   -- a functor to the category of closed typedefs
--   -> (func : CFunctor (pathCategory g) ClosedTypedefsAsCategory.closedTypedefsAsCategory)
--   -- a path in the graph from `initialVertex` to `finalVertex`
--   -> Path g initialVertex finalVertex
--   -- a value of the initial type
--   -> Ty [] (mapObj func initialVertex)
--   -- and we return a value of the final type
--   -> Ty [] (mapObj func finalVertex)
-- compute g initialVertex finalVertex func path initialValue =
--   (mapMor func initialVertex finalVertex path) initialValue

cClosedTypedefsKleiliCategory : FFI -> Category
cClosedTypedefsKleiliCategory ffi = ClosedTypedefsAsCategory.closedTypedefsAsKleisliCategory $ ioMonad ffi

compute:
  Show v => -- TODO: remove
  -- a graph
     (graph : Graph v)
  -- the data for building a functor to the category of closed typedefs
  -> (iso : Iso v (Fin k))
  -> (vertices : Vect k (obj $ Computer.cClosedTypedefsKleiliCategory ffi))
  -> Vect (numEdges graph) (mor' $ Computer.cClosedTypedefsKleiliCategory ffi)
  -- a path in the graph
  -> Path graph initialVertex finalVertex
  -- a value of the initial type
  -> Ty [] (Vect.index (to iso initialVertex) vertices)
  -- and we return a value of the final type
  -> Maybe (IO' ffi (Ty [] (Vect.index (to iso finalVertex) vertices)))
compute {ffi} {initialVertex} {finalVertex} graph iso vertices edges path initialValue with (assembleElemM {cat = Computer.cClosedTypedefsKleiliCategory ffi}
                                                                                                           --{m = Maybe}
                                                                                                           (Graph.edges graph)
                                                                                                           (to iso)
                                                                                                           vertices
                                                                                                           (\k, l => extractMorphism {cat = Computer.cClosedTypedefsKleiliCategory ffi}
                                                                                                                                     {f = Maybe}
                                                                                                                                     vertices
                                                                                                                                     (rewrite sym $ numEdgesPrf graph in edges)))
  compute {ffi} {initialVertex} {finalVertex} graph iso vertices edges path initialValue | Nothing                = -- Nothing
    (Just $ do putStrLn' "#------#"
               printLn' graph
               printLn' vertices
               printLn' $ (\edge => (fst edge, fst $ snd edge)) <$> edges
               printLn' $ isJust (assembleElemM {cat = Computer.cClosedTypedefsKleiliCategory ffi}
                                                --{m = Maybe}
                                                (Graph.edges graph)
                                                (to iso)
                                                vertices
                                                (\k, l => extractMorphism {cat = Computer.cClosedTypedefsKleiliCategory ffi}
                                                                          {f = Maybe}
                                                                          vertices
                                                                          (rewrite sym $ numEdgesPrf graph in edges)))
               ?asdf) <+> Nothing
  compute {ffi} {initialVertex} {finalVertex} graph iso vertices edges path initialValue | Just morphismsFunction = let
      graphEmbedding = MkGraphEmbedding {cat=Computer.cClosedTypedefsKleiliCategory ffi} (flip Vect.index vertices . (to iso)) morphismsFunction
      func = freeFunctor graph graphEmbedding
      mor = mapMor func initialVertex finalVertex path
    in
      Just $ ExtensionalTypeMorphism.func mor initialValue
