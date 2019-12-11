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

-- base
import Control.Isomorphism
import Data.Vect

-- idris-ct
import Basic.Category
import Basic.Functor
import Graph.FreeFunctor
import Graph.Graph
import Graph.Path
import Graph.PathCategory
import Idris.TypesAsCategoryExtensional
import Monad.IOMonad
import Monad.Monad

-- typedefs-core
import Typedefs.Typedefs
import Typedefs.TypedefsDecEq

import GraphFunctor.GraphEmbedding
import TypedefsCategory.ClosedTypedefsAsCategory

%access public export
%default total

compute:
  -- a graph
     (graph : Graph v)
  -- the data for building a functor to the category of closed typedefs
  -> (iso : Iso v (Fin k))
  -> (vertices : Vect k (obj $ ioClosedTypedefsKleisliCategory ffi))
  -> Vect (numEdges graph) (mor' $ ioClosedTypedefsKleisliCategory ffi)
  -- a path in the graph
  -> Path graph initialVertex finalVertex
  -- a value of the initial type
  -> Ty [] (Vect.index (to iso initialVertex) vertices)
  -- and we return a value of the final type
  -> Maybe (IO' ffi (Ty [] (Vect.index (to iso finalVertex) vertices)))
compute {ffi} {initialVertex} {finalVertex} graph iso vertices edges path initialValue
  with (assert_total $ assembleElemM {cat = ioClosedTypedefsKleisliCategory ffi}
                                     {f = Maybe}
                                     (Graph.edges graph)
                                     (to iso)
                                     vertices
                                     (\_, _ => extractMorphism {cat = ioClosedTypedefsKleisliCategory ffi}
                                                               {f = Maybe}
                                                               vertices
                                                               (rewrite sym $ numEdgesPrf graph in edges)))
  compute {ffi} {initialVertex} {finalVertex} graph iso vertices edges path initialValue
    | Nothing                = Nothing
  compute {ffi} {initialVertex} {finalVertex} graph iso vertices edges path initialValue
    | Just morphismsFunction = let
        graphEmbedding = MkGraphEmbedding {cat=ioClosedTypedefsKleisliCategory ffi}
                                          (flip Vect.index vertices . (to iso))
                                          morphismsFunction
        func = freeFunctor graph graphEmbedding
        mor = mapMor func initialVertex finalVertex path
      in
        Just $ ExtensionalTypeMorphism.func mor initialValue
