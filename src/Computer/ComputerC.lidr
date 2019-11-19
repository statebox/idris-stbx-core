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

> module ComputerC.ComputerC
>
> import Basic.Category
> import Basic.Functor
> import Control.Isomorphism
> import Data.Fin
> import Data.Vect
> import Free.FreeFunctor
> import Free.Graph
> import Free.Path
> import Free.PathCategory
> import GraphFunctor.ClosedTypedefsAsCategory
> import GraphFunctor.GraphEmbedding
> import Idris.TypesAsCategoryExtensional
> import Monad.KleisliCategory
> import Monad.IOMonad
> import Monad.Monad
> import Typedefs.Typedefs
> import Typedefs.TypedefsDecEq
>
> %access public export
> %default total
>
> -- assembleFunctor :
> --   -- a graph
> --      (g : Graph)
> --   -- the data for building a functor to the category of closed typedefs
> --   -> (iso : Iso (vertices g) (Fin k))
> --   -> (v : Vect k (obj ClosedTypedefsAsCategory.closedTypedefsAsCategory))
> --   -> Vect (length $ edges g) (mor' ClosedTypedefsAsCategory.closedTypedefsAsCategory)
> --   -- maybe return a functor from the path category to the category of closed typedefs
> --   -> Maybe (CFunctor (pathCategory g) ClosedTypedefsAsCategory.closedTypedefsAsCategory)
> -- assembleFunctor g iso v e =
> --   (freeFunctor g) <$> (graphEmbedding {cat = ClosedTypedefsAsCategory.closedTypedefsAsCategory} iso v e)
>
> --compute :
> --  -- a graph
> --     (g : Graph)
> --  -- initial and final vertices
> --  -> (initialVertex, finalVertex : Graph.vertices g)
> --  -- a functor to the category of closed typedefs
> --  -> (func : CFunctor (pathCategory g) ClosedTypedefsAsCategory.closedTypedefsAsCategory)
> --  -- a path in the graph from `initialVertex` to `finalVertex`
> --  -> Path g initialVertex finalVertex
> --  -- a value of the initial type
> --  -> Ty [] (mapObj func initialVertex)
> --  -- and we return a value of the final type
> --  -> Ty [] (mapObj func finalVertex)
> --compute g initialVertex finalVertex func path initialValue =
> --  (mapMor func initialVertex finalVertex path) initialValue
>
> cClosedTypedefsKleisliCategory : Category
> cClosedTypedefsKleisliCategory = ClosedTypedefsAsCategory.closedTypedefsAsKleisliCategory $ ioMonad FFI_C
>
> compute :
>      (graph : Graph)
>   -> {initialVertex, finalVertex : vertices graph}
>   -> (functor : CFunctor (pathCategory graph) ComputerC.cClosedTypedefsKleisliCategory)
>   -> Path graph initialVertex finalVertex
>   -> Ty [] (mapObj functor initialVertex)
>   -> IO' FFI_C $ Ty [] (mapObj functor finalVertex)
> compute graph {initialVertex} {finalVertex} functor path initialValue = ?asdf
>   --func (mapMor functor initialVertex finalVertex path) initialValue



> --compute':
> --  -- a graph
> --     (g : Graph)
> --  -- the data for building a functor to the category of closed typedefs
> --  -> (iso : Iso (vertices g) (Fin k))
> --  -> (v : Vect k (obj ComputerC.cClosedTypedefsKleiliCategory))
> --  -> Vect (length $ edges g) (mor' ComputerC.cClosedTypedefsKleiliCategory)
> --  -- a path in the graph
> --  -> Path g initialVertex finalVertex
> --  -- a value of the initial type
> --  -> Ty [] (Vect.index (to iso initialVertex) v)
> --  -- and we return a value of the final type
> --  -> Maybe (IO' FFI_C (Ty [] (Vect.index (to iso finalVertex) v)))
> --compute' {initialVertex} {finalVertex} g iso v e path initialValue with (assembleElemM {cat=ComputerC.cClosedTypedefsKleiliCategory}
> --                                                                                       {m=Maybe}
> --                                                                                       (edges g)
> --                                                                                       (to iso)
> --                                                                                       v
> --                                                                                       (\k, l => extractMorphism {cat=ComputerC.cClosedTypedefsKleiliCategory}
> --                                                                                                                 {f=Maybe}
> --                                                                                                                 v e))
> --  compute' {initialVertex} { finalVertex} g iso v e path initialValue | Nothing = Nothing
> --  compute' {initialVertex} { finalVertex} g iso v e path initialValue | Just morphismsFunction = let
> --      gEmbedding = MkGraphEmbedding {cat=ComputerC.cClosedTypedefsKleiliCategory} (flip Vect.index v . (to iso)) morphismsFunction
> --      func = freeFunctor g gEmbedding
> --      mor = mapMor func initialVertex finalVertex path
> --    in
> --      Just $ ExtensionalTypeMorphism.func mor initialValue
