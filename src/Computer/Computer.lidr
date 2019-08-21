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

> module Computer.Computer
>
> import Basic.Category
> import Control.Isomorphism
> import Data.Fin
> import Data.Vect
> import Free.Graph
> import Free.Path
> import GraphFunctor.ClosedTypedefsAsCategory
> import GraphFunctor.GraphEmbedding
> import Typedefs.Typedefs
>
> %access public export
> %default total
>
> compute :
>   -- a graph
>      (g : Graph)
>   -- initial and final vertices
>   -> (initialVertex, finalVertex : Graph.vertices g)
>   -- a functor to the category of closed typedefs
>   -> (iso : Iso (vertices g) (Fin k))
>   -> (v : Vect k (obj ClosedTypedefsAsCategory.closedTypedefsAsCategory))
>   -> Vect (length $ edges g) (mor' ClosedTypedefsAsCategory.closedTypedefsAsCategory)
>   -- a path in the graph from `initialVertex` to `finalVertex`
>   -> Path g initialVertex finalVertex
>   -- a value of the initial type
>   -> Ty [] (index (to iso initialVertex) v)
>   -- and we return a value of the final type
>   -> Ty [] (index (to iso finalVertex) v)
