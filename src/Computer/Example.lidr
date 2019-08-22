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

> module Computer.Example
>
> import Basic.Category
> import Basic.Functor
> import Computer.Computer
> import Control.Isomorphism
> import Data.Vect
> import Free.Graph
> import Free.Path
> import Free.PathCategory
> import GraphFunctor.ClosedTypedefsAsCategory
> import GraphFunctor.GraphEmbedding
> import Typedefs.Typedefs
>
> %access public export
> %default total
>
> loopGraph : Graph
> loopGraph = MkGraph () [((),())]
>
> graphIso : Iso (vertices Example.loopGraph) (Fin 1)
> graphIso = MkIso
>   (\_ => FZ) (\_ => ()) (\FZ => Refl) (\() => Refl)
>
> -- this is mapped to Either () ()
> boolTypedef : TDef 0
> boolTypedef = TSum [T1, T1]
>
> reflect : Either () () -> Either () ()
> reflect (Left  ()) = Right ()
> reflect (Right ()) = Left  ()
>
> reflectFunctor : Maybe (CFunctor (pathCategory Example.loopGraph) ClosedTypedefsAsCategory.closedTypedefsAsCategory)
> reflectFunctor = assembleFunctor loopGraph graphIso [boolTypedef] [(boolTypedef ** boolTypedef ** reflect)]
>
> reflectPath : Path Example.loopGraph () ()
> reflectPath = [Here]
>
> applyReflect : Either () () -> Maybe (Either () ())
> applyReflect input = case reflectFunctor of
>   Nothing   => Nothing
>   Just func => Just $ compute loopGraph () () func reflectPath input
