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
> import Free.FreeFunctor
> import Free.Graph
> import Free.Path
> import Free.PathCategory
> import GraphFunctor.ClosedTypedefsAsCategory
> import GraphFunctor.GraphEmbedding
> import Typedefs.Typedefs
> import Typedefs.Names
>
> %access public export
> %default total
> %hide Language.Reflection.Elab.Tactics.compute
>
> mkCFunctorInj : MkCFunctor mo1 mm1 pi1 pc1 = MkCFunctor mo2 mm2 pi2 pc2 -> mo1=mo2
> mkCFunctorInj Refl = Refl
>
> twoLoopsGraph : Graph
> twoLoopsGraph = MkGraph () [((),()), ((), ())]
>
> graphIso : Iso (vertices Example.twoLoopsGraph) (Fin 1)
> graphIso = MkIso
>   (\_ => FZ) (\_ => ()) (\FZ => Refl) (\() => Refl)
>
> -- this is mapped to Either () ()
> natTypedef : TDef 0
> natTypedef = TMu [("ZZ", T1), ("SS", TVar 0)]
>
> succ : Ty [] Example.natTypedef -> IO' FFI_JS (Ty [] Example.natTypedef)
> succ n = pure $ Inn $ Right n
>
> succsucc : Ty [] Example.natTypedef -> IO' FFI_JS (Ty [] Example.natTypedef)
> succsucc n = pure $ Inn $ Right $ Inn $ Right n
>
> succsPath : Path Example.twoLoopsGraph () ()
> succsPath = [Here, There Here]
>
> applyReflect' : Ty [] Example.natTypedef -> Maybe (IO' FFI_JS (Ty [] Example.natTypedef))
> applyReflect' = compute'
>   twoLoopsGraph
>   graphIso
>   [ Example.natTypedef ]
>   [ (Example.natTypedef ** Example.natTypedef ** MkExtensionalTypeMorphism succ)
>   , (Example.natTypedef ** Example.natTypedef ** MkExtensionalTypeMorphism succsucc)
>   ]
>   succsPath
