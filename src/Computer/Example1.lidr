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

> module Computer.Example1
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
> graphIso : Iso (vertices Example1.twoLoopsGraph) (Fin 1)
> graphIso = MkIso
>   (\_ => FZ) (\_ => ()) (\FZ => Refl) (\() => Refl)
>
> -- this is mapped to Either () ()
> rgbTypedef : TDef 0
> rgbTypedef = TSum [T1, T1, T1]
>
> forward : Ty [] Example1.rgbTypedef -> IO' FFI_JS (Ty [] Example1.rgbTypedef)
> forward (Left ())          = pure $ Right (Left ())
> forward (Right (Left ()))  = pure $ Right (Right ())
> forward (Right (Right ())) = pure $ Left ()
>
> backward : Ty [] Example1.rgbTypedef -> IO' FFI_JS (Ty [] Example1.rgbTypedef)
> backward (Left ())          = pure $ Right (Right ())
> backward (Right (Left ()))  = pure $ Left ()
> backward (Right (Right ())) = pure $ Right (Left ())
>
> succsPath : Path Example1.twoLoopsGraph () ()
> succsPath = [Here, There Here, Here, Here]
>
> applyReflect' : Ty [] Example1.rgbTypedef -> Maybe (IO' FFI_JS (Ty [] Example1.rgbTypedef))
> applyReflect' = compute'
>   twoLoopsGraph
>   graphIso
>   [ Example1.rgbTypedef ]
>   [ (Example1.rgbTypedef ** Example1.rgbTypedef ** MkExtensionalTypeMorphism forward)
>   , (Example1.rgbTypedef ** Example1.rgbTypedef ** MkExtensionalTypeMorphism backward)
>   ]
>   succsPath
