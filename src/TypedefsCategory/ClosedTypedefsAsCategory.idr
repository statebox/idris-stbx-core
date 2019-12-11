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

module TypedefsCategory.ClosedTypedefsAsCategory

-- base
import Data.Vect

-- idris-ct
import Basic.Category
import Basic.Functor
import Idris.TypesAsCategoryExtensional
import Monad.KleisliCategory
import Monad.IOMonad
import Monad.Monad

-- typedefs-core
import Typedefs.Typedefs

%access public export
%default total

infixr 5 -&>
(-&>) : (a, b : TDef 0) -> Type
(-&>) a b = Ty [] a -> Ty [] b

infixr 7 -*-
(-*-) : {a, b, c  : TDef 0} -> (a -&> b) -> (b -&> c) -> a -&> c
(-*-) ab bc = bc . ab

tdefId : (t : TDef 0) -> t -&> t
tdefId t = Basics.id

||| The category of typedefs without free variables.
||| Objects are typedefs, morphisms are Natural transformations between typedefs.
closedTypedefsAsCategory : Category
closedTypedefsAsCategory = MkCategory
  (TDef 0)
  (-&>)
  tdefId
  (\a,b,c => (-*-) {a} {b} {c})
  (\_,_,_ => Refl)
  (\_,_,_ => Refl)
  (\_,_,_,_,_,_,_ => Refl)

closedTypedefsFunctor : CFunctor ClosedTypedefsAsCategory.closedTypedefsAsCategory TypesAsCategoryExtensional.typesAsCategoryExtensional
closedTypedefsFunctor = MkCFunctor
  (Ty [])
  (\_,_ => MkExtensionalTypeMorphism)
  (\_ => Refl)
  (\_, _, _, _, _ => Refl)

closedTypedefsAsKleisliCategory : Monad TypesAsCategoryExtensional.typesAsCategoryExtensional -> Category
closedTypedefsAsKleisliCategory monad = MkCategory
  (TDef 0)
  (\a, b => mor (kleisliCategory monad) (Ty [] a) (Ty [] b))
  (\a => identity (kleisliCategory monad) (Ty [] a))
  (\a, b, c, f, g => compose (kleisliCategory monad) (Ty [] a) (Ty [] b) (Ty [] c) f g)
  (\a, b, f => leftIdentity (kleisliCategory monad) (Ty [] a) (Ty [] b) f)
  (\a, b, f => rightIdentity (kleisliCategory monad) (Ty [] a) (Ty [] b) f)
  (\a, b, c, d, f, g, h => associativity (kleisliCategory monad) (Ty [] a) (Ty [] b) (Ty [] c) (Ty [] d) f g h)

ioClosedTypedefsKleisliCategory : FFI -> Category
ioClosedTypedefsKleisliCategory ffi = ClosedTypedefsAsCategory.closedTypedefsAsKleisliCategory $ ioMonad ffi
