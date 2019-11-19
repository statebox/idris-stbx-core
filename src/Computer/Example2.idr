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

module Computer.Example2

import Basic.Category
import Computer.ComputerC
import Computer.Example2Helper
import Control.Isomorphism
import Data.Vect
import Free.Graph
import Free.Path
import GraphFunctor.GraphEmbedding
import Typedefs.Typedefs
import Typedefs.Names

%access public export
%default total

%include c "Computer/example2.h"

-- Consider this graph
--
--                 --------------
--              |--| AddProduct |-->|
--              |  --------------   |
--              |                   |
--              --------    ---------
--                      \  /
--         ---------     \/    ------------
-- Guest --| Login |--> Cart --| Checkout |--> PurchaseCompleted
--         ---------           ------------

data EcommerceState = Guest | Cart | PurchaseCompleted

GuestNotCart : Guest = Cart -> Void
GuestNotCart Refl impossible

GuestNotPurchaseCompleted : Guest = PurchaseCompleted -> Void
GuestNotPurchaseCompleted Refl impossible

CartNotPurchaseCompleted : Cart = PurchaseCompleted -> Void
CartNotPurchaseCompleted Refl impossible

DecEq EcommerceState where
  decEq Guest Guest = Yes Refl
  decEq Guest Cart = No GuestNotCart
  decEq Guest PurchaseCompleted = No GuestNotPurchaseCompleted
  decEq Cart Guest = No (negEqSym GuestNotCart)
  decEq Cart Cart = Yes Refl
  decEq Cart PurchaseCompleted = No CartNotPurchaseCompleted
  decEq PurchaseCompleted Guest = No (negEqSym GuestNotPurchaseCompleted)
  decEq PurchaseCompleted Cart = No (negEqSym CartNotPurchaseCompleted)
  decEq PurchaseCompleted PurchaseCompleted = Yes Refl

Eq EcommerceState where
  Guest             == Guest             = True
  Cart              == Cart              = True
  PurchaseCompleted == PurchaseCompleted = True
  _                 == _                 = False

EcommerceGraph : Graph
EcommerceGraph = edgeList {n = 3} [(Guest, Cart), (Cart, Cart), (Cart, PurchaseCompleted)]

-- Proof that the set of vertices is finite

EcommerceGraphIsFinite : Iso (vertices EcommerceGraph) (Fin 3)
EcommerceGraphIsFinite = MkIso
  graphToFin
  finToGraph
  finToGraphToFin
  graphToFinToGraph
    where
      graphToFin : EcommerceState -> Fin 3
      graphToFin Guest             = FZ
      graphToFin Cart              = FS FZ
      graphToFin PurchaseCompleted = FS $ FS FZ

      finToGraph : Fin 3 -> EcommerceState
      finToGraph FZ           = Guest
      finToGraph (FS FZ)      = Cart
      finToGraph (FS (FS FZ)) = PurchaseCompleted

      finToGraphToFin : (n : Fin 3)
                     -> (graphToFin . finToGraph) n = n
      finToGraphToFin FZ           = Refl
      finToGraphToFin (FS FZ)      = Refl
      finToGraphToFin (FS (FS FZ)) = Refl

      graphToFinToGraph : (s : EcommerceState)
                       -> (finToGraph . graphToFin) s = s
      graphToFinToGraph Guest             = Refl
      graphToFinToGraph Cart              = Refl
      graphToFinToGraph PurchaseCompleted = Refl

-- we need to define a semantic
--
-- Guest             -> ()
-- Cart              -> [(ProductId, Quantity)]
-- PurchaseCompleted -> InvoiceId
--
-- where
--
-- ProductId is a sum type with 4 cases
-- Quantity  is a natural number
-- InvoiceId is a natural number

InitialState : TDef 0
InitialState = Unit

ProductId : TDef 0
ProductId = TSum [Unit, Unit, Unit, Unit]

Quantity : TDef 0
Quantity = Natural

CartItem : TDef 0
CartItem = TProd [ProductId, Quantity]

CartContent : TDef 0
CartContent = ListT CartItem

InvoiceId : TDef 0
InvoiceId = Natural

-- we also need to map the arrows of the graph

-- login just creates an empty cart

login : Ty [] Unit -> IO $ Ty [] CartContent
login () = pure $ Inn (Left ())


-- add product asks the use for a product id and a quantity,
-- and adds it to the cart

addProduct : Ty [] CartContent -> IO $ Ty [] CartContent
addProduct cartContent = do
  productId <- readProductIdFromUser
  quantity  <- readQuantityFromUser
  pure $ Inn (Right $ ( (productId, weakenNat quantity)
                      , cartContent))

-- checkout generates a random invoice id

checkout : Ty [] CartContent -> IO $ Ty [] InvoiceId
checkout (Inn cartContent) = do
  randomNat <- generateInvoiceNumber
  pure $ natToNatural randomNat

-- we provide the path

path : Path EcommerceGraph Guest PurchaseCompleted
path = edgeListPath $ Here `Cons` (There Here `Cons` (There Here `Cons` ((There $ There Here) `Cons` Empty)))

-- and finally we compute

walkOnTheWildSide : Maybe (IO $ Ty [] InvoiceId)
walkOnTheWildSide = compute'
  EcommerceGraph
  EcommerceGraphIsFinite
  [InitialState, CartContent, InvoiceId]
  [ (  InitialState ** CartContent
    ** MkExtensionalTypeMorphism login)
  , (  CartContent ** CartContent
    ** MkExtensionalTypeMorphism addProduct)
  , (  CartContent ** InvoiceId
    ** MkExtensionalTypeMorphism checkout)
  ]
  path
  ()
