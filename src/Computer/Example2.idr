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

EcommerceGraph : Graph
EcommerceGraph = MkGraph EcommerceState [(Guest, Cart), (Cart, Cart), (Cart, PurchaseCompleted)]

-- Proof that the set of vertices is finite

EcommerceGraphIsFinite : Iso (vertices EcommerceGraph) (Fin 3)
EcommerceGraphIsFinite = MkIso graphToFin finToGraph finToGraphToFin graphToFinToGraph
  where
    graphToFin : EcommerceState -> Fin 3
    graphToFin Guest             = FZ
    graphToFin Cart              = FS FZ
    graphToFin PurchaseCompleted = FS $ FS FZ

    finToGraph : Fin 3 -> EcommerceState
    finToGraph FZ           = Guest
    finToGraph (FS FZ)      = Cart
    finToGraph (FS (FS FZ)) = PurchaseCompleted

    finToGraphToFin : (n : Fin 3) -> (graphToFin . finToGraph) n = n
    finToGraphToFin FZ           = Refl
    finToGraphToFin (FS FZ)      = Refl
    finToGraphToFin (FS (FS FZ)) = Refl

    graphToFinToGraph : (s : EcommerceState) -> (finToGraph . graphToFin) s = s
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
InitialState = T1

ProductId : TDef 0
ProductId = TSum [T1, T1, T1, T1]

Quantity : TDef 0
Quantity = TMu [("ZZ", T1), ("SS", TVar 0)]

CartItem : TDef 0
CartItem = TProd [ProductId, Quantity]

CartContent : TDef 0
CartContent = TMu [("Nil", T1), ("Cons", TProd [weakenTDef CartItem 1 LTEZero, TVar 0])]

InvoiceId : TDef 0
InvoiceId = TMu [("ZZ", T1), ("SS", TVar 0)]

-- we also need to map the arrows of the graph

-- login just creates an empty cart
login : Ty [] T1 -> IO $ Ty [] CartContent
login () = pure $ Inn (Left ())

-- add product asks the use for a product id and a quantity, and adds it to the cart
readIntFromUser : String -> IO Int
readIntFromUser = foreign FFI_C "readInt" (String -> IO Int)

intToProductId : Int -> Either () (Either () (Either () ()))
intToProductId i = assert_total $
  let remainder = mod i 4 in
  if      remainder == 0 then Left ()
  else if remainder == 1 then Right $ Left ()
  else if remainder == 2 then Right $ Right $ Left  ()
  else                        Right $ Right $ Right ()

readProductIdFromUser : IO $ Ty [] ProductId
readProductIdFromUser = do
  intFromUser <- readIntFromUser "product"
  pure $ intToProductId intFromUser

natToQuantity : Nat -> Ty [] InvoiceId
natToQuantity Z     = Inn (Left ())
natToQuantity (S n) = Inn (Right $ natToQuantity n)

readQuantityFromUser : IO $ Ty [] Quantity
readQuantityFromUser = do
  intFromUser <- readIntFromUser "quantity"
  pure $ natToQuantity . cast $ intFromUser

weakenNat : Mu [] (TSum [T1, TVar FZ]) -> Mu v (TSum [T1, TVar FZ])
weakenNat (Inn (Left ())) = Inn (Left ())
weakenNat (Inn (Right r)) = Inn (Right (weakenNat r))

addProduct : Ty [] CartContent -> IO $ Ty [] CartContent
addProduct cartContent = do
  productId <- readProductIdFromUser
  quantity  <- readQuantityFromUser
  pure $ Inn (Right $ ((productId, weakenNat quantity), cartContent))

-- checkout generates a random invoice id
natToInvoiceId : Nat -> Ty [] InvoiceId
natToInvoiceId Z     = Inn (Left ())
natToInvoiceId (S n) = Inn (Right $ natToInvoiceId n)

generateRandomInt : () -> IO Int
generateRandomInt = foreign FFI_C "generateInt" (() -> IO Int)

generateInvoiceNumber : IO Nat
generateInvoiceNumber = cast <$> generateRandomInt ()

checkout : Ty [] CartContent -> IO $ Ty [] InvoiceId
checkout (Inn cartContent) = do
  randomNat <- generateInvoiceNumber
  pure $ natToInvoiceId randomNat

-- we provide the path

path : Path EcommerceGraph Guest PurchaseCompleted
path = [Here, There Here, There Here, There $ There Here]

-- and finally we compute

walkOnTheWildSide : Maybe (IO $ Ty [] InvoiceId)
walkOnTheWildSide = compute'
  EcommerceGraph
  EcommerceGraphIsFinite
  [InitialState, CartContent, InvoiceId]
  [ (InitialState ** CartContent ** MkExtensionalTypeMorphism login)
  , (CartContent  ** CartContent ** MkExtensionalTypeMorphism addProduct)
  , (CartContent  ** InvoiceId   ** MkExtensionalTypeMorphism checkout)
  ]
  path
  ()
