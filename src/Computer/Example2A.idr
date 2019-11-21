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

module Computer.Example2A

import Util.Elem
import Basic.Category
import Computer.ComputerC
import Computer.Example2Helper
import Control.Isomorphism
import Data.NEList
import Data.Vect
import Computer.IGraph
import GraphFunctor.GraphEmbedding
import Typedefs.Typedefs
import Typedefs.Names

%access public export
%default total

-- TODO validate that vertex labels are distinct
-- TODO pass in NEList (Nat, TDef) for vertices instead
parseVertices : (vs : NEList (Nat, String)) -> Vect (length vs) (Nat, String)
parseVertices = toVect

-- first param is vertex mapping
mkGraph : Vect len (Nat, String) -> NEList (Nat, Nat, String) -> Maybe (Graph (Fin len))
mkGraph {len} vs es = map (MkGraph {n=length es}) $
  traverse (\(fro, to, _) => [| MkPair (rlookup fro) (rlookup to) |]) (toVect es)
    where
     rlookup : Nat -> Maybe (Fin len)
     rlookup n = findIndex (\(m, _) => m == n) vs

edgeNumProof : (vm : Vect len (Nat, String)) -> (em : NEList (Nat, Nat, String)) -> case mkGraph vm em of
                                                                                      Just gr => numEdges gr = length em
                                                                                      Nothing => ()
edgeNumProof vm (MkNEList e em) = ?wat

-- TODO verify that edge labels are distinct
lookupLabels : List String -> (em : NEList (Nat, Nat, String)) -> Maybe (List (Fin (length em)))
lookupLabels lbs em = traverse rlookup lbs
  where
    em' : Vect (length em) (Nat, Nat, String)
    em' = toVect em
    rlookup : String -> Maybe (Fin (length em))
    rlookup l = findIndex (\(_, _, l') => l == l') em'

-- TODO lookup labels
firingPath : (g : Graph (Fin len)) -> List (Fin (numEdges g)) -> Maybe (s ** t ** Path g s t)
firingPath g [] = Nothing
firingPath g [e] = let ((i,j)**el) = indexElem e (edges g) in Just (i ** j ** [el])
firingPath g (e::es) = firingPath g es >>= go
  where
  go : (s ** t ** Path g s t) -> Maybe (s ** t ** Path g s t)
  go (s**t**p) =
    let ((i,j)**el) = indexElem e (edges g) in
    case decEq j s of
      Yes eq => Just (i ** t ** el :: (rewrite eq in p))
      No _ => Nothing

{-
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
EcommerceGraph = MkGraph
  EcommerceState
  [(Guest, Cart), (Cart, Cart), (Cart, PurchaseCompleted)]

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
path = [Here, There Here, There Here, There $ There Here]

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
-}