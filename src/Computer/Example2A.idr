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

-- base
import Data.Vect

-- idris-ct
import Basic.Category
import Graph.Graph
import Graph.Path

-- typedefs
import Typedefs.Names
import Typedefs.Typedefs

import Computer.Computer
import Computer.Example2Helper
import GraphFunctor.GraphEmbedding
import Util.Elem

%access public export
%default total

parseEdges : Vect lenV (Nat, String) -> Vect lenE (Nat, Nat, String) -> Maybe (Vect lenE (Fin lenV, Fin lenV, String))
parseEdges {lenV} vertices edges = traverse
  (\(from, to, label) => [| MkPair (rlookup from) [| MkPair (rlookup to) (pure label) |] |])
  edges
    where
      rlookup : Nat -> Maybe (Fin lenV)
      rlookup n = findIndex (\(m, _) => m == n) vertices

mkGraph : Vect lenE (Fin lenV, Fin lenV) -> (graph : Graph (Fin lenV) ** numEdges graph = lenE)
mkGraph edges = (MkGraph edges ** Refl)

-- TODO verify that edge labels are distinct
lookupEdges : (edges : Vect len (Nat, Nat, String)) -> List String -> Maybe (List (Fin len))
lookupEdges {len} edges = traverse rlookup
  where
    rlookup : String -> Maybe (Fin len)
    rlookup l = findIndex (\(_, _, l') => l == l') edges

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

vertexAsTypedefs : List (TNamed 0) -> (Nat, String) -> Maybe (Nat, TDef 0)
vertexAsTypedefs availableTypedefs (n, label) =
  let tnamed = find (\(TName name def) => name == label) availableTypedefs
  in (\(TName _ def) => (n, def)) <$> tnamed

verticesAsTypedefs : List (TNamed 0) -> Vect l (Nat, String) -> Maybe (Vect l (Nat, TDef 0))
verticesAsTypedefs availableTypedefs vertices = traverse (vertexAsTypedefs availableTypedefs) vertices

buildPath : (graph : Graph (Fin lenV))
         -> (prf : numEdges graph = lenE)
         -> List (Fin lenE)
         -> Maybe (s ** t ** Path graph s t)
buildPath graph prf labels = firingPath graph (rewrite prf in labels)

unwrap : TNamed 0 -> TDef 0
unwrap (TName _ def) = def

-- login just creates an empty cart

login : Ty [] T1 -> IO $ Ty [] (unwrap CartContent)
login () = pure $ Inn (Left ())


-- add product asks the use for a product id and a quantity,
-- and adds it to the cart

addProduct : Ty [] (unwrap CartContent) -> IO $ Ty [] (unwrap CartContent)
addProduct cartContent = do
  productId <- readProductIdFromUser
  quantity  <- readQuantityFromUser
  pure $ Inn (Right $ ( (productId, weakenNat quantity)
                      , cartContent))

-- checkout generates a random invoice id

checkout : Ty [] (unwrap CartContent) -> IO $ Ty [] (unwrap InvoiceId)
checkout (Inn cartContent) = do
  randomNat <- generateInvoiceNumber
  pure $ natToNatural randomNat

edgeAsMorphism : (Fin lenV, Fin lenV, String) -> Maybe (mor' $ Computer.cClosedTypedefsKleiliCategory FFI_C)
edgeAsMorphism (_, _, label) =
  if      label == "login"      then Just ((unwrap InitialState) ** (unwrap CartContent) ** MkExtensionalTypeMorphism login)
  else if label == "addProduct" then Just ((unwrap CartContent)  ** (unwrap CartContent) ** MkExtensionalTypeMorphism addProduct)
  else if label == "checkout"   then Just ((unwrap CartContent)  ** (unwrap InvoiceId)   ** MkExtensionalTypeMorphism checkout)
  else Nothing

edgesAsMorphisms : Vect lenE (Fin lenV, Fin lenV, String)
                -> Maybe (Vect lenE (mor' $ Computer.cClosedTypedefsKleiliCategory FFI_C))
edgesAsMorphisms edges = traverse edgeAsMorphism edges
