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

module Computer.EcommerceExample

-- base
import Data.Vect

-- idris-ct
import Basic.Category

-- typedefs
import Typedefs.Names
import Typedefs.Typedefs

import GraphFunctor.GraphEmbedding
import TypedefsCategory.ClosedTypedefsAsCategory
import Util.Elem

%access public export
%default total

%include c "Computer/ecommerceExample.h"

Natural : TNamed 0
Natural = TName "Natural" $ TMu [("ZZ", T1), ("SS", TVar 0)]

InitialState : TNamed 0
InitialState = TName "InitialState" $ T1

ProductId : TNamed 0
ProductId = TName "ProductId" $ TSum [T1, T1, T1, T1]

Quantity : TNamed 0
Quantity = TName "Quantity" $ wrap Natural

CartItem : TNamed 0
CartItem = TName "CartItem" $ TProd [wrap ProductId, wrap Quantity]

CartContent : TNamed 0
CartContent = TName "CartContent" $ TMu [("NilN", T1), ("ConsN", TProd [weakenTDef (TApp CartItem []) 1 LTEZero, TVar 0])]

InvoiceId : TNamed 0
InvoiceId = TName "InvoiceId" $ wrap Natural

-- tdef for transitions
transition1 : TNamed 0
transition1 = TName "Login" (TProd [FRef "InitialState", FRef "CartContent"])

transition2 : TNamed 0
transition2 = TName "AddProduct" (TProd [FRef "CartContent", FRef "CartContent"])

transition3 : TNamed 0
transition3 = TName "Checkout" (TProd [FRef "CartContent", FRef "InvoiceId"])

checkName : TNamed 0 -> Maybe (String, TDef 0, TDef 0)
checkName = ?todo

makeMorphisms : List (String, a : TDef 0 ** b : TDef 0 ** Ty [] (unwrap a) -> IO (Ty [] (unwrap b)))
             -> (Fin lenV, Fin lenV, String)
             -> Maybe (mor' $ ioClosedTypedefsKleisliCategory FFI_C)
makeMorphisms transitions (_, _, label) = do
  (src ** tgt ** func) <- lookup label transitions
  pure ((unwrap src) ** (unwrap tgt) ** MkExtensionalTypeMorphism func)


-- functions

readIntFromUser : String -> IO Int
readIntFromUser = foreign FFI_C "readInt" (String -> IO Int)

intToProductId : Int -> Either () (Either () (Either () ()))
intToProductId i = assert_total $
  let remainder = mod i 4 in
  if      remainder == 0 then Left ()
  else if remainder == 1 then Right $ Left ()
  else if remainder == 2 then Right $ Right $ Left  ()
  else                        Right $ Right $ Right ()

weakenNat : Mu [] (TSum [T1, TVar FZ])
         -> Mu v (TSum [T1, TVar FZ])
weakenNat (Inn (Left ())) = Inn (Left ())
weakenNat (Inn (Right r)) = Inn (Right (weakenNat r))

generateRandomInt : () -> IO Int
generateRandomInt = foreign FFI_C "generateInt" (() -> IO Int)

generateInvoiceNumber : IO Nat
generateInvoiceNumber = cast <$> generateRandomInt ()

natToNatural : Nat -> Ty [] (Typedefs.wrap Natural)
natToNatural Z     = Inn (Left ())
natToNatural (S n) = Inn (Right $ natToNatural n)

readQuantityFromUser : IO $ Ty [] (Typedefs.wrap Natural)
readQuantityFromUser = do
  intFromUser <- readIntFromUser "quantity"
  pure $ natToNatural . cast $ intFromUser

readProductIdFromUser : IO $ Either () (Either () (Either () ()))
readProductIdFromUser = do
  intFromUser <- readIntFromUser "product"
  pure $ intToProductId intFromUser

unwrap : TNamed 0 -> TDef 0
unwrap (TName _ def) = def

||| login just creates an empty cart
login : Ty [] T1 -> IO $ Ty [] (unwrap CartContent)
login () = pure $ Inn (Left ())

||| add product asks the use for a product id and a quantity,
||| and adds it to the cart
addProduct : Ty [] (unwrap CartContent) -> IO $ Ty [] (unwrap CartContent)
addProduct cartContent = do
  productId <- readProductIdFromUser
  quantity  <- readQuantityFromUser
  pure $ Inn (Right $ ( (productId, weakenNat quantity)
                      , cartContent))

||| checkout generates a random invoice id
checkout : Ty [] (unwrap CartContent) -> IO $ Ty [] (unwrap InvoiceId)
checkout (Inn cartContent) = do
  randomNat <- generateInvoiceNumber
  pure $ natToNatural randomNat

morphismList : List (String, a : TDef 0 ** b : TDef 0 ** Ty [] (unwrap a) -> IO (Ty [] (unwrap b)))
morphismList = [ ("login", InitialState ** CartContent ** login)
               , ("addProduct", CartContent ** CartContent ** addProduct)
               , ("checkout", CartContent ** InvoiceId ** checkout)
               ]

edgeAsMorphism : (Fin lenV, Fin lenV, String) -> Maybe (mor' $ ioClosedTypedefsKleisliCategory FFI_C)
edgeAsMorphism label = makeMorphisms morphismList label

edgesAsMorphisms : Vect lenE (Fin lenV, Fin lenV, String)
                -> Maybe (Vect lenE (mor' $ ioClosedTypedefsKleisliCategory FFI_C))
edgesAsMorphisms edges = traverse edgeAsMorphism edges
