module Computer.Example2Helper

import Data.Vect
import Typedefs.Typedefs
import Typedefs.Names

%access public export
%default total

%include c "Computer/example2.h"

-- typedefs

Unit : TDef n
Unit = T1

Natural : TDef 0
Natural = TMu [("ZZ", Unit), ("SS", TVar 0)]

ListT : TDef 0 -> TDef 0
ListT t = TMu
  [ ("Nil", Unit)
  , ("Cons", TProd [weakenTDef t 1 LTEZero, TVar 0])]

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

natToNatural : Nat -> Ty [] Natural
natToNatural Z     = Inn (Left ())
natToNatural (S n) = Inn (Right $ natToNatural n)

readQuantityFromUser : IO $ Ty [] Natural
readQuantityFromUser = do
  intFromUser <- readIntFromUser "quantity"
  pure $ natToNatural . cast $ intFromUser

readProductIdFromUser : IO $ Either () (Either () (Either () ()))
readProductIdFromUser = do
  intFromUser <- readIntFromUser "product"
  pure $ intToProductId intFromUser
