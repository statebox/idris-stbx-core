module Computer.Example2Helper

import Data.Vect
import Typedefs.Typedefs
import Typedefs.Names

%access public export
%default total

%include c "Computer/example2.h"

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
--CartContent = ListT CartItem

InvoiceId : TNamed 0
InvoiceId = TName "InvoiceId" $ wrap Natural

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
