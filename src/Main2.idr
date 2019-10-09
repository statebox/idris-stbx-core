module Main

import Computer.Example2
import Data.Vect
import Typedefs.Typedefs

%access public export
%default total

invoiceIdToString : Ty [] InvoiceId -> String
invoiceIdToString = cast . invoiceIdToNat
  where
    invoiceIdToNat : Ty [] InvoiceId -> Nat
    invoiceIdToNat (Inn (Left ()))        = 0
    invoiceIdToNat (Inn (Right previous)) = 1 + invoiceIdToNat previous

main : IO ()
main =
  case Example2.walkOnTheWildSide of
    Nothing => putStrLn' "Ouch, something went wrong"
    Just goForAWalk => do
      invoiceId <- goForAWalk
      putStrLn' $ "The invoice id is" ++ invoiceIdToString invoiceId

  