module Parser.Input

-- tparsec
import Data.NEList
import TParsec
import TParsec.Running

-- typedefs
import Typedefs.Typedefs
import Typedefs.Parse

import ErrDef

%access public export
%default total

readInput : String -> (String -> Result Parse.Error a) -> IO (Either ProcError a)
readInput fn parse = do
  Right str <- readFile fn
   | Left err => pure (Left $ FErr err)
  pure $ result (Left . TPErr) (Left . TPErr) Right $ parse str

||| At the moment we are using only closed typedefs
checkClosedTNamed : (n ** TNamed n) -> Either ProcError (TNamed 0)
checkClosedTNamed (Z ** def) = pure def
checkClosedTNamed _ = Left TDefErr

checkClosed : NEList (n ** TNamed n) -> Either ProcError (NEList (TNamed 0))
checkClosed = traverse checkClosedTNamed

readTypedefs : (filename : String) -> IO (Either ProcError (NEList (TNamed 0)))
readTypedefs filename = do
  Right ls <- readInput filename parseTNameds
    | Left err => pure (Left err)
  pure $ checkClosed ls

ParserF : Type -> Nat -> Type
ParserF = Parser (TParsecT Error Void Identity) chars

fsmParser : All (ParserF (NEList (Nat, String), NEList (Nat, Nat, String)))
fsmParser = states `and` (withSpaces (string "---") `rand` transitions)
  where
  states : All (ParserF (NEList (Nat, String)))
  states = nelist $ decimalNat `and` withSpaces alphas
  transitions : All (ParserF (NEList (Nat, Nat, String)))
  transitions = nelist $ decimalNat `and` (withSpaces decimalNat `and` withSpaces alphas)

readFSM : (filename : String) -> IO (Either ProcError (NEList (Nat, String), NEList (Nat, Nat, String)))
readFSM filename = readInput filename (\s => getResult $ parseResult s fsmParser)
