module Main

import Basic.Category
import Basic.Functor
import Idris.TypesAsCategory
--import GraphFunctor.Graph
--import Free.Graph
--import GraphFunctor.FreeFunctor
--import GraphFunctor.FFICategory

--import Computer.Computer
--import Computer.Example1

import Data.NEList
import Typedefs.Typedefs
import Typedefs.Parse

import TParsec
import TParsec.Running

import Free.Graph

import Data.SortedMap
import Data.Vect
import Options.Applicative
import Cmdline
import Util.Misc
import Util.Max

import Computer.IGraph
import Computer.Example2A

%access public export
%default total

%include c "fficat.h"

Show (Fin n) where
  show = show . finToNat

data ProcError = FErr FileError | PErr ParseError | TPErr Parse.Error

Show ProcError where
  show (FErr ferr) = "Filesystem error: " ++ show ferr
  show (PErr (ErrorMsg err)) = "Parse error: " ++ err
  show (TPErr err) = "Tparsec error: " ++ show err

processArgs : List String -> Either ParseError CommandLineOpts
processArgs (_ :: opts) = runParserFully parseCmdlineOpts opts
processArgs  _          = Left (ErrorMsg "Not enough arguments")

readInput : String -> (String -> Result Error a) -> IO (Either ProcError a)
readInput fn parse = do Right str <- readFile fn
                         | Left err => pure (Left $ FErr err)
                        pure $ result (Left . TPErr) (Left . TPErr) Right $ parse str

readTypedefs : InTD -> IO (Either ProcError (NEList (n : Nat ** TNamed n)))
readTypedefs (TDFile f) = readInput f parseTNameds

ParserF : Type -> Nat -> Type
ParserF = Parser (TParsecT Error Void Identity) chars

fsmParser : All (ParserF (NEList (Nat, String), NEList (Nat, Nat, String)))
fsmParser = states `and` (withSpaces (string "---") `rand` transitions)
  where
  states : All (ParserF (NEList (Nat, String)))
  states = nelist $ decimalNat `and` withSpaces alphas
  transitions : All (ParserF (NEList (Nat, Nat, String)))
  transitions = nelist $ decimalNat `and` (withSpaces decimalNat `and` withSpaces alphas)

readFSM : InFSM -> IO (Either ProcError (NEList (Nat, String), NEList (Nat, Nat, String)))
readFSM (FSMFile f) = readInput f (\s => getResult $ parseResult s fsmParser)

runWithOptions : CoreOpts -> IO ()
runWithOptions (MkCoreOpts tdf fsmf firings) =
  do disableBuffering  -- don't remove this!
     Right tdef <- readTypedefs tdf
       | Left err => putStrLn ("Typedefs read error: " ++ show err)
     Right (vs, es) <- readFSM fsmf
       | Left err => putStrLn ("FSM read error:" ++ show err)
     printLn tdef
     printLn vs
     printLn es
     putStrLn "-------"
     let mgraph = mkGraph (parseVertices vs) es
     let labels = lookupLabels firings es
     let path = [| firingPath mgraph labels |]
     ?wat
     --printLn mgraph --$ the Nat $ maybe 0 (\(MkGraph vt edg) => Vect.length edg) mgraph

  -- case constructMap ffi of
  --   Just m =>
  --     let v = ffiEdges fsm in
  --     case validateContents firings (length fsm) of
  --       Just vf =>
  --         case firingPath v vf of
  --           Just (s**t**p) => pure $ mapMor (ffiFunctor v m) s t p ()
  --           Nothing => putStrLn "malformed firing sequence: misaligned path"
  --       Nothing => putStrLn "malformed firing sequence: numbers outside of graph"
  --   Nothing => putStrLn "unknown FFI function in map"

partial
--main : IO' FFI_JS ()
--main = do
--  _ <- pure $ applyReflect' (Left ())
--  pure ()
main : IO ()
main = do Right options <- processArgs <$> getArgs
            | Left (ErrorMsg msg) => putStrLn msg
          case options of
               Help => putStrLn helpMessage
               HelpFallback => putStrLn fallbackMessage
               Run o => runWithOptions o
