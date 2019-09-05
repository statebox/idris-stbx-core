module Main

import Basic.Category
import Basic.Functor
import Idris.TypesAsCategory
import GraphFunctor.Graph
import GraphFunctor.FreeFunctor
import GraphFunctor.FFICategory

import Data.Vect
import Options.Applicative
import Cmdline
import Util

%access public export
%default total

%include c "fficat.h"

data ProcError = FErr FileError | PErr ParseError

Show ProcError where
  show (FErr ferr) = "Filesystem error: " ++ show ferr
  show (PErr (ErrorMsg err)) = "Parse error: " ++ err

processArgs : List String -> Either ParseError CommandLineOpts
processArgs (_ :: opts) = runParserFully parseCmdlineOpts opts
processArgs  _          = Left (ErrorMsg "Not enough arguments")

readInput : String -> (String -> Either ParseError a) -> IO (Either ProcError (List a))
readInput fn parseLine = do Right str <- readFile fn
                             | Left err => pure (Left $ FErr err)
                            pure $ leftMap PErr $ traverse parseLine $ lines str

readFSM : InFSM -> IO (Either ProcError (List (Nat, Nat, Nat)))
readFSM (FSMFile f) = readInput f parseLine
  where
  parseLine : String -> Either ParseError (Nat, Nat, Nat)
  parseLine str = let mv = validateLength (split (== ' ') str) 3 in
                  do v <- maybeToEither (ErrorMsg "malformed FSM file") mv
                     nats <- traverse (leftMap ErrorMsg . parseNat) v
                     pure (index 0 nats, index 1 nats, index 2 nats)

readFFI : InFFI -> IO (Either ProcError (List (Nat, String)))
readFFI (FFIFile f) = readInput f parseLine
  where
  parseLine : String -> Either ParseError (Nat, String)
  parseLine str = let mv = validateLength (split (== ' ') str) 2 in
                  do v <- maybeToEither (ErrorMsg "malformed FFI file") mv
                     nat <- leftMap ErrorMsg $ parseNat $ index 0 v
                     pure (nat, index 1 v)

runWithOptions : CoreOpts -> IO ()
runWithOptions (MkCoreOpts fsmf ffif firings) =
  do disableBuffering  -- don't remove this!
     Right fsm <- readFSM fsmf
       | _ => putStrLn "FSM read error"
     Right ffi <- readFFI ffif
       | _ => putStrLn "FFI read error"
     printLn fsm
     printLn ffi
     printLn firings
     pure $ mapMor ffiFunctor () () exampleExecution ()

partial
main : IO ()
main = do Right options <- processArgs <$> getArgs
            | Left (ErrorMsg msg) => putStrLn msg
          case options of
               Help => putStrLn helpMessage
               HelpFallback => putStrLn fallbackMessage
               Run o => runWithOptions o
