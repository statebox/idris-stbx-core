module Main

import Basic.Category
import Basic.Functor
import Idris.TypesAsCategory
import GraphFunctor.Graph
import Free.Graph
import GraphFunctor.FreeFunctor
import GraphFunctor.FFICategory

import Data.SortedMap
import Data.Vect
import Options.Applicative
import Cmdline
import Util.Misc
import Util.Max

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

readFSM : InFSM -> IO (Either ProcError (List (Nat, Nat)))
readFSM (FSMFile f) = readInput f parseLine
  where
  parseLine : String -> Either ParseError (Nat, Nat)
  parseLine str = do toks <- maybeToEither (ErrorMsg "malformed FSM file") (validateLength (split (== ' ') str) 2)
                     [v0,v1] <- traverse (maybeToEither (ErrorMsg "not a number") . parseNat) toks
                     pure (v0,v1)

readFFI : InFFI -> IO (Either ProcError (List (Nat, String)))
readFFI (FFIFile f) = readInput f parseLine
  where
  parseLine : String -> Either ParseError (Nat, String)
  parseLine str = do [tok,fun] <- maybeToEither (ErrorMsg "malformed FFI file") (validateLength (split (== ' ') str) 2)
                     e <- maybeToEither (ErrorMsg "not a number") (parseNat tok)
                     pure (e,fun)

runWithOptions : CoreOpts -> IO ()
runWithOptions (MkCoreOpts fsmf ffif firings) =
  do disableBuffering  -- don't remove this!
     Right fsm <- readFSM fsmf
       | _ => putStrLn "FSM read error"
     Right ffi <- readFFI ffif
       | _ => putStrLn "FFI read error"
     case constructMap ffi of
       Just m =>
         let v = ffiEdges fsm in
         case validateContents firings (length fsm) of
           Just vf =>
             case firingPath v vf of
               Just (s**t**p) => pure $ mapMor (ffiFunctor v m) s t p ()
               Nothing => putStrLn "malformed firing sequence: misaligned path"
           Nothing => putStrLn "malformed firing sequence: numbers outside of graph"
       Nothing => putStrLn "unknown FFI function in map"

partial
main : IO ()
main = do Right options <- processArgs <$> getArgs
            | Left (ErrorMsg msg) => putStrLn msg
          case options of
               Help => putStrLn helpMessage
               HelpFallback => putStrLn fallbackMessage
               Run o => runWithOptions o
