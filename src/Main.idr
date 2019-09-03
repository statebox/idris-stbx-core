module Main

import Basic.Category
import Basic.Functor
import Idris.TypesAsCategory
import GraphFunctor.Graph
import GraphFunctor.FreeFunctor
import GraphFunctor.FFICategory

import Options.Applicative
import Cmdline

%access public export
%default total

%include c "fficat.h"

processArgs : List String -> Either ParseError CommandLineOpts
processArgs (_ :: opts) = runParserFully parseCmdlineOpts opts
processArgs  _          = Left (ErrorMsg "Not enough arguments")

runWithOptions : CoreOpts -> IO ()
runWithOptions (MkCoreOpts fsm ffi firings) =
  do disableBuffering  -- don't remove this!
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
