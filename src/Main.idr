module Main

import Basic.Category
import Basic.Functor
import Idris.TypesAsCategory
import GraphFunctor.Graph
import GraphFunctor.FreeFunctor
import GraphFunctor.FFICategory

%access public export
%default total

%include c "fficat.h"

main : IO ()
main = do putStrLn "Running the execution:"  -- don't remove this!
          pure $ mapMor ffiFunctor () () exampleExecution ()
