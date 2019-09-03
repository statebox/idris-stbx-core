module GraphFunctor.FFICategory

import Data.Vect
import Basic.Category
import Basic.Functor
import Idris.TypesAsCategory
import GraphFunctor.Graph
import GraphFunctor.FreeFunctor

%access public export
%default total

-- Define some foreign functions
-- Generate the free category over the

printA : () -> ()
printA = unsafePerformIO . foreign FFI_C "printA" (() -> IO ())

printB : () -> ()
printB = unsafePerformIO . foreign FFI_C "printB" (() -> IO ())

printC : () -> ()
printC = unsafePerformIO . foreign FFI_C "printC" (() -> IO ())

printD : () -> ()
printD = unsafePerformIO . foreign FFI_C "printD" (() -> IO ())

printE : () -> ()
printE = unsafePerformIO . foreign FFI_C "printE" (() -> IO ())

printF : () -> ()
printF = unsafePerformIO . foreign FFI_C "printF" (() -> IO ())

printG : () -> ()
printG = unsafePerformIO . foreign FFI_C "printG" (() -> IO ())

printH : () -> ()
printH = unsafePerformIO . foreign FFI_C "printH" (() -> IO ())

data Transition : () -> () -> Type where
  PrintA : Transition () ()
  PrintB : Transition () ()
  PrintC : Transition () ()
  PrintD : Transition () ()
  PrintE : Transition () ()
  PrintF : Transition () ()
  PrintG : Transition () ()
  PrintH : Transition () ()

ffiGraph : Graph
ffiGraph = MkGraph () Transition

ffiCategory : Category
ffiCategory = pathCategory ffiGraph

ffiFunctor : CFunctor FFICategory.ffiCategory TypesAsCategory.typesAsCategory
ffiFunctor = freeFunctor ffiGraph (MkGraphEmbedding (const ()) mapEdge)
  where
  mapEdge : (i : ()) -> (j : ()) -> Transition i j -> () -> ()
  mapEdge () () PrintA = printA
  mapEdge () () PrintB = printB
  mapEdge () () PrintC = printC
  mapEdge () () PrintD = printD
  mapEdge () () PrintE = printE
  mapEdge () () PrintF = printF
  mapEdge () () PrintG = printG
  mapEdge () () PrintH = printH

exampleExecution : Path FFICategory.ffiGraph () ()
exampleExecution = [PrintB, PrintA, PrintD]
