module GraphFunctor.FFICategory

import Data.List
import Data.Vect
import Basic.Category
import Basic.Functor
import Idris.TypesAsCategory
import Free.Graph
import Free.FreeFunctor
import GraphFunctor.Graph
import GraphFunctor.FreeFunctor
import Util.Max

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

graphFromListGraph : Free.Graph.Graph -> GraphFunctor.Graph.Graph
graphFromListGraph g = MkGraph (vertices g) (Edge g)

ffiGraph : List (Nat, Nat) -> GraphFunctor.Graph.Graph
ffiGraph l = graphFromListGraph $
             Free.Graph.MkGraph {n=length l}
                                (Fin $ S $ findMax2 l)
                                (replace {P=\z=>Vect z (Fin (S (findMax2 l)), Fin (S (findMax2 l)))}
                                         (sym $ lengthMWE l _)
                                         (fromList $ maxOfSelf2 l))

ffiCategory : List (Nat, Nat) -> Category
ffiCategory = pathCategory . ffiGraph

data Singleton : a -> Type where
  MkSingleton : (v : a) -> Singleton v

ffiFunctor : (l : List (Nat, Nat)) -> CFunctor (FFICategory.ffiCategory l) TypesAsCategory.typesAsCategory
ffiFunctor l = freeFunctor (ffiGraph l) (MkGraphEmbedding (Singleton . finToNat) (\i,j,el,si => MkSingleton $ finToNat j))
