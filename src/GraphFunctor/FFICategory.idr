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

extFoo : () -> IO ()
extFoo = foreign FFI_C "foo" (() -> IO ())

%inline
foo : () -> ()
foo x = unsafePerformIO $ extFoo x

extBar : () -> IO ()
extBar = foreign FFI_C "bar" (() -> IO ())

%inline
bar : () -> ()
bar x = unsafePerformIO $ extBar x

data Transition : () -> () -> Type where 
  Foo : Transition () ()
  Bar : Transition () ()

ffiGraph : Graph
ffiGraph = MkGraph () Transition

ffiCategory : Category
ffiCategory = pathCategory ffiGraph

ffiFunctor : CFunctor FFICategory.ffiCategory TypesAsCategory.typesAsCategory
ffiFunctor = freeFunctor ffiGraph (MkGraphEmbedding (const ()) mapEdge)
  where 
  mapEdge : (i : ()) -> (j : ()) -> Transition i j -> () -> ()
  mapEdge () () Foo = foo 
  mapEdge () () Bar = bar

exampleExecution : Path FFICategory.ffiGraph () ()
exampleExecution = [Foo, Bar, Bar]
