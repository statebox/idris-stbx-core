module GraphFunctor.FFICategory

import Data.List
import Data.Vect
import Data.SortedMap
import Basic.Category
import Basic.Functor
import Idris.TypesAsCategory
import Free.Graph
import Free.FreeFunctor
import GraphFunctor.Graph
import GraphFunctor.FreeFunctor
import Util.Max
import Util.Elem

%access public export
%default total

-- Define some foreign functions
-- Generate the free category over the
--execUU : String -> () -> ()
--execUU s = unsafePerformIO . foreign FFI_C s (() -> IO ())

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

err : () -> ()
err = unsafePerformIO . foreign FFI_C "err" (() -> IO ())

graphFromListGraph : Free.Graph.Graph -> GraphFunctor.Graph.Graph
graphFromListGraph g = MkGraph (vertices g) (Edge g)

constructMap : List (Nat, String) -> Maybe (SortedMap Nat (() -> ()))
constructMap l = fromList <$> traverse mapping l
  where
  mapping : (Nat, String) -> Maybe ((Nat, () -> ()))
--  mapping (n, s) = Just (n, e)
  mapping (n, "printA") = Just (n, printA)
  mapping (n, "printB") = Just (n, printB)
  mapping (n, "printC") = Just (n, printC)
  mapping (n, "printD") = Just (n, printD)
  mapping (n, "printE") = Just (n, printE)
  mapping (n, "printF") = Just (n, printF)
  mapping (n, "printG") = Just (n, printG)
  mapping (n, "printH") = Just (n, printH)
  mapping  _            = Nothing

ffiEdges : (l : List (Nat, Nat)) -> Vect (length l) (Fin (S (findMax2 l)), Fin (S (findMax2 l)))
ffiEdges l = replace {P=\z=>Vect z (Fin (S (findMax2 l)), Fin (S (findMax2 l)))}
                     (sym $ lengthMWE l _)
                     (fromList $ maxOfSelf2 l)

ffiGraph : Vect len (Fin m, Fin m) -> GraphFunctor.Graph.Graph
ffiGraph {len} {m} v = graphFromListGraph $ Free.Graph.MkGraph {n=len} (Fin m) v

ffiCategory : Vect len (Fin m, Fin m) -> Category
ffiCategory = pathCategory . ffiGraph

ffiFunctor : (v : Vect len (Fin m, Fin m)) -> SortedMap Nat (() -> ()) -> CFunctor (FFICategory.ffiCategory v) TypesAsCategory.typesAsCategory
ffiFunctor v mp = freeFunctor (ffiGraph v) (MkGraphEmbedding (const ()) (\i,j,el => fromMaybe err (SortedMap.lookup (elem2Nat el) mp)))

firingPath : (v : Vect len (Fin m, Fin m)) -> List (Fin len) -> Maybe (s ** t ** Path (FFICategory.ffiGraph v) s t)
firingPath v []      = Nothing
firingPath v [f]     = let ((i,j)**el) = indexElem f v in Just (i ** j ** [el])
firingPath v (f::fs) = firingPath v fs >>= go
  where
  go : (s ** t ** Path (FFICategory.ffiGraph v) s t) -> Maybe (s ** t ** Path (FFICategory.ffiGraph v) s t)
  go (s**t**p) =
    let ((i,j)**el) = indexElem f v in
    case decEq j s of
      Yes eq => Just (i ** t ** el :: (rewrite eq in p))
      No _ => Nothing
