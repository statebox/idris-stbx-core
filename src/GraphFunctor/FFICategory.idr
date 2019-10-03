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

getOne : () -> Int
getOne = unsafePerformIO . foreign FFI_C "getOne" (() -> IO Int)

printIntAndSucc : Int -> Int
printIntAndSucc = unsafePerformIO . foreign FFI_C "printIntAndSucc" (Int -> IO Int)

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

data U = UNIT | INT

enumerateTypes : Fin 2 -> Type
enumerateTypes FZ = ()
enumerateTypes (FS FZ) = Int

interp : U -> Type
interp UNIT = ()
interp INT = Int

constructMap : List (Nat, String) -> Maybe (SortedMap Nat (a : U ** b : U ** (interp a -> interp b)))
constructMap l = fromList <$> traverse mapping l
  where
  mapping : (Nat, String) -> Maybe (Nat, (a : U ** b : U ** (interp a -> interp b)))
  mapping (n, "getOne")          = Just (n, (UNIT ** INT  ** getOne))
  mapping (n, "printIntAndSucc") = Just (n, (INT  ** INT  ** printIntAndSucc))
-- mapping (n, "printA")          = Just (n, (UNIT ** UNIT ** printA))
-- mapping (n, "printB")          = Just (n, (UNIT ** UNIT ** printB))
-- mapping (n, "printC")          = Just (n, (UNIT ** UNIT ** printC))
-- mapping (n, "printD")          = Just (n, (UNIT ** UNIT ** printD))
-- mapping (n, "printE")          = Just (n, (UNIT ** UNIT ** printE))
-- mapping (n, "printF")          = Just (n, (UNIT ** UNIT ** printF))
-- mapping (n, "printG")          = Just (n, (UNIT ** UNIT ** printG))
-- mapping (n, "printH")          = Just (n, (UNIT ** UNIT ** printH))
  mapping  _                     = Nothing

ffiEdges : (l : List (Nat, Nat)) -> Vect (length l) (Fin (S (findMax2 l)), Fin (S (findMax2 l)))
ffiEdges l = replace {P=\z=>Vect z (Fin (S (findMax2 l)), Fin (S (findMax2 l)))}
                     (sym $ lengthMWE l _)
                     (fromList $ maxOfSelf2 l)

ffiGraph : Vect len (Fin m, Fin m) -> GraphFunctor.Graph.Graph
ffiGraph {len} {m} v = graphFromListGraph $ Free.Graph.MkGraph {n=len} (Fin m) v

ffiCategory : Vect len (Fin m, Fin m) -> Category
ffiCategory = pathCategory . ffiGraph

edgeSpec : Vect 2 (Fin 2, Fin 2)
edgeSpec = [(FZ, FS FZ), (FS FZ, FS FZ)]

ffiFunctor : SortedMap Nat (a : U ** b : U ** (interp a -> interp b)) -> CFunctor (FFICategory.ffiCategory FFICategory.edgeSpec) TypesAsCategory.typesAsCategory
ffiFunctor mp = freeFunctor (ffiGraph edgeSpec) (MkGraphEmbedding enumerateTypes mapEdges)
  where
  mapEdges : (i,j : Fin 2) -> Elem (i,j) FFICategory.edgeSpec -> enumerateTypes i -> enumerateTypes j
  --mapEdges     FZ      FZ  el = let tt = fromMaybe (UNIT ** UNIT ** err) (SortedMap.lookup (elem2Nat el) mp) in ?wat1
  mapEdges     FZ  (FS FZ)  Here              = getOne
  --mapEdges (FS FZ)     FZ  el = ?wat3
  mapEdges (FS FZ) (FS FZ) (There Here)       = printIntAndSucc
  mapEdges     i       j   (There (There el)) = absurd el

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
