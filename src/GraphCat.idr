module GraphCat

-- base
import Data.Vect

-- idris-ct
import Basic.Category
import Graph.PathCategory
import Graph.Graph
import Graph.Path

-- typedefs
import Typedefs.Names
import Typedefs.Typedefs

import Parser.TGraph

import Util.Elem

%access public export
%default total

-- 1. Get TDef in: `FSMExec`
-- 2. Verify that is is valid
-- 3. Use it to build a graph : `FSMExec -> FSMSpec` and then `FSMSpec -> Graph`
-- 4. Build the free category out of the graph `Grph -> FreeCat`
-- 5. Build the functor to the terminal cat out of previous point `Cat -> Functor Cat Term`
--   5.1. `State -> Path -> Morphism := Id_State;Path`
--   5.2. `3, [(2,3), (3,4),(4,5)] --> Id2;(2,3);(3.4);(4,5) : Mor 2 5`
-- 6. Evaluate the functor on the given path `FSMExec -> Path -> Functor Cat Term`
-- 7. ???
-- 8. Profit!

-- TODO maybe should be a record

||| The type of categories having Fin n for some n as object type
FinCat : Type
FinCat = (n : Nat ** c : Category ** obj c = Fin n)

||| Maps a FinCat to its underlying category
getCat : FinCat -> Category
getCat (_ ** cat ** _) = cat

||| Builds a path category out of a FSM specification given in TDef format
fsmToPathCat : Ty [] FSMSpec -> Maybe FinCat
fsmToPathCat fsm =
  (\(n ** g) => (n ** pathCategory g ** Refl)) <$> mkTGraph (fromFSMSpecToEdgeList fsm)

decToMaybe : Dec a -> Maybe a
decToMaybe (No _) = Nothing
decToMaybe (Yes a) = Just a

constructPath : (g : Graph (Fin n)) -> (path : List ((Fin n), (Fin n))) -> {auto ok : NonEmpty path} ->
                Maybe (Path g (Basics.fst $ List.head path) (Basics.snd $ List.last path))
constructPath g [(x, y)] = do el <- decToMaybe $ isElem (x,y) (edges g)
                              pure [el]
constructPath g ((x, y) :: xs) = ?wot2

{-
validateExec : Ty [] FSMExec -> Maybe (cat : Category ** a : obj cat ** b : obj cat ** mor cat a b)
validateExec (spec, state, path) =
  do (n ** cat ** prf) <- fsmToPathCat spec
     let edgeList = fromFSMPathToEdgeList path
     (hd, _) <- head' edgeList
     hdF <- natToFin hd n
     (_, lt) <- last' edgeList
     ltF <- natToFin lt n
     -- mor cat = Path
     pure (cat ** rewrite prf in hdF ** rewrite prf in ltF ** ?wat)

-- (spec, a, [(a,b), (b,c)]) -> Compose (id a) (Compose (a b) (b c))
-- id state ; path 1st ; .... ; path nth
-}