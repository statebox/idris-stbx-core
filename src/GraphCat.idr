module GraphCat

-- base
import Data.Vect

-- idris-ct
import Basic.Category
import Basic.Functor
import Discrete.DiscreteCategory
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
--> 6. Evaluate the functor on the given path `FSMExec -> Path -> Functor Cat Term`
-- 7. ???
-- 8. Profit!

-- TODO maybe should be a record

||| The type of categories having Fin n for some n as object type
--FinCat : Type
--FinCat = (n : Nat ** c : Category ** obj c = Fin n)

||| Maps a FinCat to its underlying category
--getCat : FinCat -> Category
--getCat (_ ** cat ** _) = cat

||| Builds a path category out of a FSM specification given in TDef format
--fsmToPathCat : Ty [] FSMSpec -> Maybe FinCat
--fsmToPathCat fsm =
--  (\(n ** g) => (n ** pathCategory g ** Refl)) <$> mkTGraph (fromFSMSpecToEdgeList fsm)

decToEither : e -> Dec a -> Either e a
decToEither e (No _) = Left e
decToEither _ (Yes a) = Right a

-- Idea for refactoring. Instead of path : List ((Fin n), (Fin n)) you can have a list of
-- Mor a b, where a b depend on the index in the list.
-- This requires an helper function to lift (a, b) to Mor a b.

constructPath : (g : Graph (Fin n)) -> (path : List ((Fin n), (Fin n))) -> {auto ok : NonEmpty path} ->
                FSMCheck (Path g (Basics.fst $ List.head path) (Basics.snd $ List.last path))
constructPath g [(x, y)] = do el <- decToEither InvalidPath $ isElem (x,y) (edges g)
                              pure [el]
constructPath g ((x, y) :: (y',z) :: pt) with (decEq y y')
  constructPath g ((x, y) :: (y,z) :: pt) | Yes Refl =
    do el <- decToEither InvalidPath $ isElem (x,y) (edges g)
       path <- assert_total $ constructPath g ((y,z)::pt)
       pure $ el :: path
  constructPath g ((x, y) :: (y',z) :: pt) | No ctra = Left InvalidPath

validateExec : Ty [] FSMExec -> Maybe (cat : Category ** a : obj cat ** b : obj cat ** mor cat a b)
validateExec (spec, state, path) =
  do (n**g) <- mkTGraph $ fromFSMSpecToEdgeList spec
     edgeList <- traverse {b=(Fin n, Fin n)} (\(x,y) => [| MkPair (natToFin x n) (natToFin y n) |]) $
                                             fromFSMPathToEdgeList path
     case nonEmpty edgeList of
       Yes nel => do path' <- eitherToMaybe $ constructPath g edgeList
                     pure (pathCategory g ** (fst $ head edgeList) ** (snd $ last edgeList) ** path')
       No _ => Nothing

-- Next refactoring : We'll have to pass the entire graph
mkFunctor : (cat : Category) -> CFunctor cat (discreteCategory ())
mkFunctor (MkCategory o m c a _ _ _) = MkCFunctor
  (\_ => ())
  (\_, _, _ => Refl)
  (\_ => Refl)              -- Refl = Refl
  (\_, _, _, _, _ => Refl)  -- Refl = Refl

-- (spec, a, [(a,b), (b,c)]) -> Compose (id a) (Compose (a b) (b c))
-- id state ; path 1st ; .... ; path nth
