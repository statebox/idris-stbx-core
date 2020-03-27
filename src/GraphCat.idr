module GraphCat

-- base
import Data.Vect
import Data.Fin

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

-- (spec, a, [(a,b), (b,c)]) -> Compose (id a) (Compose (a b) (b c)) = (Compose (a b) (b c))

constructNEPath : (g : Graph (Fin n)) -> (path : List ((Fin n), (Fin n))) -> {auto ok : NonEmpty path} ->
                FSMCheck (Path g (Basics.fst $ List.head path) (Basics.snd $ List.last path))
constructNEPath g [(x, y)] = do el <- decToEither InvalidPath $ isElem (x,y) (edges g)
                                pure [el]
constructNEPath g ((x, y) :: (y',z) :: pt) with (decEq y y')
  constructNEPath g ((x, y) :: (y,z) :: pt) | Yes Refl =
    do el <- decToEither InvalidPath $ isElem (x,y) (edges g)
       path <- assert_total $ constructNEPath g ((y,z)::pt)
       pure $ el :: path
  constructNEPath g ((x, y) :: (y',z) :: pt) | No ctra = Left InvalidPath

validateExec : Ty [Nat, List (Nat, Nat)] FSMExec -> FSMCheck (cat : Category ** a : obj cat ** b : obj cat ** mor cat a b)
validateExec (spec, state, path) =
  do -- convert into a graph with `n` being the number of states
     (n**g) <- maybe (Left InvalidFSM) Right $ mkTGraph $ fromFSMSpecToEdgeList spec
     -- get the inital state as a fin
     st <- maybe (Left InvalidState) Right $ natToFin (state) n
     -- Convert the edge list into fins
     edgeList <- maybe (Left InvalidPath) Right $ convertList n $ fromFSMPathToEdgeList path
     case nonEmpty edgeList of
       -- if the path is not valid we need to check the initial state is the first state of the path
       Yes nel => case decEq (fst $ head edgeList) st of
                    Yes _ => do path' <- constructNEPath g edgeList
                                pure (pathCategory g ** (fst $ head edgeList) ** (snd $ last edgeList) ** path')
                    No _ => Left InvalidPath
       -- empty path is always valid
       No _ => pure (pathCategory g ** st  ** st ** [])

-- Next refactoring : We'll have to pass the entire graph
mkFunctor : (cat : Category) -> CFunctor cat (discreteCategory ())
mkFunctor (MkCategory _ _ _ _ _ _ _) = MkCFunctor
  (\_ => ())
  (\_, _, _ => Refl)
  (\_ => Refl)              -- Refl = Refl
  (\_, _, _, _, _ => Refl)  -- Refl = Refl

lastStep : (cat : Category) -> (a, b : obj cat) -> (m : mor cat a b)
       -> mor (discreteCategory ()) (mapObj (mkFunctor cat) a) (mapObj (mkFunctor cat) b)
lastStep (MkCategory _ _ _ _ _ _ _) a b m = Refl

-- (spec, a, [(a,b), (b,c)]) -> Compose (id a) (Compose (a b) (b c))
-- id state ; path 1st ; .... ; path nth


-- (5, [(1,1),(3,4),(2,1)]) <-- Valid FSM
-- (3,[]) <-- Valid FSM
-- (2, [(1,1),(3,4),(2,1)]) <-- Invalid FSM

IdrisExec : Type
IdrisExec = ((Nat, List (Nat, Nat)), Nat, List (Nat, Nat))

fromIdrisExec : IdrisExec -> Ty [Nat, List (Nat, Nat)] FSMExec
fromIdrisExec ((states, trans), init, path) =
  ( ( states
    ,  trans)
  , init
  , path
  )

-- VALID
-- ((5, [(1,1),(3,4),(2,1)]) , 3, [(3,4)])
valid1 : Ty [Nat, List (Nat, Nat)] FSMExec
valid1 = fromIdrisExec ((5, [(1,1),(3,4),(2,1)]), 3, [(3,4)])

-- ((5, [(1,1),(3,4),(2,1)]) , 2, [(2,1),(1,1),(1,1)])
valid2 : Ty [Nat, List (Nat, Nat)] FSMExec
valid2 = fromIdrisExec ((5, [(1,1),(3,4),(2,1)]) , 2, [(2,1),(1,1),(1,1)])

-- ((3,[]), 1, [])
valid3 : Ty [Nat, List (Nat, Nat)] FSMExec
valid3 = fromIdrisExec ((3,[]), 1, [])

-- INVALID, MALFORMED
-- (2, [(1,1),(3,4),(2,1)])
-- invalid1 : Ty [] FSMExec
-- invalid1 = fromIdrisExec (2, [(1,1),(3,4),(2,1)])
-- ((3,[]), 1, [(2)])
-- invalid2 : Ty [] FSMExec
-- invalid2 = fromIdrisExec ((3,[]), 1, [(2)])

-- INVALID, INVALID FSM SPEC

-- ((5, [(1,1),(5,4),(2,1)]) , 2, [(2,1),(1,1),(1,1)])
invalid1 : Ty [Nat, List (Nat, Nat)] FSMExec
invalid1 = fromIdrisExec  ((5, [(1,1),(5,4),(2,1)]) , 2, [(2,1),(1,1),(1,1)])

-- INVALID STATE, OUT OF RANGE
-- ((5, [(1,1),(3,4),(2,1)]) , 6, [(2,1),(1,1),(1,1)])
invalid2 : Ty [Nat, List (Nat, Nat)] FSMExec
invalid2 = fromIdrisExec ((5, [(1,1),(3,4),(2,1)]) , 6, [(2,1),(1,1),(1,1)])

-- ((3,[Nat, List (Nat, Nat)]), 4, [Nat, List (Nat, Nat)])
invalid3 : Ty [Nat, List (Nat, Nat)] FSMExec
invalid3 = fromIdrisExec ((3,[]), 4, [])

-- INVALID PATH, OUT OF RANGE
-- ((5, [(1,1),(3,4),(2,1)]) , 3, [(2,1),(6,1),(1,1)])
invalid4 : Ty [Nat, List (Nat, Nat)] FSMExec
invalid4 = fromIdrisExec  ((5, [(1,1),(3,4),(2,1)]) , 3, [(2,1),(6,1),(1,1)])

--  INVALID, PATH AND STATE OUT OF RANGE
-- ((3,[Nat, List (Nat, Nat)]), 1, [(1,1)])
invalid5 : Ty [Nat, List (Nat, Nat)] FSMExec
invalid5 = fromIdrisExec  ((3,[]), 1, [(1,1)])

-- PATH NOT MATCHING WITH STATE
-- ((5, [(1,1),(3,4),(2,1)]) , 3, [(2,1),(1,1),(1,1)])
invalid6 : Ty [Nat, List (Nat, Nat)] FSMExec
invalid6 = fromIdrisExec  ((5, [(1,1),(3,4),(2,1)]) , 3, [(2,1),(1,1),(1,1)])
