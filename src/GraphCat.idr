module Parser.Graph

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

fsmToPathCat : Ty [] FSMSpec -> Maybe Category
fsmToPathCat fsm = (\(_ ** g) => pathCategory g) <$> mkTGraph (fromFSMSpecToEdgeList fsm)

(f : FSMExec) -> Mor (fsmToPathCat (spec f)) a b

(spec, state, path)
(spec, v, [(x,y),(y,z)]) --> Mor v z