module Parser.TGraph

-- base
import Data.Vect

-- idris-ct
--import Graph.Graph
--import Graph.Path

-- typedefs
import Typedefs.Names
import Typedefs.Typedefs

import Util.Elem

%access public export
%default total

-- (FSM spec, nat, path)
-- -- example: ((5, [(1,2),(4,4),(3,2)]),3,[0,2,1])
-- -- -- FSM spec: (5, [(1,2),(4,4),(3,2)])
-- -- -- -- number of vertexes 5
-- -- -- -- edges: [(1,2),(4,4),(3,2)]
-- -- -- Initial state: 3
-- -- -- Morphisms to compose: 0,2,1 (meaning  (1,2), (3,2), (4,4))
-- fsmspec := (Nat * List (Nat, Nat))
-- (fsmspec * Nat * List Nat)
-- Use  (5, [(1,2),(4,4),(3,2)]) to generate a graph
-- Generate the free category C on this graph
-- Consider functor F from C to terminal cat 1
-- Evaluate: F(id_3;0;2;1)
-- Clearly, either this gives you id_1 or it gives you an error => it's an "oracle"

-- For later
--  (FSM spec, functor spec, nat, path) -- "non-oracle case"
-- ((5, [(1,2),(4,4),(3,2)]),[(string, string), (nat, string), (foo, bar)] 3,[0,2,1])

-- Base definitions

-- Defines naturals
TNat : TDef 0
TNat = TMu [("ZZ", T1), ("SS", TVar 0)]

-- Defines Lists of some type
TList : TDef 1
TList = TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

-- Maps TNat to Nat
toNat : Ty [] TNat -> Nat
toNat (Inn (Left ())) = Z
toNat (Inn (Right inn)) = S $ toNat inn

ignoreShift : {t : TDef 0} -> Ty [var] (shiftVars t) -> Ty [] t
ignoreShift {t=T0}                     ty         = absurd ty
ignoreShift {t=T1}                     ()         = ()
ignoreShift {t=TSum [x,y]}             (Left ty)  = Left $ ignoreShift ty
ignoreShift {t=TSum [x,y]}             (Right ty) = Right $ ignoreShift ty
ignoreShift {t=TSum (x::y::z::ts)}     (Left ty)  = Left $ ignoreShift ty
ignoreShift {t=TSum (x::y::z::ts)}     (Right ty) = Right $ ignoreShift {t=TSum (y::z::ts)} ty
ignoreShift {t=TProd [x,y]}            (ty1,ty2)  = (ignoreShift ty1,ignoreShift ty2)
ignoreShift {t=TProd (x::y::z::ts)}    (ty1,ty2)  = (ignoreShift ty1,ignoreShift {t=TProd (y::z::ts)} ty2)
ignoreShift {t=TMu cs}                 (Inn ty)   = Inn ?wat
ignoreShift {t=TApp (TName nam df) xs}  ty        = ?wat2

-- Maps TList to List
toList : Ty [] (TList `ap` [tdef]) -> List (Ty [] tdef)
toList (Inn (Left ())) = Nil
toList (Inn (Right (hd, tl))) = ignoreShift hd :: toList tl

-- Graph definitions

||| The type definition for vertices in the graph
TVertex : TDef 0
TVertex = TNat

||| The type definition for edges in the graph
TEdge : TDef 0
TEdge = TProd [TVertex, TVertex]

||| A Finite State Machine is defined by the number of vertices and a list of edges
||| The definition might not be valid if edges endpoints are out of range
FSMSpec : TDef 0
FSMSpec = TProd [TNat, TList `ap` [TEdge]]

||| A state is a vertex in the graph (might be out of range)
FSMState : TDef 0
FSMState = TVertex

||| A path is a list of edges (might not be valid)
FSMPath : TDef 0
FSMPath = TList `ap` [TEdge]

||| An execution is a FSM, a state representing an inital edge and a path from that edge.
||| The execution might not be valid.
FSMExec : TDef 0
FSMExec = TProd [FSMSpec, FSMState, FSMPath]

||| Errors related to checking if a FSM description is valid
data FSMError = InvalidFSM | InvalidPath | InvalidExec

||| Monad to check errors when compiling FSMs
FSMCheck : Type -> Type
FSMCheck = Either FSMError

checkFSM : Ty [] FSMSpec -> FSMCheck ()
checkFSM (num, edges) =
  let
    n = toNat num
    ls = the (List (Nat, Nat)) $
         map (\(x,y) => (toNat x, toNat y)) $ toList {tdef = TEdge} edges
   in
  if all (\(a,b) => n < a && n < b) ls   -- TODO should this be `<=` ?
    then Right ()
    else Left InvalidFSM
