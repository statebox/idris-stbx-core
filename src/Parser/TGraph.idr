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

||| The type definition for vertices in the graph is jsut
||| A natural enumerating the vertexes. e.g. 5 means
||| That there are 5 vertexes, denoted 0,1,2,3,4
FSMVertex : TDef 0
FSMVertex = TNat

||| The type definition for edges in the graph is just a couple
||| of vertexes defining the edge source and target
FSMEdge : TDef 0
FSMEdge = TProd [FSMVertex, FSMVertex]

||| A Finite State Machine is defined by its vertices and a list of edges
||| The definition might not be valid if edges endpoints are out of range
FSMSpec : TDef 0
FSMSpec = TProd [FSMVertex, TList `ap` [FSMEdge]]

||| A state is a vertex in the graph (might be out of range)
FSMState : TDef 0
FSMState = FSMVertex

||| A path is a list of edges (might not be valid)
FSMPath : TDef 0
FSMPath = TList `ap` [FSMEdge]

||| An execution is a FSM, a state representing an inital edge and a path from that edge.
||| The execution might not be valid.
FSMExec : TDef 0
FSMExec = TProd [FSMSpec, FSMState, FSMPath]

||| Errors related to checking if a FSM description is valid
data FSMError = InvalidFSM | InvalidState | InvalidPath

||| Monad to check errors when compiling FSMs
FSMCheck : Type -> Type
FSMCheck = Either FSMError

||| Functions checking that an execution specification is valid

||| Checks that the edges in a FSM specification aren't
||| out of range wrt the vertexes of the FSM
checkFSMSpec : Ty [] FSMSpec -> FSMCheck ()
checkFSMSpec (num, edges) =
  let
    n = toNat num
    ls = the (List (Nat, Nat)) $
         map (\(x,y) => (toNat x, toNat y)) $ toList {tdef = FSMEdge} edges
   in
  if all (\(a,b) => n < a && n < b) ls   -- TODO should this be `<=` ?
    then Right ()
    else Left InvalidFSM

--------------------------------
--- HIC SUNT LEONES---
--------------------------------

||| Checks that the FSM state in the execution is a valid vertex of the graph
checkFSMState : Ty [] FSMSpec -> FSMState ->FSMCheck ()
checkFSM (num, edges) state =
  let
    n = toNat num
    s = toNat state
   in
  if s < n
    then Left InvalidState
    else Right()

||| Checks that a path in an execution is made of valid edges
checkFSMPath : Ty [] FSMSpec -> FSMPath ->FSMCheck ()
-- alternatively we could use: checkFSMPath (num, edges) path =checkFSMSpec(num, path)
checkFSMPath (num, edges) path =
  let
    n = toNat num
    ls = the (List (Nat, Nat)) $
         map (\(x,y) => (toNat x, toNat y)) $ toList {tdef = FSMEdge} path
   in
  if all (\(a,b) => n < a && n < b) ls   -- TODO should this be `<=` ?
    then Right ()
    else Left InvalidPath

||| Checks the execution putting the previous functions together
checkFSMExec : Ty [] FSMExec -> FSMCheck ()
checkFSMExec (spec, state, path) =
  checkFSMSpec(spec)
  checkFSMState(state)
  checkFSMPath(path)