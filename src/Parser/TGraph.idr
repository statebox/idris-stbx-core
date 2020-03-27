module Parser.TGraph

-- base
import Data.Vect

-- idris-ct
import Graph.Graph
--import Graph.Path

-- typedefs
import Typedefs.Names
import Typedefs.Typedefs

import Util.Elem

%access public export
%default total

-- Base definitions

-- Defines naturals
TNat : TDefR 2
TNat = RRef 0

-- Defines Lists of some type
-- TList : TDefR 1
-- TList = TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

-- Map TNat to Nat and back
toNat : Ty (Nat :: rest) TNat -> Nat
toNat n = n

fromNat : Nat -> Ty (Nat :: rest) TNat
fromNat n = n

-- TODO add to typdefs?
ignoreShift : {t : TDefR l} -> {rest : Vect l Type} -> Ty (var :: rest) (shiftVars t) -> Ty rest t
ignoreShift {t=T0}                     ty         = absurd ty
ignoreShift {t=T1}                     ()         = ()
ignoreShift {t=TSum [x,y]}             (Left ty)  = Left $ ignoreShift ty
ignoreShift {t=TSum [x,y]}             (Right ty) = Right $ ignoreShift ty
ignoreShift {t=TSum (x::y::z::ts)}     (Left ty)  = Left $ ignoreShift ty
ignoreShift {t=TSum (x::y::z::ts)}     (Right ty) = Right $ ignoreShift {t=TSum (y::z::ts)} ty
ignoreShift {t=TProd [x,y]}            (ty1,ty2)  = (ignoreShift ty1,ignoreShift ty2)
ignoreShift {t=TProd (x::y::z::ts)}    (ty1,ty2)  = (ignoreShift ty1,ignoreShift {t=TProd (y::z::ts)} ty2)
ignoreShift {t=TMu cs}                 (Inn ty)   =
  --TODO finish
  Inn $ really_believe_me ty
ignoreShift {t=TApp (TName nam df) xs}  ty        = really_believe_me ty
ignoreShift {t=TVar x}                  ty        = ty
ignoreShift {t=RRef x}                  ty        = ty

addShift : {t : TDefR l} -> Ty vars t -> Ty (var :: vars) (shiftVars t)
addShift {t=T0}                     ty         = absurd ty
addShift {t=T1}                     ()         = ()
addShift {t=TSum [x,y]}             (Left ty)  = Left $ addShift ty
addShift {t=TSum [x,y]}             (Right ty) = Right $ addShift ty
addShift {t=TSum (x::y::z::ts)}     (Left ty)  = Left $ addShift ty
addShift {t=TSum (x::y::z::ts)}     (Right ty) = Right $ addShift {t=TSum (y::z::ts)} ty
addShift {t=TProd [x,y]}            (ty1,ty2)  = (addShift ty1,addShift ty2)
addShift {t=TProd (x::y::z::ts)}    (ty1,ty2)  = (addShift ty1,addShift {t=TProd (y::z::ts)} ty2)
addShift {t=TMu cs}                 (Inn ty)   =
  --TODO finish
  Inn $ really_believe_me ty
addShift {t=(TApp x xs)} ty = really_believe_me ty
addShift {t=(RRef x)} ty = ty
addShift {t=(TVar i)} ty = ty

-- Map TList to List and back
-- toList : {tdef : TDefR n} -> {x : Vect n Type} -> Ty x (TList `ap` [tdef]) -> List (Ty x tdef)
-- toList ls = ?wat
-- toList (Inn (Left ())) = Nil
-- toList (Inn (Right (hs, tl))) = (assert_total $ ignoreShift hs) :: toList tl

-- fromList : {tdef : TDefR n} -> {x : Vect n Type} -> List (Ty x tdef) -> Ty x (TList `ap` [tdef])
-- fromList ls = ?wot
-- fromList  Nil      = Inn (Left ())
-- fromList (x :: xs) = Inn (Right (addShift x, fromList xs))

-- Graph definitions

||| The type definition for vertices in the graph is jsut
||| A natural enumerating the vertexes. e.g. 5 means
||| That there are 5 vertexes, denoted 0,1,2,3,4
FSMVertex : TDefR 2
FSMVertex = TNat

||| The type definition for edges in the graph is just a couple
||| of vertexes defining the edge source and target
-- FSMEdge : TDefR 2
-- FSMEdge = RRef 1-- TProd [FSMVertex, FSMVertex]

ListPair : TDefR 2
ListPair = RRef 1

||| A Finite State Machine is defined by its vertices and a list of edges
||| The definition might not be valid if edges endpoints are out of range
FSMSpec : TDefR 2
FSMSpec = TProd [FSMVertex, ListPair]

||| A state is a vertex in the graph (might be out of range)
FSMState : TDefR 2
FSMState = FSMVertex

||| A path is a list of edges (might not be valid)
FSMPath : TDefR 2
FSMPath = ListPair -- TList `ap` [FSMEdge]

||| An execution is a FSM, a state representing an inital edge and a path from that edge.
||| The execution might not be valid.
FSMExec : TDefR 2
FSMExec = TProd [FSMSpec, FSMState, FSMPath]

||| Errors related to checking if a FSM description is valid
data FSMError = InvalidFSM | InvalidState | InvalidPath

TFSMErr : TDefR 2
TFSMErr = TMu [("InvalidFSM", T1), ("InvalidState", T1), ("InvalidPath", T1)]

toTDefErr : FSMError -> Ty [List Nat, Nat] TFSMErr
toTDefErr InvalidFSM = Inn (Left ())
toTDefErr InvalidState = Inn (Right  (Left ()))
toTDefErr InvalidPath = Inn (Right (Right ()))

Show FSMError where
  show InvalidFSM   = "Invalid FSM"
  show InvalidState = "Invalid state"
  show InvalidPath  = "Invalid path"

||| Monad to check errors when compiling FSMs
FSMCheck : Type -> Type
FSMCheck = Either FSMError

convertEdgeList : Ty [Nat, List (Nat, Nat)] (RRef 1) -> List (Nat, Nat)
convertEdgeList val =  val

fromFSMSpecToEdgeList : Ty [Nat, List (Nat, Nat)] FSMSpec -> (Nat, List (Nat, Nat))
fromFSMSpecToEdgeList (vertex, edges) = (vertex, convertEdgeList edges)

fromFSMPathToEdgeList : Ty [Nat, List (Nat, Nat)] FSMPath -> List (Nat,Nat)
fromFSMPathToEdgeList  = convertEdgeList

convertList : (n : Nat) -> List (Nat, Nat) -> Maybe (List (Fin n, Fin n))
convertList n edges = traverse (\(x,y) => [| MkPair (natToFin x n) (natToFin y n) |]) edges

-- > record Graph vertices where
-- >   constructor MkGraph
-- >   edges : Vect n (vertices, vertices)

mkTGraph : (Nat, List (Nat, Nat)) -> Maybe (DPair Nat (\size => Graph (Fin size)))
mkTGraph (vertex, edges) = do convertedEdges <- convertList vertex edges
                              pure (vertex ** MkGraph $ fromList convertedEdges)
