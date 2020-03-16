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
TNat : TDef 0
TNat = TMu [("ZZ", T1), ("SS", TVar 0)]

-- Defines Lists of some type
TList : TDef 1
TList = TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

-- Map TNat to Nat and back
toNat : Ty [] TNat -> Nat
toNat (Inn (Left ()))   = Z
toNat (Inn (Right inn)) = S $ toNat inn

fromNat : Nat -> Ty [] TNat
fromNat  Z    = Inn (Left ())
fromNat (S n) = Inn (Right $ fromNat n)

-- TODO add to typdefs?
ignoreShift : {t : TDef 0} -> Ty [var] (shiftVars t) -> Ty [] t
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

addShift : {t : TDef 0} -> Ty [] t -> Ty [var] (shiftVars t)
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
addShift {t=TApp (TName nam df) xs}  ty        = really_believe_me ty

-- Map TList to List and back
toList : Ty [] (TList `ap` [tdef]) -> List (Ty [] tdef)
toList (Inn (Left ()))        = Nil
toList (Inn (Right (hd, tl))) = ignoreShift hd :: toList tl

fromList : List (Ty [] tdef) -> Ty [] (TList `ap` [tdef])
fromList  Nil      = Inn (Left ())
fromList (x :: xs) = Inn (Right (addShift x, fromList xs))

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

Show FSMError where
  show InvalidFSM   = "Invalid FSM"
  show InvalidState = "Invalid state"
  show InvalidPath  = "Invalid path"

||| Monad to check errors when compiling FSMs
FSMCheck : Type -> Type
FSMCheck = Either FSMError

convertEdgeList : Ty [] (TList `ap` [FSMEdge]) -> List (Nat, Nat)
convertEdgeList = map (\(n1, n2) => (toNat n1, toNat n2)) . toList {tdef = FSMEdge}

fromFSMSpecToEdgeList : Ty [] FSMSpec -> (Nat, List (Nat, Nat))
fromFSMSpecToEdgeList (vertex, edges) = (toNat vertex, convertEdgeList edges)

fromFSMPathToEdgeList : Ty [] FSMPath -> List (Nat,Nat)
fromFSMPathToEdgeList  = convertEdgeList

convertList : (n : Nat) -> List (Nat, Nat) -> Maybe (List (Fin n, Fin n))
convertList n edges = traverse (\(x,y) => [| MkPair (natToFin x n) (natToFin y n) |]) edges

--> record Graph vertices where
-->   constructor MkGraph
-->   edges : Vect n (vertices, vertices)

mkTGraph : (Nat, List (Nat, Nat)) -> Maybe (DPair Nat (\size => Graph (Fin size)))
mkTGraph (vertex, edges) = do convertedEdges <- convertList vertex edges
                              pure (vertex ** MkGraph $ fromList convertedEdges)
