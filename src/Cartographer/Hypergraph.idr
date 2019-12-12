module Cartographer.Hypergraph

import Data.SortedMap
import Data.SortedSet
import Data.Fin
import Control.Isomorphism

%access public export
%default total

data BoundarySigType = Sig | Tau

data Boundary = LeftB | RightB

arityExtender : {Sigma : Type} -> (arity : Sigma -> (Nat, Nat)) -> (n,m: Nat) -> Either Sigma BoundarySigType -> (Nat, Nat)
arityExtender arity n m (Left sigma) = arity sigma
arityExtender arity n m (Right Sig) = (n, 0)
arityExtender arity n m (Right Tau) = (0, m)

-- (typ : HyperEdge -> Sigma) -> (k,m : Nat) -> (typ' : Either HyperEdge BoundarySigtype -> Either )
HyperEdge : Type
HyperEdge = Nat

record Hypergraph (sigma : Type) (arity : sigma -> (Nat, Nat)) (k : Nat) (m : Nat) where
  constructor MkHypergraph
  Typ : HyperEdge -> sigma
  wiring : SortedSet ( (e : Maybe HyperEdge ** Fin (Basics.fst $ arityExtender arity k m $ maybe (Right Sig) (Left . Typ) e)) 
                     , (f : Maybe HyperEdge ** Fin (Basics.snd $ arityExtender arity k m $ maybe (Right Tau) (Left . Typ) f)) 
                     )

  -- for each e hyperedge,  (e,i) i-th port of e, where i ranges between 0 and pi1 arity (typ e)
  -- (e_i, f^j)  e_i := (e,i)  f^j := (f,j) j-th port of f where j ranges between 0 and pi2 arity (typ e)
  -- 


{-
data PortRole = Source | Target

HyperEdgeId : Type
HyperEdgeId = Nat

data Port : (a : PortRole) -> (f : Type -> Type) -> Type where 
  MkPort : f HyperEdgeId -> Int -> Port a f

record Hypergraph (sig : Type) (f : Type -> Type) where
  constructor MkHypergraph
  connections     : List (Port Source f, Port Target f)
  signatures      : SortedMap HyperEdgeId sig
  nextHyperEdgeId : HyperEdgeId


data Open a = Gen a | Boundary

OpenHypergraph sig = Hypergraph sig Open
-}