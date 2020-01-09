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
arityExtender arity n m (Right Sig) = (0, n)
arityExtender arity n m (Right Tau) = (m, 0)

-- (typ : HyperEdge -> Sigma) -> (k,m : Nat) -> (typ' : Either HyperEdge BoundarySigtype -> Either )

record Hypergraph (sigma : Type) (arity : sigma -> (Nat, Nat)) (k : Nat) (m : Nat) where
  constructor MkHypergraph
  HyperEdge : Type
  Typ : HyperEdge -> sigma
  -- For wiring we don't need pairs, no dangling wires + no loop condition means 
  -- number of inputs is isomorphic to number of outputs.
  wiring : Iso (Either (Fin k) (e: HyperEdge ** Fin (Basics.snd . arity . Typ $ e)))
               (Either (Fin m) (f: HyperEdge ** Fin (Basics.fst . arity . Typ $ f)))

-- mkRight : Iso (Either (Fin k) (e :        he1     ** Fin (snd (a (t1 e)))))                           (Either (Fin m) (f : he1 ** Fin (fst (a (t1 f))))) ->
--           Iso (Either (Fin k) (e : Either he1 he2 ** Fin (snd (a (either (Delay t1) (Delay t2) e))))) b

-- mkLeft : Iso (Either (Fin k) (e :        he2     ** Fin (snd (a (t2 e)))))                           (Either (Fin m) (f : he1 ** Fin (fst (a (t1 f))))) ->
--          Iso b (Either (Fin k) (e : Either he1 he2 ** Fin (snd (a (either (Delay t1) (Delay t2) e)))))



compose : (g1 : Hypergraph s a k m) -> (g2: Hypergraph s a m n) -> Hypergraph s a k n
compose (MkHypergraph he1 t1 w1) (MkHypergraph he2 t2 w2) = MkHypergraph
  -- Either won't work later if we need to prove Eckmann-Hilton
  (Either he1 he2)
  (either t1 t2)
  (MkIso composeTo composeFrom ?wat ?whut)
  where
    composeTo : Either (Fin k) (e : Either he1 he2 ** Fin (snd (a (either (Delay t1) (Delay t2) e)))) ->
                Either (Fin n) (f : Either he1 he2 ** Fin (fst (a (either (Delay t1) (Delay t2) f))))

    composeFrom : Either (Fin n) (f : Either he1 he2 ** Fin (fst (a (either (Delay t1) (Delay t2) f)))) ->
                  Either (Fin k) (e : Either he1 he2 ** Fin (snd (a (either (Delay t1) (Delay t2) e))))

 -- https://hackmd.io/jD2Avh0xSTm1-Yr40bdEBA

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