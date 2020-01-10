module Cartographer.Hypergraph

-- import Data.SortedMap
-- import Data.SortedSet
import Data.Fin
import Control.Isomorphism

%access public export
%default total

data BoundarySigType = Sig | Tau

data Boundary = LeftB | RightB

-- arityExtender : {Sigma : Type} -> (arity : Sigma -> (Nat, Nat)) -> (n,m: Nat) -> Either Sigma BoundarySigType -> (Nat, Nat)
-- arityExtender arity n m (Left sigma) = arity sigma
-- arityExtender arity n m (Right Sig) = (0, n)
-- arityExtender arity n m (Right Tau) = (m, 0)

-- (typ : HyperEdge -> Sigma) -> (k,m : Nat) -> (typ' : Either HyperEdge BoundarySigtype -> Either )

record Hypergraph (sigma : Type) (arity : sigma -> (Nat, Nat)) (k : Nat) (m : Nat) where
  constructor MkHypergraph
  -- HyperEdge count
  h : Nat
  Typ : Fin h -> sigma
  -- For wiring we don't need pairs, no dangling wires + no loop condition means
  -- number of inputs is isomorphic to number of outputs.
  wiring : Iso (Either (Fin k) (e: Fin h ** Fin (Basics.snd . arity . Typ $ e)))
               (Either (Fin m) (f: Fin h ** Fin (Basics.fst . arity . Typ $ f)))


singleton : {s : Type} -> {a : s -> (Nat, Nat)} -> (edge : s) -> Hypergraph s a (fst (a edge)) (snd (a edge))
singleton edge = MkHypergraph 1 (const edge) (MkIso
  (either (\i => Right (FZ ** i)) (Left . snd))
  (either (\i => Right (FZ ** i)) (Left . snd))
  ?toFromSing ?fromToSing)

identity : {s : Type} -> {a : s -> (Nat, Nat)} -> (n : Nat) -> Hypergraph s a n n
identity n = MkHypergraph 0 FinZElim (MkIso
  (map (FinZElim . fst))
  (map (FinZElim . fst))
  ?toFromId ?fromToId)

-- mkRight : Iso (Either (Fin k) (e :        he1     ** Fin (snd (a (t1 e)))))                           (Either (Fin m) (f : he1 ** Fin (fst (a (t1 f))))) ->
--           Iso (Either (Fin k) (e : Either he1 he2 ** Fin (snd (a (either (Delay t1) (Delay t2) e))))) b

-- mkLeft : Iso (Either (Fin k) (e :        he2     ** Fin (snd (a (t2 e)))))                           (Either (Fin m) (f : he1 ** Fin (fst (a (t1 f))))) ->
--          Iso b (Either (Fin k) (e : Either he1 he2 ** Fin (snd (a (either (Delay t1) (Delay t2) e)))))


coprodFin : {m : Nat} -> {n : Nat} -> {a : Type} -> (Fin m -> a) -> (Fin n -> a) -> Fin (m + n) -> a

compose : (g1 : Hypergraph s a k m) -> (g2: Hypergraph s a m n) -> Hypergraph s a k n
compose (MkHypergraph h1 t1 w1) (MkHypergraph h2 t2 w2) = MkHypergraph
  -- Either won't work later if we need to prove Eckmann-Hilton
  (h1 + h2)
  (coprodFin t1 t2)
  (MkIso composeTo composeFrom ?wat ?whut)
  where
    composeTo : Either (Fin k) (e : Fin (h1 + h2) ** Fin (snd (a (coprodFin t1 t2 e)))) ->
                Either (Fin n) (f : Fin (h1 + h2) ** Fin (fst (a (coprodFin t1 t2 f))))

    composeFrom : Either (Fin n) (f : Fin (h1 + h2) ** Fin (fst (a (coprodFin t1 t2 f)))) ->
                  Either (Fin k) (e : Fin (h1 + h2) ** Fin (snd (a (coprodFin t1 t2 e))))

 -- https://hackmd.io/jD2Avh0xSTm1-Yr40bdEBA

zero : {s : Type} -> {a : s -> (Nat, Nat)} -> Hypergraph s a 0 0
zero = identity 0

add : Hypergraph s a k l -> Hypergraph s a m n -> Hypergraph s a (k + m) (l + n)
add (MkHypergraph h1 t1 w1) (MkHypergraph h2 t2 w2) = MkHypergraph
  (h1 + h2)
  (coprodFin t1 t2)
  ?wut -- (MkIso addTo addFrom ?toFromAdd ?fromToAdd)
  where
    addTo : Either (Fin (k + m)) (e : Fin (h1 + h2) ** Fin (snd (a (coprodFin t1 t2 e)))) ->
            Either (Fin (l + n)) (f : Fin (h1 + h2) ** Fin (fst (a (coprodFin t1 t2 f))))

    addFrom : Either (Fin (l + n)) (f : Fin (h1 + h2) ** Fin (fst (a (coprodFin t1 t2 f)))) ->
              Either (Fin (k + m)) (e : Fin (h1 + h2) ** Fin (snd (a (coprodFin t1 t2 e))))

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
