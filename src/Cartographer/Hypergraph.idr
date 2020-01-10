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


coprodFin : {m : Nat} -> {n : Nat} -> (Fin m -> a) -> (Fin n -> a) -> Fin (m + n) -> a
coprodFin {m = Z} _ r i = r i
coprodFin {m = S m'} l r FZ = l FZ
coprodFin {m = S m'} l r (FS i) = coprodFin {m = m'} (l . FS) r i
injLFin : (m : Nat) -> (n : Nat) -> Fin m -> Fin (m + n)
injLFin _ n = weakenN n
injRFin : (m : Nat) -> (n : Nat) -> Fin n -> Fin (m + n)
injRFin m _ = shift m
proofL : {m : Nat} -> {n : Nat} -> (l : Fin m -> a) -> (r : Fin n -> a) -> (i : Fin m) -> coprodFin l r (injLFin m n i) = l i
proofL {m = Z} _ _ i = FinZElim i
proofL {m = S m'} _ _ FZ = Refl
proofL {m = S m'} l r (FS i) = proofL {m = m'} (l . FS) r i
proofR : {m : Nat} -> {n : Nat} -> (l : Fin m -> a) -> (r : Fin n -> a) -> (i : Fin n) -> coprodFin l r (injRFin m n i) = r i
proofR {m = Z} _ _ _ = Refl
proofR {m = S m'} l r i = proofR {m = m'} (l . FS) r i

compose : (g1 : Hypergraph s a k m) -> (g2: Hypergraph s a m n) -> Hypergraph s a k n
compose (MkHypergraph h1 t1 w1) (MkHypergraph h2 t2 w2) = MkHypergraph
  -- Either won't work later if we need to prove Eckmann-Hilton
  (h1 + h2)
  (coprodFin t1 t2)
  (MkIso composeTo composeFrom ?wat ?whut)
  where
    injL : (e: Fin h1 ** Fin (fst (a (t1 e)))) -> (e: Fin (h1 + h2) ** Fin (fst (a (coprodFin t1 t2 e))))
    injL (e ** i) = (injLFin h1 h2 e ** rewrite proofL t1 t2 e in i)
    injR : (e: Fin h2 ** Fin (fst (a (t2 e)))) -> (e: Fin (h1 + h2) ** Fin (fst (a (coprodFin t1 t2 e))))
    injR (e ** i) = (injRFin h1 h2 e ** rewrite proofR t1 t2 e in i)
    coprod
      : (((e: Fin h1 ** Fin (snd (a (t1 e))))) -> r)
     -> (((f: Fin h2 ** Fin (snd (a (t2 f))))) -> r)
     -> (e: Fin (h1 + h2) ** Fin (snd (a (coprodFin t1 t2 e)))) -> r
    coprod l r (e ** o) = coprodFin (\h1 => l (h1 ** ?ol)) (\h2 => r (h2 ** ?or)) e

    composeTo : Either (Fin k) (e : Fin (h1 + h2) ** Fin (snd (a (coprodFin t1 t2 e)))) ->
                Either (Fin n) (f : Fin (h1 + h2) ** Fin (fst (a (coprodFin t1 t2 f))))
    composeTo = either (z . to w1 . Left) (coprod (z . to w1 . Right) (map injR . to w2 . Right))
      where
        z = either (map injR . to w2 . Left) (Right . injL)

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
