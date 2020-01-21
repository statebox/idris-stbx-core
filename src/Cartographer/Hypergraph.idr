module Cartographer.Hypergraph

import Data.Fin

%access public export
%default total


--== Perm ==--

data Perm : {o : Type} -> List o -> List o -> Type where
  Nil : Perm [] []
  Ins : Perm as (l ++ r) -> Perm (a :: as) (l ++ [a] ++ r)

permId : (as : List o) -> Perm as as
permId [] = Nil
permId (a::as) = Ins {l=[]} (permId as)

place : Perm (l ++ [a] ++ r) cs -> (l' ** r' ** cs = l' ++ [a] ++ r')
place {l=[]} (Ins {l=l'} {r=r'} _) = (l' ** r' ** Refl)
place {l=x::xs} (Ins cs') = case place cs' of (l' ** r' ** prf) => ?p

deleted : Perm {o} (l ++ [a] ++ r) cs -> List o
deleted p = case place p of (l' ** r' ** _) => l' ++ r'

delete : (p : Perm (l ++ [a] ++ r) cs) -> Perm (l ++ r) (deleted p)

permComp : {o : Type} -> Perm {o} as bs -> Perm bs cs -> Perm as cs
permComp Nil p = p
permComp (Ins {l} {a} {r} ab') bc =
  case place bc of
    (l' ** r' ** prf) => rewrite prf in
      Ins {l=l'} {r=r'} $
        permComp ab' (delete {l} {a} {r} bc)

permAdd : Perm as bs -> Perm cs ds -> Perm (as ++ cs) (bs ++ ds)
permAdd Nil p = p
permAdd {ds} (Ins {l} {r} {a} ab) cd =
  rewrite sym (appendAssociative l (a :: r) ds) in
    Ins {l=l} {r=r++ds} (rewrite appendAssociative l r ds in permAdd ab cd)

swap : (l : List o) -> (r : List o) -> Perm (l ++ r) (r ++ l)
swap [] r = rewrite appendNilRightNeutral r in permId r
swap (a::as) r = Ins (swap as r)

permEqLength : Perm as bs -> length as = length bs
permEqLength Nil = Refl
permEqLength (Ins {l} {r} as) = cong {f=S} (permEqLength as) `trans` h l r
  where
    h : (l, r : List o) -> S (length (l ++ r)) = length (l ++ [a] ++ r)
    h [] r = Refl
    h (l::ls) r = cong {f=S} (h ls r)

--== Hypergraph ==--

sumArity : {h : Nat} -> (f : Fin h -> List o) -> List o
sumArity {h=Z} _ = []
sumArity {h=S n} f = f FZ ++ sumArity {h=n} (f . FS)

record Hypergraph (sigma : Type) (arityIn : sigma -> List o) (arityOut : sigma -> List o) (k : List o) (m : List o) where
  constructor MkHypergraph
  -- HyperEdge count
  h : Nat
  Typ : Fin h -> sigma
  wiring : Perm (k ++ sumArity (arityOut . Typ)) (m ++ sumArity (arityIn . Typ))

singleton : {s : Type} -> {ai, ao : s -> List o} -> (edge : s) -> Hypergraph s ai ao (ai edge) (ao edge)
singleton edge = MkHypergraph 1 (const edge) perm
  where
    perm : Perm (ai edge ++ ao edge ++ []) (ao edge ++ ai edge ++ [])
    perm = rewrite appendNilRightNeutral (ao edge) in
           rewrite appendNilRightNeutral (ai edge) in
             swap (ai edge) (ao edge)

identity : {s : Type} -> {ai, ao : s -> List o} -> (n : List o) -> Hypergraph s ai ao n n
identity n = MkHypergraph 0 FinZElim (rewrite appendNilRightNeutral n in permId n)

coprodFin : {m : Nat} -> {n : Nat} -> (Fin m -> a) -> (Fin n -> a) -> Fin (m + n) -> a
coprodFin {m = Z} _ r i = r i
coprodFin {m = S m'} l r FZ = l FZ
coprodFin {m = S m'} l r (FS i) = coprodFin {m = m'} (l . FS) r i

coprod
   : {s : Type} -> {a : s -> List o} -> {h1 : Nat} -> {h2 : Nat} -> {t1 : Fin h1 -> s} -> {t2 : Fin h2 -> s}
  -> sumArity (a . t1) ++ sumArity (a . t2) = sumArity (a . coprodFin t1 t2)
coprod {h1=Z} {a} {t2} = Refl
coprod {h1=S h} {t1} = sym (appendAssociative _ _ _) `trans` cong (coprod {h1=h} {t1=t1 . FS})

compose : (g1 : Hypergraph s ai ao k m) -> (g2 : Hypergraph s ai ao m n) -> Hypergraph s ai ao k n
compose (MkHypergraph h1 t1 c1) (MkHypergraph h2 t2 c2) = MkHypergraph
  (h1 + h2)
  (coprodFin t1 t2)
  perm
  where
    helper2 : Perm (m ++ s2) (n ++ f2) -> Perm ((m ++ f1) ++ s2) (n ++ (f2 ++ f1))
    helper2 {s2} {f1} {f2} c2 =
      rewrite sym $ appendAssociative m f1 s2 in
      rewrite appendAssociative n f2 f1 in
        permComp (permId m `permAdd` swap f1 s2)
        (rewrite appendAssociative m s2 f1 in
          c2 `permAdd` permId f1)

    helper : Perm (k ++ s1) (m ++ f1) -> Perm (m ++ s2) (n ++ f2) -> s1 ++ s2 = s12 -> f1 ++ f2 = f12 -> Perm (k ++ s12) (n ++ f12)
    helper {s1} {s2} {f1} {f2} c1 c2 cps cpf =
      rewrite sym cps in
      rewrite sym cpf in
      rewrite appendAssociative k s1 s2 in
        (c1 `permAdd` permId s2) `permComp` helper2 c2 `permComp` (permId n `permAdd` swap f2 f1)

    perm : Perm (k ++ sumArity (ao . coprodFin t1 t2)) (n ++ sumArity (ai . coprodFin t1 t2))
    perm = helper c1 c2 coprod coprod

zero : {s : Type} -> {ai, ao : s -> List o} -> Hypergraph s ai ao [] []
zero = identity []

add : Hypergraph s ai ao k l -> Hypergraph s ai ao m n -> Hypergraph s ai ao (k ++ m) (l ++ n)
add {k} {l} {m} {n} (MkHypergraph h1 t1 c1) (MkHypergraph h2 t2 c2) = MkHypergraph
  (h1 + h2)
  (coprodFin t1 t2)
  perm
  where
    helper2 : Perm ((a ++ b) ++ (c ++ d)) ((a ++ c) ++ (b ++ d))
    helper2 {a} {b} {c} {d} =
      rewrite appendAssociative (a ++ b) c d in
      rewrite appendAssociative (a ++ c) b d in
      rewrite sym $ appendAssociative a b c in
      rewrite sym $ appendAssociative a c b in
      (permId a `permAdd` swap b c) `permAdd` permId d

    helper : Perm (k ++ s1) (l ++ f1) -> Perm (m ++ s2) (n ++ f2) -> s1 ++ s2 = s12 -> f1 ++ f2 = f12 -> Perm ((k ++ m) ++ s12) ((l ++ n) ++ f12)
    helper {s1} {s2} {f1} {f2} c1 c2 cps cpf =
      rewrite sym cps in
      rewrite sym cpf in
        helper2 `permComp` ((c1 `permAdd` c2) `permComp` helper2)

    perm : Perm ((k ++ m) ++ sumArity (ao . coprodFin t1 t2)) ((l ++ n) ++ sumArity (ai . coprodFin t1 t2))
    perm = helper c1 c2 coprod coprod
