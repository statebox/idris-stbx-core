module Cartographer.Hypergraph

import Data.List

import Permutations.Permutations
import Permutations.PermutationsCategory

%access public export
%default total

-- equivalent to concatMap, but `concatMap a t` is expanded in holes to this ugly thing:
-- Prelude.List.List implementation of Prelude.Foldable.Foldable, method foldr (\x, meth => a x ++ meth) [] t
sumArity : (a : sigma -> List o) -> List sigma -> List o
sumArity _ Nil = []
sumArity a (s :: ss) = a s ++ sumArity a ss

record Hypergraph (sigma : Type) (arityIn : sigma -> List o) (arityOut : sigma -> List o) (k : List o) (m : List o) where
  constructor MkHypergraph
  -- HyperEdges
  Typ : List sigma
  wiring : Perm (k ++ sumArity arityOut Typ) (m ++ sumArity arityIn Typ)

singleton : {s : Type} -> {ai, ao : s -> List o} -> (edge : s) -> Hypergraph s ai ao (ai edge) (ao edge)
singleton edge = MkHypergraph [edge] perm
  where
    perm : Perm (ai edge ++ ao edge ++ []) (ao edge ++ ai edge ++ [])
    perm = rewriteLeft (cong $ appendNilRightNeutral (ao edge)) $
           rewriteRight (cong $ appendNilRightNeutral (ai edge)) $
             swap (ai edge) (ao edge)

identity : {s : Type} -> {ai, ao : s -> List o} -> (n : List o) -> Hypergraph s ai ao n n
identity n = MkHypergraph [] (rewriteRight (appendNilRightNeutral n) (rewriteLeft (appendNilRightNeutral n) (permId n)))

coprod
   : (a : s -> List o) -> (t1 : List s) -> (t2 : List s)
  -> sumArity a t1 ++ sumArity a t2 = sumArity a (t1 ++ t2)
coprod a Nil     _  = Refl
coprod a (s::t1) t2 = sym (appendAssociative _ _ _) `trans` cong (coprod a t1 t2)

coprodNilRightNeutral : (a : s -> List o) -> (t : List s) -> sumArity a t ++ sumArity a [] = sumArity a (t ++ [])
coprodNilRightNeutral {o} a Nil = Refl
coprodNilRightNeutral {o} a (t::ts) = sym (appendAssociative _ _ _) `trans` cong (coprodNilRightNeutral a ts)

compose : (g1 : Hypergraph s ai ao k m) -> (g2 : Hypergraph s ai ao m n) -> Hypergraph s ai ao k n
compose (MkHypergraph t1 c1) (MkHypergraph t2 c2) = MkHypergraph (t1 ++ t2) perm
  where
    helper2 : Perm (m ++ s2) (n ++ f2) -> Perm ((m ++ f1) ++ s2) (n ++ (f2 ++ f1))
    helper2 {s2} {f1} {f2} c2 =
      rewriteLeft (sym $ appendAssociative m f1 s2) $
      rewriteRight (appendAssociative n f2 f1) $
        permComp (permId m `permAdd` swap f1 s2)
        (rewriteLeft (appendAssociative m s2 f1) $
          c2 `permAdd` permId f1)

    helper : Perm (k ++ s1) (m ++ f1) -> Perm (m ++ s2) (n ++ f2) -> s1 ++ s2 = s12 -> f1 ++ f2 = f12 -> Perm (k ++ s12) (n ++ f12)
    helper {s1} {s2} {f1} {f2} c1 c2 sEq fEq =
      rewriteLeft (cong (sym sEq)) $
      rewriteRight (cong (sym fEq)) $
      rewriteLeft (appendAssociative k s1 s2) $
        ((c1 `permAdd` permId s2) `permComp` helper2 c2) `permComp` (permId n `permAdd` swap f2 f1)

    perm : Perm (k ++ sumArity ao (t1 ++ t2)) (n ++ sumArity ai (t1 ++ t2))
    perm = helper c1 c2 (coprod ao t1 t2) (coprod ai t1 t2)

zero : {s : Type} -> {ai, ao : s -> List o} -> Hypergraph s ai ao [] []
zero = identity []

add : Hypergraph s ai ao k l -> Hypergraph s ai ao m n -> Hypergraph s ai ao (k ++ m) (l ++ n)
add {k} {l} {m} {n} (MkHypergraph t1 c1) (MkHypergraph t2 c2) = MkHypergraph (t1 ++ t2) perm
  where
    helper2 : Perm ((a ++ b) ++ (c ++ d)) ((a ++ c) ++ (b ++ d))
    helper2 {a} {b} {c} {d} =
      rewriteLeft (trans (appendAssociative (a ++ b) c d) (cong {f=\l => l ++ d} $ sym $ appendAssociative a b c)) $
      rewriteRight (trans (appendAssociative (a ++ c) b d) (cong {f=\l => l ++ d} $ sym $ appendAssociative a c b)) $
      (permId a `permAdd` swap b c) `permAdd` permId d

    helper : Perm (k ++ s1) (l ++ f1) -> Perm (m ++ s2) (n ++ f2) -> s1 ++ s2 = s12 -> f1 ++ f2 = f12 -> Perm ((k ++ m) ++ s12) ((l ++ n) ++ f12)
    helper {s1} {s2} {f1} {f2} c1 c2 sEq fEq =
      rewriteLeft (cong (sym sEq)) $
      rewriteRight (cong (sym fEq)) $
      helper2 `permComp` ((c1 `permAdd` c2) `permComp` helper2)

    perm : Perm ((k ++ m) ++ sumArity ao (t1 ++ t2)) ((l ++ n) ++ sumArity ai (t1 ++ t2))
    perm = helper c1 c2 (coprod ao t1 t2) (coprod ai t1 t2)
