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
sumArity a (s :: ss) = sumArity a ss ++ a s

record Hypergraph (sigma : Type) (arityIn : sigma -> List o) (arityOut : sigma -> List o) (k : List o) (m : List o) where
  constructor MkHypergraph
  -- HyperEdges
  Typ : List sigma
  wiring : Perm (sumArity arityOut Typ ++ k) (sumArity arityIn Typ ++ m)

singleton : {s : Type} -> {ai, ao : s -> List o} -> (edge : s) -> Hypergraph s ai ao (ai edge) (ao edge)
singleton edge = MkHypergraph [edge] (swap (ao edge) (ai edge))


identity : {s : Type} -> {ai, ao : s -> List o} -> (n : List o) -> Hypergraph s ai ao n n
identity n = MkHypergraph [] (permId n)

coprod
   : (a : s -> List o) -> (t1 : List s) -> (t2 : List s)
  -> sumArity a t2 ++ sumArity a t1 = sumArity a (t1 ++ t2)
coprod a Nil     _  = appendNilRightNeutral _
coprod a (s::t1) t2 = appendAssociative _ _ _ `trans` cong {f=\z=>z++a s} (coprod a t1 t2)

compose : (g1 : Hypergraph s ai ao k m) -> (g2 : Hypergraph s ai ao m n) -> Hypergraph s ai ao k n
compose (MkHypergraph t1 c1) (MkHypergraph t2 c2) = MkHypergraph (t1 ++ t2) perm
  where
    helper : Perm (s1 ++ k) (f1 ++ m) -> Perm (s2 ++ m) (f2 ++ n) -> s2 ++ s1 = s12 -> f2 ++ f1 = f12 -> Perm (s12 ++ k) (f12 ++ n)
    helper {s1} {s2} {f1} {f2} c1 c2 sEq fEq =
      rewriteLeft (cong {f=\z=>z++k} (sym sEq) `trans` sym (appendAssociative s2 s1 k)) $
      rewriteRight (cong {f=\z=>z++n} (sym fEq) `trans` sym (appendAssociative f2 f1 n)) $
        permComp (permComp (s2 `permAddIdL` c1) (swapAddIdR s2 f1 m))
                 (permComp (f1 `permAddIdL` c2) (swapAddIdR f1 f2 n))

    perm : Perm (sumArity ao (t1 ++ t2) ++ k) (sumArity ai (t1 ++ t2) ++ n)
    perm = helper c1 c2 (coprod ao t1 t2) (coprod ai t1 t2)

zero : {s : Type} -> {ai, ao : s -> List o} -> Hypergraph s ai ao [] []
zero = identity []

add : Hypergraph s ai ao k l -> Hypergraph s ai ao m n -> Hypergraph s ai ao (k ++ m) (l ++ n)
add {k} {l} {m} {n} (MkHypergraph t1 c1) (MkHypergraph t2 c2) = MkHypergraph (t1 ++ t2) perm
  where
    helper2 : Perm ((a ++ b) ++ (c ++ d)) ((a ++ c) ++ (b ++ d))
    helper2 {a} {b} {c} {d} =
      rewriteLeft (sym $ appendAssociative a b (c ++ d)) $
      rewriteRight (sym $ appendAssociative a c (b ++ d)) $
        a `permAddIdL` swapAddIdR b c d

    helper : Perm (s1 ++ k) (f1 ++ l) -> Perm (s2 ++ m) (f2 ++ n) -> s2 ++ s1 = s12 -> f2 ++ f1 = f12 -> Perm (s12 ++ (k ++ m)) (f12 ++ (l ++ n))
    helper {s1} {s2} {f1} {f2} c1 c2 sEq fEq =
      rewriteLeft (cong {f=\z=>z++(k++m)} (sym sEq)) $
      rewriteRight (cong {f=\z=>z++(l++n)} (sym fEq)) $
        permComp ((swap s2 s1 `permAdd` permId (k++m)) `permComp` helper2)
                 (permComp (c1 `permAdd` c2)
                           (helper2 `permComp` (swap f1 f2 `permAdd` permId (l++n))))

    perm : Perm (sumArity ao (t1 ++ t2) ++ (k ++ m)) (sumArity ai (t1 ++ t2) ++ (l ++ n))
    perm = helper c1 c2 (coprod ao t1 t2) (coprod ai t1 t2)
