module HypergraphCategory

import Data.List
import Control.Isomorphism

import Basic.Category

import Permutations.Sandwich
import Permutations.Permutations
import Permutations.PermutationsCategory
import Permutations.PermutationsStrictMonoidalCategory

import Cartographer.Hypergraph as HG

hgCong2 : {s : Type} -> {ai, ao : s -> List o} -> {k : List o} -> {l : List o}
       -> {t1 : List s} -> {t2 : List s} -> (t1 = t2)
       -> {w1 : Perm (k ++ sumArity ao t1) (m ++ sumArity ai t1)}
       -> {w2 : Perm (k ++ sumArity ao t2) (m ++ sumArity ai t2)}
       -> (w1 = w2) -> MkHypergraph t1 w1 = MkHypergraph t2 w2
hgCong2 Refl Refl = Refl

wlz : {ai, ao : s -> List o} -> {t : List s} -> (l : List o) -> {w : Perm (sumArity ao t) (l ++ sumArity ai t)}
    -> permComp (permComp (permId (sumArity ao t)) (rewriteRight (appendAssociative l (sumArity ai t) []) (permComp (rewriteRight (appendNilRightNeutral (sumArity ao t)) (permId (sumArity ao t))) (permAdd w [])))) (permAdd (permId l) (swap (sumArity ai t) [])) = w
wlz {w} {ai} {ao} {t} l = step9 `trans` permCompRightId w
  where
    step1 : permAdd w [] = w
    step1 = permAddNilRightNeutral w
    type1 : Perm (sumArity ao t) (sumArity ao t ++ [])
    type1 = rewriteRight (appendNilRightNeutral (sumArity ao t)) (permId (sumArity ao t))
    step2 : type1 = permId (sumArity ao t)
    step2 = rewriteRightIgnore Refl
    step3 : permComp type1 (permAdd w []) = permComp (permId (sumArity ao t)) w
    step3 = permCompCong5 Refl (appendNilRightNeutral _) (appendNilRightNeutral _) step2 step1
    step4 : permComp type1 (permAdd w []) = w
    step4 = step3 `trans` permCompLeftId w
    type2 : Perm (sumArity ao t) (l ++ sumArity ai t ++ [])
    type2 = rewriteRight (appendAssociative l (sumArity ai t) []) (permComp type1 (permAdd w []))
    step5 : type2 = w
    step5 = rewriteRightIgnore step4
    step6 : permComp (permId (sumArity ao t)) type2 = w
    step6 = permCompLeftId _ `trans` step5
    step7 : permAdd (permId l) (swap (sumArity ai t) []) = permAdd (permId l) (permId (sumArity ai t))
    step7 = permAddCong6 Refl Refl (appendNilRightNeutral (sumArity ai t)) Refl Refl (swapNilRightNeutral (sumArity ai t))
    step8 : permAdd (permId l) (swap (sumArity ai t) []) = permId (l ++ sumArity ai t)
    step8 = step7 `trans` permPreserveId l (sumArity ai t)
    step9 : permComp (permComp (permId (sumArity ao t)) type2) (permAdd (permId l) (swap (sumArity ai t) [])) = permComp w (permId (l ++ sumArity ai t))
    step9 = permCompCong5 Refl (cong (appendNilRightNeutral (sumArity ai t))) Refl step6 step8

hgLeftId : {s : Type} -> {ai, ao : s -> List o} -> (k : List o) -> (l : List o)
        -> (hg : Hypergraph s ai ao k l) -> compose (identity k) hg = hg
hgLeftId {ao} []      l (MkHypergraph t w) = hgCons2 Refl ?wlz
hgLeftId {ao} (k::ks) l (MkHypergraph t w) = hgCons2 Refl ?wls
-- actually not splitting up seems more doable:
-- hgLeftId k l (MkHypergraph t w) = hgCong2 {l} Refl ?wl

hgRightId : {s : Type} -> {ai, ao : s -> List o} -> (k : List o) -> (l : List o)
         -> (hg : Hypergraph s ai ao k l) -> compose hg (identity l) = hg
hgRightId {ai} {ao} k l (MkHypergraph [] w) = hgCong2 Refl ?wrz
hgRightId {ai} {ao} k l (MkHypergraph (t::ts) w) = hgCong2 (appendNilRightNeutral (t::ts)) ?wrs

hypergraphCat : (sigma : Type) -> (arityIn : sigma -> List o) -> (arityOut : sigma -> List o) -> Category
hypergraphCat {o} sigma arityIn arityOut = MkCategory
  (List o)
  (Hypergraph sigma arityIn arityOut)
  identity
  (\_,_,_ => compose)
  hgLeftId
  hgRightId
  (\_,_,_,_,(MkHypergraph t1 w1),(MkHypergraph t2 w2),(MkHypergraph t3 w3) => ?assoc) --Refl)
