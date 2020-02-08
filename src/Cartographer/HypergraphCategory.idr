module HypergraphCategory

import Data.List
import Control.Isomorphism

import Basic.Category

import Permutations.Sandwich
import Permutations.Permutations
import Permutations.PermutationsCategory
import Permutations.PermutationsStrictMonoidalCategory

import Cartographer.Hypergraph as HG

hgCong2 : {s : Type} -> {ai, ao : s -> List o} -> {k : List o}
       -> {t1 : List s} -> {t2 : List s} -> (t1 = t2)
       -> {w1 : Perm (k ++ sumArity ao t1) (m ++ sumArity ai t1)}
       -> {w2 : Perm (k ++ sumArity ao t2) (m ++ sumArity ai t2)}
       -> (w1 = w2) -> MkHypergraph t1 w1 = MkHypergraph t2 w2
hgCong2 Refl Refl = Refl

wl : {ai, ao : s -> List o} -> {t : List s} -> (k, l : List o) -> {w : Perm (k ++ sumArity ao t) (l ++ sumArity ai t)}
   -> rewriteLeft (appendAssociative k [] (sumArity ao t))
                  (permComp (permComp (permAdd (rewriteRight (appendNilRightNeutral k) (rewriteLeft (appendNilRightNeutral k) (permId k)))
                                               (permId (sumArity ao t)))
                                      (rewriteLeft (sym (appendAssociative k [] (sumArity ao t)))
                                                   (rewriteRight (appendAssociative l (sumArity ai t) [])
                                                                 (permComp (permAdd (permId k)
                                                                                    (rewriteRight (appendNilRightNeutral (sumArity ao t)) (permId (sumArity ao t))))
                                                                           (rewriteLeft (appendAssociative k (sumArity ao t) []) (permAdd w []))))))
                            (permAdd (permId l) (swap (sumArity ai t) [])))
     = w
wl {ai} {ao} {t} k l {w} = rewriteLeftIgnore $
                           permCompCong5 (cong {f=\z=>z ++ sumArity ao t} (appendNilRightNeutral k))
                                         (cong (appendNilRightNeutral (sumArity ai t)))
                                         Refl
                                         step4
                                         step5
                            `trans` permCompRightId w
  where
  step1 : permAdd (rewriteRight (appendNilRightNeutral k) (rewriteLeft (appendNilRightNeutral k) (permId k)))
                  (permId (sumArity ao t))
          = permId (k ++ sumArity ao t)
  step1 = permAddCong6 (appendNilRightNeutral k)
                       (appendNilRightNeutral k)
                       Refl
                       Refl
                       (rewriteRightIgnore $ rewriteLeftIgnore Refl)
                       Refl
            `trans` permPreserveId k (sumArity ao t)
  step2 : permAdd (permId k)
                  (rewriteRight (appendNilRightNeutral (sumArity ao t)) (permId (sumArity ao t)))
          = permId (k ++ sumArity ao t)
  step2 = permAddCong6 Refl
                       Refl
                       Refl
                       (appendNilRightNeutral (sumArity ao t))
                       Refl
                       (rewriteRightIgnore Refl)
            `trans` permPreserveId k (sumArity ao t)
  step3 : rewriteLeft (sym (appendAssociative k [] (sumArity ao t)))
                      (rewriteRight (appendAssociative l (sumArity ai t) [])
                                    (permComp (permAdd (permId k)
                                                       (rewriteRight (appendNilRightNeutral (sumArity ao t)) (permId (sumArity ao t))))
                                              (rewriteLeft (appendAssociative k (sumArity ao t) []) (permAdd w []))))
          = w
  step3 = rewriteLeftIgnore $ rewriteRightIgnore $
          permCompCong5 Refl
                        (trans (appendAssociative k (sumArity ao t) [])
                               (appendNilRightNeutral (k ++ sumArity ao t)))
                        (appendNilRightNeutral $ l ++ sumArity ai t)
                        step2
                        (rewriteLeftIgnore $ permAddNilRightNeutral w)
            `trans` permCompLeftId w
  step4 : permComp (permAdd (rewriteRight (appendNilRightNeutral k) (rewriteLeft (appendNilRightNeutral k) (permId k)))
                            (permId (sumArity ao t)))
                   (rewriteLeft (sym (appendAssociative k [] (sumArity ao t)))
                                (rewriteRight (appendAssociative l (sumArity ai t) [])
                                              (permComp (permAdd (permId k)
                                                                 (rewriteRight (appendNilRightNeutral (sumArity ao t)) (permId (sumArity ao t))))
                                                        (rewriteLeft (appendAssociative k (sumArity ao t) []) (permAdd w [])))))
          = w
  step4 = permCompCong5 (cong {f=\z=>z ++ sumArity ao t} (appendNilRightNeutral k))
                        (cong {f=\z=>z ++ sumArity ao t} (appendNilRightNeutral k))
                        (trans (appendAssociative l (sumArity ai t) [])
                               (appendNilRightNeutral (l ++ sumArity ai t)))
                        step1
                        step3
           `trans` permCompLeftId w
  step5 : permAdd (permId l) (swap (sumArity ai t) []) = permId (l ++ sumArity ai t)
  step5 = permAddCong6 Refl
                       Refl
                       (appendNilRightNeutral (sumArity ai t))
                       Refl
                       Refl
                       (swapNilRightNeutral (sumArity ai t))
            `trans` permPreserveId l (sumArity ai t)

hgLeftId : {s : Type} -> {ai, ao : s -> List o} -> (k, l : List o)
        -> (hg : Hypergraph s ai ao k l) -> compose (identity k) hg = hg
hgLeftId k l (MkHypergraph t w) = hgCong2 Refl (wl k l)

hgRightId : {s : Type} -> {ai, ao : s -> List o} -> (k, l : List o)
         -> (hg : Hypergraph s ai ao k l) -> compose hg (identity l) = hg
hgRightId k l (MkHypergraph t w) = hgCong2 (appendNilRightNeutral t) ?wr
--hgRightId {ai} {ao} k l (MkHypergraph [] w) = hgCong2 Refl ?wrz
--hgRightId {ai} {ao} k l (MkHypergraph (t::ts) w) = hgCong2 (appendNilRightNeutral (t::ts)) ?wrs

hypergraphCat : (sigma : Type) -> (arityIn : sigma -> List o) -> (arityOut : sigma -> List o) -> Category
hypergraphCat {o} sigma arityIn arityOut = MkCategory
  (List o)
  (Hypergraph sigma arityIn arityOut)
  identity
  (\_,_,_ => compose)
  hgLeftId
  hgRightId
  (\_,_,_,_,(MkHypergraph t1 w1),(MkHypergraph t2 w2),(MkHypergraph t3 w3) => ?assoc) --Refl)
