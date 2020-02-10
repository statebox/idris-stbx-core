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

wr : {ai, ao : s -> List o} -> {t : List s} -> (k, l : List o) -> {w : Perm (k ++ sumArity ao t) (l ++ sumArity ai t)}
  -> rewriteLeft (cong (sym (coprod ao t [])))
                 (rewriteRight (cong (sym (coprod ai t [])))
                               (rewriteLeft (appendAssociative k (sumArity ao t) [])
                                            (permComp (permComp (permAdd w [])
                                                                (rewriteLeft (sym (appendAssociative l (sumArity ai t) []))
                                                                             (rewriteRight (appendAssociative l [] (sumArity ai t))
                                                                                           (permComp (permAdd (permId l) (swap (sumArity ai t) []))
                                                                                                     (rewriteLeft (appendAssociative l [] (sumArity ai t))
                                                                                                                  (permAdd (rewriteRight (appendNilRightNeutral l)
                                                                                                                                         (rewriteLeft (appendNilRightNeutral l)
                                                                                                                                                      (permId l)))
                                                                                                                           (permId (sumArity ai t))))))))
                                                      (permAdd (permId l) (rewriteRight (appendNilRightNeutral (sumArity ai t)) (permId (sumArity ai t))))))) =
     w
wr {ai} {ao} {t} k l {w} = rewriteLeftIgnore $ rewriteRightIgnore $ rewriteLeftIgnore step6
  where
  step1 : permAdd (rewriteRight (appendNilRightNeutral l)
                                (rewriteLeft (appendNilRightNeutral l)
                                             (permId l)))
                  (permId (sumArity ai t))
          = permId (l ++ sumArity ai t)
  step1 = permAddCong6 (appendNilRightNeutral l)
                       (appendNilRightNeutral l)
                       Refl
                       Refl
                       (rewriteRightIgnore $ rewriteLeftIgnore Refl)
                       Refl
          `trans` permPreserveId l (sumArity ai t)
  step2 : permAdd (permId l) (swap (sumArity ai t) []) = permId (l ++ sumArity ai t)
  step2 = permAddCong6 Refl
                       Refl
                       (appendNilRightNeutral (sumArity ai t))
                       Refl
                       Refl
                       (swapNilRightNeutral (sumArity ai t))
          `trans` permPreserveId l (sumArity ai t)
  step3 : permComp (permAdd (permId l) (swap (sumArity ai t) []))
                   (rewriteLeft (appendAssociative l [] (sumArity ai t))
                                (permAdd (rewriteRight (appendNilRightNeutral l)
                                                       (rewriteLeft (appendNilRightNeutral l)
                                                                    (permId l)))
                                         (permId (sumArity ai t))))
          = permId (l ++ sumArity ai t)
  step3 = permCompCong5 (rewrite appendNilRightNeutral (sumArity ai t) in Refl)
                        Refl
                        (rewrite appendNilRightNeutral l in Refl)
                        step2
                        (rewriteLeftIgnore step1)
          `trans` permCompRightId (permId (l ++ sumArity ai t))
  step4 : permComp (permAdd w [])
                   (rewriteLeft (sym (appendAssociative l (sumArity ai t) []))
                                (rewriteRight (appendAssociative l [] (sumArity ai t))
                                              (permComp (permAdd (permId l) (swap (sumArity ai t) []))
                                                        (rewriteLeft (appendAssociative l [] (sumArity ai t))
                                                                     (permAdd (rewriteRight (appendNilRightNeutral l)
                                                                                            (rewriteLeft (appendNilRightNeutral l)
                                                                                                         (permId l)))
                                                                              (permId (sumArity ai t)))))))
          = w
  step4 = permCompCong5 (appendNilRightNeutral (k ++ sumArity ao t))
                        (appendNilRightNeutral (l ++ sumArity ai t))
                        Refl
                        (permAddNilRightNeutral w)
                        (rewriteLeftIgnore $ rewriteRightIgnore step3)
          `trans` permCompRightId w
  step5 : permAdd (permId l) (rewriteRight (appendNilRightNeutral (sumArity ai t)) (permId (sumArity ai t)))
          = permId (l ++ sumArity ai t)
  step5 = permAddCong6 Refl
                       Refl
                       Refl
                       (appendNilRightNeutral (sumArity ai t))
                       Refl
                       (rewriteRightIgnore Refl)
          `trans` permPreserveId l (sumArity ai t)
  step6 : permComp (permComp (permAdd w [])
                             (rewriteLeft (sym (appendAssociative l (sumArity ai t) []))
                                          (rewriteRight (appendAssociative l [] (sumArity ai t))
                                                        (permComp (permAdd (permId l) (swap (sumArity ai t) []))
                                                                  (rewriteLeft (appendAssociative l [] (sumArity ai t))
                                                                               (permAdd (rewriteRight (appendNilRightNeutral l)
                                                                                                      (rewriteLeft (appendNilRightNeutral l)
                                                                                                                   (permId l)))
                                                                                        (permId (sumArity ai t))))))))
                   (permAdd (permId l) (rewriteRight (appendNilRightNeutral (sumArity ai t)) (permId (sumArity ai t))))
          = w
  step6 = permCompCong5 (appendNilRightNeutral (k ++ sumArity ao t))
                        Refl
                        (rewrite appendNilRightNeutral (sumArity ai t) in Refl)
                        step4
                        step5
          `trans` permCompRightId w

--      ____                 ____                ____
-- k --| w1 |-- l ----- l --| w2 |-- m -----m --| w3 |-- n -------------- n --
-- o1 -|____|- i1 -\/-- o2 -|____|- i2 -\/- o3 -|____|- i3 -\/- i2 --\/- i1 --
-- o2 -------- o2 -/\/- o3 -------- o3 -/\- i2 -------- i2 -/\- i3 -\/\- i2 --
-- o3 -------- o3 --/\- i1 ------------------------------------ i1 -/\-- i3 --
--
--                                    equals
--      ____                ____                         ____
-- k --| w1 |-- l ---- l --| w2 |-- m ------------- m --| w3 |-- n ------ n --
-- o1 -|____|- i1 -\/- o2 -|____|- i2 -\/- i1 --\/- o3 -|____|- i3 -\/-- i1 --
-- o2 -------- o2 -/\- i1 -------- i1 -/\- i2 -\/\- i1 -------- i1 -/\/- i2 --
-- o3 -------------------------------------o3 -/\-- i2 -------- i2 --/\- i3 --
--
assoc : {ai, ao : s -> List o} -> {t1, t2, t3 : List s} -> (k, l, m, n : List o)
     -> {w1 : Perm (k ++ sumArity ao t1) (l ++ sumArity ai t1)}
     -> {w2 : Perm (l ++ sumArity ao t2) (m ++ sumArity ai t2)}
     -> {w3 : Perm (m ++ sumArity ao t3) (n ++ sumArity ai t3)}
     -> rewriteLeft (cong (sym (coprod ao t1 (t2 ++ t3))))
                    (rewriteRight (cong (sym (coprod ai t1 (t2 ++ t3))))
                                  (rewriteLeft (appendAssociative k (sumArity ao t1) (sumArity ao (t2 ++ t3)))
                                               (permComp (permComp (permAdd w1 (permId (sumArity ao (t2 ++ t3))))
                                                                   (rewriteLeft (sym (appendAssociative l (sumArity ai t1) (sumArity ao (t2 ++ t3))))
                                                                                (rewriteRight (appendAssociative n (sumArity ai (t2 ++ t3)) (sumArity ai t1))
                                                                                              (permComp (permAdd (permId l) (swap (sumArity ai t1) (sumArity ao (t2 ++ t3))))
                                                                                                        (rewriteLeft (appendAssociative l (sumArity ao (t2 ++ t3)) (sumArity ai t1))
                                                                                                                     (permAdd (rewriteLeft (cong (sym (coprod ao t2 t3)))
                                                                                                                                           (rewriteRight (cong (sym (coprod ai t2 t3)))
                                                                                                                                                         (rewriteLeft (appendAssociative l (sumArity ao t2) (sumArity ao t3))
                                                                                                                                                                      (permComp (permComp (permAdd w2 (permId (sumArity ao t3)))
                                                                                                                                                                                          (rewriteLeft (sym (appendAssociative m (sumArity ai t2) (sumArity ao t3)))
                                                                                                                                                                                                       (rewriteRight (appendAssociative n (sumArity ai t3) (sumArity ai t2))
                                                                                                                                                                                                                     (permComp (permAdd (permId m) (swap (sumArity ai t2) (sumArity ao t3)))
                                                                                                                                                                                                                               (rewriteLeft (appendAssociative m (sumArity ao t3) (sumArity ai t2))
                                                                                                                                                                                                                                            (permAdd w3 (permId (sumArity ai t2))))))))
                                                                                                                                                                                (permAdd (permId n) (swap (sumArity ai t3) (sumArity ai t2)))))))
                                                                                                                              (permId (sumArity ai t1))))))))
                                                         (permAdd (permId n) (swap (sumArity ai (t2 ++ t3)) (sumArity ai t1)))))) =
        rewriteLeft (cong (sym (coprod ao (t1 ++ t2) t3)))
                    (rewriteRight (cong (sym (coprod ai (t1 ++ t2) t3)))
                                  (rewriteLeft (appendAssociative k (sumArity ao (t1 ++ t2)) (sumArity ao t3))
                                               (permComp (permComp (permAdd (rewriteLeft (cong (sym (coprod ao t1 t2)))
                                                                                         (rewriteRight (cong (sym (coprod ai t1 t2)))
                                                                                                       (rewriteLeft (appendAssociative k (sumArity ao t1) (sumArity ao t2))
                                                                                                                    (permComp (permComp (permAdd w1 (permId (sumArity ao t2)))
                                                                                                                                        (rewriteLeft (sym (appendAssociative l (sumArity ai t1) (sumArity ao t2)))
                                                                                                                                                     (rewriteRight (appendAssociative m (sumArity ai t2) (sumArity ai t1))
                                                                                                                                                                   (permComp (permAdd (permId l) (swap (sumArity ai t1) (sumArity ao t2)))
                                                                                                                                                                             (rewriteLeft (appendAssociative l (sumArity ao t2) (sumArity ai t1)) (permAdd w2 (permId (sumArity ai t1))))))))
                                                                                                                              (permAdd (permId m) (swap (sumArity ai t2) (sumArity ai t1)))))))
                                                                            (permId (sumArity ao t3)))
                                                                   (rewriteLeft (sym (appendAssociative m (sumArity ai (t1 ++ t2)) (sumArity ao t3)))
                                                                                (rewriteRight (appendAssociative n (sumArity ai t3) (sumArity ai (t1 ++ t2)))
                                                                                              (permComp (permAdd (permId m) (swap (sumArity ai (t1 ++ t2)) (sumArity ao t3))) (rewriteLeft (appendAssociative m (sumArity ao t3) (sumArity ai (t1 ++ t2))) (permAdd w3 (permId (sumArity ai (t1 ++ t2)))))))))
                                                         (permAdd (permId n) (swap (sumArity ai t3) (sumArity ai (t1 ++ t2)))))))

hgLeftId : {s : Type} -> {ai, ao : s -> List o} -> (k, l : List o)
        -> (hg : Hypergraph s ai ao k l) -> compose (identity k) hg = hg
hgLeftId k l (MkHypergraph t w) = hgCong2 Refl (wl k l)

hgRightId : {s : Type} -> {ai, ao : s -> List o} -> (k, l : List o)
         -> (hg : Hypergraph s ai ao k l) -> compose hg (identity l) = hg
hgRightId k l (MkHypergraph t w) = hgCong2 (appendNilRightNeutral t) (wr k l)

hgAssoc : {s : Type} -> {ai, ao : s -> List o} -> (k, l, m, n : List o)
       -> (hg1 : Hypergraph s ai ao k l) -> (hg2 : Hypergraph s ai ao l m) -> (hg3 : Hypergraph s ai ao m n)
       -> compose hg1 (compose hg2 hg3) = compose (compose hg1 hg2) hg3
hgAssoc k l m n (MkHypergraph t1 w1) (MkHypergraph t2 w2) (MkHypergraph t3 w3) = hgCong2 (appendAssociative t1 t2 t3) (assoc k l m n)

hypergraphCat : (sigma : Type) -> (arityIn : sigma -> List o) -> (arityOut : sigma -> List o) -> Category
hypergraphCat {o} sigma arityIn arityOut = MkCategory
  (List o)
  (Hypergraph sigma arityIn arityOut)
  identity
  (\_,_,_ => compose)
  hgLeftId
  hgRightId
  hgAssoc
