module Cartographer.HypergraphCategory

import Data.List

import Basic.Category

import Permutations.Sandwich
import Permutations.Permutations
import Permutations.PermutationsCategory
import Permutations.PermutationsStrictMonoidalCategory

import Cartographer.Hypergraph

%access public export
%default total

hgCong2 : {s : Type} -> {ai, ao : s -> List o} -> {k : List o}
       -> {t1 : List s} -> {t2 : List s} -> (t1 = t2)
       -> {w1 : Perm (sumArity ao t1 ++ k) (sumArity ai t1 ++ m)}
       -> {w2 : Perm (sumArity ao t2 ++ k) (sumArity ai t2 ++ m)}
       -> (w1 = w2) -> MkHypergraph t1 w1 = MkHypergraph t2 w2
hgCong2 Refl Refl = Refl

wl : {ai, ao : s -> List o} -> {t : List s} -> (k, l : List o) -> {w : Perm (sumArity ao t ++ k) (sumArity ai t ++ l)}
  -> rewriteLeft (trans (cong {f=\z=>z++k} (sym (appendNilRightNeutral (sumArity ao t)))) (sym (appendAssociative (sumArity ao t) [] k)))
                 (rewriteRight (trans (cong {f=\z=>z++l} (sym (appendNilRightNeutral (sumArity ai t)))) (sym (appendAssociative (sumArity ai t) [] l)))
                               (permComp (permComp (permAddIdL (sumArity ao t) (permId k))
                                                   (swapAddIdR (sumArity ao t) [] k))
                                         (permComp w (permId (sumArity ai t ++ l))))) =
     w
wl {ao} {t} k _ {w} = rewriteLeftIgnore $ rewriteRightIgnore $
  permCompCong5 Refl Refl Refl
    (permCompCong5 Refl Refl Refl
      (permAddIdLPreserveId (sumArity ao t) k)
      (swapAddIdRNilRightNeutral (sumArity ao t) k)
    `trans` permCompLeftId (permId (sumArity ao t ++ k)))
    (permCompRightId w)
  `trans` permCompLeftId w

wr : {ai, ao : s -> List o} -> {t : List s} -> (k, l : List o) -> {w : Perm (sumArity ao t ++ k) (sumArity ai t ++ l)}
  -> rewriteLeft (trans (cong {f=\z=>z++k} (sym (coprod ao t []))) Refl)
                 (rewriteRight (trans (cong {f=\z=>[]++z++l} (sym (coprod ai t []))) Refl)
                               (permComp (permComp w (permId (sumArity ai t ++ l)))
                                         (permComp (permAddIdL (sumArity ai t) (permId l))
                                                   (swapAddIdR (sumArity ai t) [] l)))) =
     w
wr {ai} {t} _ l {w} = rewriteLeftIgnore $ rewriteRightIgnore $
  permCompCong5 Refl Refl Refl
    (permCompRightId w)
    (permCompCong5 Refl Refl Refl
      (permAddIdLPreserveId (sumArity ai t) l)
      (swapAddIdRNilRightNeutral (sumArity ai t) l)
    `trans` permCompRightId (permId (sumArity ai t ++ l)))
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
     -> {w1 : Perm (sumArity ao t1 ++ k) (sumArity ai t1 ++ l)}
     -> {w2 : Perm (sumArity ao t2 ++ l) (sumArity ai t2 ++ m)}
     -> {w3 : Perm (sumArity ao t3 ++ m) (sumArity ai t3 ++ n)}
     -> rewriteLeft (trans (cong {f=\z=>z++k} (sym (coprod ao t1 (t2 ++ t3)))) (sym (appendAssociative (sumArity ao (t2 ++ t3)) (sumArity ao t1) k)))
                    (rewriteRight (trans (cong {f=\z=>z++n} (sym (coprod ai t1 (t2 ++ t3)))) (sym (appendAssociative (sumArity ai (t2 ++ t3)) (sumArity ai t1) n)))
                                  (permComp (permComp (permAddIdL (sumArity ao (t2 ++ t3)) w1) (swapAddIdR (sumArity ao (t2 ++ t3)) (sumArity ai t1) l))
                                            (permComp (permAddIdL (sumArity ai t1)
                                                                  (rewriteLeft (trans (cong {f=\z=>z++l} (sym (coprod ao t2 t3)))
                                                                                      (sym (appendAssociative (sumArity ao t3) (sumArity ao t2) l)))
                                                                               (rewriteRight (trans (cong {f=\z=>z++n} (sym (coprod ai t2 t3)))
                                                                                                    (sym (appendAssociative (sumArity ai t3) (sumArity ai t2) n)))
                                                                                             (permComp (permComp (permAddIdL (sumArity ao t3) w2)
                                                                                                                 (swapAddIdR (sumArity ao t3) (sumArity ai t2) m))
                                                                                                       (permComp (permAddIdL (sumArity ai t2) w3)
                                                                                                                 (swapAddIdR (sumArity ai t2) (sumArity ai t3) n))))))
                                                      (swapAddIdR (sumArity ai t1) (sumArity ai (t2 ++ t3)) n)))) =
        rewriteLeft (trans (cong {f=\z=>z++k} (sym (coprod ao (t1 ++ t2) t3))) (sym (appendAssociative (sumArity ao t3) (sumArity ao (t1 ++ t2)) k)))
                    (rewriteRight (trans (cong {f=\z=>z++n} (sym (coprod ai (t1 ++ t2) t3))) (sym (appendAssociative (sumArity ai t3) (sumArity ai (t1 ++ t2)) n)))
                                  (permComp (permComp (permAddIdL (sumArity ao t3)
                                                                  (rewriteLeft (trans (cong {f=\z=>z++k} (sym (coprod ao t1 t2)))
                                                                                      (sym (appendAssociative (sumArity ao t2) (sumArity ao t1) k)))
                                                                               (rewriteRight (trans (cong {f=\z=>z++m} (sym (coprod ai t1 t2)))
                                                                                                    (sym (appendAssociative (sumArity ai t2) (sumArity ai t1) m)))
                                                                                             (permComp (permComp (permAddIdL (sumArity ao t2) w1)
                                                                                                                 (swapAddIdR (sumArity ao t2) (sumArity ai t1) l))
                                                                                                       (permComp (permAddIdL (sumArity ai t1) w2)
                                                                                                                 (swapAddIdR (sumArity ai t1) (sumArity ai t2) m))))))
                                                      (swapAddIdR (sumArity ao t3) (sumArity ai (t1 ++ t2)) m))
                                            (permComp (permAddIdL (sumArity ai (t1 ++ t2)) w3) (swapAddIdR (sumArity ai (t1 ++ t2)) (sumArity ai t3) n))))

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
