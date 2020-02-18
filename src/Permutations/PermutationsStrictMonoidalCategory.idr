module Permutations.PermutationsStrictMonoidalCategory

import Basic.Category
import Basic.Functor
import MonoidalCategory.StrictMonoidalCategory
import Product.ProductCategory

import Permutations.Sandwich
import Permutations.Permutations
import Permutations.PermutationsCategory

%access public export
%default total

permPreserveId : (as, bs : List o) -> permAdd (permId as) (permId bs) = permId (as ++ bs)
permPreserveId     []  bs = Refl
permPreserveId (a::as) bs = insCong Refl Refl Refl (permPreserveId as bs) Refl

permAddIdLPreserveId : (as, bs : List o) -> permAddIdL as (permId bs) = permId (as ++ bs)
permAddIdLPreserveId     []  bs = Refl
permAddIdLPreserveId (a::as) bs = insCong Refl Refl Refl (permAddIdLPreserveId as bs) Refl

permAddNilRightNeutral : (ab : Perm as bs) -> permAdd ab Nil = ab
permAddNilRightNeutral              Nil          = Refl
permAddNilRightNeutral {as=a::as1} (Ins {r} p s) =
  insCong (appendNilRightNeutral as1)
          Refl
          (appendNilRightNeutral r)
          (rewriteRightIgnore (permAddNilRightNeutral p))
          (appendedNilNeutral s)

permPreserveCompose : (a, b, c : (List o, List o))
                   -> (f : ProductMorphism (permutationsCat o) (permutationsCat o) a b)
                   -> (g : ProductMorphism (permutationsCat o) (permutationsCat o) b c)
                   -> permAdd (permComp (pi1 f) (pi1 g)) (permComp (pi2 f) (pi2 g))
                    = permComp (permAdd (pi1 f) (pi2 f)) (permAdd (pi1 g) (pi2 g))
permPreserveCompose (_, _) (_, _) (_, _) (MkProductMorphism Nil f2) (MkProductMorphism Nil g2) = Refl
permPreserveCompose (as, _) (bs, _) (cs, _) (MkProductMorphism f1 Nil) (MkProductMorphism g1 Nil) =
  trans (permAddNilRightNeutral (permComp f1 g1)) $ permCompCong5
    (sym $ appendNilRightNeutral as)
    (sym $ appendNilRightNeutral bs)
    (sym $ appendNilRightNeutral cs)
    (sym $ permAddNilRightNeutral f1)
    (sym $ permAddNilRightNeutral g1)
permPreserveCompose (a1::as1, a2::as2) (bs1, bs2) (cs1, cs2)
  (MkProductMorphism (Ins pf1 sf1) (Ins pf2 sf2)) (MkProductMorphism g1 g2) = ?y

permTensor : (o : Type) -> CFunctor (productCategory (permutationsCat o) (permutationsCat o)) (permutationsCat o)
permTensor _ = MkCFunctor
  (\a => fst a ++ snd a)
  (\a, b, f => permAdd (pi1 f) (pi2 f) {as=fst a} {bs=fst b} {cs=snd a} {ds=snd b})
  (\a => permPreserveId (fst a) (snd a))
  permPreserveCompose

permAddAssociativeMor : (pab : Perm as bs) -> (pcd : Perm cs ds) -> (pef : Perm es fs)
                     -> permAdd pab (permAdd pcd pef) = permAdd (permAdd pab pcd) pef
permAddAssociativeMor Nil _ _ = Refl
permAddAssociativeMor {as=a::as} {bs} {cs} {ds} {es} {fs} (Ins {r} pab s) pcd pef = insCong
  (appendAssociative as cs es)
  Refl
  (appendAssociative r ds fs)
  ?z
  (appendedAppendDistr ds fs s)

permutationsSMC : (o : Type) -> StrictMonoidalCategory
permutationsSMC o = MkStrictMonoidalCategory
  (permutationsCat o)
  (permTensor o)
  []
  (\as => Refl)
  (\as => appendNilRightNeutral as)
  appendAssociative
  (\_, _, _, _, _, _ => permAddAssociativeMor)


-- for symmetric monoidal category

swapNilRightNeutral : (l : List o) -> swap l [] = permId l
swapNilRightNeutral [] = Refl
swapNilRightNeutral (l::ls) = insCong (appendNilRightNeutral ls) Refl Refl (swapNilRightNeutral ls) Refl

swapAddIdRNilRightNeutral : (l : List o) -> (k : List o) -> swapAddIdR l [] k = permId (l ++ k)
swapAddIdRNilRightNeutral [] k = Refl
swapAddIdRNilRightNeutral (l::ls) k = insCong Refl Refl Refl (swapAddIdRNilRightNeutral ls k) Refl

swapHexagonal : (as, bs, cs : List o) ->
  rewriteRight (sym $ appendAssociative bs cs as)
    (rewriteRight (appendAssociative bs as cs) (permAdd (swap as bs) (permId cs)) `permComp` permAdd (permId bs) (swap as cs))
  = swap as (bs ++ cs)
swapHexagonal [] bs cs = rewriteRightIgnore $ rewriteRightIgnoreR $ step2 `trans` step3
  where
    step1 : permAdd (permId bs) (rewriteRight (appendNilRightNeutral cs) (permId cs)) = permId (bs ++ cs)
    step1 = permAddCong6 Refl
                         Refl
                         Refl
                         (appendNilRightNeutral cs)
                         Refl
                         (rewriteRightIgnore Refl)
            `trans` permPreserveId bs cs
    step2 : permComp (rewriteRight (appendAssociative bs [] cs) (permAdd (rewriteRight (appendNilRightNeutral bs) (permId bs)) (permId cs)))
              (permAdd (permId bs) (rewriteRight (appendNilRightNeutral cs) (permId cs)))
            = rewriteRight (appendAssociative bs [] cs) (permAdd (rewriteRight (appendNilRightNeutral bs) (permId bs)) (permId cs))
    step2 = permCompCong5 Refl
                          Refl
                          (rewrite appendNilRightNeutral cs in Refl)
                          Refl
                          step1
            `trans` permCompRightId _
    step3 : rewriteRight (appendAssociative bs [] cs) (permAdd (rewriteRight (appendNilRightNeutral bs) (permId bs)) (permId cs))
            = permId (bs ++ cs)
    step3 = rewriteRightIgnore $
      permAddCong6 Refl
                   (appendNilRightNeutral bs)
                   Refl
                   Refl
                   (rewriteRightIgnore Refl)
                   Refl
      `trans` permPreserveId bs cs
-- swapHexagonal (a::as) [] cs =
--   insCong (rewrite appendNilRightNeutral as in Refl)
--           Refl
--           Refl
--           step2
--           Refl
--   where
--     step1 : permAdd (swap as []) (permId cs) = permId (as ++ cs)
--     step1 = permAddCong6 (appendNilRightNeutral as)
--                          Refl
--                          Refl
--                          Refl
--                          (swapNilRightNeutral as)
--                          Refl
--             `trans` permPreserveId as cs
--     step2 : permComp (permAdd (swap as []) (permId cs)) (swap as cs) = swap as cs
--     step2 = permCompCong5 (rewrite appendNilRightNeutral as in Refl)
--                           Refl
--                           Refl
--                           step1
--                           Refl
--             `trans` permCompLeftId _
swapHexagonal {o} (a::as) bs cs = ?ws
