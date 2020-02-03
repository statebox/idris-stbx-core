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

permPreserveId: (as, bs : List o) -> permAdd (permId as) (permId bs) = permId (as ++ bs)
permPreserveId     []  bs = Refl
permPreserveId (a::as) bs = insCong Refl Refl Refl (permPreserveId as bs) Refl

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
permPreserveCompose ([], as) ([], bs) ([], cs) (MkProductMorphism Nil f2) (MkProductMorphism Nil g2) = Refl
permPreserveCompose (as, []) (bs, []) (cs, []) (MkProductMorphism f1 Nil) (MkProductMorphism g1 Nil) =
  rewrite permAddNilRightNeutral (permComp f1 g1) in ?x
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
