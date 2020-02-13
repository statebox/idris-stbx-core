module Cartographer.HypergraphStrictMonoidalCategory

import Data.List

import Basic.Category
import Basic.Functor
import MonoidalCategory.StrictMonoidalCategory
import Product.ProductCategory

import Permutations.Sandwich
import Permutations.Permutations
import Permutations.PermutationsCategory
import Permutations.PermutationsStrictMonoidalCategory

import Cartographer.Hypergraph as HG
import Cartographer.HypergraphCategory

%access public export
%default total

hgPreserveId : {s : Type} -> {ai, ao : s -> List o} -> (as, bs : List o)
            -> add (identity {s} {ai} {ao} as) (identity {s} {ai} {ao} bs) = identity {s} {ai} {ao} (as ++ bs)
hgPreserveId {s} {ai} {ao} as bs with (identity {s} {ai} {ao} as)
  | MkHypergraph ta pa with (identity {s} {ai} {ao} bs)
    | MkHypergraph tb pb = hgCong2 Refl $
                           rewriteRightIgnoreR $ rewriteLeftIgnoreR $
                             (permCompCong5 (appendNilRightNeutral $ as ++ bs)
                                            (trans (trans (cong {f=\z=>z++bs++[]} $ appendNilRightNeutral $ as)
                                                          (appendAssociative as bs []))
                                                   (appendNilRightNeutral $ as ++ bs))
                                            (appendNilRightNeutral $ as ++ bs)
                                            step1
                                            (permCompCong5 (trans (trans (cong {f=\z=>z++bs++[]} $ appendNilRightNeutral $ as)
                                                                         (appendAssociative as bs []))
                                                                  (appendNilRightNeutral $ as ++ bs))
                                                           (trans (trans (cong {f=\z=>z++bs++[]} $ appendNilRightNeutral $ as)
                                                                         (appendAssociative as bs []))
                                                                  (appendNilRightNeutral $ as ++ bs))
                                                           (appendNilRightNeutral $ as ++ bs)
                                                           step2
                                                           step3)
                             `trans`
                             permCompLeftId _)
                             `trans`
                             permCompLeftId _
      where
      step1 : rewriteLeft (trans (appendAssociative (as ++ bs) [] []) (cong {f=\z=>z++[]} (sym (appendAssociative as bs []))))
                          (rewriteRight (trans (appendAssociative (as ++ []) bs []) (cong {f=\z=>z++[]} (sym (appendAssociative as [] bs))))
                                        (permAdd (permAdd (permId as) (swap bs [])) [])) = permId (as ++ bs)
      step1 = rewriteLeftIgnore $ rewriteRightIgnore $
              trans (permAddNilRightNeutral _) $
              permAddCong6 Refl
                       Refl
                       (appendNilRightNeutral bs)
                       Refl
                       Refl
                       (swapNilRightNeutral bs)
              `trans` permPreserveId as bs
      step2 : permAdd (rewriteRight (appendNilRightNeutral as) (rewriteLeft (appendNilRightNeutral as) (permId as)))
                                (rewriteRight (appendNilRightNeutral bs) (rewriteLeft (appendNilRightNeutral bs) (permId bs))) = permId (as ++ bs)
      step2 = permAddCong6 (appendNilRightNeutral as)
                           (appendNilRightNeutral as)
                           (appendNilRightNeutral bs)
                           (appendNilRightNeutral bs)
                           (rewriteRightIgnore $ rewriteLeftIgnore Refl)
                           (rewriteRightIgnore $ rewriteLeftIgnore Refl)
              `trans` permPreserveId as bs
      step3 : rewriteLeft (trans (appendAssociative (as ++ []) bs []) (cong {f=\z=>z++[]} (sym (appendAssociative as [] bs))))
                          (rewriteRight (trans (appendAssociative (as ++ bs) [] []) (cong {f=\z=>z++[]} (sym (appendAssociative as bs []))))
                                        (permAdd (permAdd (permId as) (rewriteRight (appendNilRightNeutral bs) (permId bs))) [])) = permId (as ++ bs)
      step3 = rewriteLeftIgnore $ rewriteRightIgnore $
              trans (permAddNilRightNeutral _) $
              permAddCong6 Refl
                           Refl
                           Refl
                           (appendNilRightNeutral bs)
                           Refl
                           (rewriteRightIgnore Refl)
              `trans` permPreserveId as bs

hgPreserveCompose : {s : Type} -> {ai, ao : s -> List o} -> (a, b, c : (List o, List o))
                 -> (f : ProductMorphism (hypergraphCat s ai ao) (hypergraphCat s ai ao) a b)
                 -> (g : ProductMorphism (hypergraphCat s ai ao) (hypergraphCat s ai ao) b c)
                 -> add (compose (pi1 f) (pi1 g)) (compose (pi2 f) (pi2 g))
                  = compose (add (pi1 f) (pi2 f)) (add (pi1 g) (pi2 g))

hgTensor : (s : Type) -> (ai, ao : s -> List o) -> CFunctor (productCategory (hypergraphCat s ai ao) (hypergraphCat s ai ao)) (hypergraphCat s ai ao)
hgTensor s ai ao = MkCFunctor
  (\a => fst a ++ snd a)
  (\a, b, f => add (pi1 f) (pi2 f) {k=fst a} {l=fst b} {m=snd a} {n=snd b})
  (\a => hgPreserveId (fst a) (snd a))
  hgPreserveCompose
