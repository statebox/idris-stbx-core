module Cartographer.GoodHypergraphCategory

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

data GoodHypergraph : {s : Type} -> {ai, ao : s -> List o} -> (g : Hypergraph s ai ao k l) -> Type where
    Singleton : (edge : s) -> GoodHypergraph (singleton edge)
    Permutation : (p : Perm k l) -> GoodHypergraph (permutation p)
    HComp : (a : GoodHypergraph g)
         -> (b : GoodHypergraph h)
         -> GoodHypergraph (compose g h)
    VComp : (a : GoodHypergraph g)
         -> (b : GoodHypergraph h)
         -> GoodHypergraph (add g h)

getHypergraph : {g : Hypergraph s ai ao k l} -> GoodHypergraph g -> Hypergraph s ai ao k l
getHypergraph _ {g} = g

postulate subsetEq : Subset.getWitness g = Subset.getWitness h -> g = h

goodHypergraphCat : (sigma : Type) -> (arityIn : sigma -> List o) -> (arityOut : sigma -> List o) -> Category
goodHypergraphCat {o} sigma arityIn arityOut = MkCategory
  (List o)
  (\k, l => Subset (Hypergraph sigma arityIn arityOut k l) GoodHypergraph)
  (\n => Element (identity n) (Permutation (permId n)))
  (\_,_,_,f,g => Element (compose (getWitness f) (getWitness g)) (HComp (getProof f) (getProof g)))
  (\a, b, (Element g gg) => subsetEq (hgLeftId a b g))
  (\a, b, (Element g gg) => subsetEq (hgRightId a b g))
  (\a, b, c, d, (Element f ff), (Element g gg), (Element h hh) => subsetEq (hgAssoc a b c d f g h))

--   (Hypergraph sigma arityIn arityOut)
