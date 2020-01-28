module HypergraphCategory

import Data.List
import Control.Isomorphism

import Cartographer.Hypergraph as HG
import Basic.Category

hgCons2 : {s : Type} -> {ai, ao : s -> List o} -> {k : List o} -> {l : List o}
       -> {t1 : List s} -> {t2 : List s} -> (t1 = t2)
       -> {w1 : Perm (k ++ concatMap ao t1) (m ++ concatMap ai t1)}
       -> {w2 : Perm (k ++ concatMap ao t2) (m ++ concatMap ai t2)}
       -> (w1 = w2) -> MkHypergraph t1 w1 = MkHypergraph t2 w2
hgCons2 Refl Refl = Refl

hgLeftId : {s : Type} -> {ai, ao : s -> List o} -> (k : List o) -> (l : List o)
        -> (hg : Hypergraph s ai ao k l) -> compose (identity k) hg = hg
hgLeftId {ao} []      l (MkHypergraph t w) = hgCons2 Refl ?wlz
hgLeftId {ao} (k::ks) l (MkHypergraph t w) = hgCons2 Refl ?wls

hgRightId : {s : Type} -> {ai, ao : s -> List o} -> (k : List o) -> (l : List o)
         -> (hg : Hypergraph s ai ao k l) -> compose hg (identity l) = hg
hgRightId k []      (MkHypergraph t w) = hgCons2 (appendNilRightNeutral t) ?wrz
hgRightId k (l::ls) (MkHypergraph t w) = hgCons2 (appendNilRightNeutral t) ?wrs

hypergraphCat : (sigma : Type) -> (arityIn : sigma -> List o) -> (arityOut : sigma -> List o) -> Category
hypergraphCat {o} sigma arityIn arityOut = MkCategory
  (List o)
  (Hypergraph sigma arityIn arityOut)
  identity
  (\_,_,_ => compose)
  hgLeftId
  hgRightId
  (\_,_,_,_,(MkHypergraph t1 w1),(MkHypergraph t2 w2),(MkHypergraph t3 w3) => ?assoc) --Refl)
