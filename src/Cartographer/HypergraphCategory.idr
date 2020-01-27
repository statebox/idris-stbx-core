module HypergraphCategory

import Data.Vect
import Control.Isomorphism

import Cartographer.Hypergraph as HG
import Basic.Category

hgCons3 : {s : Type} -> {ai, ao : s -> List o} -> {k : List o} -> {l : List o}
       -> (h1 = h2) -> {t1 : Vect h1 s} -> {t2 : Vect h2 s} -> (t1 = t2)
       -> {w1 : Perm (k ++ sumArity ao t1) (m ++ sumArity ai t1)}
       -> {w2 : Perm (k ++ sumArity ao t2) (m ++ sumArity ai t2)}
       -> (w1 = w2) -> MkHypergraph h1 t1 w1 = MkHypergraph h2 t2 w2
hgCons3 Refl Refl Refl = Refl

hgLeftId : {s : Type} -> {ai, ao : s -> List o} -> (k : List o) -> (l : List o)
        -> (hg : Hypergraph s ai ao k l) -> compose (identity k) hg = hg
hgLeftId {ao} []      l (MkHypergraph h t w) = hgCons3 Refl Refl ?wlz
hgLeftId {ao} (k::ks) l (MkHypergraph h t w) = hgCons3 Refl Refl ?wls

hgRightId : {s : Type} -> {ai, ao : s -> List o} -> (k : List o) -> (l : List o)
         -> (hg : Hypergraph s ai ao k l) -> compose hg (identity l) = hg
hgRightId k []      (MkHypergraph h t w) = hgCons3 (plusZeroRightNeutral h) (vectNilRightNeutral t) ?wrz
hgRightId k (l::ls) (MkHypergraph h t w) = hgCons3 (plusZeroRightNeutral h) (vectNilRightNeutral t) ?wrs

hypergraphCat : (sigma : Type) -> (arityIn : sigma -> List o) -> (arityOut : sigma -> List o) -> Category
hypergraphCat {o} sigma arityIn arityOut = MkCategory
  (List o)
  (Hypergraph sigma arityIn arityOut)
  identity
  (\_,_,_ => compose)
  hgLeftId
  hgRightId
  (\_,_,_,_,(MkHypergraph h1 t1 w1),(MkHypergraph h2 t2 w2),(MkHypergraph h3 t3 w3) => ?assoc) --Refl)
