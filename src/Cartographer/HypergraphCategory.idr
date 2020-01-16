module HypergraphCategory

import Data.Fin
import Control.Isomorphism

import Cartographer.Hypergraph
import Basic.Category

hypergraphCat : (sigma : Type) -> (arity : sigma -> (Nat, Nat)) -> Category
hypergraphCat sigma arity = MkCategory 
  Nat 
  (Hypergraph sigma arity)
  identity
  (\_,_,_ => Cartographer.Hypergraph.compose)
  (\_,_,_ => Refl)
  ?lid --(\_,_,_ => Refl)
  (\_,_,_,_,(MkHypergraph h1 t1 w1),(MkHypergraph h2 t2 w2),(MkHypergraph h3 t3 w3) => ?assoc) --Refl)
