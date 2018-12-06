module PreorderAsCategory.idr

import Category

-- contrib
import Decidable.Order

interface Preorder t po => UniquePreorder t (po : t -> t -> Type) where
  unique : (a, b : t) -> (f, g : po a b) -> f = g

identity : Preorder t po => (a : t) -> po a a
identity = reflexive

compose : Preorder t po => (a, b, c : t) -> po a b -> po b c -> po a c
compose = transitive

identityLeft : UniquePreorder t po => (a, b : t) -> (f : po a b) -> compose a a b (identity a) f = f
identityLeft a b f = unique a b (compose a a b (identity a) f) f

identityRight : UniquePreorder t po => (a, b : t) -> (f : po a b) -> compose a b b f (identity b) = f
identityRight a b f = unique a b (compose a b b f (identity b)) f

ass : UniquePreorder t po => (a, b, c, d : t) -> (f : po a b) -> (g : po b c) -> (h : po c d) -> transitive a b d f (transitive b c d g h) = transitive a c d (transitive a b c f g) h
ass a b c d f g h = unique a d (transitive a b d f (transitive b c d g h)) (transitive a c d (transitive a b c f g) h)

UniquePreorder t po => Category t po where
  identity = identity
  compose {a} {b} {c} = compose a b c
  identityLeft {a} {b} {f} = identityLeft a b f
  identityRight {a} {b} {f} = identityRight a b f
  associativity {a} {b} {c} {d} {f} {g} {h} = ass a b c d f g h
