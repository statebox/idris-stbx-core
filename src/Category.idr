module Category

export
interface Category object (morphism : object -> object -> Type) where
  identity : (a : object) -> morphism a a
  compose : morphism a b -> morphism b c -> morphism a c
  identityLeft : (f : morphism a b) -> compose (identity a) f = f
  identityRight :  (f : morphism a b) -> compose f (identity b) = f
  associativity : (f: morphism a b) -> (g : morphism b c) -> (h : morphism c d) -> compose f (compose g h) = compose (compose f g) h
