module ProductCategory

import Category
import Utils

data ProductMorphism : {morphism : object -> object -> Type} -> {morphism' : object' -> object' -> Type} -> (x, y : (object, object')) -> Type where
  MkProductMorphism : {morphism : object -> object -> Type} -> {morphism' : object' -> object' -> Type} -> morphism (fst x) (fst y) -> morphism' (snd x) (snd y) -> ProductMorphism {morphism} {morphism'} x y

identity : (Category object morphism, Category object' morphism') => (x : (object, object')) -> ProductMorphism {morphism} {morphism'} x x
identity x = MkProductMorphism (identity (fst x)) (identity (snd x))

compose : (Category object morphism, Category object' morphism') =>
  ProductMorphism {morphism} {morphism'} x y ->
  ProductMorphism {morphism} {morphism'} y z ->
  ProductMorphism {morphism} {morphism'} x z
compose (MkProductMorphism f g) (MkProductMorphism h i) = MkProductMorphism {morphism} {morphism'} (compose f h) (compose g i)

identityLeft : (Category object morphism, Category object' morphism') => (f : ProductMorphism {morphism} {morphism'} x y) -> compose (identity x) f = f
identityLeft (MkProductMorphism g h) = cong2 {f = MkProductMorphism} (identityLeft g) (identityLeft h)

identityRight : (Category object morphism, Category object' morphism') => (f : ProductMorphism {morphism} {morphism'} x y) -> compose f (identity y) = f
identityRight (MkProductMorphism g h) = cong2 {f = MkProductMorphism} (identityRight g) (identityRight h)

associativity : (Category object morphism, Category object' morphism') =>
  (f : ProductMorphism {morphism} {morphism'} x y) ->
  (g : ProductMorphism {morphism} {morphism'} y z) ->
  (h : ProductMorphism {morphism} {morphism'} z w) ->
  compose f (compose g h) = compose (compose f g) h
associativity (MkProductMorphism i j) (MkProductMorphism k l) (MkProductMorphism m n) = cong2 {f = MkProductMorphism} (associativity i k m) (associativity j l n)

(Category object morphism, Category object' morphism') => Category (object, object') (ProductMorphism {morphism} {morphism'}) where
  identity = identity {morphism} {morphism'}
  compose = compose {morphism} {morphism'}
  identityLeft = identityLeft
  identityRight = identityRight
  associativity = associativity
