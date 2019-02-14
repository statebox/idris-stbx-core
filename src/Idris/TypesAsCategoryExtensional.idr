module Idris.TypesAsCategoryExtensional

import Category

%access public export
%default total

record ExtensionalTypeMorphism (a : Type) (b : Type) where
  constructor MkExtensionalTypeMorphism
  func : a -> b

funExt : {a, b : Type} -> {f, g : ExtensionalTypeMorphism a b} -> ((x : a) -> func f x = func g x) -> f = g
funExt fxgx = really_believe_me fxgx

extIdentity : (a : Type) -> ExtensionalTypeMorphism a a
extIdentity a = MkExtensionalTypeMorphism (\x => x)

extCompose :
     (a, b, c : Type)
  -> (f : ExtensionalTypeMorphism a b)
  -> (g : ExtensionalTypeMorphism b c)
  -> ExtensionalTypeMorphism a c
extCompose a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g)
  = MkExtensionalTypeMorphism (\x  => g (f x))

extLeftIdentity :
     (a, b : Type)
  -> (f : ExtensionalTypeMorphism a b)
  -> extCompose a a b (extIdentity a) f = f
extLeftIdentity a b (MkExtensionalTypeMorphism func) = Refl

extRightIdentity :
     (a, b : Type)
  -> (f : ExtensionalTypeMorphism a b)
  -> extCompose a b b f (extIdentity b) = f
extRightIdentity a b (MkExtensionalTypeMorphism func) = Refl

extAssociativity :
     (a, b, c, d : Type)
  -> (f : ExtensionalTypeMorphism a b)
  -> (g : ExtensionalTypeMorphism b c)
  -> (h : ExtensionalTypeMorphism c d)
  -> extCompose a b d f (extCompose b c d g h) = extCompose a c d (extCompose a b c f g) h
extAssociativity a b c d (MkExtensionalTypeMorphism func) (MkExtensionalTypeMorphism gunc) (MkExtensionalTypeMorphism hunc) = Refl

typesAsCategoryExtensional : Category
typesAsCategoryExtensional = MkCategory
  Type
  ExtensionalTypeMorphism
  extIdentity
  extCompose
  extLeftIdentity
  extRightIdentity
  extAssociativity
