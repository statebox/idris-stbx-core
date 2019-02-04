module PointedTypes.PointedTypesCategory

import Category

%access public export
%default total

PointedObject : Type
PointedObject = (a : Type ** a)

data PointedMorphism : (a, b : PointedObject) -> Type where
  MkPointedMorphism : (x : a) -> (y : b) -> (f : a -> b) -> f x = y -> PointedMorphism (a ** x) (b ** y)

identity : (a : PointedObject) -> PointedMorphism a a
identity (a' ** x) = MkPointedMorphism x x id Refl

compose : (a, b, c : PointedObject) -> (f : PointedMorphism a b) -> (g : PointedMorphism b c) -> PointedMorphism a c
compose
  (a' ** x)
  (b' ** y)
  (c' ** z)
  (MkPointedMorphism x y f' fxy)
  (MkPointedMorphism y z g' gyz)
  = MkPointedMorphism x z (g' . f') (trans (cong {f = g'} fxy) gyz)

leftReflId : (p : x = y) -> trans Refl p = p
leftReflId Refl = Refl

leftIdentity :
     (a, b : PointedObject)
  -> (f : PointedMorphism a b)
  -> compose a a b (identity a) f = f
leftIdentity
  (a' ** x)
  (b' ** y)
  (MkPointedMorphism x y f' fxy)
  = cong {f = MkPointedMorphism x y f'} (leftReflId fxy)

rightReflId : (p : x = y) -> trans p Refl = p
rightReflId Refl = Refl

congId : (p : x = y) -> cong {f = Basics.id} p = p
congId Refl = Refl

rightIdentity :
     (a, b : PointedObject)
  -> (f : PointedMorphism a b)
  -> compose a b b f (identity b) = f
rightIdentity
  (a' ** x)
  (b' ** y)
  (MkPointedMorphism x y f' fxy)
  = cong {f = MkPointedMorphism x y f'} (trans (rightReflId (cong {f = id} fxy)) (congId fxy))

transCongAssociacivity :
     (f : a -> b)
  -> (g : b -> c)
  -> (h : c -> d)
  -> (fxy : f x = y)
  -> (gyw : g y = w)
  -> (hwz : h w = z)
  -> trans
      (cong {f = h . g} fxy)
      (trans (cong {f = h} gyw) hwz)
    = trans
      (cong {f = h} (trans (cong {f = g} fxy) gyw)) hwz
transCongAssociacivity f g h Refl Refl Refl = Refl

associativity :
     (a, b, c, d : PointedObject)
  -> (f : PointedMorphism a b)
  -> (g : PointedMorphism b c)
  -> (h : PointedMorphism c d)
  -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h
associativity
  (a' ** x)
  (b' ** y)
  (c' ** w)
  (d' ** z)
  (MkPointedMorphism x y f' fxy)
  (MkPointedMorphism y w g' gyw)
  (MkPointedMorphism w z h' hwz)
  = cong {f = MkPointedMorphism x z (h' . g' . f')} (transCongAssociacivity f' g' h' fxy gyw hwz)

pointedTypesCategory : VerifiedCategory PointedObject PointedMorphism
pointedTypesCategory = MkVerifiedCategory
  (MkCategory identity compose)
  leftIdentity
  rightIdentity
  associativity
