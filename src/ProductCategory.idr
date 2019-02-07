module ProductCategory

import Category
import Utils

%access public export
%default total

data ProductMorphism :
     {mor1 : obj1 -> obj1 -> Type}
  -> {mor2 : obj2 -> obj2 -> Type}
  -> (a, b : (obj1, obj2))
  -> Type
where
  MkProductMorphism :
     {mor1 : obj1 -> obj1 -> Type}
  -> {mor2 : obj2 -> obj2 -> Type}
  -> mor1 (fst a) (fst b)
  -> mor2 (snd a) (snd b)
  -> ProductMorphism {mor1} {mor2} a b

productIdentity :
     {mor1 : obj1 -> obj1 -> Type}
  -> {mor2 : obj2 -> obj2 -> Type}
  -> (identity1 : (a1 : obj1) -> mor1 a1 a1)
  -> (identity2 : (a2 : obj2) -> mor2 a2 a2)
  -> (a : (obj1, obj2))
  -> ProductMorphism {mor1} {mor2} a a
productIdentity {mor1} {mor2} identity1 identity2 a
  = MkProductMorphism {mor1} {mor2} (identity1 (fst a)) (identity2 (snd a))

productCompose :
     {mor1 : obj1 -> obj1 -> Type}
  -> {mor2 : obj2 -> obj2 -> Type}
  -> (compose1 : (a1, b1, c1 : obj1) -> (f1 : mor1 a1 b1) -> (g1 : mor1 b1 c1) -> mor1 a1 c1)
  -> (compose2 : (a2, b2, c2 : obj2) -> (f2 : mor2 a2 b2) -> (g2 : mor2 b2 c2) -> mor2 a2 c2)
  -> (a, b, c : (obj1, obj2))
  -> (f : ProductMorphism {mor1} {mor2} a b)
  -> (g : ProductMorphism {mor1} {mor2} b c)
  -> ProductMorphism {mor1} {mor2} a c
productCompose
  compose1
  compose2
  a
  b
  c
  (MkProductMorphism {mor1} {mor2} f1 f2)
  (MkProductMorphism {mor1} {mor2} g1 g2)
  = MkProductMorphism {mor1} {mor2} (compose1 (fst a) (fst b) (fst c) f1 g1) (compose2 (snd a) (snd b) (snd c) f2 g2)

productCategory :
     (cat1 : Category obj1 mor1)
  -> (cat2 : Category obj2 mor2)
  -> Category (obj1, obj2) (ProductMorphism {mor1} {mor2})
productCategory
  (MkCategory identity1 compose1)
  (MkCategory identity2 compose2)
  = MkCategory {obj = (obj1, obj2)} {mor = ProductMorphism {mor1} {mor2}}
      (productIdentity {mor1} {mor2} identity1 identity2)
      (productCompose {mor1} {mor2} compose1 compose2)

productLeftIdentity :
     {mor1 : obj1 -> obj1 -> Type}
  -> {mor2 : obj2 -> obj2 -> Type}
  -> (cat1 : VerifiedCategory obj1 mor1)
  -> (cat2 : VerifiedCategory obj2 mor2)
  -> (a, b : (obj1, obj2))
  -> (f : ProductMorphism {mor1} {mor2} a b)
  -> LeftIdentity f (productCategory (innerCategory cat1) (innerCategory cat2))
productLeftIdentity
  (MkVerifiedCategory {obj = obj1} {mor = mor1} (MkCategory _ _) leftIdentity1 _ _)
  (MkVerifiedCategory {obj = obj2} {mor = mor2} (MkCategory _ _) leftIdentity2 _ _)
  a
  b
  (MkProductMorphism {mor1} {mor2} f1 f2)
  = cong2 {f = MkProductMorphism} (leftIdentity1 (fst a) (fst b) f1) (leftIdentity2 (snd a) (snd b) f2)

productRightIdentity :
     {mor1 : obj1 -> obj1 -> Type}
  -> {mor2 : obj2 -> obj2 -> Type}
  -> (cat1 : VerifiedCategory obj1 mor1)
  -> (cat2 : VerifiedCategory obj2 mor2)
  -> (a, b : (obj1, obj2))
  -> (f : ProductMorphism {mor1} {mor2} a b)
  -> RightIdentity f (productCategory (innerCategory cat1) (innerCategory cat2))
productRightIdentity
  (MkVerifiedCategory {obj = obj1} {mor = mor1} (MkCategory _ _) _ rightIdentity1 _)
  (MkVerifiedCategory {obj = obj2} {mor = mor2} (MkCategory _ _) _ rightIdentity2 _)
  a
  b
  (MkProductMorphism {mor1} {mor2} f1 f2)
  = cong2 {f = MkProductMorphism} (rightIdentity1 (fst a) (fst b) f1) (rightIdentity2 (snd a) (snd b) f2)

productAssociativity :
     {mor1 : obj1 -> obj1 -> Type}
  -> {mor2 : obj2 -> obj2 -> Type}
  -> (cat1 : VerifiedCategory obj1 mor1)
  -> (cat2 : VerifiedCategory obj2 mor2)
  -> (a, b, c, d : (obj1, obj2))
  -> (f : ProductMorphism {mor1} {mor2} a b)
  -> (g : ProductMorphism {mor1} {mor2} b c)
  -> (h : ProductMorphism {mor1} {mor2} c d)
  -> Associativity {f} {g} {h} (productCategory (innerCategory cat1) (innerCategory cat2))
productAssociativity
  (MkVerifiedCategory {obj = obj1} {mor = mor1} (MkCategory _ _) _ _ associativity1)
  (MkVerifiedCategory {obj = obj2} {mor = mor2} (MkCategory _ _) _ _ associativity2)
  a b c d
  (MkProductMorphism {mor1} {mor2} f1 f2)
  (MkProductMorphism {mor1} {mor2} g1 g2)
  (MkProductMorphism {mor1} {mor2} h1 h2)
  = cong2 {f = MkProductMorphism}
    (associativity1 (fst a) (fst b) (fst c) (fst d) f1 g1 h1)
    (associativity2 (snd a) (snd b) (snd c) (snd d) f2 g2 h2)

productVerifiedCategory :
     (cat1 : VerifiedCategory obj1 mor1)
  -> (cat2 : VerifiedCategory obj2 mor2)
  -> VerifiedCategory (obj1, obj2) (ProductMorphism {mor1} {mor2})
productVerifiedCategory
  verCat1@(MkVerifiedCategory {obj = obj1} {mor = mor1}
    cat1@(MkCategory identity1 compose1)
    leftIdentity1
    rightIdentity1
    associativity1
  )
  verCat2@(MkVerifiedCategory {obj = obj2} {mor = mor2}
    cat2@(MkCategory identity2 compose2)
    leftIdentity2
    rightIdentity2
    associativity2
  )
  = MkVerifiedCategory
    (productCategory cat1 cat2)
    (productLeftIdentity {mor1} {mor2} verCat1 verCat2)
    (productRightIdentity {mor1} {mor2} verCat1 verCat2)
    (productAssociativity {mor1} {mor2} verCat1 verCat2)
