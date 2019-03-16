> module ProductCategory3
>
> import Category
> import Functor
> import Utils
>
> %access public export
> %default total
>
> record ProductMorphism3
>   (cat1 : Category)
>   (cat2 : Category)
>   (cat3 : Category)
>   (a : (obj cat1, obj cat2, obj cat3))
>   (b : (obj cat1, obj cat2, obj cat3))
>   where
>     constructor MkProductMorphism3
>     pi1 : mor cat1 (fst a) (fst b)
>     pi2 : mor cat2 (fst (snd a)) (fst (snd b))
>     pi3 : mor cat3 (snd (snd a)) (snd (snd b))
>
> productIdentity3 :
>      {cat1, cat2, cat3 : Category}
>   -> (a : (obj cat1, obj cat2, obj cat3))
>   -> ProductMorphism3 cat1 cat2 cat3 a a
> productIdentity3 {cat1} {cat2} {cat3} a = MkProductMorphism3 (identity cat1 (fst a)) (identity cat2 (fst (snd a))) (identity cat3 (snd (snd a)))
>
> productCompose3 :
>      {cat1, cat2, cat3 : Category}
>   -> (a, b, c : (obj cat1, obj cat2, obj cat3))
>   -> (f : ProductMorphism3 cat1 cat2 cat3 a b)
>   -> (g : ProductMorphism3 cat1 cat2 cat3 b c)
>   -> ProductMorphism3 cat1 cat2 cat3 a c
> productCompose3 {cat1} {cat2} {cat3} a b c f g = MkProductMorphism3
>   (compose cat1 (fst a) (fst b) (fst c) (pi1 f) (pi1 g))
>   (compose cat2 (fst (snd a)) (fst (snd b)) (fst (snd c)) (pi2 f) (pi2 g))
>   (compose cat3 (snd (snd a)) (snd (snd b)) (snd (snd c)) (pi3 f) (pi3 g))
>
> productLeftIdentity3 :
>      {cat1, cat2, cat3 : Category}
>   -> (a, b : (obj cat1, obj cat2, obj cat3))
>   -> (f : ProductMorphism3 cat1 cat2 cat3 a b)
>   -> productCompose3 a a b (productIdentity3 a) f = f
> productLeftIdentity3 {cat1} {cat2} {cat3} a b (MkProductMorphism3 f1 f2 f3)
>   = cong3 {f = MkProductMorphism3}
>           (leftIdentity cat1 (fst a) (fst b) f1)
>           (leftIdentity cat2 (fst (snd a)) (fst (snd b)) f2)
>           (leftIdentity cat3 (snd (snd a)) (snd (snd b)) f3)
>
> productRightIdentity3 :
>      {cat1, cat2, cat3 : Category}
>   -> (a, b : (obj cat1, obj cat2, obj cat3))
>   -> (f : ProductMorphism3 cat1 cat2 cat3 a b)
>   -> productCompose3 a b b f (productIdentity3 b) = f
> productRightIdentity3 {cat1} {cat2} {cat3} a b (MkProductMorphism3 f1 f2 f3)
>   = cong3 {f = MkProductMorphism3}
>           (rightIdentity cat1 (fst a) (fst b) f1)
>           (rightIdentity cat2 (fst (snd a)) (fst (snd b)) f2)
>           (rightIdentity cat3 (snd (snd a)) (snd (snd b)) f3)
>
> productAssociativity3 :
>      {cat1, cat2, cat3 : Category}
>   -> (a, b, c, d : (obj cat1, obj cat2, obj cat3))
>   -> (f : ProductMorphism3 cat1 cat2 cat3 a b)
>   -> (g : ProductMorphism3 cat1 cat2 cat3 b c)
>   -> (h : ProductMorphism3 cat1 cat2 cat3 c d)
>   -> productCompose3 a b d f (productCompose3 b c d g h) = productCompose3 a c d (productCompose3 a b c f g) h
> productAssociativity3 {cat1} {cat2} {cat3} a b c d f g h
>   = cong3 {f = MkProductMorphism3}
>           (associativity cat1 (fst a) (fst b) (fst c) (fst d) (pi1 f) (pi1 g) (pi1 h))
>           (associativity cat2 (fst (snd a)) (fst (snd b)) (fst (snd c)) (fst (snd d)) (pi2 f) (pi2 g) (pi2 h))
>           (associativity cat3 (snd (snd a)) (snd (snd b)) (snd (snd c)) (snd (snd d)) (pi3 f) (pi3 g) (pi3 h))
>
> productCategory3 : (cat1, cat2, cat3 : Category) -> Category
> productCategory3 cat1 cat2 cat3 = MkCategory
>   (obj cat1, obj cat2, obj cat3)
>   (ProductMorphism3 cat1 cat2 cat3)
>   (productIdentity3 {cat1} {cat2} {cat3})
>   (productCompose3 {cat1} {cat2} {cat3})
>   (productLeftIdentity3 {cat1} {cat2} {cat3})
>   (productRightIdentity3 {cat1} {cat2} {cat3})
>   (productAssociativity3 {cat1} {cat2} {cat3})

-- >
-- > productAssociator :
-- >      (cat1, cat2, cat3 : Category)
-- >   -> CFunctor (productCategory (productCategory cat1 cat2) cat3) (productCategory cat1 (productCategory cat2 cat3))
-- > productAssociator cat1 cat2 cat3 = MkCFunctor
-- >   (\o => (fst (fst o), (snd (fst o), snd o)))
-- >   (\abc1, abc2, m => MkProductMorphism (pi1 (pi1 m)) (MkProductMorphism (pi2 (pi1 m)) (pi2 m)))
-- >   (\((o1, o2), o3) => Refl)
-- >   (\a1, a2, c, f, g => Refl)
