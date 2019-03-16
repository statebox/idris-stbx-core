> module ProductCategory
>
> import Category
> import Functor
> import Utils
>
> %access public export
> %default total
>
> record ProductMorphism
>   (cat1 : Category)
>   (cat2 : Category)
>   (a : (obj cat1, obj cat2))
>   (b : (obj cat1, obj cat2))
>   where
>     constructor MkProductMorphism
>     pi1 : mor cat1 (fst a) (fst b)
>     pi2 : mor cat2 (snd a) (snd b)
>
> productIdentity :
>      {cat1, cat2 : Category}
>   -> (a : (obj cat1, obj cat2))
>   -> ProductMorphism cat1 cat2 a a
> productIdentity {cat1} {cat2} a = MkProductMorphism (identity cat1 (fst a)) (identity cat2 (snd a))
>
> productCompose :
>      {cat1, cat2 : Category}
>   -> (a, b, c : (obj cat1, obj cat2))
>   -> (f : ProductMorphism cat1 cat2 a b)
>   -> (g : ProductMorphism cat1 cat2 b c)
>   -> ProductMorphism cat1 cat2 a c
> productCompose {cat1} {cat2} a b c f g = MkProductMorphism
>   (compose cat1 (fst a) (fst b) (fst c) (pi1 f) (pi1 g))
>   (compose cat2 (snd a) (snd b) (snd c) (pi2 f) (pi2 g))
>
> productLeftIdentity :
>      {cat1, cat2 : Category}
>   -> (a, b : (obj cat1, obj cat2))
>   -> (f : ProductMorphism cat1 cat2 a b)
>   -> productCompose a a b (productIdentity a) f = f
> productLeftIdentity {cat1} {cat2} a b (MkProductMorphism f1 f2)
>   = cong2 {f = MkProductMorphism} (leftIdentity cat1 (fst a) (fst b) f1) (leftIdentity cat2 (snd a) (snd b) f2)
>
> productRightIdentity :
>      {cat1, cat2 : Category}
>   -> (a, b : (obj cat1, obj cat2))
>   -> (f : ProductMorphism cat1 cat2 a b)
>   -> productCompose a b b f (productIdentity b) = f
> productRightIdentity {cat1} {cat2} a b (MkProductMorphism f1 f2)
>   = cong2 {f = MkProductMorphism} (rightIdentity cat1 (fst a) (fst b) f1) (rightIdentity cat2 (snd a) (snd b) f2)
>
> productAssociativity :
>      {cat1, cat2 : Category}
>   -> (a, b, c, d : (obj cat1, obj cat2))
>   -> (f : ProductMorphism cat1 cat2 a b)
>   -> (g : ProductMorphism cat1 cat2 b c)
>   -> (h : ProductMorphism cat1 cat2 c d)
>   -> productCompose a b d f (productCompose b c d g h) = productCompose a c d (productCompose a b c f g) h
> productAssociativity {cat1} {cat2} a b c d f g h = cong2 {f = MkProductMorphism}
>   (associativity cat1 (fst a) (fst b) (fst c) (fst d) (pi1 f) (pi1 g) (pi1 h))
>   (associativity cat2 (snd a) (snd b) (snd c) (snd d) (pi2 f) (pi2 g) (pi2 h))
>
> productCategory : (cat1, cat2 : Category) -> Category
> productCategory cat1 cat2 = MkCategory
>   (obj cat1, obj cat2)
>   (ProductMorphism cat1 cat2)
>   (productIdentity {cat1} {cat2})
>   (productCompose {cat1} {cat2})
>   (productLeftIdentity {cat1} {cat2})
>   (productRightIdentity {cat1} {cat2})
>   (productAssociativity {cat1} {cat2})
>
> productAssociator :
>      (cat1, cat2, cat3 : Category)
>   -> CFunctor (productCategory cat1 (productCategory cat2 cat3)) (productCategory (productCategory cat1 cat2) cat3)
> productAssociator cat1 cat2 cat3 = MkCFunctor
>   (\o => ((fst o, fst (snd o)), (snd (snd o))))
>   (\abc1, abc2, m => MkProductMorphism (MkProductMorphism (pi1 m) (pi1 (pi2 m))) (pi2 (pi2 m)))
>   (\o => Refl)
>   (\a1, a2, c, f, g => Refl)
