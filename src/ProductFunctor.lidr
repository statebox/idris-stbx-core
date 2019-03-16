> module ProductFunctor
>
> import Category
> import Functor
> import ProductCategory
> import ProductCategory3
> import Utils
>
> %access public export
> %default total
>
> productFunctor :
>      {cat1, cat2, cat3, cat4 : Category}
>   -> CFunctor cat1 cat2
>   -> CFunctor cat3 cat4
>   -> CFunctor (productCategory cat1 cat3) (productCategory cat2 cat4)
> productFunctor func1 func2 = MkCFunctor
>   (\a => (mapObj func1 (fst a), mapObj func2 (snd a)))
>   (\a, b, f => MkProductMorphism (mapMor func1 (fst a) (fst b) (pi1 f)) (mapMor func2 (snd a) (snd b) (pi2 f)))
>   (\a => cong2 {f = MkProductMorphism} (preserveId func1 (fst a)) (preserveId func2 (snd a)))
>   (\a, b, c, f, g => cong2 {f = MkProductMorphism} (preserveCompose func1 (fst a) (fst b) (fst c) (pi1 f) (pi1 g))
>                                                    (preserveCompose func2 (snd a) (snd b) (snd c) (pi2 f) (pi2 g)))
>
> productFunctor2111 :
>      CFunctor (productCategory cat1 cat2) cat3
>   -> CFunctor cat4 cat5
>   -> CFunctor (productCategory3 cat1 cat2 cat4) (productCategory cat3 cat5)
> productFunctor2111 func1 func2 = MkCFunctor
>   (\a => (mapObj func1 (fst a, fst (snd a)), mapObj func2 (snd (snd a))))
>   (\a, b, f => MkProductMorphism (mapMor func1 (fst a, fst (snd a)) (fst b, fst (snd b)) (MkProductMorphism (pi1 f) (pi2 f)))
>                                  (mapMor func2 (snd (snd a)) (snd (snd b)) (pi3 f)))
>   (\a => cong2 {f = MkProductMorphism} (preserveId func1 (fst a, (fst (snd a)))) (preserveId func2 (snd (snd a))))
>   (\a, b, c, f, g => cong2 {f = MkProductMorphism}
>                            (preserveCompose func1 (fst a, fst (snd a)) (fst b, fst (snd b)) (fst c, fst (snd c)) (MkProductMorphism (pi1 f) (pi2 f)) (MkProductMorphism (pi1 g) (pi2 g)))
>                            (preserveCompose func2 (snd (snd a)) (snd (snd b)) (snd (snd c)) (pi3 f) (pi3 g)))
>
> productFunctor1121 :
>      CFunctor cat1 cat2
>   -> CFunctor (productCategory cat3 cat4) cat5
>   -> CFunctor (productCategory3 cat1 cat3 cat4) (productCategory cat2 cat5)
> productFunctor1121 func1 func2 = MkCFunctor
>   (\a => (mapObj func1 (fst a), mapObj func2 (fst (snd a),snd (snd a))))
>   (\a, b, f => MkProductMorphism (mapMor func1 (fst a) (fst b) (pi1 f))
>                                  (mapMor func2 (fst (snd a), snd (snd a)) (fst (snd b), snd (snd b)) (MkProductMorphism (pi2 f) (pi3 f))))
>   (\a => cong2 {f = MkProductMorphism} (preserveId func1 (fst a)) (preserveId func2 (fst (snd a), snd (snd a))))
>   (\a, b, c, f, g => cong2 {f = MkProductMorphism}
>                            (preserveCompose func1 (fst a) (fst b) (fst c) (pi1 f) (pi1 g))
>                            (preserveCompose func2 (fst (snd a), snd (snd a)) (fst (snd b), snd (snd b)) (fst (snd c), snd (snd c)) (MkProductMorphism (pi2 f) (pi3 f)) (MkProductMorphism (pi2 g) (pi3 g))))
