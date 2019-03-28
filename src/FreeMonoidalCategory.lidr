> module FreeMonoidalCategory
>
> import Data.Fin
> import Category
> import Functor
> import ProductCategory
> import Discrete.DiscreteCategory
> import StrictMonoidalCategory
> import Monoid.Monoid
> import Monoid.FreeMonoid
>
> %access public export
> %default total
>
> finSetCategory : Nat -> Category
> finSetCategory n = discreteCategory (set $ finSetToFreeMonoid n)
>
> help : (ab : (List (Fin n), List (Fin n))) -> (cd : (List (Fin n), List (Fin n))) 
>     -> ProductMorphism (finSetCategory n) (finSetCategory n) ab cd
>     -> fst ab ++ snd ab = fst cd ++ snd cd
> help (c, d) (c, d) (MkProductMorphism Refl Refl) = Refl
>
> finSetTensor : (n : Nat) -> CFunctor (productCategory (finSetCategory n) (finSetCategory n)) (finSetCategory n)
> finSetTensor n = 
>   MkCFunctor
>     (\ab => fst ab ++ snd ab)
>     help
>     (\(a, b) => Refl)
>     (\(a, b), (c, d), (e, f), (MkProductMorphism Refl Refl), (MkProductMorphism Refl Refl) => Refl)
>
> help2 : (a, b, c, d, e, f : List (Fin n)) ->
>         (g : a = b) ->
>         (h : c = d) ->
>         (k : e = f) ->
>         help (a, c ++ e) (b, d ++ f) (MkProductMorphism g (help (c, e) (d, f) (MkProductMorphism h k))) =
>         help (a ++ c, e) (b ++ d, f) (MkProductMorphism (help (a, c) (b, d) (MkProductMorphism g h)) k)
> help2 b b d d f f Refl Refl Refl  = ?wat Refl

 finSetToFMC : Nat -> StrictMonoidalCategory
 finSetToFMC n = MkStrictMonoidalCategory 
                   (finSetCategory n)
                   (finSetTensor n)
                   []
                   (\a => Refl)
                   appendNilRightNeutral
                   appendAssociative
                   help2


