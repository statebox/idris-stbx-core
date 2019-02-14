> module MonoidalCategory
> 
> import Category
> import Functor
> import ProductCategory
> 
> %access public export
> %default total
> 
> record StrictMonoidalCategory where
>   constructor MkStrictMonoidalCategory
>   cat : Category
>   tensor : CFunctor (productCategory cat cat) cat
>   unit : obj cat
>   tensorIsLeftUnital  : (a : obj cat) -> (mapObj tensor) (unit, a) = a
>   tensorIsRightUnital : (a : obj cat) -> (mapObj tensor) (a, unit) = a
>   tensorIsAssociativeObj : (a, b, c : obj cat) -> let mo = mapObj tensor in
>                            mo (a, mo (b, c)) = mo (mo (a, b), c)
>   tensorIsAssociativeMor : (a, b, c, d, e, f : obj cat)
>                         -> (g : mor cat a b)
>                         -> (h : mor cat c d)
>                         -> (k : mor cat e f)
>                         -> let
>                              mo = mapObj tensor
>                              mm = mapMor tensor
>                            in
>                           mm (a, mo (c,e)) (b, mo (d,f)) (MkProductMorphism g (mm (c,e) (d,f) (MkProductMorphism h k)))
>                         = mm (mo (a,c), e) (mo (b,d), f) (MkProductMorphism (mm (a,c) (b,d) (MkProductMorphism g h)) k)
