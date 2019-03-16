> module MonoidalCategory
>
> import Category
> import Functor
> import NaturalIsomorphism
> import ProductCategory
> import ProductFunctor
>
> %access public export
> %default total
>
> leftTensor3' :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory cat cat) cat)
>   -> CFunctor (productCategory (productCategory cat cat) cat) cat
> leftTensor3' cat tensor = functorComposition (productCategory (productCategory cat cat) cat)
>                                              (productCategory cat cat)
>                                              cat
>                                              (productFunctor tensor (idFunctor cat))
>                                              tensor
>
> leftTensor3 :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory cat cat) cat)
>   -> CFunctor (productCategory cat (productCategory cat cat)) cat
> leftTensor3 cat tensor = functorComposition (productCategory cat (productCategory cat cat))
>                                             (productCategory (productCategory cat cat) cat)
>                                             cat
>                                             (productAssociator cat cat cat)
>                                             (leftTensor3' cat tensor)
>
> rightTensor3 :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory cat cat) cat)
>   -> CFunctor (productCategory cat (productCategory cat cat)) cat
> rightTensor3 cat tensor = functorComposition (productCategory cat (productCategory cat cat))
>                                              (productCategory cat cat)
>                                              cat
>                                              (productFunctor (idFunctor cat) tensor)
>                                              tensor
>
> -- we are not using a record here because compilation does not terminate in that case
> data MonoidalCategory : Type where
>   MkMonoidalCategory :
>        (cat : Category)
>     -> (tensor : CFunctor (productCategory cat cat) cat)
>     -> (unit : obj cat)
>     -> (associator : NaturalIsomorphism (productCategory cat (productCategory cat cat)) cat (leftTensor3  cat tensor) (rightTensor3 cat tensor))
>     -> MonoidalCategory

-- >
-- > record MonoidalCategory where
-- >   constructor MkMonoidalCategory
-- >   cat : Category
-- >   tensor : CFunctor (productCategory cat cat) cat
-- >   unit : obj cat
-- >   associator : NaturalIsomorphism (productCategory3 cat cat cat) cat
-- >                                   (leftTensor3  cat tensor)
-- >                                   (rightTensor3 cat tensor)
-- >   tensorIsLeftUnital  : (a : obj cat) -> (mapObj tensor) (unit, a) = a
-- >   tensorIsRightUnital : (a : obj cat) -> (mapObj tensor) (a, unit) = a
-- >   tensorIsAssociativeObj : (a, b, c : obj cat) -> let mo = mapObj tensor in
-- >                            mo (a, mo (b, c)) = mo (mo (a, b), c)
-- >   tensorIsAssociativeMor : (a, b, c, d, e, f : obj cat)
-- >                         -> (g : mor cat a b)
-- >                         -> (h : mor cat c d)
-- >                         -> (k : mor cat e f)
-- >                         -> let
-- >                              mo = mapObj tensor
-- >                              mm = mapMor tensor
-- >                            in
-- >                           mm (a, mo (c,e)) (b, mo (d,f)) (MkProductMorphism g (mm (c,e) (d,f) (MkProductMorphism h k)))
-- >                         = mm (mo (a,c), e) (mo (b,d), f) (MkProductMorphism (mm (a,c) (b,d) (MkProductMorphism g h)) k)
