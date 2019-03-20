> module MonoidalCategory
>
> import Category
> import Functor
> import NaturalIsomorphism
> import NaturalTransformation
> import ProductCategory
> import ProductFunctor
> import Utils
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
> leftIdTensor :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory cat cat) cat)
>   -> (unit : obj cat)
>   -> CFunctor cat cat
> leftIdTensor cat tensor unit = MkCFunctor
>   (\a => mapObj tensor (unit, a))
>   (\a, b, f => mapMor tensor (unit, a) (unit, b) (MkProductMorphism (identity cat unit) f))
>   (\a => preserveId tensor (unit, a))
>   (\a, b, c, f, g => trans (cong {f = mapMor tensor (unit, a) (unit, c)}
>                                  (cong2 {f = MkProductMorphism}
>                                         (sym (leftIdentity cat unit unit (identity cat unit)))
>                                         Refl))
>                            (preserveCompose tensor
>                                             (unit, a)
>                                             (unit, b)
>                                             (unit, c)
>                                             (MkProductMorphism (identity cat unit) f)
>                                             (MkProductMorphism (identity cat unit) g)))
>
> rightIdTensor :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory cat cat) cat)
>   -> (unit : obj cat)
>   -> CFunctor cat cat
> rightIdTensor cat tensor unit = MkCFunctor
>   (\a => mapObj tensor (a, unit))
>   (\a, b, f => mapMor tensor (a, unit) (b, unit) (MkProductMorphism f (identity cat unit)))
>   (\a => preserveId tensor (a, unit))
>   (\a, b, c, f, g => trans (cong {f = mapMor tensor (a, unit) (c, unit)}
>                                  (cong2 {f = MkProductMorphism}
>                                         Refl
>                                         (sym (leftIdentity cat unit unit (identity cat unit)))))
>                            (preserveCompose tensor
>                                             (a, unit)
>                                             (b, unit)
>                                             (c, unit)
>                                             (MkProductMorphism f (identity cat unit))
>                                             (MkProductMorphism g (identity cat unit))))
>
> MonoidalPentagon :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory cat cat) cat)
>   -> (associator : NaturalIsomorphism (productCategory cat (productCategory cat cat))
>                                       cat
>                                       (leftTensor3  cat tensor)
>                                       (rightTensor3 cat tensor))
>   -> (a, b, c, d : obj cat)
>   -> Type
>
> MonoidalTriangle :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory cat cat) cat)
>   -> (unit : obj cat)
>   -> (associator : NaturalIsomorphism (productCategory cat (productCategory cat cat))
>                                       cat
>                                       (leftTensor3  cat tensor)
>                                       (rightTensor3 cat tensor))
>   -> (leftUnitor  : NaturalIsomorphism cat cat (leftIdTensor  cat tensor unit) idFunctor)
>   -> (rightUnitor : NaturalIsomorphism cat cat (rightIdTensor cat tensor unit) idFunctor)
>   -> (a, b : obj cat)
>   -> Type
> MonoidalTriangle cat tensor unit associator leftUnitor rightUnitor a b =
>   (mapMor tensor
>           (mapObj tensor (a, unit), b)
>           (a, b)
>           (MkProductMorphism (component (natTrans rightUnitor) a) ?er)) =

-->           (MkProductMorphism (component (natTrans rightUnitor) a) (identity cat b))) =

>   (compose cat
>            (mapObj tensor (mapObj tensor (a, unit), b))
>            (mapObj tensor (a, mapObj tensor (unit, b)))
>            (mapObj tensor (a, b))
>            (component (natTrans associator) (a, unit, b))
>            ?asdf)

-- >            (mapMor tensor
-- >                    (mapObj tensor (a, mapObj tensor (unit, b)))
-- >                    (mapObj tensor (a, b))
-- >                    (MkProductMorphism (identity cat a) (component (natTrans leftUnitor) b))))

>
> -- we are not using a record here because compilation does not terminate in that case
> data MonoidalCategory : Type where
>   MkMonoidalCategory :
>        (cat : Category)
>     -> (tensor : CFunctor (productCategory cat cat) cat)
>     -> (unit : obj cat)
>     -> (associator : NaturalIsomorphism (productCategory cat (productCategory cat cat))
>                                         cat
>                                         (leftTensor3  cat tensor)
>                                         (rightTensor3 cat tensor))
>     -> (leftUnitor  : NaturalIsomorphism cat cat (leftIdTensor  cat tensor unit) idFunctor)
>     -> (rightUnitor : NaturalIsomorphism cat cat (rightIdTensor cat tensor unit) idFunctor)
>     -> ((a, b, c, d : obj cat) -> MonoidalPentagon cat tensor associator a b c d)
>     -> ((a, b : obj cat) -> MonoidalTriangle cat tensor unit associator leftunitor rightUnitor a b)
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
